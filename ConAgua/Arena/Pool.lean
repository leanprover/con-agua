module

public import ConAgua.L.Logic
public import ConAgua.Arena.GrindAttr

@[expose] public section

/-!
# The limb pool: layout, abstraction, invariant

con-ron's `ron::Nat` (`crates/con-ron-core/src/ron/nat.rs`) is a `Vec<u64>` of little-endian
limbs with no trailing zero limb. In L there are no vectors: every number lives in ONE word array,
the limb pool `POOL`, as a slice `(o, l)` (offset, length). The pool grows at the top: word 0 of
the control array `CTL` holds the top `T`; `[0, T)` is in use, `[T, len(POOL))` is free. A
function that makes a number appends its limbs at `T` and moves `T` up; nothing below `T` is
ever written again, so every slice handed out stays valid (the frame is `Agree`).

* abstraction: `pv p o l` is the number the slice `(o, l)` of the pool array `p` denotes,
  `Σ_{i<l} p[o+i] * 2^(64 i)`;
* normal form: `Norm p o l`: the slice has no trailing zero limb (con-ron's `Nat.WF`), so equal
  numbers have equal slices up to position;
* invariant of the pool (`PoolOK`): `T ≤ len(POOL) < 2^64` and `CTL` has its word.

All of this is stated over the pool *array* `p : Array Word` and Lean `Nat` positions, and the
lemmas are guarded equations about the named functions `pv`, `xv`, `lv`, registered for
`grind` with multi-patterns that bind every variable (DESIGN.md, "Proof recipe").
-/

namespace L.Arena

open L

/-- The limb pool: word array 0. -/
abbrev POOL : ArrId := 0
/-- The tier-0 pool top while the scratch tier is open (`CTL[0]` then holds the tier-1 top;
lane tierpool): saved by `scratch_reset` when it leaves tier 0, restored when it drops the
scratch tier. -/
abbrev PTOP0 : GVar := ⟨0⟩
/-- The control words: word array 1; word 0 is the pool top. -/
abbrev CTL : ArrId := 1

/-- The weight of limb `i`: `2^(64 i)`. A named function, so that `grind`'s ring solver treats
it as one atom (`2 ^ (64 * i)` is "a ring term with unexpected instance" to it). -/
def wt (i : Nat) : Nat := 2 ^ (64 * i)

/-- The abstraction: the number denoted by the `l` limbs of `p` at `o`, little-endian. -/
def pv (p : Array Word) (o : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => pv p o k + (p[o + k]?.getD 0).toNat * wt k

/-- Limb `i` of the slice `(o, l)`, zero past its end (con-ron's `limb`). -/
def lv (p : Array Word) (o l i : Nat) : Nat := if i < l then (p[o + i]?.getD 0).toNat else 0

/-- The first `k` limbs of the zero-extended slice `(o, l)`: what a loop that runs past the
shorter operand has read. -/
def xv (p : Array Word) (o l : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => xv p o l k + lv p o l k * wt k

/-- No trailing zero limb (con-ron's `Nat.WF`). -/
def Norm (p : Array Word) (o l : Nat) : Prop := 0 < l → (p[o + (l - 1)]?.getD 0) ≠ 0

/-- `p` and `q` agree below `t`: the frame of every pool operation. -/
def Agree (p q : Array Word) (t : Nat) : Prop := ∀ j, j < t → p[j]? = q[j]?

/-! ## Memory -/

/-- `m'` is `m` with at most word array `a` changed: the frame of a function that writes only
`a`. A named predicate with its own `grind` lemmas, rather than an equation
`m' = m.setArr64 a (m'.arr64 a)`, whose read-back needs `a < m.words.size` at every use. -/
def Frame (a : ArrId) (m m' : Mem) : Prop :=
  m'.bytes = m.bytes ∧ m'.words.size = m.words.size ∧ ∀ b, b ≠ a → m'.arr64 b = m.arr64 b

theorem Frame.refl (a : ArrId) (m : Mem) : Frame a m m := ⟨rfl, rfl, fun _ _ => rfl⟩
grind_pattern [arena_grind] Frame.refl => Frame a m m

theorem Frame.set64 (a : ArrId) (m m' : Mem) (i v : Word) (h : Frame a m m') :
    Frame a m (m'.set64 a i v) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, by simp [Mem.set64, h2], fun b hb => ?_⟩
  rw [← h3 b hb]
  simp only [Mem.set64, Mem.arr64, Array.getD_eq_getD_getElem?]; grind
grind_pattern [arena_grind] Frame.set64 => Frame a m (m'.set64 a i v)

theorem Frame.trans (a : ArrId) (m m' m'' : Mem) (h : Frame a m m') (h' : Frame a m' m'') :
    Frame a m m'' := by
  obtain ⟨h1, h2, h3⟩ := h; obtain ⟨h1', h2', h3'⟩ := h'
  exact ⟨h1'.trans h1, h2'.trans h2, fun b hb => (h3' b hb).trans (h3 b hb)⟩
grind_pattern [arena_grind] Frame.trans => Frame a m m'', Frame a m' m''

theorem Frame.arr64 (a b : ArrId) (m m' : Mem) (h : Frame a m m') (hb : b ≠ a) :
    m'.arr64 b = m.arr64 b := h.2.2 b hb
grind_pattern [arena_grind] Frame.arr64 => Frame a m m', m'.arr64 b

theorem Frame.size (a : ArrId) (m m' : Mem) (h : Frame a m m') : m'.words.size = m.words.size :=
  h.2.1
grind_pattern [arena_grind] Frame.size => Frame a m m', m'.words.size

theorem Frame.bytes (a : ArrId) (m m' : Mem) (h : Frame a m m') : m'.bytes = m.bytes := h.1
grind_pattern [arena_grind] Frame.bytes => Frame a m m', m'.bytes

@[arena_grind =] theorem Mem.arr64_set64_same (m : Mem) (a : ArrId) (i v : Word) :
    (m.set64 a i v).arr64 a = (m.arr64 a).set! i.toNat v := by
  simp only [Mem.set64, Mem.arr64, Array.getD_eq_getD_getElem?]
  by_cases h : a < m.words.size <;> simp [h]

@[arena_grind =] theorem Mem.arr64_set64_ne (m : Mem) (a b : ArrId) (i v : Word) (h : b ≠ a) :
    (m.set64 a i v).arr64 b = m.arr64 b := by
  simp only [Mem.set64, Mem.arr64, Array.getD_eq_getD_getElem?]
  grind

@[arena_grind =] theorem Mem.size_arr64_set64 (m : Mem) (a : ArrId) (i v : Word) :
    ((m.set64 a i v).arr64 a).size = (m.arr64 a).size := by
  rw [Mem.arr64_set64_same]; simp

@[arena_grind =] theorem Mem.words_size_set64 (m : Mem) (a : ArrId) (i v : Word) :
    (m.set64 a i v).words.size = m.words.size := by simp [Mem.set64]

@[arena_grind =] theorem Mem.bytes_set64 (m : Mem) (a : ArrId) (i v : Word) :
    (m.set64 a i v).bytes = m.bytes := rfl

theorem Frame.set64_both (a b : ArrId) (m m' : Mem) (i v : Word) (h : Frame a m m') (hb : b ≠ a) :
    Frame a (m.set64 b i v) (m'.set64 b i v) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, by simp [Mem.set64, h2], fun c hc => ?_⟩
  by_cases hcb : c = b
  · subst hcb; rw [Mem.arr64_set64_same, Mem.arr64_set64_same, h3 c hc]
  · rw [Mem.arr64_set64_ne _ _ _ _ _ hcb, Mem.arr64_set64_ne _ _ _ _ _ hcb, h3 c hc]
grind_pattern [arena_grind] Frame.set64_both => Frame a (m.set64 b i v) (m'.set64 b i v)


/-! ## The virtual pool: the pool as proofs see it (lane tierpool)

The pool is a tiered word array: tier `t` is array `tierA POOL t` (`POOL` = 0, `POOL1` = 256).
Its slices are named by *tier-tagged* addresses: bit 40 is the tier, the low 40 bits are the
index into the tier's array (`⦃x⦄.tier`, `⦃x⦄.idx`, `L/Notation.lean`). Tier 1 is the scratch
tier, open while the arena's scratch flag is set (`scratch_reset`, `Scratch.lean`): `CTL[0]` is
the top of the current tier, `PTOP0` the tier-0 top while tier 1 is open.

Proofs read the pool only through `vpool m`, an array with a word for every address below
`2^41`: `prd m x`, what the L load `POOL⦃x⦄` reads (`0` where it aborts). They bound addresses
with `pcap m` (`2^41 - 1` on a pool whose tier arrays have fewer than `2^40` words, so that a
hypothesis `pcap m < 2^64` carries the tier arrays' bound), and never unfold `vpool`/`prd`. -/

/-- The pool's tier-1 array, `tierA POOL 1`. -/
abbrev POOL1 : ArrId := 256

theorem tierA_pool0 : tierA POOL 0 = POOL := by decide
theorem tierA_pool1 : tierA POOL 1 = POOL1 := by decide

/-- The pool's tiers are its two arrays. -/
theorem tierA_pool (t : Word) : tierA POOL t = POOL ∨ tierA POOL t = POOL1 := by
  have h : (t &&& 1).toNat = 0 ∨ (t &&& 1).toNat = 1 := by
    rw [UInt64.toNat_and, UInt64.toNat_one, Nat.and_one_is_mod]; omega
  rcases h with h | h <;> simp [tierA, tierOff, h]
grind_pattern [arena_grind] tierA_pool => tierA POOL t

theorem tierA_pool_ne (t : Word) (b : ArrId) (h0 : b ≠ POOL) (h1 : b ≠ POOL1) : b ≠ tierA POOL t := by
  rcases tierA_pool t with h | h <;> rw [h] <;> assumption

@[arena_grind =] theorem tag_tier_toNat (x : Word) : (x >>> 40).toNat = x.toNat / 2 ^ 40 := by
  rw [UInt64.toNat_shiftRight]; simp [Nat.shiftRight_eq_div_pow]

theorem tag_idx_toNat (x : Word) : (x &&& 1099511627775).toNat = x.toNat % 2 ^ 40 := by
  rw [UInt64.toNat_and]
  have : (1099511627775 : Word).toNat = 2 ^ 40 - 1 := by decide
  rw [this, Nat.and_two_pow_sub_one_eq_mod]

@[arena_grind =] theorem tag_base_toNat (x : Word) :
    ((x >>> 40) <<< 40).toNat = x.toNat / 2 ^ 40 * 2 ^ 40 := by
  rw [UInt64.toNat_shiftLeft, tag_tier_toNat]
  simp only [show (40 : Word).toNat % 64 = 40 from rfl, Nat.shiftLeft_eq]
  apply Nat.mod_eq_of_lt; have := x.toNat_lt; omega

@[arena_grind =] theorem tag_off_toNat (x : Word) :
    (x - ((x >>> 40) <<< 40)).toNat = x.toNat % 2 ^ 40 := by
  have hle : ((x >>> 40) <<< 40) ≤ x := by
    rw [UInt64.le_iff_toNat_le, tag_base_toNat]; exact Nat.div_mul_le_self _ _
  rw [UInt64.toNat_sub_of_le _ _ hle, tag_base_toNat]; omega

theorem tierA_word (t : Word) (ht : t.toNat ≤ 1) :
    tierA POOL t = if t.toNat = 0 then POOL else POOL1 := by
  have e : (t &&& 1).toNat = t.toNat := by
    rw [UInt64.toNat_and, UInt64.toNat_one, Nat.and_one_is_mod]; omega
  unfold tierA tierOff; rw [e]
  by_cases h : t.toNat = 0
  · simp [h]
  · have : t.toNat = 1 := by omega
    simp [this]

theorem tierA_tag (x : Word) (hx : x.toNat < 2 ^ 41) :
    tierA POOL (x >>> 40) = if x.toNat < 2 ^ 40 then POOL else POOL1 := by
  have h1 : (x >>> 40).toNat ≤ 1 := by rw [tag_tier_toNat]; omega
  rw [tierA_word _ h1, tag_tier_toNat]
  by_cases h : x.toNat < 2 ^ 40
  · simp [h, Nat.div_eq_of_lt h]
  · have : x.toNat / 2 ^ 40 ≠ 0 := by omega
    simp [h, this]

/-- The pool word at the tagged address `x`: what the L load `POOL⦃x⦄` reads, `0` where it
aborts (and at addresses of no tier, `2^41` and up). -/
def prd (m : Mem) (x : Word) : Word :=
  if x.toNat < 2 ^ 41 then (m.arr64 (tierA POOL (x >>> 40)))[(x &&& 1099511627775).toNat]?.getD 0
  else 0

/-- The store `POOL⟨⦃x⦄.tier⟩[⦃x⦄.idx] := v` at the tagged address `x` (a model's pool write). -/
def pst (m : Mem) (x v : Word) : Mem := m.set64 (tierA POOL (x >>> 40)) (x &&& 1099511627775) v

/-- The tier arrays are below `2^40` words. -/
def PSmall (m : Mem) : Prop := (m.arr64 POOL).size < 2 ^ 40 ∧ (m.arr64 POOL1).size < 2 ^ 40

instance (m : Mem) : Decidable (PSmall m) := by unfold PSmall; infer_instance

/-- The bound of the pool's addresses: `2^41 - 1` on a pool whose tier arrays have fewer than
`2^40` words, else `2^64` (so a hypothesis `pcap m < 2^64` says the tier arrays are small). -/
def pcap (m : Mem) : Nat := if PSmall m then 2 ^ 41 - 1 else 2 ^ 64

theorem pcap_eq (m : Mem) (h : pcap m < 2 ^ 64) : pcap m = 2 ^ 41 - 1 := by
  unfold pcap at h ⊢; split <;> simp_all
grind_pattern [arena_grind] pcap_eq => pcap m

theorem pcap_small (m : Mem) (h : pcap m < 2 ^ 64) : PSmall m := by
  unfold pcap at h; split at h <;> simp_all

theorem pcap_size0 (m : Mem) (h : pcap m < 2 ^ 64) : (m.arr64 POOL).size < 2 ^ 40 :=
  (pcap_small m h).1
grind_pattern [arena_grind] pcap_size0 => pcap m, (m.arr64 POOL).size

theorem pcap_size1 (m : Mem) (h : pcap m < 2 ^ 64) : (m.arr64 POOL1).size < 2 ^ 40 :=
  (pcap_small m h).2
grind_pattern [arena_grind] pcap_size1 => pcap m, (m.arr64 POOL1).size

theorem pcap_ge (m : Mem) : 2 ^ 41 - 1 ≤ pcap m := by unfold pcap; split <;> omega

theorem pcap_of_small (m : Mem) (h : PSmall m) : pcap m = 2 ^ 41 - 1 := by simp [pcap, h]

/-- A value the kernel cannot unfold, with its equation. -/
structure Sealed (α : Type) (a : α) where
  val : α
  eq : val = a

instance (α : Type) (a : α) : Inhabited (Sealed α a) := ⟨⟨a, rfl⟩⟩

/-- `2^41`, sealed: the kernel never computes the virtual pool's `2^41` words (a proof whose
check reduces `(vpool m).size` would otherwise build them: 16 GB). -/
opaque vszS : Sealed Nat (2 ^ 41)

/-- The virtual pool's length, `2^41` (`vsz_eq`). -/
def vsz : Nat := vszS.val

theorem vsz_eq : vsz = 2 ^ 41 := vszS.eq

/-- **The virtual pool**: word `j` is `prd m j`, for every address `j` below `2^41`. -/
def vpool (m : Mem) : Array Word := Array.ofFn fun j : Fin vsz => prd m (UInt64.ofNat j)

@[arena_grind =] theorem vpool_size (m : Mem) : (vpool m).size = 2 ^ 41 := by
  rw [vpool, Array.size_ofFn, vsz_eq]

-- not `simp [vpool]`: it evaluates the `2^41`-element array
theorem vpool_getNat? (m : Mem) (j : Nat) (h : j < 2 ^ 41) :
    (vpool m)[j]? = some (prd m (UInt64.ofNat j)) := by
  have h' : j < vsz := vsz_eq ▸ h
  rw [vpool, Array.getElem?_ofFn]; simp only [h', ↓reduceDIte]

-- no tactic may unfold the `2^41`-element array
attribute [irreducible] vpool

theorem vpool_get? (m : Mem) (x : Word) (h : x.toNat < 2 ^ 41) :
    (vpool m)[x.toNat]? = some (prd m x) := by
  rw [vpool_getNat? m _ h, UInt64.ofNat_toNat]

/-- A total read of the virtual pool is `prd`. -/
theorem vpool_getD (m : Mem) (x : Word) : (vpool m)[x.toNat]?.getD 0 = prd m x := by
  by_cases h : x.toNat < 2 ^ 41
  · rw [vpool_get? m x h]; rfl
  · rw [Array.getElem?_eq_none (by rw [vpool_size]; omega)]
    simp [prd, h]
grind_pattern [arena_grind] vpool_getD => (vpool m)[x.toNat]?.getD 0

/-- An L load of the pool at the tagged address `x` (`POOL⦃x⦄`), in bounds, reads the virtual
pool. -/
theorem vpool_ld (m : Mem) (x : Word)
    (h : (x &&& 1099511627775).toNat < (m.arr64 (tierA POOL (x >>> 40))).size)
    (h' : x.toNat < (vpool m).size) :
    (m.arr64 (tierA POOL (x >>> 40)))[(x &&& 1099511627775).toNat] = (vpool m)[x.toNat] := by
  have h41 : x.toNat < 2 ^ 41 := vpool_size m ▸ h'
  have e := vpool_get? m x h41
  rw [Array.getElem?_eq_getElem h'] at e
  have e2 : prd m x = (m.arr64 (tierA POOL (x >>> 40)))[(x &&& 1099511627775).toNat] := by
    unfold prd; rw [if_pos h41, Array.getElem?_eq_getElem h]; rfl
  rw [Option.some.inj e, e2]
grind_pattern [arena_grind] vpool_ld =>
  (m.arr64 (tierA POOL (x >>> 40)))[(x &&& 1099511627775).toNat], vpool m

/-- The tagged address of index `i` of tier `t`. -/
theorem tag_of (t i : Word) (ht : t.toNat ≤ 1) (hi : i.toNat < 2 ^ 40) :
    (UInt64.ofNat (t.toNat * 2 ^ 40 + i.toNat) >>> 40) = t ∧
    (UInt64.ofNat (t.toNat * 2 ^ 40 + i.toNat) &&& 1099511627775) = i := by
  have hlt : t.toNat * 2 ^ 40 + i.toNat < 2 ^ 64 := by omega
  constructor
  · apply UInt64.toNat_inj.mp
    rw [tag_tier_toNat, UInt64.toNat_ofNat_of_lt' hlt]; omega
  · apply UInt64.toNat_inj.mp
    rw [tag_idx_toNat, UInt64.toNat_ofNat_of_lt' hlt]; omega

/-- `prd` at a `Nat` address of a tier. -/
theorem prd_nat (m : Mem) (x : Nat) (hx : x < 2 ^ 41) :
    prd m (UInt64.ofNat x) =
      (m.arr64 (if x < 2 ^ 40 then POOL else POOL1))[x % 2 ^ 40]?.getD 0 := by
  have hxw : (UInt64.ofNat x).toNat = x := UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  unfold prd
  rw [hxw, if_pos hx, tierA_tag _ (by rw [hxw]; exact hx), hxw, tag_idx_toNat, hxw]

theorem prd_set64t (m : Mem) (t i v : Word) (x : Nat) (ht : t.toNat ≤ 1)
    (hi : i.toNat < (m.arr64 (tierA POOL t)).size) (hs : (m.arr64 (tierA POOL t)).size ≤ 2 ^ 40)
    (hx : x < 2 ^ 41) :
    prd (m.set64 (tierA POOL t) i v) (UInt64.ofNat x) =
      if x = t.toNat * 2 ^ 40 + i.toNat then v else prd m (UInt64.ofNat x) := by
  rw [prd_nat _ x hx, prd_nat m x hx, tierA_word t ht]
  rw [tierA_word t ht] at hi hs
  by_cases ht0 : t.toNat = 0
  · simp only [ht0, ↓reduceIte] at hi hs ⊢
    by_cases hx0 : x < 2 ^ 40
    · simp only [hx0, ↓reduceIte, Mem.arr64_set64_same, Array.set!_eq_setIfInBounds,
        Array.getElem?_setIfInBounds]
      by_cases e : i.toNat = x % 2 ^ 40
      · have e2 : x = 0 * 2 ^ 40 + i.toNat := by omega
        rw [if_pos e, if_pos hi, if_pos e2]; rfl
      · have e2 : ¬ x = 0 * 2 ^ 40 + i.toNat := by omega
        simp only [e, e2, ↓reduceIte]
    · have e2 : ¬ x = 0 * 2 ^ 40 + i.toNat := by omega
      simp only [hx0, e2, ↓reduceIte, Mem.arr64_set64_ne _ _ _ _ _ (show POOL1 ≠ POOL by decide)]
  · have ht1 : t.toNat = 1 := by omega
    simp only [ht0, ↓reduceIte] at hi hs ⊢
    by_cases hx0 : x < 2 ^ 40
    · have e2 : ¬ x = t.toNat * 2 ^ 40 + i.toNat := by omega
      simp only [hx0, e2, ↓reduceIte, Mem.arr64_set64_ne _ _ _ _ _ (show POOL ≠ POOL1 by decide)]
    · simp only [hx0, ↓reduceIte, Mem.arr64_set64_same, Array.set!_eq_setIfInBounds,
        Array.getElem?_setIfInBounds]
      by_cases e : i.toNat = x % 2 ^ 40
      · have e2 : x = t.toNat * 2 ^ 40 + i.toNat := by omega
        rw [if_pos e, if_pos hi, if_pos e2]; rfl
      · have e2 : ¬ x = t.toNat * 2 ^ 40 + i.toNat := by omega
        simp only [e, e2, ↓reduceIte]

/-- **An L store into the pool** (`POOL⟨t⟩[i] := v`), in bounds, is a store into the virtual pool
at the tagged address `t·2^40 + i`. -/
theorem vpool_set64t (m : Mem) (t i v : Word) (ht : t.toNat ≤ 1)
    (hi : i.toNat < (m.arr64 (tierA POOL t)).size) (hs : (m.arr64 (tierA POOL t)).size ≤ 2 ^ 40) :
    vpool (m.set64 (tierA POOL t) i v) = (vpool m).set! (t.toNat * 2 ^ 40 + i.toNat) v := by
  apply Array.ext_getElem?
  intro j
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  by_cases hj : j < 2 ^ 41
  · rw [vpool_getNat? _ j hj, vpool_getNat? m j hj, prd_set64t m t i v j ht hi hs hj]
    have hb : t.toNat * 2 ^ 40 + i.toNat < (vpool m).size := by rw [vpool_size]; omega
    by_cases e : t.toNat * 2 ^ 40 + i.toNat = j
    · subst e; simp [hb]
    · simp [e, Ne.symm e]
  · have e1 : (vpool (m.set64 (tierA POOL t) i v))[j]? = none :=
      Array.getElem?_eq_none (by rw [vpool_size]; omega)
    have e2 : (vpool m)[j]? = none := Array.getElem?_eq_none (by rw [vpool_size]; omega)
    have hij : t.toNat * 2 ^ 40 + i.toNat ≠ j := by omega
    simp [e1, e2, hij]
grind_pattern [arena_grind] vpool_set64t => vpool (m.set64 (tierA POOL t) i v)

/-- An L load of the pool's tier `t` at index `i` (`POOL⟨t⟩[i]`), in bounds, reads the virtual
pool at the tagged address `t·2^40 + i`. -/
theorem vpool_ldt (m : Mem) (t i : Word) (ht : t.toNat ≤ 1)
    (hi : i.toNat < (m.arr64 (tierA POOL t)).size) (hs : (m.arr64 (tierA POOL t)).size ≤ 2 ^ 40)
    (h' : t.toNat * 2 ^ 40 + i.toNat < (vpool m).size) :
    (m.arr64 (tierA POOL t))[i.toNat] = (vpool m)[t.toNat * 2 ^ 40 + i.toNat] := by
  have hx : t.toNat * 2 ^ 40 + i.toNat < 2 ^ 41 := by omega
  have e := vpool_getNat? m _ hx
  rw [Array.getElem?_eq_getElem h'] at e
  have key : (m.arr64 (tierA POOL t))[i.toNat]?.getD 0 = prd m (UInt64.ofNat (t.toNat * 2 ^ 40 + i.toNat)) := by
    rw [prd_nat m _ hx, tierA_word t ht]
    have hs' := hs; rw [tierA_word t ht] at hs'
    by_cases ht0 : t.toNat = 0
    · have h1 : t.toNat * 2 ^ 40 + i.toNat < 2 ^ 40 := by omega
      have h2 : (t.toNat * 2 ^ 40 + i.toNat) % 2 ^ 40 = i.toNat := by omega
      simp only [h1, h2, ↓reduceIte]; simp only [ht0, ↓reduceIte]
    · have h1 : ¬ t.toNat * 2 ^ 40 + i.toNat < 2 ^ 40 := by omega
      have h2 : (t.toNat * 2 ^ 40 + i.toNat) % 2 ^ 40 = i.toNat := by omega
      simp only [h1, h2, ↓reduceIte]; simp only [ht0, ↓reduceIte]
  rw [Array.getElem?_eq_getElem hi, Option.getD_some] at key
  rw [key]; exact (Option.some.inj e).symm

/-- A writer's store `POOL⟨⦃T⦄.tier⟩[(T - ⦃T⦄.base) + k] := v` (`T` its top, the tier and the
relative base decoded once) is a store into the virtual pool at `T + k`. -/
theorem tag_rel (T k : Word) (hT : T.toNat < 2 ^ 41)
    (hk : (T - ((T >>> 40) <<< 40)).toNat + k.toNat < 2 ^ 40) :
    (T >>> 40).toNat * 2 ^ 40 + (T - ((T >>> 40) <<< 40) + k).toNat = (T + k).toNat := by
  have hb : ((T >>> 40) <<< 40).toNat = T.toNat / 2 ^ 40 * 2 ^ 40 := by
    rw [UInt64.toNat_shiftLeft, tag_tier_toNat]
    simp only [show (40 : Word).toNat % 64 = 40 from rfl, Nat.shiftLeft_eq]
    apply Nat.mod_eq_of_lt; omega
  have hle : ((T >>> 40) <<< 40) ≤ T := by
    rw [UInt64.le_iff_toNat_le, hb]; exact Nat.div_mul_le_self _ _
  have hsub : (T - ((T >>> 40) <<< 40)).toNat = T.toNat % 2 ^ 40 := by
    rw [UInt64.toNat_sub_of_le _ _ hle, hb]; omega
  have e1 : (T - ((T >>> 40) <<< 40) + k).toNat = T.toNat % 2 ^ 40 + k.toNat := by
    rw [UInt64.toNat_add, hsub]; rw [hsub] at hk; exact Nat.mod_eq_of_lt (by omega)
  have e2 : (T + k).toNat = T.toNat + k.toNat := by
    rw [UInt64.toNat_add]; rw [hsub] at hk; exact Nat.mod_eq_of_lt (by omega)
  rw [tag_tier_toNat, e1, e2]; omega
grind_pattern [arena_grind] tag_rel => (T - ((T >>> 40) <<< 40) + k).toNat

/-- A writer's store `POOL⟨⦃T⦄.tier⟩[(T - ⦃T⦄.base) + k] := v`, in bounds, is a store into the
virtual pool at `T + k`. -/
theorem vpool_strel (m : Mem) (T k v : Word) (hT : T.toNat < 2 ^ 41)
    (hi : (T - ((T >>> 40) <<< 40) + k).toNat < (m.arr64 (tierA POOL (T >>> 40))).size)
    (hs : (m.arr64 (tierA POOL (T >>> 40))).size ≤ 2 ^ 40)
    (hk : (T - ((T >>> 40) <<< 40)).toNat + k.toNat < 2 ^ 40) :
    vpool (m.set64 (tierA POOL (T >>> 40)) (T - ((T >>> 40) <<< 40) + k) v) =
      (vpool m).set! (T + k).toNat v := by
  have ht : (T >>> 40).toNat ≤ 1 := by rw [tag_tier_toNat]; omega
  rw [vpool_set64t m _ _ v ht hi hs, tag_rel T k hT hk]
grind_pattern [arena_grind] vpool_strel =>
  vpool (m.set64 (tierA POOL (T >>> 40)) (T - ((T >>> 40) <<< 40) + k) v)

/-- A writer's load `POOL⟨⦃T⦄.tier⟩[(T - ⦃T⦄.base) + k]` (its top `T`, the tier and the relative
base decoded once), in bounds, reads the virtual pool at `T + k`. -/
theorem vpool_ldrel (m : Mem) (T k : Word) (hT : T.toNat < 2 ^ 41)
    (hi : (T - ((T >>> 40) <<< 40) + k).toNat < (m.arr64 (tierA POOL (T >>> 40))).size)
    (hs : (m.arr64 (tierA POOL (T >>> 40))).size ≤ 2 ^ 40)
    (hk : (T - ((T >>> 40) <<< 40)).toNat + k.toNat < 2 ^ 40)
    (h' : (T + k).toNat < (vpool m).size) :
    (m.arr64 (tierA POOL (T >>> 40)))[(T - ((T >>> 40) <<< 40) + k).toNat] = (vpool m)[(T + k).toNat] := by
  have ht : (T >>> 40).toNat ≤ 1 := by rw [tag_tier_toNat]; omega
  have e := tag_rel T k hT hk
  rw [vpool_ldt m _ _ ht hi hs (by rw [e]; exact h')]
  simp only [e]
grind_pattern [arena_grind] vpool_ldrel =>
  (m.arr64 (tierA POOL (T >>> 40)))[(T - ((T >>> 40) <<< 40) + k).toNat], vpool m

/-- A pool store leaves the other words of the virtual pool alone. -/
theorem vpool_set64t_get (m : Mem) (t i v : Word) (j : Nat) (ht : t.toNat ≤ 1)
    (hi : i.toNat < (m.arr64 (tierA POOL t)).size) (hs : (m.arr64 (tierA POOL t)).size ≤ 2 ^ 40)
    (hij : t.toNat * 2 ^ 40 + i.toNat ≠ j) :
    (vpool (m.set64 (tierA POOL t) i v))[j]? = (vpool m)[j]? := by
  rw [vpool_set64t m t i v ht hi hs, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  simp [hij]

/-- Stores elsewhere leave the virtual pool alone. -/
theorem vpool_set64_ne (m : Mem) (a : ArrId) (i v : Word) (h : a ≠ POOL ∧ a ≠ POOL1) :
    vpool (m.set64 a i v) = vpool m := by
  have e : ∀ t, (m.set64 a i v).arr64 (tierA POOL t) = m.arr64 (tierA POOL t) := fun t =>
    Mem.arr64_set64_ne _ _ _ _ _ (Ne.symm (tierA_pool_ne t a h.1 h.2))
  simp only [vpool, prd, e]
grind_pattern [arena_grind] vpool_set64_ne => vpool (m.set64 a i v)

/-- The virtual pool reads only the pool's two arrays. -/
theorem vpool_congr {m m' : Mem} (h0 : m'.arr64 POOL = m.arr64 POOL)
    (h1 : m'.arr64 POOL1 = m.arr64 POOL1) : vpool m' = vpool m := by
  have e : ∀ t, m'.arr64 (tierA POOL t) = m.arr64 (tierA POOL t) := fun t => by
    rcases tierA_pool t with h | h <;> rw [h] <;> assumption
  simp only [vpool, prd, e]

theorem pcap_congr {m m' : Mem} (h0 : (m'.arr64 POOL).size = (m.arr64 POOL).size)
    (h1 : (m'.arr64 POOL1).size = (m.arr64 POOL1).size) : pcap m' = pcap m := by
  simp only [pcap, PSmall, h0, h1]

@[arena_grind =] theorem pcap_set64 (m : Mem) (a : ArrId) (i v : Word) :
    pcap (m.set64 a i v) = pcap m := by
  apply pcap_congr
  · by_cases h : a = POOL
    · subst h; rw [Mem.size_arr64_set64]
    · rw [Mem.arr64_set64_ne _ _ _ _ _ (Ne.symm h)]
  · by_cases h : a = POOL1
    · subst h; rw [Mem.size_arr64_set64]
    · rw [Mem.arr64_set64_ne _ _ _ _ _ (Ne.symm h)]

@[arena_grind =] theorem pcap_setG (m : Mem) (g : GVar) (v : Word) : pcap (m.setG g v) = pcap m := rfl

@[arena_grind =] theorem vpool_setG (m : Mem) (g : GVar) (v : Word) : vpool (m.setG g v) = vpool m :=
  vpool_congr rfl rfl

/-- `m'` is `m` with at most the pool's two arrays written (in place: their sizes stay), and
the globals unchanged: the frame of a pool writer. -/
structure PFrame (m m' : Mem) : Prop where
  bytes : m'.bytes = m.bytes
  size : m'.words.size = m.words.size
  arr : ∀ b, b ≠ POOL → b ≠ POOL1 → m'.arr64 b = m.arr64 b
  size0 : (m'.arr64 POOL).size = (m.arr64 POOL).size
  size1 : (m'.arr64 POOL1).size = (m.arr64 POOL1).size
  glob : m'.glob = m.glob


theorem PFrame.refl (m : Mem) : PFrame m m := ⟨rfl, rfl, fun _ _ _ => rfl, rfl, rfl, rfl⟩
grind_pattern [arena_grind] PFrame.refl => PFrame m m

theorem PFrame.trans {m m' m'' : Mem} (h : PFrame m m') (h' : PFrame m' m'') : PFrame m m'' :=
  ⟨h'.bytes.trans h.bytes, h'.size.trans h.size, fun b h0 h1 => (h'.arr b h0 h1).trans (h.arr b h0 h1),
    h'.size0.trans h.size0, h'.size1.trans h.size1, h'.glob.trans h.glob⟩
grind_pattern [arena_grind] PFrame.trans => PFrame m m'', PFrame m' m''

theorem PFrame.set64 {m m' : Mem} (t i v : Word) (h : PFrame m m') :
    PFrame m (m'.set64 (tierA POOL t) i v) := by
  refine ⟨h.bytes, by simp [Mem.set64, h.size], fun b h0 h1 => ?_, ?_, ?_, h.glob⟩
  · rw [Mem.arr64_set64_ne _ _ _ _ _ (tierA_pool_ne t b h0 h1), h.arr b h0 h1]
  · rcases tierA_pool t with e | e <;> rw [e]
    · rw [Mem.size_arr64_set64, h.size0]
    · rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide), h.size0]
  · rcases tierA_pool t with e | e <;> rw [e]
    · rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide), h.size1]
    · rw [Mem.size_arr64_set64, h.size1]
grind_pattern [arena_grind] PFrame.set64 => PFrame m (m'.set64 (tierA POOL t) i v)

theorem PFrame.set64_both {m m' : Mem} (b : ArrId) (i v : Word) (h : PFrame m m')
    (h0 : b ≠ POOL) (h1 : b ≠ POOL1) : PFrame (m.set64 b i v) (m'.set64 b i v) := by
  refine ⟨h.bytes, by simp [Mem.set64, h.size], fun c c0 c1 => ?_, ?_, ?_, h.glob⟩
  · by_cases hcb : c = b
    · subst hcb; rw [Mem.arr64_set64_same, Mem.arr64_set64_same, h.arr c c0 c1]
    · rw [Mem.arr64_set64_ne _ _ _ _ _ hcb, Mem.arr64_set64_ne _ _ _ _ _ hcb, h.arr c c0 c1]
  · rw [Mem.arr64_set64_ne _ _ _ _ _ (Ne.symm h0), Mem.arr64_set64_ne _ _ _ _ _ (Ne.symm h0), h.size0]
  · rw [Mem.arr64_set64_ne _ _ _ _ _ (Ne.symm h1), Mem.arr64_set64_ne _ _ _ _ _ (Ne.symm h1), h.size1]
grind_pattern [arena_grind] PFrame.set64_both => PFrame (m.set64 b i v) (m'.set64 b i v)

theorem PFrame.arr64 {m m' : Mem} (b : ArrId) (h : PFrame m m') (h0 : b ≠ POOL ∧ b ≠ POOL1) :
    m'.arr64 b = m.arr64 b := h.arr b h0.1 h0.2
grind_pattern [arena_grind] PFrame.arr64 => PFrame m m', m'.arr64 b

theorem PFrame.tsize {m m' : Mem} (t : Word) (h : PFrame m m') :
    (m'.arr64 (tierA POOL t)).size = (m.arr64 (tierA POOL t)).size := by
  rcases tierA_pool t with e | e <;> rw [e]
  · exact h.size0
  · exact h.size1
grind_pattern [arena_grind] PFrame.tsize => PFrame m m', (m'.arr64 (tierA POOL t)).size

theorem PFrame.pcap {m m' : Mem} (h : PFrame m m') : pcap m' = pcap m :=
  pcap_congr h.size0 h.size1
grind_pattern [arena_grind] PFrame.pcap => PFrame m m', pcap m'

theorem PFrame.ctl {m m' : Mem} (h : PFrame m m') : m'.arr64 CTL = m.arr64 CTL :=
  h.arr CTL (by decide) (by decide)
grind_pattern [arena_grind] PFrame.ctl => PFrame m m', m'.arr64 CTL

/-! ## The pool invariant -/

/-- The pool top, `CTL[0]`: the top of the current tier, a tagged address. -/
def _root_.L.Mem.top (m : Mem) : Word := (m.arr64 CTL)[0]?.getD 0

theorem Mem.top_eq (m : Mem) (h : 0 < (m.arr64 CTL).size) : m.top = (m.arr64 CTL)[0] := by
  simp [Mem.top, h]
grind_pattern [arena_grind] Mem.top_eq => m.top, (m.arr64 CTL)[0]

theorem Mem.top_set64 (m : Mem) (v : Word) (h : 0 < (m.arr64 CTL).size) :
    (m.set64 CTL 0 v).top = v := by
  simp [Mem.top, Mem.arr64_set64_same, h]
grind_pattern [arena_grind] Mem.top_set64 => (m.set64 CTL 0 v).top

@[arena_grind =] theorem Mem.top_setG (m : Mem) (g : GVar) (v : Word) : (m.setG g v).top = m.top := rfl

theorem Frame.top (m m' : Mem) (h : Frame POOL m m') : m'.top = m.top := by
  simp only [Mem.top, h.2.2 CTL (by decide)]
grind_pattern [arena_grind] Frame.top => Frame POOL m m', m'.top

theorem Frame.size_ctl (m m' : Mem) (h : Frame POOL m m') :
    (m'.arr64 CTL).size = (m.arr64 CTL).size := by
  rw [h.2.2 CTL (by decide)]
grind_pattern [arena_grind] Frame.size_ctl => Frame POOL m m', (m'.arr64 CTL).size

theorem PFrame.top {m m' : Mem} (h : PFrame m m') : m'.top = m.top := by
  simp only [Mem.top, h.ctl]
grind_pattern [arena_grind] PFrame.top => PFrame m m', m'.top

theorem PFrame.size_ctl {m m' : Mem} (h : PFrame m m') :
    (m'.arr64 CTL).size = (m.arr64 CTL).size := by rw [h.ctl]
grind_pattern [arena_grind] PFrame.size_ctl => PFrame m m', (m'.arr64 CTL).size

/-- The pool invariant: `CTL` has its word, the tier arrays have fewer than `2^40` words
(`pcap m < 2^63`), the top is an address of a tier (`top ≤ pcap`) inside its tier's array, and
the saved tier-0 top `PTOP0` is inside tier 0's array. -/
def PoolOK (m : Mem) : Prop :=
  CTL < m.words.size ∧ 0 < (m.arr64 CTL).size ∧ pcap m < 2 ^ 63 ∧ m.top.toNat ≤ pcap m ∧
  (m.glob PTOP0).toNat ≤ (m.arr64 POOL).size ∧
  (m.top - ((m.top >>> 40) <<< 40)).toNat ≤ (m.arr64 (tierA POOL (m.top >>> 40))).size

/-- `m'` is `m` with limbs appended to the pool: only the pool's tier arrays and the top
changed, the pool below the old top did not, and the top only moved up, inside its tier. Every
pool function posts it; a state relation that refers only to slices below the top is preserved
by it (`L.Arena.Refine`, `hgrow`). -/
structure Grows (m m' : Mem) : Prop where
  frame : PFrame (m.set64 CTL 0 m'.top) m'
  agree : Agree (vpool m') (vpool m) m.top.toNat
  le : m.top.toNat ≤ m'.top.toNat
  cap : m'.top.toNat ≤ pcap m'
  pcapEq : pcap m' = pcap m
  tier : m'.top.toNat < 2 ^ 40 ∨ 2 ^ 40 ≤ m.top.toNat
  inn : (m'.top - ((m'.top >>> 40) <<< 40)).toNat ≤ (m'.arr64 (tierA POOL (m'.top >>> 40))).size


/-- A slice of the pool in use: below the top, and, while the scratch tier is open (the top in
tier 1), a slice of tier 0 lies below the saved tier-0 top `PTOP0` (the words of tier 0 above
it are written by the promotion's copies, `pool_alloc0`). -/
def SliceOK (m : Mem) (o l : Word) : Prop :=
  o.toNat + l.toNat ≤ m.top.toNat ∧
  (m.top.toNat < 2 ^ 40 ∨ 2 ^ 40 ≤ o.toNat ∨ o.toNat + l.toNat ≤ (m.glob PTOP0).toNat)

/-- The tier-array size facts of a pool invariant. -/
theorem PoolOK.small {m : Mem} (h : PoolOK m) : PSmall m := pcap_small m (by have := h.2.2.1; omega)

theorem PoolOK.top41 {m : Mem} (h : PoolOK m) : m.top.toNat < 2 ^ 41 := by
  have := h.2.2.2.1; rw [pcap_eq m (by have := h.2.2.1; omega)] at this; omega

theorem PSmall.tier {m : Mem} (h : PSmall m) (t : Word) : (m.arr64 (tierA POOL t)).size < 2 ^ 40 := by
  rcases tierA_pool t with e | e <;> rw [e]
  · exact h.1
  · exact h.2

/-- Two addresses whose `Nat`s have the same quotient by `2^40` have the same tier. -/
theorem tag_tier_eq {x y : Word} (h : x.toNat / 2 ^ 40 = y.toNat / 2 ^ 40) : x >>> 40 = y >>> 40 :=
  UInt64.toNat_inj.mp (by rw [tag_tier_toNat, tag_tier_toNat, h])

/-- **The writer's `Grows`**: a pool function that wrote only the pool's tiers and the top, kept
the pool below the old top, and moved the top up by `k` words that fit in the top's tier array
(its length check), grew the pool. -/
theorem Grows.intro (m m' : Mem) (hok : PoolOK m) (hf : PFrame (m.set64 CTL 0 m'.top) m')
    (ha : Agree (vpool m') (vpool m) m.top.toNat) (hle : m.top.toNat ≤ m'.top.toNat)
    (hk : (m.top - ((m.top >>> 40) <<< 40)).toNat + (m'.top.toNat - m.top.toNat) ≤
      (m.arr64 (tierA POOL (m.top >>> 40))).size) : Grows m m' := by
  have hs := hok.small
  have h41 := hok.top41
  have hsz := hs.tier (m.top >>> 40)
  rw [tag_off_toNat] at hk
  have hp : pcap m' = pcap m := by rw [hf.pcap, pcap_set64]
  have hp' : pcap m = 2 ^ 41 - 1 := pcap_of_small m hs
  have hq : m'.top.toNat / 2 ^ 40 = m.top.toNat / 2 ^ 40 := by omega
  have ht : m'.top >>> 40 = m.top >>> 40 := tag_tier_eq hq
  have hsize : (m'.arr64 (tierA POOL (m'.top >>> 40))).size = (m.arr64 (tierA POOL (m.top >>> 40))).size := by
    rw [ht]
    rcases tierA_pool (m.top >>> 40) with e | e <;> rw [e]
    · rw [hf.size0, Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
    · rw [hf.size1, Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  refine ⟨hf, ha, hle, by omega, hp, by omega, ?_⟩
  rw [tag_off_toNat, hsize]; omega
grind_pattern [arena_grind] Grows.intro => Grows m m'

/-- A grown pool keeps the pool invariant. -/
theorem PoolOK.grows {m m' : Mem} (h : PoolOK m) (hg : Grows m m') : PoolOK m' := by
  obtain ⟨hf, -, hle, htp, hp, ht, hin⟩ := hg
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hc : m'.arr64 CTL = (m.set64 CTL 0 m'.top).arr64 CTL := hf.ctl
  refine ⟨?_, ?_, by omega, htp, ?_, hin⟩
  · rw [hf.size, Mem.words_size_set64]; exact h1
  · rw [hc, Mem.size_arr64_set64]; exact h2
  · rw [congrFun hf.glob PTOP0, hf.size0, Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
    exact h5
grind_pattern [arena_grind] PoolOK.grows => Grows m m', PoolOK m'

/-- A slice in use stays in use when the pool grows. -/
theorem SliceOK.grows {m m' : Mem} {o l : Word} (h : SliceOK m o l) (hg : Grows m m') :
    SliceOK m' o l := by
  obtain ⟨hf, -, hle, -, -, ht, -⟩ := hg
  have hglob : m'.glob PTOP0 = m.glob PTOP0 := congrFun hf.glob PTOP0
  obtain ⟨h1, h2⟩ := h
  refine ⟨by omega, ?_⟩
  rw [hglob]; omega
grind_pattern [arena_grind] SliceOK.grows => Grows m m', SliceOK m' o l

/-! ## `wt` and carries -/

theorem wt_succ (i k : Nat) (h : k = i + 1) : wt k = wt i * 2 ^ 64 := by
  subst h; simp only [wt, Nat.mul_add, Nat.pow_add, Nat.mul_one]
grind_pattern [arena_grind] wt_succ => wt i, wt k

theorem wt_add (i j k : Nat) (h : k = i + j) : wt k = wt i * wt j := by
  subst h; simp only [wt, ← Nat.pow_add, Nat.mul_add]
grind_pattern [arena_grind] wt_add => wt k, wt i * wt j

@[arena_grind =] theorem wt_zero : wt 0 = 1 := rfl

theorem wt_pos (i : Nat) : 0 < wt i := Nat.two_pow_pos _
grind_pattern [arena_grind] wt_pos => wt i

/-! The carry of a word addition, as an equation between `toNat`s that `grind`'s ring solver
sees (`grind` derives the same fact inside its linear-arithmetic module, from where it does not
reach the ring solver; then the step `V + c·wt i = …` fails). Triggered by the comparison the
program makes. -/
theorem add_nc (x y : Word) (h : ¬ x + y < x) : (x + y).toNat = x.toNat + y.toNat := by grind
theorem add_c (x y : Word) (h : x + y < x) : (x + y).toNat + 2 ^ 64 = x.toNat + y.toNat := by
  grind
theorem add_nc' (x y : Word) (h : ¬ x + y < y) : (x + y).toNat = x.toNat + y.toNat := by grind
theorem add_c' (x y : Word) (h : x + y < y) : (x + y).toNat + 2 ^ 64 = x.toNat + y.toNat := by
  grind
grind_pattern [arena_grind] add_nc => x + y < x
grind_pattern [arena_grind] add_c => x + y < x
grind_pattern [arena_grind] add_nc' => x + y < y
grind_pattern [arena_grind] add_c' => x + y < y

/-- The carry out of the word addition `x + y + c`. -/
def adcHi (x y c : Word) : Nat := (x.toNat + y.toNat + c.toNat) / 2 ^ 64

/-- `x + y + c = low word + carry · 2^64`, as an equation the ring solver sees. -/
theorem adc_split (x y c : Word) :
    (x + y + c).toNat + adcHi x y c * 2 ^ 64 = x.toNat + y.toNat + c.toNat := by
  simp only [adcHi]; grind
grind_pattern [arena_grind] adc_split => adcHi x y c

theorem adcHi_le (x y c : Word) (h : c.toNat ≤ 1) : adcHi x y c ≤ 1 := by
  simp only [adcHi]; grind
grind_pattern [arena_grind] adcHi_le => adcHi x y c

/-! ## `pv`, `xv`, `lv` -/

section
variable (p : Array Word) (o : Nat)

@[arena_grind =] theorem pv_zero : pv p o 0 = 0 := rfl

theorem pv_succ (k k' j : Nat) (hk : k' = k + 1) (hj : j = o + k) (h : j < p.size) :
    pv p o k' = pv p o k + p[j].toNat * wt k := by
  subst hk hj; simp [pv, h]
grind_pattern [arena_grind] pv_succ => pv p o k', pv p o k, p[j]

/-- Writing above a slice does not change it. -/
theorem pv_set_above (k j : Nat) (v : Word) (h : o + k ≤ j) :
    pv (p.set! j v) o k = pv p o k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [pv, ih (by omega)]
    rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    simp [show j ≠ o + k by omega]
grind_pattern [arena_grind] pv_set_above => pv (p.set! j v) o k

/-- Writing the limb just above a slice extends it by one limb. -/
theorem pv_set_succ (k k' j : Nat) (v : Word) (hk : k' = k + 1) (hj : j = o + k) (h : j < p.size) :
    pv (p.set! j v) o k' = pv p o k + v.toNat * wt k := by
  subst hk hj
  simp only [pv, pv_set_above p o k (o + k) v (Nat.le_refl _)]
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]; simp [h]
grind_pattern [arena_grind] pv_set_succ => pv (p.set! j v) o k', pv p o k

/-- Overwriting limb `k₁ + k₂` inside a slice, with the weight split as `wt k₁ * wt k₂` (the
form `nat_mul`'s inner loop uses: limb `i + j` of the product). -/
theorem pv_set_mid (n k₁ k₂ j : Nat) (v : Word) (hj : j = o + k₁ + k₂) (hn : k₁ + k₂ < n)
    (h : j < p.size) :
    pv (p.set! j v) o n + p[j].toNat * (wt k₁ * wt k₂) = pv p o n + v.toNat * (wt k₁ * wt k₂) := by
  have hw : wt k₁ * wt k₂ = wt (k₁ + k₂) := by simp only [wt, ← Nat.pow_add, Nat.mul_add]
  rw [hw]
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [pv]
    rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    by_cases hk : k₁ + k₂ = n
    · subst hj; subst hk
      have ha := pv_set_above p o (k₁ + k₂) (o + k₁ + k₂) v (by omega)
      rw [Array.set!_eq_setIfInBounds] at ha
      rw [ha]
      have h' : o + (k₁ + k₂) < p.size := by omega
      simp only [show o + k₁ + k₂ = o + (k₁ + k₂) by omega, h', ite_true, Option.getD_some,
        getElem?_pos]
      grind
    · have := ih (by omega)
      rw [Array.set!_eq_setIfInBounds] at this
      simp [show j ≠ o + n by omega]; omega
grind_pattern [arena_grind] pv_set_mid => pv (p.set! j v) o n, p[j], wt k₁ * wt k₂

theorem xv_succ (l k k' : Nat) (hk : k' = k + 1) : xv p o l k' = xv p o l k + lv p o l k * wt k := by
  subst hk; rfl
grind_pattern [arena_grind] xv_succ => xv p o l k', xv p o l k

@[arena_grind =] theorem xv_zero (l : Nat) : xv p o l 0 = 0 := rfl

theorem lv_ge (l i : Nat) (h : l ≤ i) : lv p o l i = 0 := by simp [lv]; omega
grind_pattern [arena_grind] lv_ge => lv p o l i

theorem lv_lt (l i j : Nat) (hj : j = o + i) (hi : i < l) (h : j < p.size) :
    lv p o l i = p[j].toNat := by
  subst hj; simp [lv, hi, h]
grind_pattern [arena_grind] lv_lt => lv p o l i, p[j]

/-- Limb `i` of a slice of `p`, read through a pool `q` that agrees with `p` below `t`. -/
theorem lv_read (q : Array Word) (t l i j : Nat) (ha : Agree q p t) (hj : j = o + i) (hi : i < l)
    (hl : o + l ≤ t) (hq : j < q.size) : lv p o l i = q[j].toNat := by
  subst hj
  have := ha (o + i) (by omega)
  simp only [lv, hi, ite_true]
  rw [← this]; simp [hq]
grind_pattern [arena_grind] lv_read => Agree q p t, lv p o l i, q[j]

/-- The zero-extended prefix of a slice, once it covers the slice, is the slice. -/
theorem xv_full (l k : Nat) (h : l ≤ k) : xv p o l k = pv p o l := by
  induction k with
  | zero => have : l = 0 := by omega
            subst this; rfl
  | succ k ih =>
    by_cases hl : l ≤ k
    · simp only [xv, ih hl, lv, show ¬ k < l by omega, ite_false]; simp
    · have : l = k + 1 := by omega
      subst this
      have hx : ∀ m, m ≤ k + 1 → xv p o (k + 1) m = pv p o m := by
        intro m hm
        induction m with
        | zero => rfl
        | succ m ihm => simp only [xv, pv, lv, ihm (by omega), show m < k + 1 by omega, ite_true]
      exact hx _ (Nat.le_refl _)
grind_pattern [arena_grind] xv_full => xv p o l k

end

/-! ## `Agree` and `Norm` -/

theorem Agree.refl (p : Array Word) (t : Nat) : Agree p p t := fun _ _ => rfl
grind_pattern [arena_grind] Agree.refl => Agree p p t

theorem Agree.set (p q : Array Word) (t j : Nat) (v : Word) (h : Agree p q t) (hj : t ≤ j) :
    Agree (p.set! j v) q t := by
  intro i hi
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  simp [show j ≠ i by omega, h i hi]
grind_pattern [arena_grind] Agree.set => Agree (p.set! j v) q t

theorem Agree.pv (p q : Array Word) (t o k : Nat) (h : Agree p q t) (hk : o + k ≤ t) :
    pv p o k = pv q o k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [L.Arena.pv, ih (by omega), h (o + k) (by omega)]
grind_pattern [arena_grind] Agree.pv => Agree p q t, pv p o k

theorem Agree.get (p q : Array Word) (t j : Nat) (h : Agree p q t) (hj : j < t)
    (hp : j < p.size) (hq : j < q.size) : p[j] = q[j] := by
  have := h j hj; simp [hp, hq] at this; exact this
grind_pattern [arena_grind] Agree.get => Agree p q t, p[j]

theorem Agree.lv (p q : Array Word) (t o l i : Nat) (h : Agree p q t) (hk : o + l ≤ t) :
    lv p o l i = lv q o l i := by
  simp only [L.Arena.lv]; split
  · rw [h (o + i) (by omega)]
  · rfl
grind_pattern [arena_grind] Agree.lv => Agree p q t, lv p o l i

/-! ## Agreement, the other way round -/

theorem Agree.vsymm {p q : Array Word} {t : Nat} (h : Agree p q t) : Agree q p t :=
  fun j hj => (h j hj).symm

theorem Agree.vtrans {p q r : Array Word} {t : Nat} (h₁ : Agree p q t) (h₂ : Agree q r t) :
    Agree p r t := fun j hj => (h₁ j hj).trans (h₂ j hj)

theorem Agree.vmono {p q : Array Word} {t t' : Nat} (h : Agree p q t) (ht : t' ≤ t) :
    Agree p q t' := fun j hj => h j (by omega)

theorem Norm.zero (p : Array Word) (o : Nat) : Norm p o 0 := by simp [Norm]
grind_pattern [arena_grind] Norm.zero => Norm p o 0

theorem Norm.of_top (p : Array Word) (o l j : Nat) (hj : j = o + (l - 1))
    (h : j < p.size) (hne : p[j] ≠ 0) : Norm p o l := by
  subst hj; simp [Norm, h, hne]
grind_pattern [arena_grind] Norm.of_top => Norm p o l, p[j]

end L.Arena
