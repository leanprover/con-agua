module

public import ConAgua.L.Semantics
public import ConAgua.Arena.GrindAttr
import Std.Data.DTreeMap.Internal.Operations
public import ConAgua.Layout

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

The pool is a tiered word array: tier `t` is array `tierA 0 t` (`POOL` = 0, `POOL1` = 256).
Its slices are named by *tier-tagged* addresses: bit 40 is the tier, the low 40 bits are the
index into the tier's array (`⦃x⦄.tier`, `⦃x⦄.idx`, `L/Notation.lean`). Tier 1 is the scratch
tier, open while the arena's scratch flag is set (`scratch_reset`, `Scratch.lean`): `CTL[0]` is
the top of the current tier, `PT0[0]` the tier-0 top while tier 1 is open.

Proofs read the pool only through `vpool m`, an array with a word for every address below
`2^41`: `prd m x`, what the L load `POOL⦃x⦄` reads (`0` where it aborts). They bound addresses
with `pcap m` (`2^41 - 1` on a pool whose tier arrays have fewer than `2^40` words, so that a
hypothesis `pcap m < 2^64` carries the tier arrays' bound), and never unfold `vpool`/`prd`. -/

theorem tierA_pool0 : tierA 0 0 = POOL := by decide
theorem tierA_pool1 : tierA 0 1 = POOL1 := by decide

/-- The pool's tiers are its two arrays. -/
theorem tierA_pool (t : Word) : tierA 0 t = POOL ∨ tierA 0 t = POOL1 := by
  have h : (t &&& 1).toNat = 0 ∨ (t &&& 1).toNat = 1 := by
    rw [UInt64.toNat_and, UInt64.toNat_one, Nat.and_one_is_mod]; omega
  rcases h with h | h <;> simp [tierA, tierOff, h]

/-- A store into a pool tier leaves the other arrays alone (no case split on the tier). -/
theorem arr64_set64_tier_ne (m : Mem) (t i v : Word) (b : ArrId) (h : b ≠ POOL ∧ b ≠ POOL1) :
    (m.set64 (tierA 0 t) i v).arr64 b = m.arr64 b := by
  rcases tierA_pool t with e | e <;> rw [e] <;> exact Mem.arr64_set64_ne _ _ _ _ _ (by
    first | exact h.1 | exact h.2)
grind_pattern [arena_grind] arr64_set64_tier_ne => (m.set64 (tierA 0 t) i v).arr64 b

/-- A tiered store array (an id in `1‥255`) is neither of the pool's arrays. -/
theorem tierA_ne_pool (a : Nat) (ha : 0 < a ∧ a < 256) (t : Word) :
    tierA a t ≠ POOL ∧ tierA a t ≠ POOL1 := by
  have h : (t &&& 1).toNat = 0 ∨ (t &&& 1).toNat = 1 := by
    rw [UInt64.toNat_and, UInt64.toNat_one, Nat.and_one_is_mod]; omega
  have e : (tierA a t : Nat) = a + 256 * (t &&& 1).toNat := rfl
  obtain ⟨h1, h2⟩ := ha
  constructor
  · intro hc
    have h' : (a + 256 * (t &&& 1).toNat : Nat) = 0 := e.symm.trans hc
    rcases h with h | h <;> rw [h] at h' <;> omega
  · intro hc
    have h' : (a + 256 * (t &&& 1).toNat : Nat) = 256 := e.symm.trans hc
    rcases h with h | h <;> rw [h] at h' <;> omega

/-- Tier `t` of a store array `a < 256` is not another array `b < 256`. -/
theorem tierA_ne_small (a b : Nat) (ha : a < 256) (hb : b < 256) (h : b ≠ a) (t : Word) :
    tierA a t ≠ b := by
  have hc : (t &&& 1).toNat = 0 ∨ (t &&& 1).toNat = 1 := by
    rw [UInt64.toNat_and, UInt64.toNat_one, Nat.and_one_is_mod]; omega
  have e : (tierA a t : Nat) = a + 256 * (t &&& 1).toNat := rfl
  intro hc'
  have h' : (a + 256 * (t &&& 1).toNat : Nat) = b := e.symm.trans hc'
  rcases hc with hc | hc <;> rw [hc] at h' <;> omega

theorem tierA_pool_ne (t : Word) (b : ArrId) (h0 : b ≠ POOL) (h1 : b ≠ POOL1) : b ≠ tierA 0 t := by
  rcases tierA_pool t with h | h <;> rw [h] <;> assumption

theorem tag_tier_toNat (x : Word) : (x >>> 40).toNat = x.toNat / 2 ^ 40 := by
  rw [UInt64.toNat_shiftRight]; simp [Nat.shiftRight_eq_div_pow]

theorem tag_idx_toNat (x : Word) : (x &&& 1099511627775).toNat = x.toNat % 2 ^ 40 := by
  rw [UInt64.toNat_and]
  have : (1099511627775 : Word).toNat = 2 ^ 40 - 1 := by decide
  rw [this, Nat.and_two_pow_sub_one_eq_mod]

theorem tag_base_toNat (x : Word) :
    ((x >>> 40) <<< 40).toNat = x.toNat / 2 ^ 40 * 2 ^ 40 := by
  rw [UInt64.toNat_shiftLeft, tag_tier_toNat]
  simp only [show (40 : Word).toNat % 64 = 40 from rfl, Nat.shiftLeft_eq]
  apply Nat.mod_eq_of_lt; have := x.toNat_lt; omega

theorem tag_off_toNat (x : Word) :
    (x - ((x >>> 40) <<< 40)).toNat = x.toNat % 2 ^ 40 := by
  have hle : ((x >>> 40) <<< 40) ≤ x := by
    rw [UInt64.le_iff_toNat_le, tag_base_toNat]; exact Nat.div_mul_le_self _ _
  rw [UInt64.toNat_sub_of_le _ _ hle, tag_base_toNat]; omega

/-- An address is its tier's base plus its index (linear facts for `grind`, no `/`/`%`). -/
theorem tag_split (x : Word) : (x >>> 40).toNat * 2 ^ 40 + (x &&& 1099511627775).toNat = x.toNat := by
  rw [tag_tier_toNat, tag_idx_toNat]; omega
grind_pattern [arena_grind] tag_split => x >>> 40, x &&& 1099511627775

theorem tag_idx_lt (x : Word) : (x &&& 1099511627775).toNat < 2 ^ 40 := by
  rw [tag_idx_toNat]; omega
grind_pattern [arena_grind] tag_idx_lt => x &&& 1099511627775

theorem tag_tier_le (x : Word) (h : x.toNat < 2 ^ 41) : (x >>> 40).toNat ≤ 1 := by
  rw [tag_tier_toNat]; omega
grind_pattern [arena_grind] tag_tier_le => x >>> 40

theorem tierA_word (t : Word) (ht : t.toNat ≤ 1) :
    tierA 0 t = if t.toNat = 0 then POOL else POOL1 := by
  have e : (t &&& 1).toNat = t.toNat := by
    rw [UInt64.toNat_and, UInt64.toNat_one, Nat.and_one_is_mod]; omega
  unfold tierA tierOff; rw [e]
  by_cases h : t.toNat = 0
  · simp [h]
  · have : t.toNat = 1 := by omega
    simp [this]; rfl

theorem tierA_tag (x : Word) (hx : x.toNat < 2 ^ 41) :
    tierA 0 (x >>> 40) = if x.toNat < 2 ^ 40 then POOL else POOL1 := by
  have h1 : (x >>> 40).toNat ≤ 1 := by rw [tag_tier_toNat]; omega
  rw [tierA_word _ h1, tag_tier_toNat]
  by_cases h : x.toNat < 2 ^ 40
  · simp [h, Nat.div_eq_of_lt h]
  · have : x.toNat / 2 ^ 40 ≠ 0 := by omega
    simp [h, this]

/-- The pool word at the tagged address `x`: what the L load `POOL⦃x⦄` reads, `0` where it
aborts (at an address `2^41` and up the tier wraps: `tierA` reads the tier's low bit). -/
def prd (m : Mem) (x : Word) : Word := (m.arr64 (tierA 0 (x >>> 40)))[(x &&& 1099511627775).toNat]?.getD 0

/-- `prd` reads only the pool's arrays. -/
theorem prd_congr {m m' : Mem} (x : Word) (h0 : m'.arr64 POOL = m.arr64 POOL)
    (h1 : m'.arr64 POOL1 = m.arr64 POOL1) : prd m' x = prd m x := by
  have e : ∀ t, m'.arr64 (tierA 0 t) = m.arr64 (tierA 0 t) := fun t => by
    rcases tierA_pool t with h | h <;> rw [h] <;> assumption
  simp only [prd, e]

/-- The word at the tagged address `x` of the tiered array `a` (an L load `a⦃x⦄`, `0` where it
aborts): `prd` for the pool, and for a template's value array. -/
def trd (m : Mem) (a : ArrId) (x : Word) : Word :=
  (m.arr64 (tierA a (x >>> 40)))[(x &&& 1099511627775).toNat]?.getD 0

theorem trd_ld (m : Mem) (a : ArrId) (x : Word)
    (h : (x &&& 1099511627775).toNat < (m.arr64 (tierA a (x >>> 40))).size) :
    (m.arr64 (tierA a (x >>> 40)))[(x &&& 1099511627775).toNat] = trd m a x := by
  unfold trd; rw [Array.getElem?_eq_getElem h]; rfl
grind_pattern [arena_grind] trd_ld => (m.arr64 (tierA a (x >>> 40)))[(x &&& 1099511627775).toNat], trd m a x

theorem trd_pool (m : Mem) (x : Word) : trd m POOL x = prd m x := rfl

/-- The store `POOL⟨⦃x⦄.tier⟩[⦃x⦄.idx] := v` at the tagged address `x` (a model's pool write). -/
def pst (m : Mem) (x v : Word) : Mem := m.set64 (tierA 0 (x >>> 40)) (x &&& 1099511627775) v

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

/-- A total read of the virtual pool at an address of a tier is `prd`. -/
theorem vpool_getD (m : Mem) (x : Word) (h : x.toNat < 2 ^ 41) : (vpool m)[x.toNat]?.getD 0 = prd m x := by
  rw [vpool_get? m x h]; rfl
grind_pattern [arena_grind] vpool_getD => (vpool m)[x.toNat]?.getD 0

/-- An L load of the pool at the tagged address `x` (`POOL⦃x⦄`), in bounds, reads the virtual
pool. -/
theorem vpool_ld (m : Mem) (x : Word)
    (h : (x &&& 1099511627775).toNat < (m.arr64 (tierA 0 (x >>> 40))).size)
    (h' : x.toNat < (vpool m).size) :
    (m.arr64 (tierA 0 (x >>> 40)))[(x &&& 1099511627775).toNat] = (vpool m)[x.toNat] := by
  have h41 : x.toNat < 2 ^ 41 := vpool_size m ▸ h'
  have e := vpool_get? m x h41
  rw [Array.getElem?_eq_getElem h'] at e
  have e2 : prd m x = (m.arr64 (tierA 0 (x >>> 40)))[(x &&& 1099511627775).toNat] := by
    unfold prd; rw [Array.getElem?_eq_getElem h]; rfl
  rw [Option.some.inj e, e2]
grind_pattern [arena_grind] vpool_ld =>
  (m.arr64 (tierA 0 (x >>> 40)))[(x &&& 1099511627775).toNat], vpool m

/-- An L load `POOL⦃x⦄`, in bounds, reads `prd m x` (a `grind` lemma where a model names `prd`). -/
theorem prd_ld (m : Mem) (x : Word)
    (h : (x &&& 1099511627775).toNat < (m.arr64 (tierA 0 (x >>> 40))).size) :
    (m.arr64 (tierA 0 (x >>> 40)))[(x &&& 1099511627775).toNat] = prd m x := by
  unfold prd; rw [Array.getElem?_eq_getElem h]; rfl
grind_pattern [arena_grind] prd_ld => (m.arr64 (tierA 0 (x >>> 40)))[(x &&& 1099511627775).toNat], prd m x

/-- `2^64`, sealed (`vszS`'s reason). -/
opaque tszS : Sealed Nat (2 ^ 64)

/-- The total pool view's length, `2^64`. -/
def tsz : Nat := tszS.val

theorem tsz_eq : tsz = 2 ^ 64 := tszS.eq

/-- **The total pool view**: word `x` is `prd m x` for every word `x`, including the addresses
`2^41` and up where the tiers wrap. Bound-free reader models (`limbs_eq`, the key hashes and
matchers of the stores) read it; below `2^41` it is `vpool` (`tpool_vpool`). -/
def tpool (m : Mem) : Array Word := Array.ofFn fun j : Fin tsz => prd m (UInt64.ofNat j)

@[arena_grind =] theorem tpool_size (m : Mem) : (tpool m).size = 2 ^ 64 := by
  rw [tpool, Array.size_ofFn, tsz_eq]

theorem tpool_get? (m : Mem) (x : Word) : (tpool m)[x.toNat]? = some (prd m x) := by
  have h' : x.toNat < tsz := tsz_eq ▸ x.toNat_lt
  rw [tpool, Array.getElem?_ofFn]; simp only [h', ↓reduceDIte, UInt64.ofNat_toNat]

attribute [irreducible] tpool

theorem tpool_getD (m : Mem) (x : Word) : (tpool m)[x.toNat]?.getD 0 = prd m x := by
  rw [tpool_get?]; rfl
grind_pattern [arena_grind] tpool_getD => (tpool m)[x.toNat]?.getD 0

/-- An L load `POOL⦃x⦄`, in bounds, reads the total pool view (no bound on `x`). -/
theorem tpool_ld (m : Mem) (x : Word)
    (h : (x &&& 1099511627775).toNat < (m.arr64 (tierA 0 (x >>> 40))).size)
    (h' : x.toNat < (tpool m).size) :
    (m.arr64 (tierA 0 (x >>> 40)))[(x &&& 1099511627775).toNat] = (tpool m)[x.toNat] := by
  have e := tpool_get? m x
  rw [Array.getElem?_eq_getElem h'] at e
  have e2 : prd m x = (m.arr64 (tierA 0 (x >>> 40)))[(x &&& 1099511627775).toNat] := by
    unfold prd; rw [Array.getElem?_eq_getElem h]; rfl
  rw [Option.some.inj e, e2]
grind_pattern [arena_grind] tpool_ld =>
  (m.arr64 (tierA 0 (x >>> 40)))[(x &&& 1099511627775).toNat], tpool m

/-- Below `2^41`, the total view is the virtual pool. -/
theorem tpool_vpool (m : Mem) : Agree (tpool m) (vpool m) (2 ^ 41) := by
  intro j hj
  have hx : (UInt64.ofNat j).toNat = j := UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  have e1 := tpool_get? m (UInt64.ofNat j)
  have e2 := vpool_get? m (UInt64.ofNat j) (by rw [hx]; exact hj)
  rw [hx] at e1 e2; rw [e1, e2]

/-- The total view reads only the pool's arrays. -/
theorem tpool_congr {m m' : Mem} (h0 : m'.arr64 POOL = m.arr64 POOL)
    (h1 : m'.arr64 POOL1 = m.arr64 POOL1) : tpool m' = tpool m := by
  have e : ∀ t, m'.arr64 (tierA 0 t) = m.arr64 (tierA 0 t) := fun t => by
    rcases tierA_pool t with h | h <;> rw [h] <;> assumption
  simp only [tpool, prd, e]

theorem tpool_set64_ne (m : Mem) (a : ArrId) (i v : Word) (h : a ≠ POOL ∧ a ≠ POOL1) :
    tpool (m.set64 a i v) = tpool m :=
  tpool_congr (Mem.arr64_set64_ne _ _ _ _ _ (Ne.symm h.1)) (Mem.arr64_set64_ne _ _ _ _ _ (Ne.symm h.2))
grind_pattern [arena_grind] tpool_set64_ne => tpool (m.set64 a i v)

@[arena_grind =] theorem tpool_setG (m : Mem) (g : GVar) (v : Word) : tpool (m.setG g v) = tpool m :=
  tpool_congr rfl rfl

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
  rw [tierA_tag _ (by rw [hxw]; exact hx), hxw, tag_idx_toNat, hxw]

theorem prd_set64t (m : Mem) (t i v : Word) (x : Nat) (ht : t.toNat ≤ 1)
    (hi : i.toNat < (m.arr64 (tierA 0 t)).size) (hs : (m.arr64 (tierA 0 t)).size ≤ 2 ^ 40)
    (hx : x < 2 ^ 41) :
    prd (m.set64 (tierA 0 t) i v) (UInt64.ofNat x) =
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
        rw [ite_eq_left e, ite_eq_left hi, ite_eq_left e2]; rfl
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
        rw [ite_eq_left e, ite_eq_left hi, ite_eq_left e2]; rfl
      · have e2 : ¬ x = t.toNat * 2 ^ 40 + i.toNat := by omega
        simp only [e, e2, ↓reduceIte]

/-- **An L store into the pool** (`POOL⟨t⟩[i] := v`), in bounds, is a store into the virtual pool
at the tagged address `t·2^40 + i`. -/
theorem vpool_set64t (m : Mem) (t i v : Word) (ht : t.toNat ≤ 1)
    (hi : i.toNat < (m.arr64 (tierA 0 t)).size) (hs : (m.arr64 (tierA 0 t)).size ≤ 2 ^ 40) :
    vpool (m.set64 (tierA 0 t) i v) = (vpool m).set! (t.toNat * 2 ^ 40 + i.toNat) v := by
  apply Array.ext_getElem?
  intro j
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  by_cases hj : j < 2 ^ 41
  · rw [vpool_getNat? _ j hj, vpool_getNat? m j hj, prd_set64t m t i v j ht hi hs hj]
    have hb : t.toNat * 2 ^ 40 + i.toNat < (vpool m).size := by rw [vpool_size]; omega
    by_cases e : t.toNat * 2 ^ 40 + i.toNat = j
    · subst e; simp [hb]
    · simp [e, Ne.symm e]
  · have e1 : (vpool (m.set64 (tierA 0 t) i v))[j]? = none :=
      Array.getElem?_eq_none (by rw [vpool_size]; omega)
    have e2 : (vpool m)[j]? = none := Array.getElem?_eq_none (by rw [vpool_size]; omega)
    have hij : t.toNat * 2 ^ 40 + i.toNat ≠ j := by omega
    simp [e1, e2, hij]

/-- An L load of the pool's tier `t` at index `i` (`POOL⟨t⟩[i]`), in bounds, reads the virtual
pool at the tagged address `t·2^40 + i`. -/
theorem vpool_ldt (m : Mem) (t i : Word) (ht : t.toNat ≤ 1)
    (hi : i.toNat < (m.arr64 (tierA 0 t)).size) (hs : (m.arr64 (tierA 0 t)).size ≤ 2 ^ 40)
    (h' : t.toNat * 2 ^ 40 + i.toNat < (vpool m).size) :
    (m.arr64 (tierA 0 t))[i.toNat] = (vpool m)[t.toNat * 2 ^ 40 + i.toNat] := by
  have hx : t.toNat * 2 ^ 40 + i.toNat < 2 ^ 41 := by omega
  have e := vpool_getNat? m _ hx
  rw [Array.getElem?_eq_getElem h'] at e
  have key : (m.arr64 (tierA 0 t))[i.toNat]?.getD 0 = prd m (UInt64.ofNat (t.toNat * 2 ^ 40 + i.toNat)) := by
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

/-- `vpool_ldt` for a writer's relative index `pb + k` (a `grind` lemma only for that shape: on a
tagged load `POOL⦃x⦄`, whose index is `x &&& …`, it would compete with `vpool_ld`). -/
theorem vpool_ldt_add (m : Mem) (t i k : Word) (ht : t.toNat ≤ 1)
    (hi : (i + k).toNat < (m.arr64 (tierA 0 t)).size) (hs : (m.arr64 (tierA 0 t)).size ≤ 2 ^ 40)
    (h' : t.toNat * 2 ^ 40 + (i + k).toNat < (vpool m).size) :
    (m.arr64 (tierA 0 t))[(i + k).toNat] = (vpool m)[t.toNat * 2 ^ 40 + (i + k).toNat] :=
  vpool_ldt m t (i + k) ht hi hs h'
-- (no grind pattern: `vpool_ldrel`/`vpool_ldidx` cover the writers' loads)

/-- A writer's store `POOL⟨⦃T⦄.tier⟩[⦃T⦄.idx + k] := v`, in bounds, is a store into the virtual
pool at `T + k`. -/
theorem vpool_stidx (m : Mem) (T k v : Word) (hT : T.toNat < 2 ^ 41)
    (hi : ((T &&& 1099511627775) + k).toNat < (m.arr64 (tierA 0 (T >>> 40))).size)
    (hs : (m.arr64 (tierA 0 (T >>> 40))).size ≤ 2 ^ 40)
    (hk : (T &&& 1099511627775).toNat + k.toNat < 2 ^ 40) :
    vpool (m.set64 (tierA 0 (T >>> 40)) ((T &&& 1099511627775) + k) v) =
      (vpool m).set! (T + k).toNat v := by
  rw [tag_idx_toNat] at hk
  have ht : (T >>> 40).toNat ≤ 1 := by rw [tag_tier_toNat]; omega
  rw [vpool_set64t m _ _ v ht hi hs]
  congr 1
  rw [tag_tier_toNat, UInt64.toNat_add, tag_idx_toNat, UInt64.toNat_add,
    Nat.mod_eq_of_lt (a := T.toNat % 2 ^ 40 + k.toNat) (by omega),
    Nat.mod_eq_of_lt (a := T.toNat + k.toNat) (by omega)]; omega
grind_pattern [arena_grind] vpool_stidx =>
  vpool (m.set64 (tierA 0 (T >>> 40)) ((T &&& 1099511627775) + k) v)

/-- A one-word store at the top, `POOL⟨⦃T⦄.tier⟩[⦃T⦄.idx] := v`, is a store into the virtual
pool at `T`. -/
theorem vpool_stidx0 (m : Mem) (T v : Word) (hT : T.toNat < 2 ^ 41)
    (hi : (T &&& 1099511627775).toNat < (m.arr64 (tierA 0 (T >>> 40))).size)
    (hs : (m.arr64 (tierA 0 (T >>> 40))).size ≤ 2 ^ 40) :
    vpool (m.set64 (tierA 0 (T >>> 40)) (T &&& 1099511627775) v) = (vpool m).set! T.toNat v := by
  have ht : (T >>> 40).toNat ≤ 1 := by rw [tag_tier_toNat]; omega
  rw [vpool_set64t m _ _ v ht hi hs, tag_split]
grind_pattern [arena_grind] vpool_stidx0 => vpool (m.set64 (tierA 0 (T >>> 40)) (T &&& 1099511627775) v)

/-- A writer's load `POOL⟨⦃T⦄.tier⟩[⦃T⦄.idx + k]`, in bounds, reads the virtual pool at `T + k`. -/
theorem vpool_ldidx (m : Mem) (T k : Word) (hT : T.toNat < 2 ^ 41)
    (hi : ((T &&& 1099511627775) + k).toNat < (m.arr64 (tierA 0 (T >>> 40))).size)
    (hs : (m.arr64 (tierA 0 (T >>> 40))).size ≤ 2 ^ 40)
    (hk : (T &&& 1099511627775).toNat + k.toNat < 2 ^ 40) (h' : (T + k).toNat < (vpool m).size) :
    (m.arr64 (tierA 0 (T >>> 40)))[((T &&& 1099511627775) + k).toNat] = (vpool m)[(T + k).toNat] := by
  rw [tag_idx_toNat] at hk
  have ht : (T >>> 40).toNat ≤ 1 := by rw [tag_tier_toNat]; omega
  have e : (T >>> 40).toNat * 2 ^ 40 + ((T &&& 1099511627775) + k).toNat = (T + k).toNat := by
    rw [tag_tier_toNat, UInt64.toNat_add, tag_idx_toNat, UInt64.toNat_add,
      Nat.mod_eq_of_lt (a := T.toNat % 2 ^ 40 + k.toNat) (by omega),
      Nat.mod_eq_of_lt (a := T.toNat + k.toNat) (by omega)]; omega
  rw [vpool_ldt m _ _ ht hi hs (by rw [e]; exact h')]
  simp only [e]
grind_pattern [arena_grind] vpool_ldidx =>
  (m.arr64 (tierA 0 (T >>> 40)))[((T &&& 1099511627775) + k).toNat], vpool m

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
    (hi : (T - ((T >>> 40) <<< 40) + k).toNat < (m.arr64 (tierA 0 (T >>> 40))).size)
    (hs : (m.arr64 (tierA 0 (T >>> 40))).size ≤ 2 ^ 40)
    (hk : (T - ((T >>> 40) <<< 40)).toNat + k.toNat < 2 ^ 40) :
    vpool (m.set64 (tierA 0 (T >>> 40)) (T - ((T >>> 40) <<< 40) + k) v) =
      (vpool m).set! (T + k).toNat v := by
  have ht : (T >>> 40).toNat ≤ 1 := by rw [tag_tier_toNat]; omega
  rw [vpool_set64t m _ _ v ht hi hs, tag_rel T k hT hk]
grind_pattern [arena_grind] vpool_strel =>
  vpool (m.set64 (tierA 0 (T >>> 40)) (T - ((T >>> 40) <<< 40) + k) v)

/-- A writer's load `POOL⟨⦃T⦄.tier⟩[(T - ⦃T⦄.base) + k]` (its top `T`, the tier and the relative
base decoded once), in bounds, reads the virtual pool at `T + k`. -/
theorem vpool_ldrel (m : Mem) (T k : Word) (hT : T.toNat < 2 ^ 41)
    (hi : (T - ((T >>> 40) <<< 40) + k).toNat < (m.arr64 (tierA 0 (T >>> 40))).size)
    (hs : (m.arr64 (tierA 0 (T >>> 40))).size ≤ 2 ^ 40)
    (hk : (T - ((T >>> 40) <<< 40)).toNat + k.toNat < 2 ^ 40)
    (h' : (T + k).toNat < (vpool m).size) :
    (m.arr64 (tierA 0 (T >>> 40)))[(T - ((T >>> 40) <<< 40) + k).toNat] = (vpool m)[(T + k).toNat] := by
  have ht : (T >>> 40).toNat ≤ 1 := by rw [tag_tier_toNat]; omega
  have e := tag_rel T k hT hk
  rw [vpool_ldt m _ _ ht hi hs (by rw [e]; exact h')]
  simp only [e]
grind_pattern [arena_grind] vpool_ldrel =>
  (m.arr64 (tierA 0 (T >>> 40)))[(T - ((T >>> 40) <<< 40) + k).toNat], vpool m

/-- A pool store leaves the other words of the virtual pool alone. -/
theorem vpool_set64t_get (m : Mem) (t i v : Word) (j : Nat) (ht : t.toNat ≤ 1)
    (hi : i.toNat < (m.arr64 (tierA 0 t)).size) (hs : (m.arr64 (tierA 0 t)).size ≤ 2 ^ 40)
    (hij : t.toNat * 2 ^ 40 + i.toNat ≠ j) :
    (vpool (m.set64 (tierA 0 t) i v))[j]? = (vpool m)[j]? := by
  rw [vpool_set64t m t i v ht hi hs, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  simp [hij]

/-- Stores elsewhere leave the virtual pool alone. -/
theorem vpool_set64_ne (m : Mem) (a : ArrId) (i v : Word) (h : a ≠ POOL ∧ a ≠ POOL1) :
    vpool (m.set64 a i v) = vpool m := by
  have e : ∀ t, (m.set64 a i v).arr64 (tierA 0 t) = m.arr64 (tierA 0 t) := fun t =>
    Mem.arr64_set64_ne _ _ _ _ _ (Ne.symm (tierA_pool_ne t a h.1 h.2))
  simp only [vpool, prd, e]
grind_pattern [arena_grind] vpool_set64_ne => vpool (m.set64 a i v)

/-- The virtual pool reads only the pool's two arrays. -/
theorem vpool_congr {m m' : Mem} (h0 : m'.arr64 POOL = m.arr64 POOL)
    (h1 : m'.arr64 POOL1 = m.arr64 POOL1) : vpool m' = vpool m := by
  have e : ∀ t, m'.arr64 (tierA 0 t) = m.arr64 (tierA 0 t) := fun t => by
    rcases tierA_pool t with h | h <;> rw [h] <;> assumption
  simp only [vpool, prd, e]

theorem pcap_congr {m m' : Mem} (h0 : (m'.arr64 POOL).size = (m.arr64 POOL).size)
    (h1 : (m'.arr64 POOL1).size = (m.arr64 POOL1).size) : pcap m' = pcap m := by
  simp only [pcap, PSmall, h0, h1]

theorem pcap_congr' {m m' : Mem} (h0 : m'.arr64 POOL = m.arr64 POOL)
    (h1 : m'.arr64 POOL1 = m.arr64 POOL1) : pcap m' = pcap m :=
  pcap_congr (by rw [h0]) (by rw [h1])

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

grind_pattern [arena_grind] PFrame.size => PFrame m m', m'.words.size
grind_pattern [arena_grind] PFrame.bytes => PFrame m m', m'.bytes
grind_pattern [arena_grind] PFrame.glob => PFrame m m', m'.glob
grind_pattern [arena_grind] PFrame.size0 => PFrame m m', (m'.arr64 POOL).size
grind_pattern [arena_grind] PFrame.size1 => PFrame m m', (m'.arr64 POOL1).size

theorem PFrame.refl (m : Mem) : PFrame m m := ⟨rfl, rfl, fun _ _ _ => rfl, rfl, rfl, rfl⟩
grind_pattern [arena_grind] PFrame.refl => PFrame m m

theorem PFrame.trans {m m' m'' : Mem} (h : PFrame m m') (h' : PFrame m' m'') : PFrame m m'' :=
  ⟨h'.bytes.trans h.bytes, h'.size.trans h.size, fun b h0 h1 => (h'.arr b h0 h1).trans (h.arr b h0 h1),
    h'.size0.trans h.size0, h'.size1.trans h.size1, h'.glob.trans h.glob⟩
grind_pattern [arena_grind] PFrame.trans => PFrame m m'', PFrame m' m''

theorem PFrame.set64 {m m' : Mem} (t i v : Word) (h : PFrame m m') :
    PFrame m (m'.set64 (tierA 0 t) i v) := by
  refine ⟨h.bytes, by simp [Mem.set64, h.size], fun b h0 h1 => ?_, ?_, ?_, h.glob⟩
  · rw [Mem.arr64_set64_ne _ _ _ _ _ (tierA_pool_ne t b h0 h1), h.arr b h0 h1]
  · rcases tierA_pool t with e | e <;> rw [e]
    · rw [Mem.size_arr64_set64, h.size0]
    · rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide), h.size0]
  · rcases tierA_pool t with e | e <;> rw [e]
    · rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide), h.size1]
    · rw [Mem.size_arr64_set64, h.size1]
grind_pattern [arena_grind] PFrame.set64 => PFrame m (m'.set64 (tierA 0 t) i v)

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
    (m'.arr64 (tierA 0 t)).size = (m.arr64 (tierA 0 t)).size := by
  rcases tierA_pool t with e | e <;> rw [e]
  · exact h.size0
  · exact h.size1
grind_pattern [arena_grind] PFrame.tsize => PFrame m m', (m'.arr64 (tierA 0 t)).size

theorem PFrame.pcap {m m' : Mem} (h : PFrame m m') : pcap m' = pcap m :=
  pcap_congr h.size0 h.size1
grind_pattern [arena_grind] PFrame.pcap => PFrame m m', pcap m'

theorem PFrame.ctl {m m' : Mem} (h : PFrame m m') : m'.arr64 CTL = m.arr64 CTL :=
  h.arr CTL (by decide) (by decide)
grind_pattern [arena_grind] PFrame.ctl => PFrame m m', m'.arr64 CTL

/-! ## The pool invariant -/

/-- The pool top, `CTL[0]`: the top of the current tier, a tagged address. -/
def _root_.L.Mem.top (m : Mem) : Word := (m.arr64 CTL)[0]?.getD 0

/-- The saved tier-0 pool top, `PT0[0]`. -/
def _root_.L.Mem.ptop0 (m : Mem) : Word := (m.arr64 PT0)[0]?.getD 0

theorem Mem.ptop0_eq (m : Mem) (h : 0 < (m.arr64 PT0).size) : m.ptop0 = (m.arr64 PT0)[0] := by
  simp [Mem.ptop0, h]
grind_pattern [arena_grind] Mem.ptop0_eq => m.ptop0, (m.arr64 PT0)[0]

theorem Mem.ptop0_set64 (m : Mem) (v : Word) (h : 0 < (m.arr64 PT0).size) :
    (m.set64 PT0 0 v).ptop0 = v := by
  simp [Mem.ptop0, Mem.arr64_set64_same, h]
grind_pattern [arena_grind] Mem.ptop0_set64 => (m.set64 PT0 0 v).ptop0

@[arena_grind =] theorem Mem.ptop0_set64_ne (m : Mem) (a : ArrId) (i v : Word) (h : a ≠ PT0) :
    (m.set64 a i v).ptop0 = m.ptop0 := by
  simp only [Mem.ptop0, Mem.arr64_set64_ne _ _ _ _ _ (Ne.symm h)]

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
(`pcap m < 2^63`), the top is an address of a tier (`top ≤ pcap`) inside its tier's array, and,
while the top is in tier 1, the saved tier-0 top `PT0[0]` is inside tier 0's array (with the top
in tier 0, `PT0[0]` is dead: `scratch_reset` overwrites it before reading it, `pool_alloc0`
reads it only in tier 1; so the truncation, which cuts `POOL` to the top, keeps the invariant). -/
def PoolOK (m : Mem) : Prop :=
  CTL < m.words.size ∧ 0 < (m.arr64 CTL).size ∧ pcap m < 2 ^ 63 ∧ m.top.toNat ≤ pcap m ∧
  (m.top.toNat < 2 ^ 40 ∨ m.ptop0.toNat ≤ (m.arr64 POOL).size) ∧
  (m.top &&& 1099511627775).toNat ≤ (m.arr64 (tierA 0 (m.top >>> 40))).size

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
  inn : (m'.top &&& 1099511627775).toNat ≤ (m'.arr64 (tierA 0 (m'.top >>> 40))).size

/-- A slice of the pool in use: below the top, and, while the scratch tier is open (the top in
tier 1), a slice of tier 0 lies below the saved tier-0 top `PT0[0]` (the words of tier 0 above
it are written by the promotion's copies, `pool_alloc0`). -/
def SliceOK (m : Mem) (o l : Word) : Prop :=
  o.toNat + l.toNat ≤ m.top.toNat ∧
  (m.top.toNat < 2 ^ 40 ∨ 2 ^ 40 ≤ o.toNat ∨ o.toNat + l.toNat ≤ m.ptop0.toNat)

/-- The tier-array size facts of a pool invariant. -/
theorem PoolOK.small {m : Mem} (h : PoolOK m) : PSmall m := pcap_small m (by have := h.2.2.1; omega)

theorem PoolOK.top41 {m : Mem} (h : PoolOK m) : m.top.toNat < 2 ^ 41 := by
  have := h.2.2.2.1; rw [pcap_eq m (by have := h.2.2.1; omega)] at this; omega

theorem PSmall.tier {m : Mem} (h : PSmall m) (t : Word) : (m.arr64 (tierA 0 t)).size < 2 ^ 40 := by
  rcases tierA_pool t with e | e <;> rw [e]
  · exact h.1
  · exact h.2

theorem pcap_tier (m : Mem) (t : Word) (h : pcap m < 2 ^ 64) : (m.arr64 (tierA 0 t)).size < 2 ^ 40 :=
  (pcap_small m h).tier t
grind_pattern [arena_grind] pcap_tier => pcap m, (m.arr64 (tierA 0 t)).size

/-- Two addresses whose `Nat`s have the same quotient by `2^40` have the same tier. -/
theorem tag_tier_eq {x y : Word} (h : x.toNat / 2 ^ 40 = y.toNat / 2 ^ 40) : x >>> 40 = y >>> 40 :=
  UInt64.toNat_inj.mp (by rw [tag_tier_toNat, tag_tier_toNat, h])

/-- **The writer's `Grows`**: a pool function that wrote only the pool's tiers and the top, kept
the pool below the old top, and moved the top up by `k` words that fit in the top's tier array
(its length check), grew the pool. -/
theorem Grows.intro (m m' : Mem) (hok : PoolOK m) (hf : PFrame (m.set64 CTL 0 m'.top) m')
    (ha : Agree (vpool m') (vpool m) m.top.toNat) (hle : m.top.toNat ≤ m'.top.toNat)
    (hk : (m.top &&& 1099511627775).toNat + (m'.top.toNat - m.top.toNat) ≤
      (m.arr64 (tierA 0 (m.top >>> 40))).size) : Grows m m' := by
  rw [tag_idx_toNat] at hk
  have hs := hok.small
  have h41 := hok.top41
  have hsz := hs.tier (m.top >>> 40)
  have hp : pcap m' = pcap m := by rw [hf.pcap, pcap_set64]
  have hp' : pcap m = 2 ^ 41 - 1 := pcap_of_small m hs
  have hq : m'.top.toNat / 2 ^ 40 = m.top.toNat / 2 ^ 40 := by omega
  have ht : m'.top >>> 40 = m.top >>> 40 := tag_tier_eq hq
  have hsize : (m'.arr64 (tierA 0 (m'.top >>> 40))).size = (m.arr64 (tierA 0 (m.top >>> 40))).size := by
    rw [ht]
    rcases tierA_pool (m.top >>> 40) with e | e <;> rw [e]
    · rw [hf.size0, Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
    · rw [hf.size1, Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  refine ⟨hf, ha, hle, by omega, hp, by omega, ?_⟩
  rw [hsize, tag_idx_toNat]; omega
grind_pattern [arena_grind] Grows.intro => Grows m m'

/-- **The writer's final step**: the pool writes `m ↝ m₂` (only the tier arrays, `PFrame`), the
pool below the top kept, then `CTL[0] := top + n` with the `n` words inside the top's tier array
(the length check): the pool grew. -/
theorem Grows.write (m m₂ : Mem) (n : Word) (hok : PoolOK m) (hf : PFrame m m₂)
    (ha : Agree (vpool m₂) (vpool m) m.top.toNat)
    (hk : (m.top &&& 1099511627775).toNat + n.toNat ≤ (m.arr64 (tierA 0 (m.top >>> 40))).size) :
    Grows m (m₂.set64 CTL 0 (m.top + n)) := by
  rw [tag_idx_toNat] at hk
  have hs := hok.small
  have h41 := hok.top41
  have hsz := hs.tier (m.top >>> 40)
  have hctl : 0 < (m₂.arr64 CTL).size := by rw [hf.ctl]; exact hok.2.1
  have htop : (m₂.set64 CTL 0 (m.top + n)).top = m.top + n := Mem.top_set64 _ _ hctl
  have hn : (m.top + n).toNat = m.top.toNat + n.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  apply Grows.intro m _ hok
  · rw [htop]; exact PFrame.set64_both CTL 0 _ hf (by decide) (by decide)
  · rw [vpool_set64_ne _ _ _ _ ⟨by decide, by decide⟩]; exact ha
  · rw [htop, hn]; omega
  · rw [htop, hn, tag_idx_toNat]; omega
grind_pattern [arena_grind] Grows.write => Grows m (m₂.set64 CTL 0 (m.top + n))

theorem ptop0_congr {m m' : Mem} (h : m'.arr64 PT0 = m.arr64 PT0) : m'.ptop0 = m.ptop0 := by
  simp only [Mem.ptop0, h]

/-- The pool invariant survives a frame that keeps the pool's arrays, `PT0`, `CTL`'s size and top. -/
theorem PoolOK.frame {m m' : Mem} (h : PoolOK m) (h0 : m'.arr64 POOL = m.arr64 POOL)
    (h1 : m'.arr64 POOL1 = m.arr64 POOL1) (ht : m'.arr64 PT0 = m.arr64 PT0)
    (hc : (m'.arr64 CTL).size = (m.arr64 CTL).size) (htop : m'.top = m.top)
    (hw : m'.words.size = m.words.size) : PoolOK m' := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h
  have hp : pcap m' = pcap m := pcap_congr' h0 h1
  refine ⟨by rw [hw]; exact a1, by rw [hc]; exact a2, by rw [hp]; exact a3, by rw [hp, htop]; exact a4,
    by rw [ptop0_congr ht, h0, htop]; exact a5, ?_⟩
  rw [htop]
  rcases tierA_pool (m.top >>> 40) with e | e <;> rw [e] <;> rw [e] at a6
  · rw [h0]; exact a6
  · rw [h1]; exact a6

/-- A grown pool keeps the pool invariant. -/
theorem PoolOK.grows {m m' : Mem} (h : PoolOK m) (hg : Grows m m') : PoolOK m' := by
  obtain ⟨hf, -, hle, htp, hp, ht, hin⟩ := hg
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hc : m'.arr64 CTL = (m.set64 CTL 0 m'.top).arr64 CTL := hf.ctl
  refine ⟨?_, ?_, by omega, htp, ?_, hin⟩
  · rw [hf.size, Mem.words_size_set64]; exact h1
  · rw [hc, Mem.size_arr64_set64]; exact h2
  · rw [Mem.ptop0, hf.arr PT0 (by decide) (by decide), Mem.arr64_set64_ne _ _ _ _ _ (by decide),
      hf.size0, Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
    rcases h5 with h5 | h5
    · rcases ht with ht | ht
      · exact .inl ht
      · omega
    · exact .inr h5
grind_pattern [arena_grind] PoolOK.grows => Grows m m', PoolOK m'

/-- A slice in use stays in use when the pool grows. -/
theorem SliceOK.grows {m m' : Mem} {o l : Word} (h : SliceOK m o l) (hg : Grows m m') :
    SliceOK m' o l := by
  obtain ⟨hf, -, hle, -, -, ht, -⟩ := hg
  have hglob : m'.ptop0 = m.ptop0 := by
    rw [Mem.ptop0, Mem.ptop0, hf.arr PT0 (by decide) (by decide), Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  obtain ⟨h1, h2⟩ := h
  refine ⟨by omega, ?_⟩
  rw [hglob]; omega
grind_pattern [arena_grind] SliceOK.grows => Grows m m', SliceOK m' o l

/-- The slice a pool function appended, `[top, top')`, is in use. -/
theorem SliceOK.fresh {m m' : Mem} {r : Word} (hg : Grows m m') (h : m'.top = m.top + r) :
    SliceOK m' m.top r := by
  have hle := hg.le
  have ht := hg.tier
  have hr := r.toNat_lt
  have hn : m'.top.toNat = m.top.toNat + r.toNat := by
    rw [h] at hle ⊢
    rw [UInt64.toNat_add] at hle ⊢
    rcases Nat.lt_or_ge (m.top.toNat + r.toNat) (2 ^ 64) with h1 | h1
    · exact Nat.mod_eq_of_lt h1
    · exfalso
      have e : (m.top.toNat + r.toNat) % 2 ^ 64 = m.top.toNat + r.toNat - 2 ^ 64 := by
        rw [Nat.mod_eq_sub_mod h1]; exact Nat.mod_eq_of_lt (by omega)
      omega
  unfold SliceOK
  omega
grind_pattern [arena_grind] SliceOK.fresh => Grows m m', SliceOK m' m.top r

theorem SliceOK.le {m : Mem} {o l : Word} (h : SliceOK m o l) : o.toNat + l.toNat ≤ m.top.toNat := h.1
grind_pattern [arena_grind] SliceOK.le => SliceOK m o l

/-- Growth is transitive. -/
theorem Grows.trans (m m' m'' : Mem) (h : Grows m m') (h' : Grows m' m'') : Grows m m'' := by
  have hc : (m'.arr64 CTL).size = (m.arr64 CTL).size := by
    rw [h.frame.ctl, Mem.size_arr64_set64]
  have hf : PFrame (m.set64 CTL 0 m''.top) m'' := by
    refine ⟨by rw [h'.frame.bytes, Mem.bytes_set64, h.frame.bytes, Mem.bytes_set64, Mem.bytes_set64],
      by rw [h'.frame.size, Mem.words_size_set64, h.frame.size, Mem.words_size_set64, Mem.words_size_set64],
      fun b h0 h1 => ?_, ?_, ?_, by show m''.glob = m.glob; rw [h'.frame.glob]; exact h.frame.glob⟩
    · rw [h'.frame.arr b h0 h1]
      by_cases hbc : b = CTL
      · subst hbc
        rw [Mem.arr64_set64_same, Mem.arr64_set64_same, h.frame.ctl, Mem.arr64_set64_same]
        simp
      · rw [Mem.arr64_set64_ne _ _ _ _ _ hbc, h.frame.arr b h0 h1, Mem.arr64_set64_ne _ _ _ _ _ hbc,
          Mem.arr64_set64_ne _ _ _ _ _ hbc]
    · rw [h'.frame.size0, Mem.arr64_set64_ne _ _ _ _ _ (by decide), h.frame.size0,
        Mem.arr64_set64_ne _ _ _ _ _ (by decide), Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
    · rw [h'.frame.size1, Mem.arr64_set64_ne _ _ _ _ _ (by decide), h.frame.size1,
        Mem.arr64_set64_ne _ _ _ _ _ (by decide), Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  have h1 := h.le; have h2 := h'.le; have t1 := h.tier; have t2 := h'.tier
  exact ⟨hf, fun j hj => (h'.agree j (by omega)).trans (h.agree j hj), by omega, h'.cap,
    h'.pcapEq.trans h.pcapEq, by omega, h'.inn⟩
grind_pattern [arena_grind] Grows.trans => Grows m m', Grows m' m''

/-- The scratch flag, `CTL[1]`. -/
def _root_.L.Mem.flag (m : Mem) : Word := (m.arr64 CTL)[1]?.getD 0

theorem PFrame.flag {m m' : Mem} (h : PFrame m m') : m'.flag = m.flag := by
  simp only [Mem.flag, h.ctl]
grind_pattern [arena_grind] PFrame.flag => PFrame m m', m'.flag

@[arena_grind =] theorem Mem.flag_set64_top (m : Mem) (v : Word) : (m.set64 CTL 0 v).flag = m.flag := by
  simp only [Mem.flag, Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  simp

@[arena_grind =] theorem Mem.flag_set64_ne (m : Mem) (a : ArrId) (i v : Word) (h : a ≠ CTL) :
    (m.set64 a i v).flag = m.flag := by
  simp only [Mem.flag, Mem.arr64_set64_ne _ _ _ _ _ (Ne.symm h)]

@[arena_grind =] theorem Mem.flag_setG (m : Mem) (g : GVar) (v : Word) : (m.setG g v).flag = m.flag := rfl

/-- **The mode**: outside the scratch tier (flag `0`) the top is in tier 0. It holds in the
kernel (flag set) and in the front end (tier 0), not inside a promotion (flag cleared around the
persistent interning while the top is in tier 1, which copies its slices to tier 0). -/
def ModeOK (m : Mem) : Prop := m.flag ≠ 0 ∨ m.top.toNat < 2 ^ 40

/-- A slice in use is a tier-0 slice whenever the flag is `0`, under the mode. -/
theorem ModeOK.slice0 {m : Mem} {o l : Word} (h : ModeOK m) (hs : SliceOK m o l) :
    m.flag = 0 → o.toNat < 2 ^ 40 := by
  intro hf
  rcases h with h | h
  · exact absurd hf h
  · have := hs.1; omega

/-- **A record's slice** (of a node of tier `t`): in use (`SliceOK`), and, for a node of tier 0
(the persistent tables), a slice of tier 0: the promotion copies a scratch slice to tier 0
(`pool_copy0`), so dropping the scratch tier keeps every persistent node's slice (`scratch_reset`). -/
def RSlice (m : Mem) (t o l : Word) : Prop := SliceOK m o l ∧ (t = 0 → o.toNat < 2 ^ 40)

/-- The slice of a node the library pushes into tier `t` (tier 0 only with the flag `0`). -/
theorem RSlice.intern {m : Mem} {t o l : Word} (hs : SliceOK m o l) (h0 : m.flag = 0 → o.toNat < 2 ^ 40)
    (ht : t = 0 → m.flag = 0) : RSlice m t o l := ⟨hs, fun e => h0 (ht e)⟩

theorem RSlice.le {m : Mem} {t o l : Word} (h : RSlice m t o l) : o.toNat + l.toNat ≤ m.top.toNat :=
  h.1.1
grind_pattern [arena_grind] RSlice.le => RSlice m t o l

theorem RSlice.grows {m m' : Mem} {t o l : Word} (h : RSlice m t o l) (hg : Grows m m') :
    RSlice m' t o l := ⟨SliceOK.grows h.1 hg, h.2⟩
grind_pattern [arena_grind] RSlice.grows => Grows m m', RSlice m' t o l

theorem SliceOK_congr {m m' : Mem} (o l : Word) (ht : m'.top = m.top) (hp : m'.ptop0 = m.ptop0) :
    SliceOK m' o l ↔ SliceOK m o l := by
  simp only [SliceOK, ht, hp]

theorem RSlice_congr {m m' : Mem} (t o l : Word) (ht : m'.top = m.top) (hp : m'.ptop0 = m.ptop0) :
    RSlice m' t o l ↔ RSlice m t o l := by
  simp only [RSlice, SliceOK_congr o l ht hp]

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

/-- A slice below the old top reads the same after growth. -/
theorem Grows.pv {m m' : Mem} {o l : Nat} (hg : Grows m m') (h : o + l ≤ m.top.toNat) :
    L.Arena.pv (vpool m') o l = L.Arena.pv (vpool m) o l :=
  Agree.pv _ _ _ _ _ hg.agree h
grind_pattern [arena_grind] Grows.pv => Grows m m', L.Arena.pv (vpool m') o l

theorem Grows.norm {m m' : Mem} {o l : Nat} (hg : Grows m m') (h : o + l ≤ m.top.toNat) :
    Norm (vpool m') o l ↔ Norm (vpool m) o l := by
  simp only [Norm]
  constructor <;> intro hn hl
  · rw [← hg.agree _ (by omega)]; exact hn hl
  · rw [hg.agree _ (by omega)]; exact hn hl
grind_pattern [arena_grind] Grows.norm => Grows m m', Norm (vpool m') o l

/-- Below `2^41` the total view and the virtual pool hold the same slices. -/
theorem pv_tpool (m : Mem) (o l : Nat) (h : o + l ≤ 2 ^ 41) :
    L.Arena.pv (tpool m) o l = L.Arena.pv (vpool m) o l :=
  Agree.pv _ _ _ _ _ (tpool_vpool m) h

theorem Norm_tpool (m : Mem) (o l : Nat) (h : o + l ≤ 2 ^ 41) :
    Norm (tpool m) o l ↔ Norm (vpool m) o l := by
  simp only [Norm]
  constructor <;> intro hn hl
  · rw [← tpool_vpool m _ (by omega)]; exact hn hl
  · rw [tpool_vpool m _ (by omega)]; exact hn hl

/-- Growth keeps the total view below the old top (an address of a tier). -/
theorem Grows.tagree {m m' : Mem} (hg : Grows m m') (h : m.top.toNat ≤ 2 ^ 41) :
    Agree (tpool m') (tpool m) m.top.toNat := fun j hj => by
  rw [tpool_vpool m' j (by omega), tpool_vpool m j (by omega)]; exact hg.agree j hj

theorem Norm.zero (p : Array Word) (o : Nat) : Norm p o 0 := by simp [Norm]
grind_pattern [arena_grind] Norm.zero => Norm p o 0

theorem Norm.of_top (p : Array Word) (o l j : Nat) (hj : j = o + (l - 1))
    (h : j < p.size) (hne : p[j] ≠ 0) : Norm p o l := by
  subst hj; simp [Norm, h, hne]
grind_pattern [arena_grind] Norm.of_top => Norm p o l, p[j]

end L.Arena
