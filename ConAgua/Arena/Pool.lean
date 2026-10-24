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

Proofs read the pool only through `vpool m`, an array with a word for every word address `x`:
`prd m x`, what the L load of the pool at `x` reads (`0` where it aborts). On today's layout
that is word `x` of the pool array; when the pool becomes a tiered array (`docs/design/tierpool.md`)
only `prd`, the access lemmas below and `PoolOK`/`SliceOK`/`Grows` change. So that the switch
stays inside this file, proofs outside it never unfold `vpool`/`prd`, and bound the pool with
`pcap`, never with `(vpool m).size` (which is `2^64`). -/

/-- The pool word at address `x`: what the L load of the pool at `x` reads, `0` where it aborts. -/
def prd (m : Mem) (x : Word) : Word := (m.arr64 POOL)[x.toNat]?.getD 0

/-- The pool's capacity: the words an address can reach. -/
def pcap (m : Mem) : Nat := (m.arr64 POOL).size

/-- A value the kernel cannot unfold, with its equation. -/
structure Sealed (α : Type) (a : α) where
  val : α
  eq : val = a

instance (α : Type) (a : α) : Inhabited (Sealed α a) := ⟨⟨a, rfl⟩⟩

/-- `2^64`, sealed: the kernel never computes the virtual pool's `2^64` words (a proof whose
check reduces `(vpool m).size` would otherwise build them: 16 GB). -/
opaque vszS : Sealed Nat (2 ^ 64)

/-- The virtual pool's length, `2^64` (`vsz_eq`). -/
def vsz : Nat := vszS.val

theorem vsz_eq : vsz = 2 ^ 64 := vszS.eq

/-- **The virtual pool**: word `j` is `prd m j`, for every word address `j`. -/
def vpool (m : Mem) : Array Word := Array.ofFn fun j : Fin vsz => prd m (UInt64.ofNat j)

@[arena_grind =] theorem vpool_size (m : Mem) : (vpool m).size = 2 ^ 64 := by
  rw [vpool, Array.size_ofFn, vsz_eq]

-- not `simp [vpool]`: it evaluates the `2^64`-element array (16 GB)
theorem vpool_get? (m : Mem) (x : Word) : (vpool m)[x.toNat]? = some (prd m x) := by
  have h : x.toNat < vsz := vsz_eq ▸ x.toNat_lt
  rw [vpool, Array.getElem?_ofFn]; simp only [h, ↓reduceDIte]
  exact congrArg (fun y => some (prd m y)) (UInt64.ofNat_toNat)

-- no tactic may unfold the `2^64`-element array
attribute [irreducible] vpool

theorem vpool_getNat? (m : Mem) (j : Nat) (h : j < 2 ^ 64) :
    (vpool m)[j]? = some ((m.arr64 POOL)[j]?.getD 0) := by
  have hx : (UInt64.ofNat j).toNat = j := by
    simp only [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt h
  rw [← hx, vpool_get?, prd, hx]

/-- An L load of the pool, in bounds, reads the virtual pool. -/
theorem vpool_ld (m : Mem) (j : Nat) (h : j < (m.arr64 POOL).size) (h' : j < (vpool m).size) :
    (m.arr64 POOL)[j] = (vpool m)[j] := by
  have h64 : j < 2 ^ 64 := vpool_size m ▸ h'
  have e := vpool_getNat? m j h64
  rw [Array.getElem?_eq_getElem h', Array.getElem?_eq_getElem h, Option.getD_some] at e
  exact (Option.some.inj e).symm
grind_pattern [arena_grind] vpool_ld => (m.arr64 POOL)[j], vpool m

/-- A total read of the virtual pool is a total read of the pool (today's layout). -/
theorem vpool_getD (m : Mem) (x : Word) :
    (vpool m)[x.toNat]?.getD 0 = (m.arr64 POOL)[x.toNat]?.getD 0 := by
  rw [vpool_get?]; rfl
grind_pattern [arena_grind] vpool_getD => (vpool m)[x.toNat]?.getD 0

/-- Below the capacity, the virtual pool is the pool. -/
theorem vpool_agree (m : Mem) (h : pcap m < 2 ^ 64) : Agree (vpool m) (m.arr64 POOL) (pcap m) := by
  intro j hj
  simp only [pcap] at hj h
  rw [vpool_getNat? m j (by omega), Array.getElem?_eq_getElem hj]; rfl

/-- An L store into the pool, in bounds, is a store into the virtual pool. -/
theorem vpool_set64 (m : Mem) (i v : Word) (h : i.toNat < pcap m) :
    vpool (m.set64 POOL i v) = (vpool m).set! i.toNat v := by
  apply Array.ext_getElem?
  intro j
  simp only [pcap] at h
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  by_cases hj : j < 2 ^ 64
  · rw [vpool_getNat? _ j hj, vpool_getNat? m j hj, Mem.arr64_set64_same,
      Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    have hi : i.toNat < (vpool m).size := by rw [vpool_size]; exact i.toNat_lt
    by_cases hij : i.toNat = j
    · subst hij; simp [h, hi]
    · simp [hij]
  · have e1 : (vpool (m.set64 POOL i v))[j]? = none :=
      Array.getElem?_eq_none (by rw [vpool_size]; omega)
    have e2 : (vpool m)[j]? = none := Array.getElem?_eq_none (by rw [vpool_size]; omega)
    have hij : i.toNat ≠ j := fun e => hj (e ▸ i.toNat_lt)
    simp [e1, e2, hij]
grind_pattern [arena_grind] vpool_set64 => vpool (m.set64 POOL i v)

/-- Stores elsewhere leave the virtual pool alone. -/
theorem vpool_set64_ne (m : Mem) (a : ArrId) (i v : Word) (h : a ≠ POOL) :
    vpool (m.set64 a i v) = vpool m := by
  simp only [vpool, prd, Mem.arr64_set64_ne _ _ _ _ _ (Ne.symm h)]
grind_pattern [arena_grind] vpool_set64_ne => vpool (m.set64 a i v)

/-- The virtual pool reads only the pool. -/
theorem vpool_congr {m m' : Mem} (h : m'.arr64 POOL = m.arr64 POOL) : vpool m' = vpool m := by
  simp only [vpool, prd, h]

theorem pcap_congr {m m' : Mem} (h : m'.arr64 POOL = m.arr64 POOL) : pcap m' = pcap m := by
  simp only [pcap, h]

@[arena_grind =] theorem pcap_set64 (m : Mem) (a : ArrId) (i v : Word) :
    pcap (m.set64 a i v) = pcap m := by
  simp only [pcap]
  by_cases h : a = POOL
  · subst h; rw [Mem.size_arr64_set64]
  · rw [Mem.arr64_set64_ne _ _ _ _ _ (Ne.symm h)]

/-! ## The pool invariant -/

/-- The pool top, `CTL[0]`. -/
def _root_.L.Mem.top (m : Mem) : Word := (m.arr64 CTL)[0]?.getD 0

theorem Mem.top_eq (m : Mem) (h : 0 < (m.arr64 CTL).size) : m.top = (m.arr64 CTL)[0] := by
  simp [Mem.top, h]
grind_pattern [arena_grind] Mem.top_eq => m.top, (m.arr64 CTL)[0]

theorem Mem.top_set64 (m : Mem) (v : Word) (h : 0 < (m.arr64 CTL).size) :
    (m.set64 CTL 0 v).top = v := by
  simp [Mem.top, Mem.arr64_set64_same, h]
grind_pattern [arena_grind] Mem.top_set64 => (m.set64 CTL 0 v).top

theorem Frame.top (m m' : Mem) (h : Frame POOL m m') : m'.top = m.top := by
  simp only [Mem.top, h.2.2 CTL (by decide)]
grind_pattern [arena_grind] Frame.top => Frame POOL m m', m'.top

theorem Frame.size_ctl (m m' : Mem) (h : Frame POOL m m') :
    (m'.arr64 CTL).size = (m.arr64 CTL).size := by
  rw [h.2.2 CTL (by decide)]
grind_pattern [arena_grind] Frame.size_ctl => Frame POOL m m', (m'.arr64 CTL).size

/-- The pool invariant: both arrays exist and the top is inside the pool. The pool has fewer
than `2^63` words, so that the sum of two slice lengths (`nat_mul`'s `la + lb`) is a word. -/
def PoolOK (m : Mem) : Prop :=
  CTL < m.words.size ∧ 0 < (m.arr64 CTL).size ∧ pcap m < 2 ^ 63 ∧ m.top.toNat ≤ pcap m

/-- `m'` is `m` with limbs appended to the pool: only the pool and the top changed, the pool
below the old top did not, and the top only moved up, staying inside the pool. Every pool
function posts it; a state relation that refers only to slices below the top is preserved by
it (`L.Arena.Refine`, `hgrow`). -/
def Grows (m m' : Mem) : Prop :=
  Frame POOL (m.set64 CTL 0 m'.top) m' ∧ Agree (vpool m') (vpool m) m.top.toNat ∧
  m.top.toNat ≤ m'.top.toNat ∧ m'.top.toNat ≤ pcap m' ∧ pcap m' = pcap m

/-- A slice of the pool in use: below the top. -/
def SliceOK (m : Mem) (o l : Word) : Prop := o.toNat + l.toNat ≤ m.top.toNat

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

theorem Norm.zero (p : Array Word) (o : Nat) : Norm p o 0 := by simp [Norm]
grind_pattern [arena_grind] Norm.zero => Norm p o 0

theorem Norm.of_top (p : Array Word) (o l j : Nat) (hj : j = o + (l - 1))
    (h : j < p.size) (hne : p[j] ≠ 0) : Norm p o l := by
  subst hj; simp [Norm, h, hne]
grind_pattern [arena_grind] Norm.of_top => Norm p o l, p[j]

end L.Arena
