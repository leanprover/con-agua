import ConAgua.Arena.ConsLibRel
import ConAgua.Arena.Store
import ConAgua.Arena.GrindAttr
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# The `lit` store refines the arena's `lit` tables; `natAddLit_refines` without hypotheses

`ConAgua/Arena/Store.lean` has the L code of the `lit` node store and its specs against
word-level models (`probeW`, `matchW`, `internW`). This file relates them to con-ron's arena, as
an instance of the store library (`StoreLib.lean`):

* **The instance**: the schema `litSch` (`REC`, `SLOT`, four words per node, counts at
  `CTL[2 + t]`, tag `8`), the record relation `RecRel` (a `natVal` is a normalised slice below
  the pool top, with its hash; a `strVal` is kind `1`, a slice below the pool top holding its
  UTF-8 bytes one byte per word, with its hash — the same shape as the name store's `str` table,
  `NStrRefine.lean`, minus the prefix), the node hash `litH` (word 3), the lens `litLens` on the
  arena's two `lit` tables, and the obligations: `litFrame`, the match (`litMatchOK`/
  `litMatchStrOK`: matching is equality of literals, by the uniqueness of normalised slices for
  `natVal`, by `slice_key`'s word-list equality for `strVal`), the home slot (`litHomeOK`/
  `litHomeOKStr`), the new record (`litNewOK`/`litNewOKStr`), and the bridges from the L models
  (`litCS_wf`/`litStrCS_wf`, `pushOK_room`).
* **`LitR m a`**, the state relation (`natAddLit_refines`'s `R`): the pool is well formed and the
  library's `ConsR` holds for the `lit` tables.
* **`intern_correct`/`internStr_correct`**: `internW`/`internWStr` refine `internE (.lit (.natVal
  _))`/`internE (.lit (.strVal _))`, by `consIntern_correct`.
* **`LitR.grow`**, `natAddLit_refines_store`, `natAddLit_run_store`.

The pool facts (normalised slices are unique) are by hand; the `strVal` arm's slices-as-keys
facts (`sliceL`, `slice_key`, `strWords`) live here too (below `eqW_iff`/`hashN_congr`, which they
share with the normalised-slice argument), since the name `str` table (`NStrRefine.lean`, via
`PoolSlice.lean`) and the level-list store (`LsRefine.lean`, via `PoolSlice.lean`) both import
this file already and reuse them from here.

Not represented: the arena's derived column for `lit` nodes (`derOfLit`, through Lean's opaque
`mixHash`), and every other table of `AState`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

/-- The arena's `lit` cons key of a literal. -/
abbrev litKey (l : ConLeche.Literal) : LitNode := ⟨l⟩

/-- `a` with the scratch / persistent `lit` table replaced. -/
def withScrLits (a : AState) (t : Tbl LitNode EIdx UInt64) : AState :=
  { a with store := { a.store with scr := { a.store.scr with lits := t } } }
def withPersLits (a : AState) (t : Tbl LitNode EIdx UInt64) : AState :=
  { a with store := { a.store with pers := { a.store.pers with lits := t } } }

/-- The arena's two `lit` tables. -/
def litLens : Lens LitNode UInt64 .expr where
  on a := a.store.scratchOn
  getP a := a.store.pers.lits
  getS a := a.store.scr.lits
  setP := withPersLits
  setS := withScrLits
  on_setP _ _ := rfl
  on_setS _ _ := rfl
  getP_setP _ _ := rfl
  getS_setP _ _ := rfl
  getP_setS _ _ := rfl
  getS_setS _ _ := rfl

/-- `internE` at a literal is the library's protocol, with no skip. -/
theorem internE_lit_run (l : ConLeche.Literal) (a : AState) :
    (internE (.lit l)).run a =
      protoRun litLens (litKey l) ETag.lit a.store.pers.lits.cons[litKey l]?
        (a.store.derOfView (.lit l)) (.native "arena: expression constructor array full") a := by
  simp only [internE, internNodeE, EStore.find?, EStore.persFindMaybe,
    EStore.eViewHasScratchChild, EStore.intern, ETables.find?, Tbl.find?, ETables.sizeOf,
    ETables.push]
  cases hp : a.store.pers.lits.cons[litKey l]? <;> cases hs : a.store.scratchOn <;>
    cases hc : a.store.scr.lits.cons[litKey l]? <;>
    simp only [StateT.run_bind, StateT.run_get, pure_bind, hp, hs, hc, Bool.false_eq_true,
      ↓reduceIte, litKey, ite_self, protoRun, litLens] <;>
    (try split) <;> simp_all [withScrLits, withPersLits, fail,
      throwThe, MonadExceptOf.throw, StateT.run, set, StateT.set,
      StateT.lift, bind, Except.bind, pure, Except.pure, StateT.bind, StateT.pure]

/-! ## Normalised slices are unique -/

theorem wt_mono {i j : Nat} (h : i ≤ j) : wt i ≤ wt j :=
  Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ h)

theorem pv_lt (p : Array Word) (o l : Nat) : pv p o l < wt l := by
  induction l with
  | zero => simp [pv, wt]
  | succ k ih =>
    have hx := (p[o + k]?.getD 0).toNat_lt
    have hw : wt (k + 1) = wt k * 2 ^ 64 := wt_succ k _ rfl
    simp only [pv, hw]
    have : (p[o + k]?.getD 0).toNat * wt k ≤ (2 ^ 64 - 1) * wt k :=
      Nat.mul_le_mul_right _ (by omega)
    have : (2 ^ 64 - 1) * wt k + wt k = wt k * 2 ^ 64 := by
      rw [Nat.mul_comm (wt k)]; have := wt_pos k; rw [Nat.sub_mul]; omega
    omega

theorem pv_ge (p : Array Word) (o l : Nat) (hl : 0 < l) (hn : Norm p o l) : wt (l - 1) ≤ pv p o l := by
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
  have h := hn hl
  simp only [Nat.add_sub_cancel] at h ⊢
  simp only [pv]
  have : 1 ≤ (p[o + k]?.getD 0).toNat := by
    rcases Nat.eq_zero_or_pos (p[o + k]?.getD 0).toNat with h0 | h0
    · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) h
    · exact h0
  have := Nat.mul_le_mul_right (wt k) this
  omega

/-- Two normalised slices with the same value have the same length. -/
theorem pv_len (p q : Array Word) (a b la lb : Nat) (ha : Norm p a la) (hb : Norm q b lb)
    (h : pv p a la = pv q b lb) : la = lb := by
  rcases Nat.lt_trichotomy la lb with hl | hl | hl
  · have := pv_ge q b lb (by omega) hb
    have := pv_lt p a la
    have := wt_mono (show la ≤ lb - 1 by omega)
    omega
  · exact hl
  · have := pv_ge p a la (by omega) ha
    have := pv_lt q b lb
    have := wt_mono (show lb ≤ la - 1 by omega)
    omega

/-- Two slices of the same length with the same value agree limb for limb. -/
theorem pv_limbs (p q : Array Word) (a b l : Nat) (h : pv p a l = pv q b l) :
    ∀ i < l, p[a + i]?.getD 0 = q[b + i]?.getD 0 := by
  induction l with
  | zero => intro i hi; omega
  | succ k ih =>
    simp only [pv] at h
    have hA := pv_lt p a k
    have hB := pv_lt q b k
    have hw := wt_pos k
    have hx : (p[a + k]?.getD 0).toNat = (q[b + k]?.getD 0).toNat := by
      have e1 : (pv p a k + (p[a + k]?.getD 0).toNat * wt k) / wt k = (p[a + k]?.getD 0).toNat := by
        rw [Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt hA]; simp
      have e2 : (pv q b k + (q[b + k]?.getD 0).toNat * wt k) / wt k = (q[b + k]?.getD 0).toNat := by
        rw [Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt hB]; simp
      rw [← e1, ← e2, h]
    have hk : pv p a k = pv q b k := by
      have := congrArg (· % wt k) h
      simp only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hA, Nat.mod_eq_of_lt hB] at this
      exact this
    intro i hi
    rcases Nat.lt_or_ge i k with hik | hik
    · exact ih hk i hik
    · have : i = k := by omega
      subst this; exact UInt64.toNat_inj.mp hx

theorem pv_congr (p q : Array Word) (a b l : Nat)
    (h : ∀ i < l, p[a + i]?.getD 0 = q[b + i]?.getD 0) : pv p a l = pv q b l := by
  induction l with
  | zero => rfl
  | succ k ih =>
    simp only [pv, ih (fun i hi => h i (by omega)), h k (by omega)]

theorem hashN_congr (p q : Array Word) (a b l : Nat)
    (h : ∀ i < l, p[a + i]?.getD 0 = q[b + i]?.getD 0) : hashN p a l = hashN q b l := by
  induction l with
  | zero => rfl
  | succ k ih =>
    simp only [hashN, ih (fun i hi => h i (by omega)), h k (by omega)]

theorem Agree.hashN (p q : Array Word) (t o k : Nat) (h : Agree p q t) (hk : o + k ≤ t) :
    L.Arena.hashN p o k = L.Arena.hashN q o k :=
  hashN_congr p q o o k (fun i hi => by rw [h (o + i) (by omega)])

theorem Agree.norm (p q : Array Word) (t o l : Nat) (h : Agree p q t) (hk : o + l ≤ t)
    (hn : Norm q o l) : Norm p o l := by
  intro hl; rw [h (o + (l - 1)) (by omega)]; exact hn hl

/-- `eqW` from position `i` in `Nat` terms, where no index wraps. -/
theorem eqW_iff (p : Array Word) (a b l i : Word) (ha : a.toNat + l.toNat < 2 ^ 64)
    (hb : b.toNat + l.toNat < 2 ^ 64) :
    eqW p a b l i = true ↔
      ∀ k, i.toNat ≤ k → k < l.toNat → p[a.toNat + k]?.getD 0 = p[b.toNat + k]?.getD 0 := by
  fun_induction eqW p a b l i with
  | case1 i hi he ih =>
    rw [ih]
    have e1 : (a + i).toNat = a.toNat + i.toNat := by grind
    have e2 : (b + i).toNat = b.toNat + i.toNat := by grind
    rw [e1, e2] at he
    constructor
    · intro H k hk hkl
      by_cases hk' : k = i.toNat
      · subst hk'; exact he
      · exact H k (by grind) hkl
    · grind
  | case2 i hi he =>
    have e1 : (a + i).toNat = a.toNat + i.toNat := by grind
    have e2 : (b + i).toNat = b.toNat + i.toNat := by grind
    rw [e1, e2] at he
    simp only [Bool.false_eq_true, false_iff]
    exact fun H => he (H _ (Nat.le_refl _) (by grind))
  | case3 i hi => grind

/-! ## Normalised slices, in words -/

/-- Two normalised slices with the same value: the same length, `limbs_eq` holds, the same hash. -/
theorem slice_eq (p : Array Word) (a la b lb : Word) (ha : Norm p a.toNat la.toNat)
    (hb : Norm p b.toNat lb.toNat) (hab : a.toNat + la.toNat < 2 ^ 64)
    (hbb : b.toNat + lb.toNat < 2 ^ 64) (h : pv p a.toNat la.toNat = pv p b.toNat lb.toNat) :
    la = lb ∧ eqW p a b la 0 = true ∧ hashN p a.toNat la.toNat = hashN p b.toNat lb.toNat := by
  have hl := UInt64.toNat_inj.mp (pv_len p p _ _ _ _ ha hb h)
  subst hl
  have hlimbs := pv_limbs p p _ _ _ h
  exact ⟨rfl, (eqW_iff p a b la 0 hab hbb).mpr (fun k _ hk => hlimbs k hk),
    hashN_congr p p _ _ _ hlimbs⟩

/-- Equal limbs, equal values. -/
theorem pv_of_eqW (p : Array Word) (a b l : Word) (hab : a.toNat + l.toNat < 2 ^ 64)
    (hbb : b.toNat + l.toNat < 2 ^ 64) (h : eqW p a b l 0 = true) :
    pv p a.toNat l.toNat = pv p b.toNat l.toNat :=
  pv_congr p p _ _ _ (fun k hk => (eqW_iff p a b l 0 hab hbb).mp h k (Nat.zero_le _) hk)

/-! ## Slices of the pool as keys

The level-list store (`LsRefine.lean`) and the name store's `str` table (`NStrRefine.lean`) key a
record by a list of words held as a slice `(o, l)` below the pool top, compared by `limbs_eq`
(`eqW`) after the lengths, hashed by `lit_hash` (`hashN`) — exactly the machinery above. The
`lit` store's own `strVal` arm is the same: a slice holding the string's UTF-8 bytes, one byte
per word. So the "slice as a list of words" layer (`sliceL`, `slice_key`, `slice_key_hash`) and
the `strVal` encoding (`strWords`, `strWords_inj`) live here, once, next to `eqW_iff`/
`hashN_congr`; `PoolSlice.lean` and `NStrRefine.lean` import this file and reuse them from here.
`lit`'s own `natVal` key is not a list (a natural number is a *normalised* slice, unique by
`pv_len`/`pv_limbs` above, not by `sliceL`), so it shares `eqW_iff`/`hashN_congr` with this layer,
not the statement. -/

/-- The words of the slice `(o, l)` of `p`. -/
def sliceL (p : Array Word) (o l : Nat) : List Word := List.ofFn fun k : Fin l => p[o + k]?.getD 0

theorem sliceL_length (p : Array Word) (o l : Nat) : (sliceL p o l).length = l := by
  simp [sliceL]

theorem sliceL_succ (p : Array Word) (o l : Nat) :
    sliceL p o (l + 1) = (p[o]?.getD 0) :: sliceL p (o + 1) l := by
  simp only [sliceL, List.ofFn_succ, Fin.val_zero, Nat.add_zero, Fin.val_succ]
  congr 1; congr; funext k; congr 2; omega

theorem sliceL_eq_iff (p q : Array Word) (a b l : Nat) :
    sliceL p a l = sliceL q b l ↔ ∀ k < l, p[a + k]?.getD 0 = q[b + k]?.getD 0 := by
  rw [sliceL, sliceL, List.ext_getElem_iff]
  simp

/-- The pool growing above `t` leaves the slices below `t` alone. -/
theorem Agree.sliceL (p q : Array Word) (t o l : Nat) (h : Agree p q t) (hk : o + l ≤ t) :
    L.Arena.sliceL p o l = L.Arena.sliceL q o l :=
  (sliceL_eq_iff p q o o l).mpr fun i hi => by rw [h (o + i) (by omega)]

/-- Below `2^41` the total pool view and the virtual pool hold the same slices. -/
theorem sliceL_tpool (m : Mem) (o l : Nat) (h : o + l ≤ 2 ^ 41) :
    sliceL (tpool m) o l = sliceL (vpool m) o l :=
  Agree.sliceL _ _ _ _ _ (tpool_vpool m) h

theorem hashN_tpool (m : Mem) (o l : Nat) (h : o + l ≤ 2 ^ 41) :
    hashN (tpool m) o l = hashN (vpool m) o l :=
  Agree.hashN _ _ _ _ _ (tpool_vpool m) h

/-- **A slice key matches iff the word lists are equal**: for a record slice `(a, la)` and a
query slice `(b, lb)` that do not wrap, the L match (lengths, then `limbs_eq`) holds iff the two
slices hold the same words. -/
theorem slice_key (p : Array Word) (a la b lb : Word) (ha : a.toNat + la.toNat < 2 ^ 64)
    (hb : b.toNat + lb.toNat < 2 ^ 64) :
    ((la == lb) && eqW p a b lb 0) = true ↔
      L.Arena.sliceL p a.toNat la.toNat = L.Arena.sliceL p b.toNat lb.toNat := by
  constructor
  · intro h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, he⟩ := h
    exact (sliceL_eq_iff p p _ _ _).mpr fun k hk =>
      (eqW_iff p a b la 0 ha hb).mp he k (Nat.zero_le _) hk
  · intro h
    have hl : la = lb := UInt64.toNat_inj.mp (by
      have := congrArg List.length h; simpa only [sliceL_length] using this)
    subst hl
    simp only [beq_self_eq_true, Bool.true_and]
    exact (eqW_iff p a b la 0 ha hb).mpr fun k _ hk => (sliceL_eq_iff p p _ _ _).mp h k hk

/-- Equal slices have equal hashes. -/
theorem slice_key_hash (p q : Array Word) (a la b lb : Nat)
    (h : L.Arena.sliceL p a la = L.Arena.sliceL q b lb) : hashN p a la = hashN q b lb := by
  have hl : la = lb := by have := congrArg List.length h; simpa only [sliceL_length] using this
  subst hl
  exact hashN_congr p q a b la ((sliceL_eq_iff p q a b la).mp h)

/-- The words of a string: its UTF-8 bytes, one per word. -/
def strWords (s : String) : List Word := s.toByteArray.data.toList.map UInt8.toUInt64

theorem strWords_inj (s s' : String) (h : strWords s = strWords s') : s = s' :=
  String.toByteArray_inj.mp (ByteArray.ext (Array.toList_inj.mp
    ((List.map_inj_right fun _ _ h => UInt8.toUInt64_inj.mp h).mp h)))

/-! ## The relation between L memory and the arena's `lit` tables -/

/-- The `lit` schema: `REC`, `SLOT`, four words per node, the counts at `CTL[2 + t]`. -/
def litSch : Schema := ⟨REC, SLOT, 4, 2, ETag.lit⟩

theorem litS_wf : litSch.WF :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide⟩

theorem fld_lit0 (m : Mem) (t i : Word) : fld litSch m t i 0 = rdW (m.arr64 (tierA REC t)) (i * 4) := by
  simp [fld, Schema.ad, litSch]
theorem fld_lit (m : Mem) (t i f : Word) :
    fld litSch m t i f = rdW (m.arr64 (tierA REC t)) (i * 4 + f) := rfl

/-- Node `i` of tier `t` holds the `natVal` `N`: kind `0`, a normalised slice below the top with
value `N`, and its hash. -/
def NatRec (m : Mem) (t i : Word) (N : Nat) : Prop :=
  tfld m LIT t i 0 = 0 ∧
  RSlice m t (tfld m LIT t i 1) (tfld m LIT t i 2) ∧
  Norm (vpool m) (tfld m LIT t i 1).toNat
    (tfld m LIT t i 2).toNat ∧
  pv (vpool m) (tfld m LIT t i 1).toNat
    (tfld m LIT t i 2).toNat = N ∧
  tfld m LIT t i 3 = hashN (tpool m)
    (tfld m LIT t i 1).toNat (tfld m LIT t i 2).toNat

/-- `NatRec` in the raw words (inside the store library). -/
theorem NatRec_raw (m : Mem) (t i : Word) (N : Nat) :
    NatRec m t i N ↔
    rdW (m.arr64 (tierA REC t)) (i * 4) = 0 ∧
    RSlice m t (rdW (m.arr64 (tierA REC t)) (i * 4 + 1)) (rdW (m.arr64 (tierA REC t)) (i * 4 + 2)) ∧
    Norm (vpool m) (rdW (m.arr64 (tierA REC t)) (i * 4 + 1)).toNat
      (rdW (m.arr64 (tierA REC t)) (i * 4 + 2)).toNat ∧
    pv (vpool m) (rdW (m.arr64 (tierA REC t)) (i * 4 + 1)).toNat
      (rdW (m.arr64 (tierA REC t)) (i * 4 + 2)).toNat = N ∧
    rdW (m.arr64 (tierA REC t)) (i * 4 + 3) = hashN (tpool m)
      (rdW (m.arr64 (tierA REC t)) (i * 4 + 1)).toNat (rdW (m.arr64 (tierA REC t)) (i * 4 + 2)).toNat
  := Iff.rfl

/-- Node `i` of tier `t` holds the string `s`: kind `1`, a slice below the pool top holding its
UTF-8 bytes (one byte per word, as the name store's `str` table), and the hash. -/
def StrRec (m : Mem) (t i : Word) (s : String) : Prop :=
  tfld m LIT t i 0 = 1 ∧
  RSlice m t (tfld m LIT t i 1) (tfld m LIT t i 2) ∧
  sliceL (vpool m) (tfld m LIT t i 1).toNat
    (tfld m LIT t i 2).toNat = strWords s ∧
  tfld m LIT t i 3 = hashN (tpool m)
    (tfld m LIT t i 1).toNat (tfld m LIT t i 2).toNat

/-- `StrRec` in the raw words (inside the store library). -/
theorem StrRec_raw (m : Mem) (t i : Word) (s : String) :
    StrRec m t i s ↔
    rdW (m.arr64 (tierA REC t)) (i * 4) = 1 ∧
    RSlice m t (rdW (m.arr64 (tierA REC t)) (i * 4 + 1)) (rdW (m.arr64 (tierA REC t)) (i * 4 + 2)) ∧
    sliceL (vpool m) (rdW (m.arr64 (tierA REC t)) (i * 4 + 1)).toNat
      (rdW (m.arr64 (tierA REC t)) (i * 4 + 2)).toNat = strWords s ∧
    rdW (m.arr64 (tierA REC t)) (i * 4 + 3) = hashN (tpool m)
      (rdW (m.arr64 (tierA REC t)) (i * 4 + 1)).toNat (rdW (m.arr64 (tierA REC t)) (i * 4 + 2)).toNat
  := Iff.rfl

/-- Node `i` of tier `t` holds the literal `k`: a `natVal n` is `NatRec`, a `strVal s` is
`StrRec`. -/
def RecRel (m : Mem) (t i : Word) : LitNode → Prop
  | ⟨.natVal N⟩ => NatRec m t i N
  | ⟨.strVal s⟩ => StrRec m t i s

@[store_grind =] theorem RecRel_natVal (m : Mem) (t i : Word) (N : Nat) :
    RecRel m t i ⟨.natVal N⟩ = NatRec m t i N := rfl
@[store_grind =] theorem RecRel_strVal (m : Mem) (t i : Word) (s : String) :
    RecRel m t i ⟨.strVal s⟩ = StrRec m t i s := rfl

/-- **The state relation.** The pool is well formed, and the library's relation holds for the
two `lit` tables. -/
def LitR (m : Mem) (a : AState) : Prop :=
  PoolOK m ∧ ConsR litCS RecRel m a.store.scratchOn a.store.pers.lits a.store.scr.lits

/-- A node's relation and hash depend on its four words, the pool and the top. -/
theorem litFrame : RFrame litSch RecRel litH := by
  intro m m' t i ⟨hb, htop⟩ hf
  have h0 := hf 0 (by decide)
  have h1 := hf 1 (by decide)
  have h2 := hf 2 (by decide)
  have h3 := hf 3 (by decide)
  rw [fld_lit0, fld_lit0] at h0
  rw [fld_lit, fld_lit] at h1 h2 h3
  have hpr : m'.arr64 POOL = m.arr64 POOL := hb POOL (by decide) (by decide) (by decide) (by decide) (by decide)
  have hpr₁ : m'.arr64 POOL1 = m.arr64 POOL1 := hb POOL1 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hprₜ : m'.arr64 PT0 = m.arr64 PT0 := hb PT0 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hprv := vpool_congr hpr hpr₁
  have hprc := pcap_congr' hpr hpr₁
  have hp : vpool m' = vpool m := vpool_congr hpr hpr₁
  have hpc : pcap m' = pcap m := pcap_congr' hpr hpr₁
  have ht : m'.top = m.top := htop
  have hq : tpool m' = tpool m := tpool_congr hpr hpr₁
  have hrs := fun t o l => RSlice_congr (m := m) (m' := m') t o l ht (ptop0_congr hprₜ)
  refine ⟨fun a h => ?_, by simp only [litH, h3]⟩
  obtain ⟨⟨N⟩ | ⟨s⟩⟩ := a <;> simpa only [RecRel, NatRec_raw, StrRec_raw, h0, h1, h2, h3, hp, hq, hrs, ht] using h

/-! ## The query's obligations -/

/-- The match of `lit_match` on node `i` of tier `t`. -/
def litMt (m : Mem) (o l h t i : Word) : Bool := matchW (m.arr64 (tierA REC t)) (tpool m) t i o l h

section query
variable (m : Mem) (hpool : PoolOK m) (o l : Word) (hq : SliceOK m o l)
  (hn : Norm (vpool m) o.toNat l.toNat)

include hpool hq hn in
/-- **Matching is equality of literals**, on a node of a represented tier. -/
theorem litMatchOK :
    MatchOK RecRel (litMt m o l (hashN (tpool m) o.toNat l.toNat)) m
      (litKey (.natVal (pv (vpool m) o.toNat l.toNat))) := by
  intro t i k hr
  obtain ⟨⟨N⟩ | ⟨s⟩⟩ := k
  · obtain ⟨h0, hsl, hnm, hpv, hh⟩ := (NatRec_raw m t i N).mp (RecRel_natVal m t i N ▸ hr)
    have hle := hsl.le
    have hq1 := hq.le
    have htop := hpool.2.2.2.1
    have hpc := pcap_eq m (by have := hpool.2.2.1; omega)
    have nr := (Norm_tpool m _ _ (by omega)).mpr hnm
    have nq := (Norm_tpool m _ _ (by omega)).mpr hn
    have pr := pv_tpool m (rdW (m.arr64 (tierA REC t)) (i * 4 + 1)).toNat
      (rdW (m.arr64 (tierA REC t)) (i * 4 + 2)).toNat (by omega)
    have pq := pv_tpool m o.toNat l.toNat (by omega)
    have := slice_eq (tpool m) (rdW (m.arr64 (tierA REC t)) (i * 4 + 1))
      (rdW (m.arr64 (tierA REC t)) (i * 4 + 2)) o l nr nq (by omega) (by omega)
    have := pv_of_eqW (tpool m) (rdW (m.arr64 (tierA REC t)) (i * 4 + 1)) o l
    grind [litMt, matchW]
  · grind [litMt, matchW, RecRel_strVal, StrRec_raw]

theorem litHomeOK (h : Word) : HomeOK litH (litMt m o l h) m h := by
  intro t i hm
  simp only [litMt, matchW, Bool.and_eq_true, beq_iff_eq] at hm
  exact hm.1.1.2

variable (hq0 : m.flag = 0 → o.toNat < 2 ^ 40)

include hq hn hq0 in
/-- The record `lit_push` writes holds the literal. -/
theorem litNewOK :
    NewOKR litSch RecRel litH m [0, o, l, hashN (tpool m) o.toNat l.toNat]
      (litKey (.natVal (pv (vpool m) o.toNat l.toNat))) (hashN (tpool m) o.toNat l.toNat) := by
  intro t ht hroom ht0
  have hpr : (newRecM litSch m t [0, o, l, hashN (tpool m) o.toNat l.toNat]).arr64 POOL = m.arr64 POOL := wrRec_arr_ne litSch t (cntW litSch m t) POOL (ne_tierA (by decide) (by decide) (by decide) t) _ m 0
  have hpr₁ : (newRecM litSch m t [0, o, l, hashN (tpool m) o.toNat l.toNat]).arr64 POOL1 = m.arr64 POOL1 := wrRec_arr_ne litSch t (cntW litSch m t) POOL1 (tierA_ne_pool _ (by decide) t).2.symm _ m 0
  have hprₜ : (newRecM litSch m t [0, o, l, hashN (tpool m) o.toNat l.toNat]).arr64 PT0 = m.arr64 PT0 := wrRec_arr_ne litSch t (cntW litSch m t) PT0 (ne_tierA (by decide) (by decide) (by decide) t) _ m 0
  have hprv := vpool_congr hpr hpr₁
  have hprc := pcap_congr' hpr hpr₁
  have hp : vpool (newRecM litSch m t [0, o, l, hashN (tpool m) o.toNat l.toNat]) = vpool m := vpool_congr hpr hpr₁
  have hpc : pcap (newRecM litSch m t [0, o, l, hashN (tpool m) o.toNat l.toNat]) = pcap m := pcap_congr' hpr hpr₁
  have htop : rdW ((newRecM litSch m t [0, o, l, hashN (tpool m) o.toNat l.toNat]).arr64 CTL) 0 =
      rdW (m.arr64 CTL) 0 := by
    rw [newRecM, wrRec_arr_ne litSch t (cntW litSch m t) CTL (ne_tierA (by decide) (by decide) (by decide) t)]
  have hqt : tpool (newRecM litSch m t [0, o, l, hashN (tpool m) o.toNat l.toNat]) = tpool m := tpool_congr hpr hpr₁
  have hrs : RSlice (newRecM litSch m t [0, o, l, hashN (tpool m) o.toNat l.toNat]) t o l :=
    (RSlice_congr t o l (by simp only [top_rdW]; exact htop) (ptop0_congr hprₜ)).mpr (RSlice.intern hq hq0 ht0)
  have e : ∀ f, f < 4 → fld litSch (newRecM litSch m t [0, o, l, hashN (tpool m) o.toNat l.toNat])
      t (cntW litSch m t) f =
      [0, o, l, hashN (tpool m) o.toNat l.toNat].getD f.toNat 0 := by
    intro f hf
    have := hroom.1
    have := hroom.2
    rw [fld_newRecM litSch litS_wf] <;> simp only [litSch, Schema.ad] at * <;> grind
  have e0 := e 0 (by decide)
  have e1 := e 1 (by decide)
  have e2 := e 2 (by decide)
  have e3 := e 3 (by decide)
  rw [fld_lit0] at e0
  rw [fld_lit] at e1 e2 e3
  simp only [litKey, RecRel_natVal, NatRec_raw, litH, e0, e1, e2, e3, hp, hqt, ← top_rdW] at htop ⊢
  simp only [List.getD_cons_zero, List.getD_cons_succ, show (1 : Word).toNat = 0 + 1 from rfl,
    show (2 : Word).toNat = 1 + 1 from rfl, show (3 : Word).toNat = 2 + 1 from rfl,
    show (0 : Word).toNat = 0 from rfl]
  grind [PoolOK, SliceOK]

end query

/-! ## The `strVal` arm's query obligations -/

/-- The match of `lit_match_str` on node `i` of tier `t`. -/
def litMtStr (m : Mem) (o l h t i : Word) : Bool := matchWStr (m.arr64 (tierA REC t)) (tpool m) t i o l h

section queryStr
variable (m : Mem) (hpool : PoolOK m) (o l : Word) (hq : SliceOK m o l) (s : String)
  (hk : sliceL (vpool m) o.toNat l.toNat = strWords s)

include hpool hq hk in
/-- **Matching is equality of literals**, on a node of a represented tier: a `strVal` query
never matches a `natVal` node (kind `0 ≠ 1`), and matches a `strVal` node iff the two slices hold
the same bytes (`slice_key`, `strWords_inj`), as the name store's `str` table. -/
theorem litMatchStrOK :
    MatchOK RecRel (litMtStr m o l (hashN (tpool m) o.toNat l.toNat)) m
      (litKey (.strVal s)) := by
  intro t i k hr
  obtain ⟨⟨N⟩ | ⟨s'⟩⟩ := k
  · grind [litMtStr, matchWStr, RecRel_natVal, NatRec_raw]
  · obtain ⟨h0, hsl, hw, hh⟩ := (StrRec_raw m t i s').mp (RecRel_strVal m t i s' ▸ hr)
    have hle := hsl.le
    have hq1 := hq.le
    have htop := hpool.2.2.2.1
    have hpc := pcap_eq m (by have := hpool.2.2.1; omega)
    have hw' : sliceL (tpool m) (rdW (m.arr64 (tierA REC t)) (i * 4 + 1)).toNat
        (rdW (m.arr64 (tierA REC t)) (i * 4 + 2)).toNat = strWords s' := by
      rw [sliceL_tpool m _ _ (by omega)]; exact hw
    have hk' : sliceL (tpool m) o.toNat l.toNat = strWords s := by
      rw [sliceL_tpool m _ _ (by omega)]; exact hk
    have key := slice_key (tpool m) (rdW (m.arr64 (tierA REC t)) (i * 4 + 1))
      (rdW (m.arr64 (tierA REC t)) (i * 4 + 2)) o l (by omega) (by omega)
    simp only [litMtStr, matchWStr, litKey]
    constructor
    · intro h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨-, -⟩, h2⟩, h3⟩ := h
      have := key.mp (by simp only [Bool.and_eq_true, beq_iff_eq]; exact ⟨h2, h3⟩)
      rw [hw', hk'] at this
      simp only [LitNode.mk.injEq, ConLeche.Literal.strVal.injEq]
      exact strWords_inj _ _ this
    · intro h
      simp only [LitNode.mk.injEq, ConLeche.Literal.strVal.injEq] at h
      subst h
      have e : sliceL (tpool m) (rdW (m.arr64 (tierA REC t)) (i * 4 + 1)).toNat
          (rdW (m.arr64 (tierA REC t)) (i * 4 + 2)).toNat = sliceL (tpool m) o.toNat l.toNat := by
        rw [hw', hk']
      have := key.mpr e
      simp only [Bool.and_eq_true] at this
      simp only [Bool.and_eq_true, beq_iff_eq, this, and_true, h0]
      refine ⟨trivial, ?_⟩
      rw [hh]
      exact slice_key_hash _ _ _ _ _ _ e

theorem litHomeOKStr (h : Word) : HomeOK litH (litMtStr m o l h) m h := by
  intro t i hm
  simp only [litMtStr, matchWStr, Bool.and_eq_true, beq_iff_eq] at hm
  exact hm.1.1.2

variable (hq0 : m.flag = 0 → o.toNat < 2 ^ 40)

include hq hk hq0 in
/-- The record `lit_push_str` writes holds the string. -/
theorem litNewOKStr :
    NewOKR litSch RecRel litH m [1, o, l, hashN (tpool m) o.toNat l.toNat]
      (litKey (.strVal s)) (hashN (tpool m) o.toNat l.toNat) := by
  intro t ht hroom ht0
  have hpr : (newRecM litSch m t [1, o, l, hashN (tpool m) o.toNat l.toNat]).arr64 POOL = m.arr64 POOL := wrRec_arr_ne litSch t (cntW litSch m t) POOL (ne_tierA (by decide) (by decide) (by decide) t) _ m 0
  have hpr₁ : (newRecM litSch m t [1, o, l, hashN (tpool m) o.toNat l.toNat]).arr64 POOL1 = m.arr64 POOL1 := wrRec_arr_ne litSch t (cntW litSch m t) POOL1 (tierA_ne_pool _ (by decide) t).2.symm _ m 0
  have hprₜ : (newRecM litSch m t [1, o, l, hashN (tpool m) o.toNat l.toNat]).arr64 PT0 = m.arr64 PT0 := wrRec_arr_ne litSch t (cntW litSch m t) PT0 (ne_tierA (by decide) (by decide) (by decide) t) _ m 0
  have hprv := vpool_congr hpr hpr₁
  have hprc := pcap_congr' hpr hpr₁
  have hp : vpool (newRecM litSch m t [1, o, l, hashN (tpool m) o.toNat l.toNat]) = vpool m := vpool_congr hpr hpr₁
  have hpc : pcap (newRecM litSch m t [1, o, l, hashN (tpool m) o.toNat l.toNat]) = pcap m := pcap_congr' hpr hpr₁
  have htop : rdW ((newRecM litSch m t [1, o, l, hashN (tpool m) o.toNat l.toNat]).arr64 CTL) 0 =
      rdW (m.arr64 CTL) 0 := by
    rw [newRecM, wrRec_arr_ne litSch t (cntW litSch m t) CTL (ne_tierA (by decide) (by decide) (by decide) t)]
  have hqt : tpool (newRecM litSch m t [1, o, l, hashN (tpool m) o.toNat l.toNat]) = tpool m := tpool_congr hpr hpr₁
  have hrs : RSlice (newRecM litSch m t [1, o, l, hashN (tpool m) o.toNat l.toNat]) t o l :=
    (RSlice_congr t o l (by simp only [top_rdW]; exact htop) (ptop0_congr hprₜ)).mpr (RSlice.intern hq hq0 ht0)
  have e : ∀ f, f < 4 → fld litSch (newRecM litSch m t [1, o, l, hashN (tpool m) o.toNat l.toNat])
      t (cntW litSch m t) f =
      [1, o, l, hashN (tpool m) o.toNat l.toNat].getD f.toNat 0 := by
    intro f hf
    have := hroom.1
    have := hroom.2
    rw [fld_newRecM litSch litS_wf] <;> simp only [litSch, Schema.ad] at * <;> grind
  have e0 := e 0 (by decide)
  have e1 := e 1 (by decide)
  have e2 := e 2 (by decide)
  have e3 := e 3 (by decide)
  rw [fld_lit0] at e0
  rw [fld_lit] at e1 e2 e3
  simp only [litKey, RecRel_strVal, StrRec_raw, litH, e0, e1, e2, e3, hp, hqt, ← top_rdW] at htop ⊢
  simp only [List.getD_cons_zero, List.getD_cons_succ, show (1 : Word).toNat = 0 + 1 from rfl,
    show (2 : Word).toNat = 1 + 1 from rfl, show (3 : Word).toNat = 2 + 1 from rfl,
    show (0 : Word).toNat = 0 from rfl]
  grind [SliceOK]

end queryStr

/-! ## The bridges from the L models -/

theorem pushOK_room (m : Mem) (t : Word) (h : pushOK m t = true) : PushRoom litSch m t := by
  simp only [pushOK, Bool.and_eq_true, decide_eq_true_eq] at h
  have := UInt64.toNat_shiftRight (m.len64 (tierA REC t)) 2
  simp only [PushRoom, cntW, cnt, litSch, len64_eq] at *
  grind

/-- **The `lit` tables' shape** (both schemas). -/
theorem litCS_wf : litCS.WF where
  sch := litS_wf
  P := by decide
  S := by decide
  col A h := by simp [litCS, litCSk] at h
  colRoom A h := by simp [litCS, litCSk] at h
  colLt A h := by simp [litCS, litCSk] at h
  room m t h := (pushOK_room m t ((pushOK_eqC m t).trans h)).2
  vs ks h hk := by simp [pushArgs, litCS, litCSk, hk]
  ex h := by simp [litCS, litCSk] at h

theorem litStrCS_wf : litStrCS.WF where
  sch := litS_wf
  P := by decide
  S := by decide
  col A h := by simp [litStrCS, litCSk] at h
  colRoom A h := by simp [litStrCS, litCSk] at h
  colLt A h := by simp [litStrCS, litCSk] at h
  room m t h := (pushOK_room m t ((pushOK_eqC m t).trans h)).2
  vs ks h hk := by simp [pushArgs, litStrCS, litCSk, hk]
  ex h := by simp [litStrCS, litCSk] at h

/-- The two schemas have one relation. -/
theorem litR_str {m : Mem} {on : Bool} {P Q : Tbl LitNode EIdx UInt64} :
    ConsR litCS RecRel m on P Q ↔ ConsR litStrCS RecRel m on P Q := ConsR.congr rfl rfl

/-! ## `intern_lit` refines `internE (.lit (.natVal _))` -/

section intern
variable (m : Mem) (a : AState) (hR : LitR m a) (o l : Word) (hq : SliceOK m o l)
  (hn : Norm (vpool m) o.toNat l.toNat)

variable (hq0 : m.flag = 0 → o.toNat < 2 ^ 40)

include hR hq hn hq0 in
/-- **`intern_lit`'s model refines the arena's `internE` at a `natVal` literal.** If the model
(and so the L code) returns the handle `w` and the memory `m'`, the arena's `internE` of the
literal the slice denotes succeeds with the handle `w`, in a state related to `m'`. -/
theorem intern_correct (w : Word) (m' : Mem) (hI : internW m o l = some (w, m')) :
    AM.ok (internE (.lit (.natVal (pv (vpool m) o.toNat l.toNat)))) a ∧
    LitR m' (AM.st (internE (.lit (.natVal (pv (vpool m) o.toNat l.toNat)))) a) ∧
    AM.res (internE (.lit (.natVal (pv (vpool m) o.toNat l.toNat)))) a = decE w := by
  obtain ⟨hpool, hS⟩ := hR
  have hfr := consInternM_frame litCS_wf hI
  obtain ⟨hok, hst, hres⟩ := consIntern_correct litCS_wf litFrame (colFree_none _ rfl) litLens a hS
    _ _ _ _ _ (internE_lit_run _ a) false rfl [o, l] (by simp [skipC, litCS, litCSk]) (by simp)
    ⟨rfl, litMatchOK m hpool o l hq hn, litHomeOK m o l _, litNewOK m o l hq hn hq0⟩ w m' hI
  refine ⟨hok, ⟨?_, hst⟩, hres⟩
  exact hpool.frame (hfr.1 POOL (by decide) (by decide)) (hfr.1 POOL1 (by decide) (by decide))
    (hfr.1 PT0 (by decide) (by decide)) (hfr.2.2.1 CTL)
    (by simp only [top_rdW]; exact hfr.2.1 0 (by decide)) hfr.2.2.2

end intern

/-! ## The `strVal` arm's bridges, and `intern_lit_str` refines `internE (.lit (.strVal _))` -/

section internStr
variable (m : Mem) (a : AState) (hR : LitR m a) (o l : Word) (hq : SliceOK m o l) (s : String)
  (hk : sliceL (vpool m) o.toNat l.toNat = strWords s)

variable (hq0 : m.flag = 0 → o.toNat < 2 ^ 40)

include hR hq hk hq0 in
/-- **`intern_lit_str`'s model refines the arena's `internE` at a `strVal` literal.** -/
theorem internStr_correct (w : Word) (m' : Mem) (hI : internWStr m o l = some (w, m')) :
    AM.ok (internE (.lit (.strVal s))) a ∧
    LitR m' (AM.st (internE (.lit (.strVal s))) a) ∧
    AM.res (internE (.lit (.strVal s))) a = decE w := by
  obtain ⟨hpool, hS⟩ := hR
  have hfr := consInternM_frame litStrCS_wf hI
  obtain ⟨hok, hst, hres⟩ := consIntern_correct litStrCS_wf litFrame (colFree_none _ rfl) litLens a
    (litR_str.mp hS) _ _ _ _ _ (internE_lit_run _ a) false rfl [o, l]
    (by simp [skipC, litStrCS, litCSk]) (by simp)
    ⟨rfl, litMatchStrOK m hpool o l hq s hk, litHomeOKStr m o l _, litNewOKStr m o l hq s hk hq0⟩ w m' hI
  refine ⟨hok, ⟨?_, litR_str.mpr hst⟩, hres⟩
  exact hpool.frame (hfr.1 POOL (by decide) (by decide)) (hfr.1 POOL1 (by decide) (by decide))
    (hfr.1 PT0 (by decide) (by decide)) (hfr.2.2.1 CTL)
    (by simp only [top_rdW]; exact hfr.2.1 0 (by decide)) hfr.2.2.2

end internStr

/-! ## Appending to the pool preserves the relation -/

section grow
variable (m m' : Mem) (hg : Grows m m')

include hg in
theorem grow_arr (b : ArrId) (hb : b ≠ POOL ∧ b ≠ POOL1) (hc : b ≠ CTL) : m'.arr64 b = m.arr64 b := by
  rw [hg.frame.arr b hb.1 hb.2, Mem.arr64_set64_ne _ _ _ _ _ hc]

include hg in
theorem grow_ctl (x : Word) (hx : x ≠ 0) : rdW (m'.arr64 CTL) x = rdW (m.arr64 CTL) x := by
  rw [hg.frame.ctl, rdW_set64]; simp [Ne.symm hx]

include hg in
theorem RecRel_grow (hpool : PoolOK m) (t i : Word) (k : LitNode) (h : RecRel m t i k) : RecRel m' t i k := by
  have hr := grow_arr m m' hg (tierA REC t) (tierA_ne_pool _ (by decide) t)
    (ne_tierA (by decide) (by decide) (by decide) t).symm
  have h41 := hpool.top41
  have hta := hg.tagree (by omega)
  have hag := hg.agree
  obtain ⟨⟨N⟩ | ⟨s⟩⟩ := k
  · simp only [RecRel, NatRec_raw, hr] at h ⊢
    obtain ⟨h0, hsl, hnm, hpv, hh⟩ := h
    have hle := hsl.le
    exact ⟨h0, hsl.grows hg, Agree.norm _ _ _ _ _ hag hle hnm, by rw [Agree.pv _ _ _ _ _ hag hle, hpv],
      by rw [Agree.hashN _ _ _ _ _ hta hle, hh]⟩
  · simp only [RecRel, StrRec_raw, hr] at h ⊢
    obtain ⟨h0, hsl, hw, hh⟩ := h
    have hle := hsl.le
    exact ⟨h0, hsl.grows hg, by rw [Agree.sliceL _ _ _ _ _ hag hle, hw],
      by rw [Agree.hashN _ _ _ _ _ hta hle, hh]⟩

include hg in
/-- **Appending to the pool preserves the relation** (`natAddLit_refines`'s `hgrow`). -/
theorem LitR.grow (a : AState) (hR : LitR m a) : LitR m' a := by
  obtain ⟨hpool, hS⟩ := hR
  have hr : ∀ t, m'.arr64 (tierA REC t) = m.arr64 (tierA REC t) := fun t =>
    grow_arr m m' hg _ (tierA_ne_pool _ (by decide) t)
      (ne_tierA (by decide) (by decide) (by decide) t).symm
  have := hg.frame.size
  refine ⟨hpool.grows hg, ConsR.mono hS hr (fun t => grow_arr m m' hg _
      (tierA_ne_pool _ (by decide) t)
      (ne_tierA (by decide) (by decide) (by decide) t).symm)
    (by rw [hg.frame.ctl, Mem.size_arr64_set64]) (fun x hx => grow_ctl m m' hg x (by rcases hx with rfl | rfl | rfl | rfl <;> decide))
    (fun t i k => RecRel_grow m m' hg hpool t i k) (fun t i => by simp only [litCS, litCSk, litH, hr])⟩

end grow

/-! ## `natAddLit_refines` without hypotheses -/

/-- `intern_lit` refines `internE (.lit (.natVal _))` under `LitR`: the spec
`natAddLit_refines` assumes as `hI`. -/
theorem internLit_refines (p : Prog) (hph : p.lookup "lit_hash" = some litHash)
    (hpe : p.lookup "limbs_eq" = some limbsEq) (hpm : p.lookup "lit_match" = some litMatch)
    (hpf : p.lookup "lit_find" = some litFind) (hpp : p.lookup "lit_push" = some litPush)
    (hp : p.lookup "intern_lit" = some internLit)
    (a₀ : AState) (n : Nat) (s₀ : St) (o l : Word) (hR : LitR s₀.mem a₀) (hq : SliceOK s₀.mem o l)
    (hn : Norm (vpool s₀.mem) o.toNat l.toNat) (hq0 : s₀.mem.flag = 0 → o.toNat < 2 ^ 40) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_lit" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (internE (.lit (.natVal (pv (vpool s₀.mem) o.toNat l.toNat)))) a₀ ∧
      LitR s'.mem (AM.st (internE (.lit (.natVal (pv (vpool s₀.mem) o.toNat l.toNat)))) a₀) ∧
      AM.res (internE (.lit (.natVal (pv (vpool s₀.mem) o.toNat l.toNat)))) a₀ =
        decE (r.headD 0); ⊤⦄ := by
  have hps := hR.1.2.2.1
  have htop := hR.1.2.2.2.1
  have hq1 := hq.le
  have hspec := internLit_spec p hph hpe hpm hpf hpp hp n s₀ o l (by omega) (by omega)
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hI⟩ := M.of_run (P := fun s => s = s₀) hs hrun hspec
  subst hs
  exact ⟨hloc, intern_correct s.mem a₀ hR o l hq hn hq0 _ _ hI⟩

/-- The arena functions and the store functions, as one program. -/
def storeProg : Prog := natProg ++ [("nat_add_lit", natAddLit)] ++ litProg

/- `5 + 7` twice and `12` (`7 + 5`): one node, handle `0x80000000`; `5 + 5` is the second. -/
#guard
  let m : Mem := { words := withTiers <| #[#[5, 7, 0, 0, 0, 0, 0, 0, 0, 0], #[2] ++ Array.replicate 63 0,
    Array.replicate 64 0, Array.replicate consTestWords 0] }
  let go (m : Mem) (a b : Word) : Option (Word × Mem) :=
    match run storeProg 100 "nat_add_lit" [a, 1, b, 1] m with
    | .ok (r, m') => some (r.headD 0, m')
    | .error _ => none
  match go m 0 1 with
  | some (h₁, m) => match go m 0 1 with
    | some (h₂, m) => match go m 1 0 with
      | some (h₃, m) => match go m 0 0 with
        | some (h₄, _) => [h₁, h₂, h₃, h₄] == [0x80000000, 0x80000000, 0x80000000, 0x80000001]
        | none => false
      | none => false
    | none => false
  | none => false

/-- From an L run of `nat_add_lit` to the arena run of the `Nat.add` arm, under `LitR`. -/
theorem natAddLit_run_store (fuel : Nat) (m : Mem) (a₀ : AState) (hR : LitR m a₀)
    (oa la ob lb : Word) (ha : SliceOK m oa la) (hb : SliceOK m ob lb) (hmode : ModeOK m)
    (r : List Word) (m' : Mem)
    (h : run storeProg fuel "nat_add_lit" [oa, la, ob, lb] m = .ok (r, m')) :
    ∃ a', (natAddArm (pv (vpool m) oa.toNat la.toNat) (pv (vpool m) ob.toNat lb.toNat)).run
      a₀ = .ok (some (decE (r.headD 0)), a') ∧ LitR m' a' :=
  natAddLit_run storeProg rfl rfl rfl rfl rfl LitR (fun _ _ h => h.1) (fun m m' a hR hg => LitR.grow m m' hg a hR)
    (internLit_refines storeProg rfl rfl rfl rfl rfl rfl) fuel m a₀ hR oa la ob lb ha hb hmode r m' h

end L.Arena
