import ConAgua.Arena.DeclNatSpec
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr

/-!
# `reserved_rec_name` refines `reservedRecName`; `lit_guard_has` is `litGuardNames.contains`
(lane `tails`)

`StubNames.lean`'s L code (lane `stubs`), under the inductive stage's relation `StageR` in its
`RefAM` shape (as `natOpNames_refines`, `DeclNatSpec.lean`), so that lane `indproofs3` can
discharge `IndStubs.lean`'s `reservedRecName_spec` from it. Every function here only reads the
pin table: the memory is unchanged, and the twin's runs are pure reads of a filled table
(`PinsFull`, from the flag the first `pin_at` checks).

* `pin_range_has(x, k, hi)`: its model `prhW` (by fuel, as `resFromW`), and what a returned word
  says: `1` iff `x` is one of the pins `k ‥ hi - 1` (`prhW_iff`).
* `lit_guard_has(x)`: the ten literal-guard pins read, then the `||` chain (`lghW`).
* `reserved_rec_name(x)`: `reserved_contains`, `lit_guard_has`, `pin_range_has(x, 14, 21)`
  (`natOpNames`), `pin_range_has(x, 21, 29)` (`natDivModNames`), in the twin's order.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Stubs

open L.Arena L.Ind

/-! ## `pin_range_has(x, k, hi)` -/

/-- The model of `pin_range_has(x, k, hi)` at fuel `n` (the memory is unchanged). -/
def prhW : Nat → Mem → Word → Word → Word → Option Word
  | 0, _, _, _, _ => none
  | n + 1, m, x, k, hi =>
    if hi ≤ k then some 0
    else if pinW m 0 = 0 then none
    else if 51 ≤ k then none
    else if pinW m (1 + k.toNat) = x then some 1
    else prhW n m x (k + 1) hi

theorem prhW_step (n : Nat) (m : Mem) (x k hi : Word) : prhW (n + 1) m x k hi =
    if hi ≤ k then some 0
    else if pinW m 0 = 0 then none
    else if 51 ≤ k then none
    else if pinW m (1 + k.toNat) = x then some 1
    else prhW n m x (k + 1) hi := rfl

grind_pattern [ind_grind] prhW_step => prhW (n + 1) m x k hi

theorem prh_spec (p : Prog) (hp : p.lookup "pin_range_has" = some pinRangeHas)
    (hpin : p.lookup "pin_at" = some pinAtL) (n : Nat) :
    ∀ (s₀ : St) (x k hi : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "pin_range_has" [x, k, hi]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ prhW n s₀.mem x k hi = some (r.headD 0); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ x k hi; rw [invoke_eq _ hp]; simp only [callFn, pinRangeHas]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ x k hi
    rw [invoke_eq _ hp]
    simp only [callFn, pinRangeHas]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, pinAt_pure p hpin n, ih] <;>
      finish (gen := 20)

/-- **What `pin_range_has` answers**: `1` iff `x` is a pin in slots `k ‥ hi - 1`, else `0`. -/
theorem prhW_iff (n : Nat) : ∀ (m : Mem) (x k hi r : Word), hi.toNat ≤ 51 →
    prhW n m x k hi = some r →
    r ≤ 1 ∧ (r ≠ 0 ↔ ∃ i, k.toNat ≤ i ∧ i < hi.toNat ∧ pinW m (1 + i) = x) := by
  induction n with
  | zero => intro m x k hi r _ h; simp [prhW] at h
  | succ n ih =>
    intro m x k hi r h51 h
    rw [prhW_step] at h
    by_cases hk : hi ≤ k
    · rw [ite_eq_left hk] at h; cases Option.some.inj h
      have := UInt64.le_iff_toNat_le.mp hk
      refine ⟨by decide, by simp only [ne_eq, not_true_eq_false, false_iff]; omega⟩
    rw [ite_eq_right hk] at h
    have hk' : k.toNat < hi.toNat := by
      have := UInt64.not_le.mp hk; exact UInt64.lt_iff_toNat_lt.mp this
    obtain ⟨h0, h⟩ := of_ite_none h
    obtain ⟨h5, h⟩ := of_ite_none h
    by_cases he : pinW m (1 + k.toNat) = x
    · rw [ite_eq_left he] at h; cases Option.some.inj h
      refine ⟨by decide, ?_⟩
      exact ⟨fun _ => ⟨k.toNat, Nat.le_refl _, hk', he⟩, fun _ => by decide⟩
    rw [ite_eq_right he] at h
    have hk1 : (k + 1).toNat = k.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    obtain ⟨hr, hiff⟩ := ih m x (k + 1) hi r h51 h
    refine ⟨hr, hiff.trans ?_⟩
    rw [hk1]
    constructor
    · rintro ⟨i, h1, h2, h3⟩; exact ⟨i, by omega, h2, h3⟩
    · rintro ⟨i, h1, h2, h3⟩
      rcases Nat.lt_or_ge k.toNat i with hl | hl
      · exact ⟨i, by omega, h2, h3⟩
      · have : i = k.toNat := by omega
        subst this; exact absurd h3 he

/-! ## `lit_guard_has(x)` -/

/-- Pin `k`'s word, as `pin_at(k)` returns it. -/
abbrev pk (m : Mem) (k : Word) : Word := pinW m (1 + k.toNat)

/-- The model of `lit_guard_has(x)`: the ten literal-guard pins (`pin_at(1)`, `(2)`, `(3)`,
`(5)`‥`(10)`, `(12)`). -/
def lghW (m : Mem) (x : Word) : Option Word :=
  if pinW m 0 = 0 then none
  else if x = pinW m 2 ∨ x = pinW m 3 ∨ x = pinW m 4 ∨ x = pinW m 6 ∨ x = pinW m 7 ∨
    x = pinW m 8 ∨ x = pinW m 9 ∨ x = pinW m 10 ∨ x = pinW m 11 ∨ x = pinW m 13 then some 1
  else some 0

/-- `pin_at(i)` returns to the caller's exact state. -/
theorem pinAt_eq (p : Prog) (hp : p.lookup "pin_at" = some pinAtL) (n : Nat) (s₀ : St) (i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "pin_at" [i]
    ⦃fun r s' => s' = s₀ ∧ pinW s₀.mem 0 ≠ 0 ∧ r = [pinW s₀.mem (1 + i.toNat)]; ⊤⦄ := by
  refine triple_post (pinAt_pure p hp n s₀ i) ?_
  rintro r ⟨m', l'⟩ ⟨hl, h0, -, hr, hm⟩
  obtain ⟨m, l⟩ := s₀
  simp only [LocEq] at hl
  simp only at hm hl
  subst hm hl
  exact ⟨rfl, h0, hr⟩

set_option maxHeartbeats 2000000 in
theorem lgh_spec (p : Prog) (hp : p.lookup "lit_guard_has" = some litGuardHas)
    (hpin : p.lookup "pin_at" = some pinAtL) (n : Nat) (s₀ : St) (x : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "lit_guard_has" [x]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ lghW s₀.mem x = some (r.headD 0); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, litGuardHas]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, pinAt_eq p hpin n] <;>
      finish (gen := 20) [lghW]

/-! ## `reserved_rec_name(x)` -/

/-- A pure read's spec, with the caller's exact state back. -/
theorem triple_eq_of_mem {prog : M (List Word)} {s₀ : St} {Q : List Word → Prop}
    (h : ⦃fun s => s = s₀⦄ prog ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ Q r; ⊤⦄) :
    ⦃fun s => s = s₀⦄ prog ⦃fun r s' => s' = s₀ ∧ Q r; ⊤⦄ := by
  refine triple_post h ?_
  rintro r ⟨m', l'⟩ ⟨hl, hm, hq⟩
  obtain ⟨m, l⟩ := s₀
  simp only [LocEq] at hl
  simp only at hm hl
  subst hm hl
  exact ⟨rfl, hq⟩

/-- After `pin_range_has(x, 14, 21)`. -/
def rrnK3 (n : Nat) (m : Mem) (x : Word) : Option Word → Option Word
  | none => none
  | some r => if r ≠ 0 then some 1 else prhW n m x 21 29

/-- After `lit_guard_has`. -/
def rrnK2 (n : Nat) (m : Mem) (x : Word) : Option Word → Option Word
  | none => none
  | some r => if r ≠ 0 then some 1 else rrnK3 n m x (prhW n m x 14 21)
/-- After `reserved_contains`. -/
def rrnK1 (n : Nat) (m : Mem) (x : Word) : Option Word → Option Word
  | none => none
  | some r => if r ≠ 0 then some 1 else rrnK2 n m x (lghW m x)
/-- The model of `reserved_rec_name(x)` (the memory is unchanged). -/
def rrnW (n : Nat) (m : Mem) (x : Word) : Option Word := rrnK1 n m x (resContW n m x)

set_option maxHeartbeats 2000000 in
theorem rrn_spec (p : Prog) (hp : p.lookup "reserved_rec_name" = some reservedRecNameL)
    (hrc : p.lookup "reserved_contains" = some reservedContains)
    (hrf : p.lookup "reserved_from" = some reservedFrom)
    (hlg : p.lookup "lit_guard_has" = some litGuardHas)
    (hpr : p.lookup "pin_range_has" = some pinRangeHas)
    (hpin : p.lookup "pin_at" = some pinAtL) (n : Nat) (s₀ : St) (x : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "reserved_rec_name" [x]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ rrnW n s₀.mem x = some (r.headD 0); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, reservedRecNameL]
  have h1 := fun s₀ x => triple_eq_of_mem (resCont_spec p hrf hrc n s₀ x)
  have h2 := fun s₀ x => triple_eq_of_mem (lgh_spec p hlg hpin n s₀ x)
  have h3 := fun s₀ x k hi => triple_eq_of_mem (prh_spec p hpr hpin n s₀ x k hi)
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, h1, h2, h3] <;>
    finish (gen := 20) [rrnW, rrnK1, rrnK2, rrnK3]

/-! ## What the models answer -/

/-- What `reserved_from` from `j` answers. -/
theorem resFromW_iff (n : Nat) : ∀ (m : Mem) (x j r : Word), j.toNat ≤ 16 →
    resFromW n m x j = some r →
    r ≤ 1 ∧ (r ≠ 0 ↔ ∃ i, j.toNat ≤ i ∧ i < 16 ∧ pinW m (55 + i) = x) := by
  induction n with
  | zero => intro m x j r _ h; simp [resFromW] at h
  | succ n ih =>
    intro m x j r hj h
    rw [resFromW_step] at h
    by_cases h16 : 16 ≤ j
    · rw [ite_eq_left h16] at h; cases Option.some.inj h
      have := UInt64.le_iff_toNat_le.mp h16
      simp only [UInt64.reduceToNat] at this
      refine ⟨by decide, by simp only [ne_eq, not_true_eq_false, false_iff]; omega⟩
    rw [ite_eq_right h16] at h
    have hj' : j.toNat < 16 := by
      have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp h16)
      simpa using this
    have e55 : (55 + j).toNat = 55 + j.toNat := by rw [UInt64.toNat_add]; simp; omega
    have hw : rdW (m.arr64 PINS) (55 + j) = pinW m (55 + j.toNat) := by simp [rdW, pinW, e55]
    by_cases he : rdW (m.arr64 PINS) (55 + j) = x
    · rw [ite_eq_left he] at h; cases Option.some.inj h
      refine ⟨by decide, ?_⟩
      exact ⟨fun _ => ⟨j.toNat, Nat.le_refl _, hj', hw ▸ he⟩, fun _ => by decide⟩
    rw [ite_eq_right he] at h
    have hj1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    obtain ⟨hr, hiff⟩ := ih m x (j + 1) r (by omega) h
    refine ⟨hr, hiff.trans ?_⟩
    rw [hj1]
    constructor
    · rintro ⟨i, h1, h2, h3⟩; exact ⟨i, by omega, h2, h3⟩
    · rintro ⟨i, h1, h2, h3⟩
      rcases Nat.lt_or_ge j.toNat i with hl | hl
      · exact ⟨i, by omega, h2, h3⟩
      · have : i = j.toNat := by omega
        subst this; exact absurd (hw ▸ h3) he

theorem resContW_iff {n : Nat} {m : Mem} {x r : Word} (h : resContW n m x = some r) :
    r ≤ 1 ∧ (r ≠ 0 ↔ ∃ i, i < 16 ∧ pinW m (55 + i) = x) := by
  cases n with
  | zero => simp [resContW] at h
  | succ n =>
    rw [resContW_step] at h
    obtain ⟨h0, h⟩ := of_ite_none h
    obtain ⟨hr, hiff⟩ := resFromW_iff n m x 0 r (by simp) h
    exact ⟨hr, hiff.trans (by simp)⟩

theorem lghW_iff {m : Mem} {x r : Word} (h : lghW m x = some r) :
    r ≤ 1 ∧ (r ≠ 0 ↔ x ∈ [pinW m 2, pinW m 3, pinW m 4, pinW m 6, pinW m 7, pinW m 8, pinW m 9,
      pinW m 10, pinW m 11, pinW m 13]) := by
  unfold lghW at h
  obtain ⟨h0, h⟩ := of_ite_none h
  split at h <;> rename_i hc <;> cases Option.some.inj h
  · refine ⟨by decide, ?_⟩; simp only [List.mem_cons, List.not_mem_nil, or_false]; simpa using hc
  · refine ⟨by decide, ?_⟩; simp only [List.mem_cons, List.not_mem_nil, or_false]; simpa using hc

/-- The four lists' words, as the twin reads them. -/
def rrnIn (m : Mem) (x : Word) : Prop :=
  (∃ i, i < 16 ∧ pinW m (55 + i) = x) ∨
  x ∈ [pinW m 2, pinW m 3, pinW m 4, pinW m 6, pinW m 7, pinW m 8, pinW m 9, pinW m 10, pinW m 11,
    pinW m 13] ∨
  (∃ i, 14 ≤ i ∧ i < 21 ∧ pinW m (1 + i) = x) ∨
  (∃ i, 21 ≤ i ∧ i < 29 ∧ pinW m (1 + i) = x)

theorem rrnW_iff {n : Nat} {m : Mem} {x r : Word} (h : rrnW n m x = some r) :
    r ≤ 1 ∧ (r ≠ 0 ↔ rrnIn m x) := by
  unfold rrnW at h
  cases h1 : resContW n m x with
  | none => rw [h1] at h; cases h
  | some r1 =>
  rw [h1] at h
  obtain ⟨-, i1⟩ := resContW_iff h1
  simp only [rrnK1] at h
  by_cases c1 : r1 ≠ 0
  · rw [ite_eq_left c1] at h; cases Option.some.inj h
    exact ⟨by decide, ⟨fun _ => .inl (i1.mp c1), fun _ => by decide⟩⟩
  rw [ite_eq_right c1] at h
  cases h2 : lghW m x with
  | none => rw [h2] at h; cases h
  | some r2 =>
  rw [h2] at h
  obtain ⟨-, i2⟩ := lghW_iff h2
  simp only [rrnK2] at h
  by_cases c2 : r2 ≠ 0
  · rw [ite_eq_left c2] at h; cases Option.some.inj h
    exact ⟨by decide, ⟨fun _ => .inr (.inl (i2.mp c2)), fun _ => by decide⟩⟩
  rw [ite_eq_right c2] at h
  cases h3 : prhW n m x 14 21 with
  | none => rw [h3] at h; cases h
  | some r3 =>
  rw [h3] at h
  obtain ⟨-, i3⟩ := prhW_iff n m x 14 21 r3 (by decide) h3
  simp only [rrnK3] at h
  by_cases c3 : r3 ≠ 0
  · rw [ite_eq_left c3] at h; cases Option.some.inj h
    exact ⟨by decide, ⟨fun _ => .inr (.inr (.inl (by simpa using i3.mp c3))), fun _ => by decide⟩⟩
  rw [ite_eq_right c3] at h
  obtain ⟨hr, i4⟩ := prhW_iff n m x 21 29 r (by decide) h
  refine ⟨hr, i4.trans ?_⟩
  simp only [rrnIn]
  have n1 := mt i1.mpr c1
  have n2 := mt i2.mpr c2
  have n3 := mt i3.mpr c3
  simp only [UInt64.reduceToNat] at n3 ⊢
  constructor
  · intro e; exact .inr (.inr (.inr e))
  · rintro (e | e | e | e)
    · exact absurd e n1
    · exact absurd e n2
    · exact absurd e n3
    · exact e

/-! ## The twin side -/

theorem litGuardNames_run {m : Mem} {a : AState} (hF : PinsFull m a.pins) :
    litGuardNames.run a = .ok ([decI (pinW m 2), decI (pinW m 3), decI (pinW m 4),
      decI (pinW m 6), decI (pinW m 7), decI (pinW m 8), decI (pinW m 9), decI (pinW m 10),
      decI (pinW m 11), decI (pinW m 13)], a) := by
  simp [litGuardNames, pinNat, pinNatZero, pinNatSucc, pinString, pinStringOfList, pinList,
    pinListNil, pinListCons, pinChar, pinCharOfNat, PIN_NAT, PIN_NAT_ZERO, PIN_NAT_SUCC, PIN_STRING,
    PIN_STRING_OF_LIST, PIN_LIST, PIN_LIST_NIL, PIN_LIST_CONS, PIN_CHAR, PIN_CHAR_OF_NAT,
    StateT.run_bind, pinAt_run hF, except_ok_bind] <;> rfl

/-- Membership of handles decoded from words below `2^32` is membership of the words. -/
theorem contains_decI {ws : List Word} (hws : ∀ w ∈ ws, w.toNat < 2 ^ 32) {x : Word}
    (hx : x.toNat < 2 ^ 32) :
    (ws.map (fun w => (decI w : NIdx))).contains (decI x) = true ↔ x ∈ ws := by
  simp only [List.contains_iff_mem, List.mem_map]
  constructor
  · rintro ⟨w, hw, e⟩
    have := (decI_eq_iff w (hws w hw) _).mp e
    rw [decI_word_self x hx] at this
    exact this ▸ hw
  · intro h; exact ⟨x, h, rfl⟩

/-- **The twin's `reservedRecName` on a filled table**: a pure read, `true` iff `x` is one of the
four lists' words. -/
theorem reservedRecName_run {m : Mem} {a : AState} (hF : PinsFull m a.pins) (x : Word)
    (hx : x.toNat < 2 ^ 32) :
    ∃ b, (reservedRecName (decI x)).run a = .ok (b, a) ∧ (b = true ↔ rrnIn m x) := by
  have lt : ∀ i, i < 51 → (pinW m (1 + i)).toNat < 2 ^ 32 := hF.names_lt
  have c1 : ((List.range 16).map fun i => (decI (pinW m (55 + i)) : NIdx)).contains (decI x) = true ↔
      ∃ i, i < 16 ∧ pinW m (55 + i) = x := by
    rw [show ((List.range 16).map fun i => (decI (pinW m (55 + i)) : NIdx)) =
      ((List.range 16).map fun i => pinW m (55 + i)).map (fun w => (decI w : NIdx)) by
        simp [List.map_map]]
    rw [contains_decI (by
      intro w hw; simp only [List.mem_map, List.mem_range] at hw
      obtain ⟨i, hi, rfl⟩ := hw; exact hF.reserved_lt i hi) hx]
    simp [List.mem_map, List.mem_range]
  have c2 := contains_decI (ws := [pinW m 2, pinW m 3, pinW m 4, pinW m 6, pinW m 7, pinW m 8,
      pinW m 9, pinW m 10, pinW m 11, pinW m 13]) (by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lt 1 (by decide)
    · exact lt 2 (by decide)
    · exact lt 3 (by decide)
    · exact lt 5 (by decide)
    · exact lt 6 (by decide)
    · exact lt 7 (by decide)
    · exact lt 8 (by decide)
    · exact lt 9 (by decide)
    · exact lt 10 (by decide)
    · exact lt 12 (by decide)) hx
  have c3 := contains_decI (ws := [pinW m 15, pinW m 16, pinW m 17, pinW m 18, pinW m 19, pinW m 20,
      pinW m 21]) (by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lt 14 (by decide)
    · exact lt 15 (by decide)
    · exact lt 16 (by decide)
    · exact lt 17 (by decide)
    · exact lt 18 (by decide)
    · exact lt 19 (by decide)
    · exact lt 20 (by decide)) hx
  have c4 := contains_decI (ws := [pinW m 22, pinW m 23, pinW m 24, pinW m 25, pinW m 26, pinW m 27,
      pinW m 28, pinW m 29]) (by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lt 21 (by decide)
    · exact lt 22 (by decide)
    · exact lt 23 (by decide)
    · exact lt 24 (by decide)
    · exact lt 25 (by decide)
    · exact lt 26 (by decide)
    · exact lt 27 (by decide)
    · exact lt 28 (by decide)) hx
  simp only [List.map_cons, List.map_nil] at c2 c3 c4
  have r3 : (∃ i, 14 ≤ i ∧ i < 21 ∧ pinW m (1 + i) = x) ↔
      x ∈ [pinW m 15, pinW m 16, pinW m 17, pinW m 18, pinW m 19, pinW m 20, pinW m 21] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨i, h1, h2, rfl⟩
      have : i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · rintro (e | e | e | e | e | e | e)
      · exact ⟨14, by decide, by decide, e.symm⟩
      · exact ⟨15, by decide, by decide, e.symm⟩
      · exact ⟨16, by decide, by decide, e.symm⟩
      · exact ⟨17, by decide, by decide, e.symm⟩
      · exact ⟨18, by decide, by decide, e.symm⟩
      · exact ⟨19, by decide, by decide, e.symm⟩
      · exact ⟨20, by decide, by decide, e.symm⟩
  have r4 : (∃ i, 21 ≤ i ∧ i < 29 ∧ pinW m (1 + i) = x) ↔
      x ∈ [pinW m 22, pinW m 23, pinW m 24, pinW m 25, pinW m 26, pinW m 27, pinW m 28,
        pinW m 29] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨i, h1, h2, rfl⟩
      have : i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · rintro (e | e | e | e | e | e | e | e)
      · exact ⟨21, by decide, by decide, e.symm⟩
      · exact ⟨22, by decide, by decide, e.symm⟩
      · exact ⟨23, by decide, by decide, e.symm⟩
      · exact ⟨24, by decide, by decide, e.symm⟩
      · exact ⟨25, by decide, by decide, e.symm⟩
      · exact ⟨26, by decide, by decide, e.symm⟩
      · exact ⟨27, by decide, by decide, e.symm⟩
      · exact ⟨28, by decide, by decide, e.symm⟩
  simp only [reservedRecName, reservedBasisNames, StateT.run_bind, pinReserved_run hF,
    except_ok_bind]
  by_cases b1 : ((List.range 16).map fun i => (decI (pinW m (55 + i)) : NIdx)).contains (decI x) = true
  · simp only [b1, ↓reduceIte]
    exact ⟨true, rfl, by simp only [rrnIn, true_iff]; exact .inl (c1.mp b1)⟩
  simp only [b1, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, litGuardNames_run hF,
    except_ok_bind]
  by_cases b2 : [(decI (pinW m 2) : NIdx), decI (pinW m 3), decI (pinW m 4), decI (pinW m 6),
      decI (pinW m 7), decI (pinW m 8), decI (pinW m 9), decI (pinW m 10), decI (pinW m 11),
      decI (pinW m 13)].contains (decI x) = true
  · simp only [b2, ↓reduceIte]
    exact ⟨true, rfl, by simp only [rrnIn, true_iff]; exact .inr (.inl (c2.mp b2))⟩
  simp only [b2, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, natOpNames_run hF,
    except_ok_bind]
  by_cases b3 : [(decI (pinW m 15) : NIdx), decI (pinW m 16), decI (pinW m 17), decI (pinW m 18),
      decI (pinW m 19), decI (pinW m 20), decI (pinW m 21)].contains (decI x) = true
  · simp only [b3, ↓reduceIte]
    exact ⟨true, rfl, by simp only [rrnIn, true_iff]; exact .inr (.inr (.inl (r3.mpr (c3.mp b3))))⟩
  simp only [b3, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, natDivModNames_run hF,
    except_ok_bind]
  refine ⟨_, rfl, ?_⟩
  rw [c4, ← r4]
  simp only [rrnIn]
  constructor
  · intro e; exact .inr (.inr (.inr e))
  · rintro (e | e | e | e)
    · exact absurd (c1.mpr e) b1
    · exact absurd (c2.mpr e) b2
    · exact absurd (c3.mpr (r3.mp e)) b3
    · exact e

/-! ## The refinement -/

/-- What `reserved_rec_name`'s spec needs of the program. -/
structure RrnProg (p : Prog) : Prop where
  rrn : p.lookup "reserved_rec_name" = some reservedRecNameL
  rc : p.lookup "reserved_contains" = some reservedContains
  rf : p.lookup "reserved_from" = some reservedFrom
  lg : p.lookup "lit_guard_has" = some litGuardHas
  pr : p.lookup "pin_range_has" = some pinRangeHas
  pin : p.lookup "pin_at" = some pinAtL

theorem rrnW_flag {n : Nat} {m : Mem} {x r : Word} (h : rrnW n m x = some r) : pinW m 0 ≠ 0 := by
  intro h0
  unfold rrnW at h
  cases n with
  | zero => simp [resContW, rrnK1] at h
  | succ n => rw [resContW_step, ite_eq_left h0] at h; simp [rrnK1] at h

/-- **`reserved_rec_name(x)` refines `reservedRecName`** under the stage relation: the memory and
the twin's state are unchanged, and the word is `1` exactly when the twin answers `true`. -/
@[refines ConRon.Arena.reservedRecName]
theorem reservedRecName_refines {p : Prog} (hP : RrnProg p) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (x : Word) (hx : H x) :
    RefAM p "reserved_rec_name" [x] (StageR dn vis fe) (reservedRecName (decI x))
      (KeepPost dn vis fe decW0B) := by
  refine CallRef.refAM (CallRef.of_succ fun k m a r m' hS hc => ?_)
  obtain ⟨s', rfl, -, hm, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (rrn_spec p hP.rrn hP.rc hP.rf hP.lg hP.pr hP.pin k _ x) hc
  simp only at hm hW
  obtain ⟨hr, hiff⟩ := rrnW_iff hW
  have hF := hS.1.pins.full (rrnW_flag hW)
  obtain ⟨b, hrun, hb⟩ := reservedRecName_run hF x hx
  refine ⟨b, a, hrun, ?_⟩
  rw [hm]
  refine ⟨hS, IWGrow.refl _, ?_, UInt64.le_iff_toNat_le.mp hr⟩
  cases b with
  | true => simpa using hiff.mpr (hb.mp rfl)
  | false =>
    have : ¬ rrnIn m x := fun e => by simpa using hb.mpr e
    simpa using mt hiff.mp this

end L.Stubs
