import ConAgua.Arena.StubNames
import ConAgua.Arena.DeclHeader
import ConAgua.Arena.DeclNatSpec
import ConAgua.Census.Attr

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
    · rw [if_pos hk] at h; cases Option.some.inj h
      have := UInt64.le_iff_toNat_le.mp hk
      refine ⟨by decide, by simp only [ne_eq, not_true_eq_false, false_iff]; omega⟩
    rw [if_neg hk] at h
    have hk' : k.toNat < hi.toNat := by
      have := UInt64.not_le.mp hk; exact UInt64.lt_iff_toNat_lt.mp this
    by_cases h0 : pinW m 0 = 0
    · rw [if_pos h0] at h; cases h
    rw [if_neg h0] at h
    by_cases h5 : 51 ≤ k
    · rw [if_pos h5] at h; cases h
    rw [if_neg h5] at h
    by_cases he : pinW m (1 + k.toNat) = x
    · rw [if_pos he] at h; cases Option.some.inj h
      refine ⟨by decide, ?_⟩
      exact ⟨fun _ => ⟨k.toNat, Nat.le_refl _, hk', he⟩, fun _ => by decide⟩
    rw [if_neg he] at h
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

end L.Stubs
