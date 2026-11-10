module

import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConRon.Bridge.Grind
import all ConAgua.Arena.Env
import all ConAgua.Arena.IndIface
import ConAgua.Arena.Pins
public import ConAgua.Arena.IndIface

@[expose] public section

/-!
# `install_header`'s callees (lane `decls2`, helper `decls2-header`)

On lane `indproofs`' template, as `install_value_guards` in `DeclCvg.lean`: word models of
`install_header`'s real callees (`env_row_get`/`env_find` without a handle bound,
`reserved_from`/`reserved_contains` by fuel), their `vcgen` specs and their hit/miss lemmas, and
the program's lookups `IhProg`. `install_header` and `class_const_ok_header` themselves have
unified models and refinements (`ih_ref`, `cch_ref`).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind

/-! ## `env_row_get`, `env_find` as word models (no bound on the name word) -/

/-! ## `reserved_from`, `reserved_contains` -/

/-- The model of `reserved_from(x, j)`. -/
def resFromW : Nat → Mem → Word → Word → Option Word
  | 0, _, _, _ => none
  | n + 1, m, x, j =>
    if 16 ≤ j then some 0
    else if rdW (m.arr64 PINS) (55 + j) = x then some 1
    else resFromW n m x (j + 1)

section arms
variable (n : Nat) (m : Mem) (x j : Word)
theorem resFromW_step : resFromW (n + 1) m x j =
    if 16 ≤ j then some 0
    else if rdW (m.arr64 PINS) (55 + j) = x then some 1
    else resFromW n m x (j + 1) := rfl
end arms

grind_pattern [ind_grind] resFromW_step => resFromW (n + 1) m x j

/-- The model of `reserved_contains(x)`. -/
def resContW : Nat → Mem → Word → Option Word
  | 0, _, _ => none
  | n + 1, m, x => if pinW m 0 = 0 then none else resFromW n m x 0

theorem resContW_step (n : Nat) (m : Mem) (x : Word) :
    resContW (n + 1) m x = if pinW m 0 = 0 then none else resFromW n m x 0 := rfl

grind_pattern [ind_grind] resContW_step => resContW (n + 1) m x

theorem resFrom_spec (p : Prog) (hp : p.lookup "reserved_from" = some reservedFrom) (n : Nat) :
    ∀ (s₀ : St) (x j : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "reserved_from" [x, j]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ resFromW n s₀.mem x j = some (r.headD 0); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ x j; rw [invoke_eq _ hp]; simp only [callFn, reservedFrom]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ x j
    rw [invoke_eq _ hp]
    simp only [callFn, reservedFrom]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;>
      finish (gen := 20) [rdW_eq]

theorem resCont_spec (p : Prog) (hf : p.lookup "reserved_from" = some reservedFrom)
    (hp : p.lookup "reserved_contains" = some reservedContains) (n : Nat) (s₀ : St) (x : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "reserved_contains" [x]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ resContW n s₀.mem x = some (r.headD 0); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, reservedContains]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, resFrom_spec p hf n] <;>
      finish (gen := 20) [pinW_eq]

/-- A miss of `reserved_from` from `j`: none of the reserved words from `j` on is `x`. -/
theorem resFromW_miss (n : Nat) : ∀ (m : Mem) (x j : Word), j.toNat ≤ 16 →
    resFromW n m x j = some 0 → ∀ i, j.toNat ≤ i → i < 16 → pinW m (55 + i) ≠ x := by
  induction n with
  | zero => intro m x j _ h; simp [resFromW] at h
  | succ n ih =>
    intro m x j hj h i hi hi16
    rw [resFromW_step] at h
    have hn16 : ¬ 16 ≤ j := by
      rw [UInt64.le_iff_toNat_le]; simp; omega
    rw [ite_eq_right hn16] at h
    by_cases he : rdW (m.arr64 PINS) (55 + j) = x
    · rw [ite_eq_left he] at h; simp at h
    rw [ite_eq_right he] at h
    have hj1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    rcases Nat.lt_or_ge j.toNat i with hlt | hge
    · exact ih m x (j + 1) (by omega) h i (by omega) hi16
    · have hij : i = j.toNat := by omega
      subst hij
      have : (55 + j).toNat = 55 + j.toNat := by rw [UInt64.toNat_add]; simp; omega
      simpa [rdW, pinW, this] using he

/-- **A miss of `reserved_contains` is a miss of `reservedBasisNames`.** -/
theorem resContW_miss {m : Mem} {a : AState} {n : Nat} {x : Word} (hx : x.toNat < 2 ^ 32)
    (h : resContW n m x = some 0) (hP : PinsR m a.pins) :
    ∃ l, reservedBasisNames.run a = .ok (l, a) ∧ l.contains (decI x) = false := by
  cases n with
  | zero => simp [resContW] at h
  | succ n =>
  rw [resContW_step] at h
  by_cases h0 : pinW m 0 = 0
  · rw [ite_eq_left h0] at h; simp at h
  rw [ite_eq_right h0] at h
  have hF := hP.full h0
  refine ⟨_, pinReserved_run hF, ?_⟩
  have hm := resFromW_miss n m x 0 (by simp) h
  rw [Bool.eq_false_iff]
  intro hc
  simp only [List.contains_iff_mem, List.mem_map, List.mem_range] at hc
  obtain ⟨i, hi, e⟩ := hc
  exact hm i (Nat.zero_le _) hi ((decI_eq_iff _ (hF.reserved_lt i hi) _).mp e ▸ decI_word_self x hx)

/-! ## `install_header(vis, q)` -/

end L.Arena
