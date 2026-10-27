module

public import ConAgua.Arena.LevelLeq
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.LevelGrindAttr
import ConAgua.L.GrindAttr
import Std.Data.DTreeMap.Internal.Operations
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# The specs of the comparison: `lv_leq`, `lv_rest`, `lv_imax`, `lv_cases`, `lv_cases_at`

One step lemma per function (`vcgen` + `finish`, each with its own heartbeat budget: they are
the largest bodies of the level code), and the induction on the L fuel (`leqSpecs`).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-! ## The specs: one induction on the L fuel for the five -/

section specs
variable (p : Prog) (hp : LevelProg p)

/-- The five specs at fuel `n`. -/
def LeqSpecs (n : Nat) : Prop :=
  (∀ (s₀ : St) (f l r d : Word), ⦃fun s => s = s₀⦄ invoke p (exec p n) "lv_leq" [f, l, r, d]
    ⦃fun res s' => LocEq s' s₀ ∧ leqW n s₀.mem f l r d = some (res.headD 0, s'.mem); ⊤⦄) ∧
  (∀ (s₀ : St) (f l r d : Word), ⦃fun s => s = s₀⦄ invoke p (exec p n) "lv_rest" [f, l, r, d]
    ⦃fun res s' => LocEq s' s₀ ∧ restW n s₀.mem f l r d = some (res.headD 0, s'.mem); ⊤⦄) ∧
  (∀ (s₀ : St) (f l r d : Word), ⦃fun s => s = s₀⦄ invoke p (exec p n) "lv_imax" [f, l, r, d]
    ⦃fun res s' => LocEq s' s₀ ∧ imaxRW n s₀.mem f l r d = some (res.headD 0, s'.mem); ⊤⦄) ∧
  (∀ (s₀ : St) (f l r d : Word), ⦃fun s => s = s₀⦄ invoke p (exec p n) "lv_imax_l" [f, l, r, d]
    ⦃fun res s' => LocEq s' s₀ ∧ imaxLW n s₀.mem f l r d = some (res.headD 0, s'.mem); ⊤⦄) ∧
  (∀ (s₀ : St) (f l r d : Word), ⦃fun s => s = s₀⦄ invoke p (exec p n) "lv_imax_r" [f, l, r, d]
    ⦃fun res s' => LocEq s' s₀ ∧ imaxRrW n s₀.mem f l r d = some (res.headD 0, s'.mem); ⊤⦄) ∧
  (∀ (s₀ : St) (f q l r d : Word), ⦃fun s => s = s₀⦄
    invoke p (exec p n) "lv_cases" [f, q, l, r, d]
    ⦃fun res s' => LocEq s' s₀ ∧ casesW n s₀.mem f q l r d = some (res.headD 0, s'.mem); ⊤⦄) ∧
  (∀ (s₀ : St) (f q l r d v : Word), ⦃fun s => s = s₀⦄
    invoke p (exec p n) "lv_cases_at" [f, q, l, r, d, v]
    ⦃fun res s' => LocEq s' s₀ ∧ caW n s₀.mem f q l r d v = some (res.headD 0, s'.mem); ⊤⦄)

section steps
variable (n : Nat) (ih : LeqSpecs p n)
include hp ih

set_option maxHeartbeats 2000000 in
theorem leq_step (s₀ : St) (f l r d : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "lv_leq" [f, l, r, d]
    ⦃fun res s' => LocEq s' s₀ ∧ leqW (n + 1) s₀.mem f l r d = some (res.headD 0, s'.mem); ⊤⦄ := by
  obtain ⟨-, ihR, -, -, -, -, -⟩ := ih
  rw [invoke_eq _ hp.leq]; simp only [callFn, lvLeq]
  sym only [lang_grind, arena_grind, level_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, lvNode_spec p hp.node n, ihR] <;>
    finish (gen := 20)

set_option maxHeartbeats 4000000 in
theorem rest_step (s₀ : St) (f l r d : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "lv_rest" [f, l, r, d]
    ⦃fun res s' => LocEq s' s₀ ∧ restW (n + 1) s₀.mem f l r d = some (res.headD 0, s'.mem); ⊤⦄ := by
  obtain ⟨ihL, -, ihI, -, -, -, -⟩ := ih
  rw [invoke_eq _ hp.rest]; simp only [callFn, lvRest]
  sym only [lang_grind, arena_grind, level_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, lvNode_spec p hp.node n,
      lvEq_spec p hp.node hp.eq n, ihL, ihI] <;>
    finish (gen := 20)

set_option maxHeartbeats 2000000 in
theorem imax_step (s₀ : St) (f l r d : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "lv_imax" [f, l, r, d]
    ⦃fun res s' => LocEq s' s₀ ∧ imaxRW (n + 1) s₀.mem f l r d = some (res.headD 0, s'.mem); ⊤⦄ := by
  obtain ⟨-, -, -, ihIL, -, ihC, -⟩ := ih
  rw [invoke_eq _ hp.imax]; simp only [callFn, lvImax]
  sym only [lang_grind, arena_grind, level_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, lvNode_spec p hp.node n, ihIL,
      ihC] <;>
    finish (gen := 20)

set_option maxHeartbeats 2000000 in
theorem imaxL_step (s₀ : St) (f l r d : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "lv_imax_l" [f, l, r, d]
    ⦃fun res s' => LocEq s' s₀ ∧ imaxLW (n + 1) s₀.mem f l r d = some (res.headD 0, s'.mem); ⊤⦄ := by
  obtain ⟨ihL, -, -, -, ihIR, -, -⟩ := ih
  rw [invoke_eq _ hp.imaxL]; simp only [callFn, lvImaxL]
  sym only [lang_grind, arena_grind, level_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, lvNode_spec p hp.node n,
      lvDist1_spec p hp.alloc hp.dist1 n, lvDist2_spec p hp.node hp.alloc hp.comb hp.simp hp.dist2 n,
      ihL, ihIR] <;>
    finish (gen := 20)

set_option maxHeartbeats 2000000 in
theorem imaxR_step (s₀ : St) (f l r d : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "lv_imax_r" [f, l, r, d]
    ⦃fun res s' => LocEq s' s₀ ∧ imaxRrW (n + 1) s₀.mem f l r d = some (res.headD 0, s'.mem); ⊤⦄ := by
  obtain ⟨ihL, -, -, -, -, -, -⟩ := ih
  rw [invoke_eq _ hp.imaxR]; simp only [callFn, lvImaxR]
  sym only [lang_grind, arena_grind, level_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, lvNode_spec p hp.node n,
      lvDist1_spec p hp.alloc hp.dist1 n, lvDist2_spec p hp.node hp.alloc hp.comb hp.simp hp.dist2 n,
      ihL] <;>
    finish (gen := 20)

set_option maxHeartbeats 2000000 in
theorem cases_step (s₀ : St) (f q l r d : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "lv_cases" [f, q, l, r, d]
    ⦃fun res s' => LocEq s' s₀ ∧ casesW (n + 1) s₀.mem f q l r d = some (res.headD 0, s'.mem); ⊤⦄ := by
  obtain ⟨-, -, -, -, -, -, ihA⟩ := ih
  rw [invoke_eq _ hp.cases]; simp only [callFn, lvCases]
  sym only [lang_grind, arena_grind, level_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, lhMk_spec p hp.alloc n, ihA] <;>
    finish (gen := 20)

set_option maxHeartbeats 2000000 in
theorem casesAt_step (s₀ : St) (f q l r d v : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "lv_cases_at" [f, q, l, r, d, v]
    ⦃fun res s' => LocEq s' s₀ ∧ caW (n + 1) s₀.mem f q l r d v = some (res.headD 0, s'.mem); ⊤⦄ := by
  obtain ⟨ihL, -, -, -, -, -, -⟩ := ih
  rw [invoke_eq _ hp.casesAt]; simp only [callFn, lvCasesAt]
  sym only [lang_grind, arena_grind, level_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      lvSubsimp_spec p hp.node hp.alloc hp.comb hp.simp hp.subst hp.subsimp n, ihL] <;>
    finish (gen := 20)

end steps

include hp in
/-- **The five functions are their models**, at every fuel. -/
theorem leqSpecs (n : Nat) : LeqSpecs p n := by
  induction n with
  | zero =>
    refine ⟨fun s₀ f l r d => ?_, fun s₀ f l r d => ?_, fun s₀ f l r d => ?_,
      fun s₀ f l r d => ?_, fun s₀ f l r d => ?_,
      fun s₀ f q l r d => ?_, fun s₀ f q l r d v => ?_⟩
    · rw [invoke_eq _ hp.leq]; simp only [callFn, lvLeq]; vcgen [exec] <;> grind
    · rw [invoke_eq _ hp.rest]; simp only [callFn, lvRest]; vcgen [exec] <;> grind
    · rw [invoke_eq _ hp.imax]; simp only [callFn, lvImax]; vcgen [exec] <;> grind
    · rw [invoke_eq _ hp.imaxL]; simp only [callFn, lvImaxL]; vcgen [exec] <;> grind
    · rw [invoke_eq _ hp.imaxR]; simp only [callFn, lvImaxR]; vcgen [exec] <;> grind
    · rw [invoke_eq _ hp.cases]; simp only [callFn, lvCases]; vcgen [exec] <;> grind
    · rw [invoke_eq _ hp.casesAt]; simp only [callFn, lvCasesAt]; vcgen [exec] <;> grind
  | succ n ih =>
    exact ⟨leq_step p hp n ih, rest_step p hp n ih, imax_step p hp n ih, imaxL_step p hp n ih,
      imaxR_step p hp n ih, cases_step p hp n ih, casesAt_step p hp n ih⟩

end specs

end L.Arena
