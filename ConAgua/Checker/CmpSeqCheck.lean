module

public import ConAgua.Checker.CmpSeqBank
import all ConAgua.Checker.CmpSeqEntry
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# Modes `8` and `9` (lane compare2, the sJ variant)

`check_bs()` and `check_bc()` (`Checker/CmpSeqEntry.lean`) as triples over any program with the
callees' specs as hypotheses (error-precise: the switches and `flush_caches` fail only with class
`0`): a returning call checked its guards and ran `check_jobs(PLO, PHI)` on `cqSM m` (the
solution's view: `cqBankSM`, `cqCtlSM`, caches flushed) resp. `cqCM m` (the challenge's view back:
`cqBankCM`, `cqCtlCM`, flushed); a failing one failed with class `0` or as that `check_jobs` call.
-/

namespace L.Checker
open L L.Arena L.Front
open Std.WP
open scoped Lean.Order
set_option experimental.vcgen true

/-- The memory `check_bs` runs the solution's jobs on: bank switch, index words, caches flushed. -/
def cqSM (m : Mem) : Mem := flushMem (cqCtlSM (cqBankSM m))

/-- **`check_bs()`**. -/
theorem checkBS_spec {p : Prog} (hp : p.lookup "check_bs" = some checkBSL) (n : Nat)
    (hB : ∀ s₀ : St, ⦃fun s => s = s₀⦄ invoke p (exec p n) "cq_bank_s" []
      ⦃fun _ s' => LocEq s' s₀ ∧ CqRowsSOK s₀.mem ∧ CqTailSOK (cqRowsS s₀.mem) ∧ s'.mem = cqBankSM s₀.mem;
       fun e => e.cls = 0⦄)
    (hC : ∀ s₀ : St, ⦃fun s => s = s₀⦄ invoke p (exec p n) "cq_ctl_s" []
      ⦃fun _ s' => LocEq s' s₀ ∧ CqCtlSOK s₀.mem ∧ s'.mem = cqCtlSM s₀.mem; fun e => e.cls = 0⦄)
    (hF : ∀ s₀ : St, ⦃fun s => s = s₀⦄ invoke p (exec p n) "flush_caches" []
      ⦃fun _ s' => LocEq s' s₀ ∧ FlushOK s₀.mem ∧ s'.mem = flushMem s₀.mem; fun e => e.cls = 0⦄)
    (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "check_bs" []
    ⦃fun r s' => LocEq s' s₀ ∧ r = [71757147230292] ∧ CqRowsSOK s₀.mem ∧ CqTailSOK (cqRowsS s₀.mem) ∧
      CqCtlSOK (cqBankSM s₀.mem) ∧ FlushOK (cqCtlSM (cqBankSM s₀.mem)) ∧
      ¬ rdW ((cqSM s₀.mem).arr64 DECL) 0 < (cqSM s₀.mem).glob PHI ∧
      ¬ (cqSM s₀.mem).glob PHI < (cqSM s₀.mem).glob PLO ∧
      ∃ r', callE p n "check_jobs" [(cqSM s₀.mem).glob PLO, (cqSM s₀.mem).glob PHI] (cqSM s₀.mem) = .ok (r', s'.mem);
     fun e => e.cls = 0 ∨
      callE p n "check_jobs" [(cqSM s₀.mem).glob PLO, (cqSM s₀.mem).glob PHI] (cqSM s₀.mem) = .error e⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkBSL]
  have hJ := fun (x y : Word) => callE_spec p n "check_jobs" [x, y]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, warr,
    (hB ·), (hC ·), (hF ·), (hJ · · ·)]
  all_goals clear hB hC hF hJ hp
  all_goals subst_vars
  all_goals simp_all only [L.St.setLocs_mem, cqSM, Cmp.eval, decide_eq_true_eq,
    cq_getElem_rdW, LocEq, Err.cls, true_or, or_true, not_false_eq_true]
  all_goals first | rfl | exact Or.inl rfl | exact ⟨_, rfl⟩ | fail
/-- The memory `check_bc` runs the challenge's jobs on: its view restored, caches flushed. -/
def cqCM (m : Mem) : Mem := flushMem (cqCtlCM (cqBankCM m))

/-- **`check_bc()`**. -/
theorem checkBC_spec {p : Prog} (hp : p.lookup "check_bc" = some checkBCL) (n : Nat)
    (hB : ∀ s₀ : St, ⦃fun s => s = s₀⦄ invoke p (exec p n) "cq_bank_c" []
      ⦃fun _ s' => LocEq s' s₀ ∧ s'.mem = cqBankCM s₀.mem; fun e => e.cls = 0⦄)
    (hC : ∀ s₀ : St, ⦃fun s => s = s₀⦄ invoke p (exec p n) "cq_ctl_c" []
      ⦃fun _ s' => LocEq s' s₀ ∧ CqCtlCOK s₀.mem ∧ s'.mem = cqCtlCM s₀.mem; fun e => e.cls = 0⦄)
    (hF : ∀ s₀ : St, ⦃fun s => s = s₀⦄ invoke p (exec p n) "flush_caches" []
      ⦃fun _ s' => LocEq s' s₀ ∧ FlushOK s₀.mem ∧ s'.mem = flushMem s₀.mem; fun e => e.cls = 0⦄)
    (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "check_bc" []
    ⦃fun r s' => LocEq s' s₀ ∧ r = [71757147230292] ∧ CqCtlCOK (cqBankCM s₀.mem) ∧
      FlushOK (cqCtlCM (cqBankCM s₀.mem)) ∧
      ¬ rdW ((cqCM s₀.mem).arr64 DECL) 0 < (cqCM s₀.mem).glob PHI ∧
      ¬ (cqCM s₀.mem).glob PHI < (cqCM s₀.mem).glob PLO ∧
      ∃ r', callE p n "check_jobs" [(cqCM s₀.mem).glob PLO, (cqCM s₀.mem).glob PHI] (cqCM s₀.mem) = .ok (r', s'.mem);
     fun e => e.cls = 0 ∨
      callE p n "check_jobs" [(cqCM s₀.mem).glob PLO, (cqCM s₀.mem).glob PHI] (cqCM s₀.mem) = .error e⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkBCL]
  have hJ := fun (x y : Word) => callE_spec p n "check_jobs" [x, y]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, warr,
    (hB ·), (hC ·), (hF ·), (hJ · · ·)]
  all_goals clear hB hC hF hJ hp
  all_goals subst_vars
  all_goals simp_all only [L.St.setLocs_mem, cqCM, Cmp.eval, decide_eq_true_eq,
    cq_getElem_rdW, LocEq, Err.cls, true_or, or_true, not_false_eq_true]
  all_goals first | rfl | exact Or.inl rfl | exact ⟨_, rfl⟩

end L.Checker
