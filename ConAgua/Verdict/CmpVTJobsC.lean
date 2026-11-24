module

import ConAgua.Checker.CompareTwinC
public import ConAgua.Verdict.CmpVSJobs
public import ConAgua.Verdict.ThreadsE
public import ConAgua.Checker.CmpThreadsC
public import ConAgua.Final.CompareTwinVerdict
import ConAgua.Checker.CmpThreadsPool
import ConAgua.Checker.CmpVerdictNv
import ConAgua.Checker.CrsProgPB
import ConAgua.Checker.RomProgInit
import ConAgua.Checker.JobsProg
import ConAgua.Checker.CheckARun
import ConAgua.Checker.AsmFinal
import ConAgua.Arena.FreezeFresh
import ConAgua.Arena.FreezeTrunc
import ConAgua.Arena.JobStart
import ConAgua.Arena.PoolJobsJ

@[expose] public section

/-!
# The challenge's threads of the compared run fail only where the twin's pool does (lane
compare2, helper compare2-verdict)

After the solution's pooled
accept and mode `7` (`F6`, then `par_compact(1)`), a thread over the challenge's buffer whose calls
ran and whose next call failed with a class other than `0`, the jobs below it run by the threads,
is a worker's list of the challenge's jobs failing at the solution
(`TwinCompareVerdictPooled`'s third disjunct). `cjStepE_ofJ`: `cjStepE_of` at any solution, under
the solution's guard (`JobGJ`) and `check_record_sol`'s facts (`CrsFor`).
-/

open ConRon.Arena ConAgua.Final

namespace L.Checker

open L L.Arena L.Rom L.Compiler ConRon.Bridge

local notation "VM" => ConLeche.CheckMode.verified

/-- `CjStepE` at any solution `J`, by `checkJobs_ref` (`cjStepE_of` with `JobGJ` and `CrsFor`). -/
theorem cjStepE_ofJ {pins : List INatOpPinSet} {dn : NIdx → Option ConLeche.Name}
    {ds : Array IDeclaration} {I : IStreamIndex} {a₀ : AState} {J : Option ISolution}
    {pinsP : List ConLeche.NatOpPinSet} {p : Prog}
    (hP : JobProg pins dn ds p) (hFD : FrontDecls ds) (hLD : DeclsLpsDn dn ds) (hdn : DnPers dn)
    (hpp : PersPinSets pins) (hds : ds.size < 2 ^ 63)
    (hden : ∀ x ∈ ds.toList, PersDecl x ∧ ∃ d, Frontend.denoteDecl a₀.store x = some d)
    (hPD : PinsDenote a₀.store pins pinsP) (hrec : JobSpec pins pinsP J a₀)
    (hcrs : CrsFor pins dn ds p J) (hG : JobGJ pins dn ds p J) :
    CjStepE pins dn ds I a₀ p J := by
  intro n m a j hn hj ⟨a₁, hJP, hS⟩ hF e hc
  rw [← hS.st] at hF
  have e1 : (j + 1).toNat = j.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  have h := checkJobs_ref (J := J) (I := I) hP hFD hLD hdn hpp hden hPD hrec hcrs (hi := j + 1) (j := j)
    (by rw [e1]; omega) hn hJP
    (fun t a' h1 h2 h3 => by
      obtain rfl : t = j.toNat := by omega
      rw [Nat.sub_self, List.range'_zero] at h3
      cases h3
      exact hF)
  have h' := RefC.run_err (checkJobs_specE p hP.check_jobs n ⟨m, Locals.init []⟩ j (j + 1))
    (fun e h0 => ErrClaimV.of_cls0 h0) trivial hG h hc
  rw [e1, Nat.add_sub_cancel_left, List.range'_one] at h'
  exact fun hk => twinFailsV_of_sameEnter hS (h' hk)

end L.Checker
