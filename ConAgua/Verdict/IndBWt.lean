import ConAgua.Verdict.IndBSum2
import ConAgua.Verdict.PosKnotE
import ConAgua.Verdict.KnotAllE
/-!
# `whnf_telescope`'s error claim

`WtE` (the claim `check_sum_tele_slow`'s error refinement takes) is `wt_ref`'s error half
(`IndT/Sum1.lean`), with `whnf_top`'s claim from the error knot (`whnfTop_stageE`).
-/

open ConRon.Arena

namespace L.Ind

open L.Arena

/-- **`whnf_telescope`'s error claim** (`WtE`) from the program's facts: the knot (`whnf_top`'s
claim from the error knot), the lookups of `whnf_telescope`'s model. -/
theorem wtE_of {p : Prog} (hq : KnotStageProg p) (hnv : closedNV p _root_.L.Checker.nvFns = true)
    (hP : WtProg p) : WtE p := by
  intro dn vis fe env henv k hk s₀ a₀ i n e hC hA he hin eP hdP hwsP
  exact RefE.coreSpecE (wtE_spec p hP k s₀ vis i n e) hnv
    ⟨hnv, whnfTop_stageE hq.whnfTop hq.knotOK (fun n => L.Arena.KnotAllProg.knotE_all hq.knot hnv n)⟩
    (wt_ref hq hP henv k hk s₀.mem a₀ i n e hC hA he hin hdP hwsP)

end L.Ind
