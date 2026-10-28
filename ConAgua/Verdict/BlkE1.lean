import ConAgua.Arena.IndT.Pass
import ConAgua.Arena.GrindAttr

/-!
# `check_block_ctors`' error claim (lane `verdicts-b`, helper `ia2`, fork `blk`)

`check_block_ctors` (`checkBlockCtorsE_claim`: `CheckBlockCtorsE`, the claim the block pass's
error claim takes), from its refinement `ict_ref` (`IndT/Install7`) through the run.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- **`check_block_ctors`' error claim** (`CheckBlockCtorsE`, the `err_stmt` of
`checkBlockCtors_refinesC`), from its refinement `ict_ref` through the run. -/
theorem checkBlockCtorsE_claim {p : Prog} (hnv : closedNV p _root_.L.Checker.nvFns = true)
    (eSC : CheckSumCtorsE p) : CheckBlockCtorsE p := by
  intro hq dn vis fe env henv hV hOpf hLC hLT hApd hCrk hP s₀ a₀ pp mo ml co cl bs mss cvs hC hqd hsrc hmss
    hcvs hA bsP mssP cvsP hbsP hmssP hcvsP hws hok₀ hfe F hF e he
  cases F with
  | zero =>
    exact RefE.run_err (ictE_spec p hP 0 s₀ vis vis pp mo ml co cl) hnv ⟨hnv, eSC⟩
      (G := CtorsG p) (R := fun _ _ _ => True) (by rw [ictE.eq_1]; exact RefE.of_cls0 (by simp)) he
  | succ n =>
  exact RefE.run_err (ictE_spec p hP (n + 1) s₀ vis vis pp mo ml co cl) hnv ⟨hnv, eSC⟩
    (ict_ref hq henv hV hOpf hLC hLT hApd hCrk hP n (by omega) s₀.mem a₀ pp mo ml co cl bs mss cvs hC hqd
      hsrc hmss hcvs hA hbsP hmssP hcvsP hws hok₀ hfe) he

end L.Ind
