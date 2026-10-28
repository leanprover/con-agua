import ConAgua.Verdict.IndA3
import ConAgua.Verdict.IndBE
import ConAgua.Arena.GrindAttr
import ConAgua.L.ModelGen

/-!
# `check_block_ctors`' error claim (lane `verdicts-b`, helper `ia2`, fork `blk`)

`check_block_ctors` (`checkBlockCtorsE_claim`: `CheckBlockCtorsE`): `check_block_ctors_go`'s error
half from its refinement `icbg_ref` (`IndT/Install7`) through the run.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model ictE_spec (p : Prog) (hf : p.lookup "check_block_ctors" = some checkBlockCtors)
  fns [hf ↦ ictE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

theorem blkE1_nv : ∀ f ∈ ["block_shape_lps"], f ∈ _root_.L.Checker.nvFns :=
  _root_.L.Checker.nv_sub (by decide +kernel)

/-- **`check_block_ctors`'s error claim** (`CheckBlockCtorsE`, the `err_stmt` of
`checkBlockCtors_refinesC`), from `check_sum_ctors`'s. -/
theorem checkBlockCtorsE_claim {p : Prog} (hnv : closedNV p _root_.L.Checker.nvFns = true)
    (eSC : CheckSumCtorsE p) : CheckBlockCtorsE p := by
  intro hq dn vis fe env henv hV hOpf hLC hLT hApd hCrk hP s₀ a₀ pp mo ml co cl bs mss cvs hC hqd hsrc hmss
    hcvs hA bsP mssP cvsP hbsP hmssP hcvsP hws hok₀ hfe F hF e he
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  replace he := triple_of_callE_err (ictE_spec p hP.ctors F ⟨s₀.mem, Locals.init []⟩ vis vis pp mo ml co cl) he
    (Err.code_ne_of_cls hk0)
  simp only at he
  cases F with
  | zero => rw [ictE.eq_1] at he; cases he; exact absurd Err.cls_outOfFuel hk0
  | succ n =>
  rw [ictE.arm1] at he
  cases h1 : callE p n "block_shape_lps" [pp] s₀.mem with
  | error e1 =>
    rw [h1, ictE.k_block_shape_lps.none] at he; cases he
    exact ErrClaim.of_callE_nv hnv (blkE1_nv _ (by simp)) h1
  | ok q1 =>
    obtain ⟨r1, m1⟩ := q1
    rw [h1, ictE.k_block_shape_lps.arm1] at he
    obtain ⟨s1, hs1, -, hW1, -⟩ := triple_of_callW (s₀ := ⟨s₀.mem, Locals.init []⟩)
      (blockShapeLps_spec2 p hP.alloc hP.erCopy hP.erToIw hP.lps n _ pp) (callW_of_callE h1)
    subst hs1
    obtain ⟨hS1, hg1, hd1, hb1⟩ := lpsW_ok' hW1 hC.stage hqd
    have hA1 : AbsOK s1.mem := lpsW_afr hW1 hA
    have hC1 : StageC dn vis fe env s1.mem a₀ := hC.of_pstep hS1 hA1 (ConRon.Bridge.Inductives.PStep.refl hC.check.state)
    obtain ⟨-, hq9, -⟩ := partsShapeFacts hqd hsrc
    cases h2 : callE p n "check_block_ctors_go" [vis, vis, pp, r1.headD 0, r1.tail.headD 0, mo, ml, co, cl] s1.mem with
    | error e2 =>
      rw [h2, ictE.k_check_block_ctors_go.none] at he; cases he
      exact RefE.run_err (icbgE_spec p hP n ⟨s1.mem, Locals.init []⟩ vis vis pp (r1.headD 0) (r1.tail.headD 0)
        mo ml co cl) hnv ⟨hnv, eSC⟩
        (icbg_ref hq henv hV hOpf hLC hLT hApd hCrk hP pp _ _ bs n (by omega) s1.mem a₀
        mo ml co cl mss cvs mssP cvsP hC1 (hqd.grow (decBS_mono _) hg1) (partsHsrc_grow hg1 hq9 hsrc) hd1 hb1
        (hmss.grow decMS_mono hg1) (hcvs.grow (fun q => OMono.decCVp q) hg1) hA1 hbsP hmssP hcvsP hws hok₀ hfe) h2
    | ok q2 =>
      obtain ⟨r2, m2⟩ := q2
      rw [h2, ictE.k_check_block_ctors_go.arm1] at he; cases he

end L.Ind
