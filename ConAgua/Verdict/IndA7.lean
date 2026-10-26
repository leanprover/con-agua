import ConAgua.Verdict.IndA4
import ConAgua.Arena.IndT.GenRec3

/-!
# `check_block_rec`'s error refinement (lane `verdicts-b`, helper `ia`)

A wrapper of `gen_rec_check`: `checkBlockRecE_claim` from the claim of `gen_rec_check`
(`GenRecCheckE`, the generated `err_stmt` of `genRecCheck_refinesC`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model icrE_spec (p : Prog) (hf : p.lookup "check_block_rec" = some checkBlockRec)
  fns [hf ↦ icrE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

-- `gen_rec_check`'s error claim, in the shape of `genRecCheck_refinesC`
err_stmt GenRecCheckE := genRecCheck_refinesC fuel n


section
variable {p : Prog}

theorem checkBlockRecE_claim (eG : GenRecCheckE p) : CheckBlockRecE p := by
  intro hkp env henv hV hApd hCrk hIlpf hp P fsR hclR hfR s₀ a dn vis fe pp nested pO pL tO tL rd mO mL bO bL cO cL
    bs params tbl rdv ms cvTas block hC hpre hrb hlp hP hA hkeep hcoh hfe pP paramsP tblP rdP MsP cvTasP blockP
    hsh hparP htblP hrdP hmsP hcvTP hblkP hMs hT hfRc F hF er he
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  replace he := triple_of_callE_err (icrE_spec p hp F ⟨s₀.mem, Locals.init []⟩ vis pp nested pO pL tO tL rd mO mL
    bO bL cO cL) he (Err.code_ne_of_cls hk0)
  simp only at he
  cases F with
  | zero => rw [icrE.eq_1] at he; cases he; exact absurd Err.cls_outOfFuel hk0
  | succ F =>
  rw [icrE.arm1] at he
  cases c1 : callE p F "gen_rec_check" [vis, pp, nested, pO, pL, tO, tL, rd, mO, mL, cO, cL, bO, bL] s₀.mem with
  | error e1 =>
    rw [c1, icrE.k_gen_rec_check.none] at he
    cases he
    obtain ⟨hbs, hpar, hparb, htbl, hrd, hms, hcv, hblk⟩ := hpre
    exact eG hkp henv hV hApd hCrk hIlpf P hclR hfR s₀ a hC hbs hrb hpar hparb htbl hrd hms hcv hblk hlp hP hA hkeep
      hcoh hfe hsh hparP htblP hrdP hmsP hcvTP hblkP hMs hT hfRc F (by omega) _ c1
  | ok q1 =>
    obtain ⟨r1, m1⟩ := q1
    rw [c1] at he
    cases he

end

end L.Ind
