import ConAgua.Arena.IndPos2
import ConAgua.Arena.Verdict
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Error models of `nest_pos`, `nest_pos_bind`, `nest_pos_app`, `nest_cont`, their leaves
(lane `verdicts-b`, helper `ia2`, fork `kn1`)
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Ind

open L.Arena

l_model npE_spec (p : Prog) (hf : p.lookup "nest_pos" = some nestPosL)
  fns [hf ↦ npE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

l_model npbE_spec (p : Prog) (hf : p.lookup "nest_pos_bind" = some nestPosBindL)
  fns [hf ↦ npbE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

l_model npaE_spec (p : Prog) (hf : p.lookup "nest_pos_app" = some nestPosAppL)
  fns [hf ↦ npaE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

l_model ncE_spec (p : Prog) (hf : p.lookup "nest_cont" = some nestContL)
  fns [hf ↦ ncE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

l_model pfvE_spec (p : Prog) (hf : p.lookup "nest_pos_fvar" = some nestPosFvarL)
  fns [hf ↦ pfvE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

l_model nccE_spec (p : Prog) (hf : p.lookup "nest_cont_checks" = some nestContChecksL)
  fns [hf ↦ nccE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

l_model nitE_spec (p : Prog) (hf : p.lookup "nest_inst_type" = some nestInstTypeL)
  fns [hf ↦ nitE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

l_model ntyE_spec (p : Prog) (hf : p.lookup "nest_inst_type_ty" = some nestInstTypeTyL)
  fns [hf ↦ ntyE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

end L.Ind
