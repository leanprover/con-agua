module

public import ConAgua.Arena.IotaFrame
public import ConAgua.Arena.WhnfBase
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
public import Std.WP.Tactic
import all ConAgua.Arena.IotaFrame

@[expose] public section

/-!
# The ι reading rule, part 1: the generated models (lane ronsync8)

One `l_model` per function of `IotaFrame.lean`, every callee through its run (`callW`), so that
the refinements (`IotaFrameRef*.lean`) take each callee's own refinement at its call.
-/

open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Ind

open L.Arena

l_model piTele_specW (p : Prog) (hf : p.lookup "pi_tele" = some piTeleL)
  fns [hf ↦ piTeleW list]
  specs [callW_spec p n "e_view"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model motiveLevel_specW (p : Prog) (hf : p.lookup "motive_level" = some motiveLevelL)
  fns [hf ↦ motiveLevelW list]
  specs [callW_spec p n "get_app_fn_f", callW_spec p n "e_view", callW_spec p n "expr_get_d",
    callW_spec p n "pi_result_f"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model iotaFrame_specW (p : Prog) (hf : p.lookup "iota_frame" = some iotaFrameL)
  fns [hf ↦ iotaFrameW list]
  specs [callW_spec p n "strip_pis", callW_spec p n "motive_level"]
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model isMinorAt_specW (p : Prog) (hf : p.lookup "is_minor_at" = some isMinorAtL)
  fns [hf ↦ isMinorAtW list]
  specs [callW_spec p n "expr_get_d", callW_spec p n "pi_tele", callW_spec p n "get_app_fn_f",
    callW_spec p n "e_view"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model minorsFrom_specW (p : Prog) (hf : p.lookup "minors_from" = some minorsFromL)
  fns [hf ↦ minorsFromW list]
  specs [callW_spec p n "iw_alloc", callW_spec p n "is_minor_at"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model iotaRecMajor_specW (p : Prog) (hf : p.lookup "iota_rec_major" = some iotaRecMajorL)
  fns [hf ↦ iotaRecMajorW list]
  specs [callW_spec p n "minors_from", callW_spec p n "expr_get_d", callW_spec p n "get_app_fn_f",
    callW_spec p n "e_view", callW_spec p n "get_app_args_f", callW_spec p n "expr_drop_vars_list"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model iotaRecOf_specW (p : Prog) (hf : p.lookup "iota_rec_of" = some iotaRecOfL)
  fns [hf ↦ iotaRecOfW list]
  specs [callW_spec p n "iota_frame", callW_spec p n "get_app_fn_f", callW_spec p n "e_view",
    callW_spec p n "iota_rec_major"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model liftFieldDoms_specW (p : Prog) (hf : p.lookup "lift_field_doms" = some liftFieldDomsL)
  fns [hf ↦ liftFieldDomsW list]
  specs [callW_spec p n "iw_alloc", callW_spec p n "lift_entry"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model liftIdxArgs_specW (p : Prog) (hf : p.lookup "lift_idx_args" = some liftIdxArgsL)
  fns [hf ↦ liftIdxArgsW list]
  specs [callW_spec p n "iw_alloc", callW_spec p n "expr_drop_vars", callW_spec p n "lift_entry"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model iotaPartsOfAt_specW (p : Prog) (hf : p.lookup "iota_parts_of_at" = some iotaPartsOfAtL)
  fns [hf ↦ iotaPartsOfAtW list]
  specs [callW_spec p n "expr_get_d", callW_spec p n "strip_pis", callW_spec p n "lift_field_doms",
    callW_spec p n "pi_tele", callW_spec p n "get_app_args_f", callW_spec p n "lift_idx_args"]
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model ctorLevelsAt_specW (p : Prog) (hf : p.lookup "ctor_levels_at" = some ctorLevelsAtL)
  fns [hf ↦ ctorLevelsAtW list]
  specs [callW_spec p n "er_to_iw", callW_spec p n "intern_ls_iw", callW_spec p n "param_levels"]
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model iotaBVars_specW (p : Prog) (hf : p.lookup "iota_bvars" = some iotaBVarsL)
  fns [hf ↦ iotaBVarsW list]
  specs [callW_spec p n "iw_alloc", callW_spec p n "intern_bvar"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model iotaParamsAt_specW (p : Prog) (hf : p.lookup "iota_params_at" = some iotaParamsAtL)
  fns [hf ↦ iotaParamsAtW list]
  specs [callW_spec p n "er_to_iw", callW_spec p n "iota_bvars"]
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model iotaPartsAtBody_specW (p : Prog) (hf : p.lookup "iota_parts_at_body" = some iotaPartsAtBodyL)
  fns [hf ↦ iotaPartsAtBodyW list]
  specs [callW_spec p n "instantiate_lift_fast", callW_spec p n "strip_pis",
    callW_spec p n "get_app_args_f"]
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

l_model iotaPartsAt_specW (p : Prog) (hf : p.lookup "iota_parts_at" = some iotaPartsAtL)
  fns [hf ↦ iotaPartsAtW list]
  specs [callW_spec p n "cv_lps", callW_spec p n "ctor_levels_at", callW_spec p n "iota_params_at",
    callW_spec p n "inst_lp_fast", callW_spec p n "strip_pis", callW_spec p n "iota_parts_at_body"]
  grind [arena_grind] fold [tierW, idxW, erRd]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]

end L.Ind
