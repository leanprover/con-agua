import ConAgua.Arena.Verdict
import ConAgua.Arena.WhnfCore
import ConAgua.Arena.WhnfDelta
import ConAgua.Compiler.RunEq

/-!
# Error models of `reduce_nat`'s family and the `whnf_core` arms (lane `verdicts-b`, helper `k2`)
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

l_model reduceNatWf_specE (p : Prog) (hf : p.lookup "reduce_nat_wf" = some reduceNatWfL)
  fns [hf ↦ reduceNatWfE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

l_model reduceNatOp_specE (p : Prog) (hf : p.lookup "reduce_nat_op" = some reduceNatOpL)
  fns [hf ↦ reduceNatOpE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

l_model reduceNatSucc_specE (p : Prog) (hf : p.lookup "reduce_nat_succ" = some reduceNatSuccL)
  fns [hf ↦ reduceNatSuccE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

l_model reduceNatK_specE (p : Prog) (hf : p.lookup "reduce_nat_k" = some reduceNatKL)
  fns [hf ↦ reduceNatKE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

l_model reduceNatAp_specE (p : Prog) (hf : p.lookup "reduce_nat_ap" = some reduceNatApL)
  fns [hf ↦ reduceNatApE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

l_model reduceNatHead_specE (p : Prog) (hf : p.lookup "reduce_nat_head" = some reduceNatHeadL)
  fns [hf ↦ reduceNatHeadE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

l_model reduceNat_specE (p : Prog) (hf : p.lookup "reduce_nat" = some reduceNatL)
  fns [hf ↦ reduceNatE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

l_model coreStepProj_specE (p : Prog) (hf : p.lookup "whnf_core_step_proj" = some whnfCoreStepProjL)
  fns [hf ↦ coreStepProjE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

l_model reduceProjCore_specE (p : Prog) (hf : p.lookup "reduce_proj_core" = some reduceProjCoreL)
  fns [hf ↦ reduceProjCoreE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

l_model projLitToCtor_specE (p : Prog) (hf : p.lookup "proj_lit_to_ctor" = some projLitToCtorL)
  fns [hf ↦ projLitToCtorE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

l_model coreApp_specE (p : Prog) (hf : p.lookup "whnf_core_app" = some whnfCoreAppL)
  fns [hf ↦ coreAppE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

l_model coreApp2_specE (p : Prog) (hf : p.lookup "whnf_core_app2" = some whnfCoreApp2L)
  fns [hf ↦ coreApp2E list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

l_model whnfApp_specE (p : Prog) (hf : p.lookup "whnf_app" = some whnfAppL)
  fns [hf ↦ whnfAppE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

end L.Arena
