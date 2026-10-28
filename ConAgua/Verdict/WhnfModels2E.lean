import ConAgua.Arena.Verdict
import ConAgua.Arena.WhnfCore
import ConAgua.Arena.WhnfDelta
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Checker.NoVerdictTree
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Error models of `reduce_nat`'s family and the `whnf_core` arms (lane `verdicts-b`, helper `k2`)
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

l_model reduceNatSuccE_spec (p : Prog) (hp : WhnfDeltaProg p)
  fns [hp.reduceNatSucc ↦ reduceNatSuccE list]
  specs [callW_spec p n "nat_lit_supported", callW_spec p n "pin_at", callW_spec p n "raw_nat_lit",
    callW_spec p n "nat_succ_lit"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model reduceNatOpE_spec (p : Prog) (hp : WhnfDeltaProg p)
  fns [hp.reduceNatOp ↦ reduceNatOpE list]
  specs [callW_spec p n "raw_nat_lit", callW_spec p n "nat_op_result"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model reduceNatWfE_spec (p : Prog) (hp : WhnfDeltaProg p)
  fns [hp.reduceNatWf ↦ reduceNatWfE list]
  specs [callW_spec p n "nat_op_is_wf", callW_spec p n "nat_lit_supported", callW_spec p n "raw_nat_lit"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model reduceNatKE_spec (p : Prog) (hp : WhnfDeltaProg p)
  fns [hp.reduceNatK ↦ reduceNatKE list]
  specs [callW_spec p n "pin_word", reduceNatSuccE_spec p hp n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model reduceNatApE_spec (p : Prog) (hp : WhnfDeltaProg p)
  fns [hp.reduceNatAp ↦ reduceNatApE list]
  specs [callW_spec p n "pin_word", callW_spec p n "nat_bin_op_name", callW_spec p n "nat_op_stored",
    reduceNatOpE_spec p hp n, reduceNatWfE_spec p hp n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model reduceNatHeadE_spec (p : Prog) (hp : WhnfDeltaProg p)
  fns [hp.reduceNatHead ↦ reduceNatHeadE list]
  specs [reduceNatKE_spec p hp n, reduceNatApE_spec p hp n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model reduceNatE_spec (p : Prog) (hp : WhnfDeltaProg p)
  fns [hp.reduceNat ↦ reduceNatE list]
  specs [reduceNatHeadE_spec p hp n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

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
