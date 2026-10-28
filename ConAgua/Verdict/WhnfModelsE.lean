import ConAgua.Verdict.WhnfModels2E
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Error models of the `whnf` family's slot bodies (lane `verdicts-b`, helper `k2`)
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

l_model whnfCoreE_spec (p : Prog) (hf : p.lookup "whnf_core" = some whnfCoreL)
  fns [hf ↦ whnfCoreE list]
  specs [callW_spec p n "wk_find", callW_spec p n "wk_put", callW_spec p n "wc_find",
    callW_spec p n "wc_put"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model whnfCoreStepE_spec (p : Prog) (hp : WhnfCoreProg p)
  fns [hp.step ↦ whnfCoreStepE list]
  specs [coreAppE_spec p hp.capp hp.capp2 hp.app n, coreStepProjE_spec p hp.sproj hp.rproj hp.plit n,
    callW_spec p n "inst1"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model whnf_specE (p : Prog) (hf : p.lookup "whnf" = some whnfL)
  fns [hf ↦ whnfE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] finish [tierW, idxW] errors

l_model whnfLoop_specE (p : Prog) (hf : p.lookup "whnf_loop" = some whnfLoopL)
  fns [hf ↦ whnfLoopE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] finish [tierW, idxW] errors

l_model whnfStep_specE (p : Prog) (hf : p.lookup "whnf_step" = some whnfStepL)
  fns [hf ↦ whnfStepE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] finish [tierW, idxW] errors

end L.Arena
