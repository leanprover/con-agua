module

public import ConAgua.Verdict.WhnfModels2E
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop
import ConAgua.Arena.Verdict
import ConAgua.Checker.NoVerdictTree
import ConAgua.Front.Preserve
import all ConAgua.Arena.WhnfCore

@[expose] public section

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
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model whnfCoreStepE_spec (p : Prog) (hp : WhnfCoreProg p)
  fns [hp.step ↦ whnfCoreStepE list]
  specs [coreAppE_spec p hp.capp hp.capp2 hp.app n, coreStepProjE_spec p hp.sproj hp.rproj hp.plit n,
    callW_spec p n "inst1"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model whnfStepE_spec (p : Prog) (hp : WhnfDeltaProg p)
  fns [hp.whnfStep ↦ whnfStepE list]
  specs [reduceNatE_spec p hp n, callW_spec p n "unfold_definition"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] finish [tierW, idxW] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model whnfLoopE_spec (p : Prog) (hp : WhnfDeltaProg p)
  fns [hp.whnfLoop ↦ whnfLoopE]
  specs [whnfStepE_spec p hp n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] finish [tierW, idxW] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model whnfE_spec (p : Prog) (hp : WhnfDeltaProg p)
  fns [hp.whnf ↦ whnfE list]
  specs [callW_spec p n "wh_find", callW_spec p n "wh_put", whnfLoopE_spec p hp n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] finish [tierW, idxW] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

end L.Arena
