module

import ConAgua.Arena.Verdict
public import ConAgua.Arena.WhnfCore
public import ConAgua.Arena.WhnfDelta
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Checker.NoVerdictTree
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop
import ConAgua.Front.Preserve
public import ConAgua.Checker.NoVerdictFns
public import ConAgua.L.ErrSpec
import all ConAgua.Arena.WhnfCore
import all ConAgua.Arena.WhnfDelta

@[expose] public section

/-!
# The models of `reduce_nat`'s family (both outcomes) and the `whnf_core` arms' error models

`reduce_nat`'s family: `l_model … unified`, the `whnf` slot through its run, the family through
its unified models, every other callee (outside the verdict closure) through its `Option` model.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

l_model reduceNatSuccE_spec (p : Prog) (hp : WhnfDeltaProg p)
  fns [hp.reduceNatSucc ↦ reduceNatSuccE list]
  specs [callW_spec p n "nat_lit_stored", callW_spec p n "pin_at", callW_spec p n "raw_nat_lit",
    callW_spec p n "nat_succ_lit"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model reduceNatOpE_spec (p : Prog) (hp : WhnfDeltaProg p)
  fns [hp.reduceNatOp ↦ reduceNatOpE list]
  specs [callW_spec p n "raw_nat_lit", callW_spec p n "nat_op_result"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model reduceNatWfE_spec (p : Prog) (hp : WhnfDeltaProg p)
  fns [hp.reduceNatWf ↦ reduceNatWfE list]
  specs [callW_spec p n "nat_op_is_wf", callW_spec p n "nat_lit_stored", callW_spec p n "raw_nat_lit"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model reduceNatKE_spec (p : Prog) (hp : WhnfDeltaProg p)
  fns [hp.reduceNatK ↦ reduceNatKE list]
  specs [callW_spec p n "pin_word", reduceNatSuccE_spec p hp n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model reduceNatApE_spec (p : Prog) (hp : WhnfDeltaProg p)
  fns [hp.reduceNatAp ↦ reduceNatApE list]
  specs [callW_spec p n "pin_word", callW_spec p n "nat_bin_op_name", callW_spec p n "nat_op_stored",
    reduceNatOpE_spec p hp n, reduceNatWfE_spec p hp n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model reduceNatHeadE_spec (p : Prog) (hp : WhnfDeltaProg p)
  fns [hp.reduceNatHead ↦ reduceNatHeadE list]
  specs [reduceNatKE_spec p hp n, reduceNatApE_spec p hp n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model reduceNatE_spec (p : Prog) (hp : WhnfDeltaProg p)
  fns [hp.reduceNat ↦ reduceNatE list]
  specs [reduceNatHeadE_spec p hp n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model projLitToCtorE_spec (p : Prog) (hf : p.lookup "proj_lit_to_ctor" = some projLitToCtorL)
  fns [hf ↦ projLitToCtorE list]
  specs [callW_spec p n "str_lit_stored", callW_spec p n "str_lit_ctor"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model reduceProjCoreE_spec (p : Prog) (hf : p.lookup "reduce_proj_core" = some reduceProjCoreL)
    (hl : p.lookup "proj_lit_to_ctor" = some projLitToCtorL)
  fns [hf ↦ reduceProjCoreE list]
  specs [projLitToCtorE_spec p hl n, callW_spec p n "find_proj", callW_spec p n "reduce_proj_head"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model coreStepProjE_spec (p : Prog) (hf : p.lookup "whnf_core_step_proj" = some whnfCoreStepProjL)
    (hr : p.lookup "reduce_proj_core" = some reduceProjCoreL)
    (hl : p.lookup "proj_lit_to_ctor" = some projLitToCtorL)
  fns [hf ↦ coreStepProjE list]
  specs [reduceProjCoreE_spec p hr hl n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model whnfAppE_spec (p : Prog) (hf : p.lookup "whnf_app" = some whnfAppL)
  fns [hf ↦ whnfAppE list]
  specs [callW_spec p n "beta_peel", callW_spec p n "mk_app", callW_spec p n "mk_app_n_from"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model coreApp2E_spec (p : Prog) (hf : p.lookup "whnf_core_app2" = some whnfCoreApp2L)
    (ha : p.lookup "whnf_app" = some whnfAppL)
  fns [hf ↦ coreApp2E list]
  specs [callW_spec p n "head_and_args", whnfAppE_spec p ha n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model coreAppE_spec (p : Prog) (hf : p.lookup "whnf_core_app" = some whnfCoreAppL)
    (h2 : p.lookup "whnf_core_app2" = some whnfCoreApp2L) (ha : p.lookup "whnf_app" = some whnfAppL)
  fns [hf ↦ coreAppE list]
  specs [callW_spec p n "get_app_spine", coreApp2E_spec p h2 ha n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

end L.Arena
