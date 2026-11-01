module

import ConAgua.Arena.Verdict
public import ConAgua.Arena.WhnfM2C
public import ConAgua.Arena.WhnfIota
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Checker.NoVerdictTree
public import Std.Tactic.BVDecide.Normalize.Prop
public import ConAgua.Checker.NoVerdictFns
public import ConAgua.L.ErrSpec
import all ConAgua.Arena.WhnfIota

@[expose] public section

/-!
# The models of `major_to_ctor`'s pieces, for both outcomes

`major_to_ctor`'s and its pieces' unified models (`l_model … unified`): the
knot's slots and `proof_irrel` through their runs, the pieces through their unified models, every
other callee (outside the verdict closure) through its `Option` model.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

l_model m2cPreE_spec (p : Prog) (hp : M2CProg p)
  fns [hp.pre ↦ m2cPreE list]
  specs [callW_spec p n "get_app_fn", callW_spec p n "m2c_const_view", callW_spec p n "ls_node"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model m2cCheckE_spec (p : Prog) (hp : M2CProg p)
  fns [hp.check ↦ m2cCheckE list]
  specs [callW_spec p n "fab_scope_ok"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model m2cK2E_spec (p : Prog) (hp : M2CProg p)
  fns [hp.k2 ↦ m2cK2E list]
  specs [callW_spec p n "get_app_args", callW_spec p n "intern_const", callW_spec p n "mk_app_n", m2cCheckE_spec p hp n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model m2cKE_spec (p : Prog) (hp : M2CProg p)
  fns [hp.k ↦ m2cKE list]
  specs [m2cPreE_spec p hp n, m2cK2E_spec p hp n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model m2cEtaE_spec (p : Prog) (hp : M2CProg p)
  fns [hp.eta ↦ m2cEtaE list]
  specs [m2cPreE_spec p hp n, callW_spec p n "get_app_args", callW_spec p n "caps_never_zero", callW_spec p n "m2c_eta2"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model m2cAnd2E_spec (p : Prog) (hp : M2CProg p)
  fns [hp.and2 ↦ m2cAnd2E list]
  specs [callW_spec p n "mk_proj", callW_spec p n "intern_const", callW_spec p n "mk_app_n", m2cCheckE_spec p hp n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model m2cAndE_spec (p : Prog) (hp : M2CProg p)
  fns [hp.and_ ↦ m2cAndE list]
  specs [callW_spec p n "pin_at", m2cPreE_spec p hp n, callW_spec p n "get_app_args", callW_spec p n "and_rescue_slots", m2cAnd2E_spec p hp n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model m2cArmsE_spec (p : Prog) (hp : M2CProg p)
  fns [hp.arms ↦ m2cArmsE list]
  specs [m2cKE_spec p hp n, m2cEtaE_spec p hp n, m2cAndE_spec p hp n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model m2cCtorE_spec (p : Prog) (hp : M2CProg p)
  fns [hp.ctor ↦ m2cCtorE list]
  specs [callW_spec p n "pi_result", callW_spec p n "get_app_fn", callW_spec p n "m2c_const_view", callW_spec p n "env_find", m2cArmsE_spec p hp n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model m2cHeadE_spec (p : Prog) (hp : M2CProg p)
  fns [hp.head ↦ m2cHeadE list]
  specs [callW_spec p n "is_ctor_app", callW_spec p n "env_find", m2cCtorE_spec p hp n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model mtcE_spec (p : Prog) (hp : M2CProg p) (hf : p.lookup "major_to_ctor" = some majorToCtorL)
  fns [hf ↦ mtcE list]
  specs [m2cHeadE_spec p hp n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

end L.Arena
