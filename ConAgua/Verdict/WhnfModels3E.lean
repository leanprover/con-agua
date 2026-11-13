module

import ConAgua.Arena.Verdict
public import ConAgua.Arena.WhnfIotaRec
public import ConAgua.Arena.WhnfIota
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Checker.NoVerdictTree
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop
public import ConAgua.Checker.NoVerdictFns
public import ConAgua.L.ErrSpec
import all ConAgua.Arena.WhnfIota
import all ConAgua.Arena.WhnfIotaRec

@[expose] public section

/-!
# Error models of the ι family (lane `verdicts-b`, helper `k2`)
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

l_model irFireE_spec (p : Prog) (hf : p.lookup "iota_rec_fire" = some iotaRecFireL)
  fns [hf ↦ irFireE list]
  specs [callW_spec p n "get_app_args"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model irFamE_spec (p : Prog) (hf : p.lookup "iota_rec_fam" = some iotaRecFamL)
  fns [hf ↦ irFamE list]
  specs [callW_spec p n "rec_fire_level_count", callW_spec p n "iota_no_cert", callW_spec p n "rec_fire_levels"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model pmE_spec (p : Prog) (hf : p.lookup "prepare_major" = some prepareMajorL)
  fns [hf ↦ pmE list]
  specs [callW_spec p n "rec_rule_k", callW_spec p n "is_ctor_app", callW_spec p n "is_str_lit"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model lmtcE_spec (p : Prog) (hf : p.lookup "lit_major_to_ctor" = some litMajorToCtorL)
  fns [hf ↦ lmtcE list]
  specs [callW_spec p n "lit_to_ctor_if_nat", callW_spec p n "str_lit_stored", callW_spec p n "str_lit_ctor"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model irMajorE_spec (p : Prog) (hf : p.lookup "iota_rec_major" = some iotaRecMajorL)
  fns [hf ↦ irMajorE list]
  specs [callW_spec p n "intern_bvar", callW_spec p n "get_app_fn", callW_spec p n "iota_rec_head", callW_spec p n "env_find", callW_spec p n "find_rule"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model irCE_spec (p : Prog) (hf : p.lookup "iota_rec_c" = some iotaRecCL)
    (hm : p.lookup "iota_rec_major" = some iotaRecMajorL)
  fns [hf ↦ irCE list]
  specs [callW_spec p n "env_find", callW_spec p n "ls_node", callW_spec p n "peel_pis", irMajorE_spec p hm n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model irAtE_spec (p : Prog) (hf : p.lookup "iota_rec_at" = some iotaRecAtL)
    (hc : p.lookup "iota_rec_c" = some iotaRecCL) (hm : p.lookup "iota_rec_major" = some iotaRecMajorL)
  fns [hf ↦ irAtE list]
  specs [callW_spec p n "iota_rec_head", irCE_spec p hc hm n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

end L.Arena
