module

import ConAgua.Arena.Verdict
public import ConAgua.Arena.DefEq
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Checker.NoVerdictTree
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop
public import ConAgua.Checker.NoVerdictFns
public import ConAgua.L.ErrSpec
import all ConAgua.Arena.DefEq

@[expose] public section

/-!
# Error models of the `whnf` family's `defeq` helpers (lane `verdicts-b`, helper `k2`)
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

l_model btsE_spec (p : Prog) (hf : p.lookup "bool_true_shortcut" = some boolTrueShortcutL)
  fns [hf ↦ btsE list]
  specs [callW_spec p n "is_bool_true"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model tupaE_spec (p : Prog) (hf : p.lookup "try_unfold_proj_app" = some tryUnfoldProjAppL)
  fns [hf ↦ tupaE list]
  specs [callW_spec p n "head_is_proj"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model dqE_spec (p : Prog) (hf : p.lookup "delta_quick" = some deltaQuickL)
  fns [hf ↦ dqE list]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model lnE_spec (p : Prog) (hf : p.lookup "lazy_nat" = some lazyNatL)
  fns [hf ↦ lnE list]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model piE_spec (p : Prog) (hf : p.lookup "prop_irrel" = some propIrrelL)
  fns [hf ↦ piE list]
  specs [callW_spec p n "not_proof_fast", callW_spec p n "is_proof_fast"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] gen 20 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model ectE_spec (p : Prog) (hf : p.lookup "eta_cert_ty" = some etaCertTyL)
  fns [hf ↦ ectE list]
  specs [callW_spec p n "inst1"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model ecbE_spec (p : Prog) (hf : p.lookup "eta_cert_body" = some etaCertBodyL)
    (ht : p.lookup "eta_cert_ty" = some etaCertTyL)
  fns [hf ↦ ecbE list]
  specs [callW_spec p n "intern_fvar", callW_spec p n "inst1", callW_spec p n "mk_app", ectE_spec p ht n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model ecE_spec (p : Prog) (hf : p.lookup "eta_cert" = some etaCertL)
    (hb : p.lookup "eta_cert_body" = some etaCertBodyL) (ht : p.lookup "eta_cert_ty" = some etaCertTyL)
  fns [hf ↦ ecE list]
  specs [callW_spec p n "io_neutral", ecbE_spec p hb ht n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model sectE_spec (p : Prog) (hf : p.lookup "struct_eta_cert_tail" = some structEtaCertTailL)
  fns [hf ↦ sectE list]
  specs [callW_spec p n "lvls_eq_c", callW_spec p n "eta_projs"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model secgE_spec (p : Prog) (hp : CertProg p)
  fns [hp.setGo ↦ secgE list]
  specs [callW_spec p n "er_slice_eq", callW_spec p n "ls_node", sectE_spec p hp.setTail n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model secwtbE_spec (p : Prog) (hp : CertProg p)
  fns [hp.setWtb ↦ secwtbE list]
  specs [callW_spec p n "get_app_fn", callW_spec p n "env_find", callW_spec p n "find_table", callW_spec p n "get_app_args", secgE_spec p hp n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model secwE_spec (p : Prog) (hp : CertProg p)
  fns [hp.setWith ↦ secwE list]
  specs [callW_spec p n "get_app_fn", callW_spec p n "env_find", callW_spec p n "get_app_args", secwtbE_spec p hp n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model ecpfE_spec (p : Prog) (hp : CertProg p)
  fns [hp.ecpFam ↦ ecpfE list]
  specs [callW_spec p n "pi_result", callW_spec p n "get_app_fn", callW_spec p n "env_find", callW_spec p n "find_table"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model ecpE_spec (p : Prog) (hp : CertProg p)
  fns [hp.ecp ↦ ecpE list]
  specs [callW_spec p n "get_app_fn", callW_spec p n "env_find", callW_spec p n "get_app_args", ecpfE_spec p hp n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model sefaE_spec (p : Prog) (hp : CertProg p)
  fns [hp.sefAt ↦ sefaE list]
  specs [secwE_spec p hp n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model sefE_spec (p : Prog) (hp : CertProg p)
  fns [hp.sef ↦ sefE list]
  specs [callW_spec p n "eta_ctor_shape", sefaE_spec p hp n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model seeE_spec (p : Prog) (hp : CertProg p)
  fns [hp.see ↦ seeE list]
  specs [sefE_spec p hp n, callW_spec p n "intern_fvar", callW_spec p n "mk_app", callW_spec p n "inst1"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model secpE_spec (p : Prog) (hp : CertProg p)
  fns [hp.secp ↦ secpE list]
  specs [callW_spec p n "io_neutral", seeE_spec p hp n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model secE_spec (p : Prog) (hp : CertProg p)
  fns [hp.setCert ↦ secE list]
  specs [callW_spec p n "eta_ctor_shape", sefaE_spec p hp n, ecpE_spec p hp n, secpE_spec p hp n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model iptE_spec (p : Prog) (hp : CertProg p)
  fns [hp.ipt ↦ iptE list]
  specs [callW_spec p n "e_view", callW_spec p n "pin_word", callW_spec p n "lvl_eq_c"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model ulsaE_spec (p : Prog) (hp : CertProg p)
  fns [hp.ulShapeAt ↦ ulsaE list]
  specs [callW_spec p n "env_find", callW_spec p n "inst_lp", callW_spec p n "peel_pis", callW_spec p n "inst_list"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model ulsE_spec (p : Prog) (hp : CertProg p)
  fns [hp.ulShape ↦ ulsE list]
  specs [callW_spec p n "get_app_fn", callW_spec p n "env_find", callW_spec p n "ls_node", callW_spec p n "find_table", callW_spec p n "get_app_args", ulsaE_spec p hp n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- The unit-like recursion, one group: `unit_like_loop`, `unit_like_struct`, `unit_like_fields`. -/
l_model ulE_spec (p : Prog) (hp : CertProg p)
  fns [hp.ulLoop ↦ ullE list, hp.ulStruct ↦ ulstE list, hp.ulFields ↦ ulfE list]
  specs [iptE_spec p hp n, ulsE_spec p hp n, callW_spec p n "intern_fvar", callW_spec p n "inst1"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model sutE_spec (p : Prog) (hp : CertProg p)
  fns [hp.suTail ↦ sutE list]
  specs [callW_spec p n "io_neutral"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model sucE_spec (p : Prog) (hp : CertProg p)
  fns [hp.sunit ↦ sucE list]
  specs [callW_spec p n "io_neutral", (ulE_spec p hp n).1, sutE_spec p hp n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

end L.Arena
