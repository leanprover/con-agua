import ConAgua.Arena.Verdict
import ConAgua.Arena.DefEq
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Checker.NoVerdictTree
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

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
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model tupaE_spec (p : Prog) (hf : p.lookup "try_unfold_proj_app" = some tryUnfoldProjAppL)
  fns [hf ↦ tupaE list]
  specs [callW_spec p n "head_is_proj"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model dqE_spec (p : Prog) (hf : p.lookup "delta_quick" = some deltaQuickL)
  fns [hf ↦ dqE list]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model lnE_spec (p : Prog) (hf : p.lookup "lazy_nat" = some lazyNatL)
  fns [hf ↦ lnE list]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model piE_spec (p : Prog) (hf : p.lookup "prop_irrel" = some propIrrelL)
  fns [hf ↦ piE list]
  specs [callW_spec p n "not_proof_fast", callW_spec p n "is_proof_fast"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] gen 20 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model ectE_spec (p : Prog) (hf : p.lookup "eta_cert_ty" = some etaCertTyL)
  fns [hf ↦ ectE list]
  specs [callW_spec p n "inst1"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model ecbE_spec (p : Prog) (hf : p.lookup "eta_cert_body" = some etaCertBodyL)
    (ht : p.lookup "eta_cert_ty" = some etaCertTyL)
  fns [hf ↦ ecbE list]
  specs [callW_spec p n "intern_fvar", callW_spec p n "inst1", callW_spec p n "mk_app", ectE_spec p ht n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model ecE_spec (p : Prog) (hf : p.lookup "eta_cert" = some etaCertL)
    (hb : p.lookup "eta_cert_body" = some etaCertBodyL) (ht : p.lookup "eta_cert_ty" = some etaCertTyL)
  fns [hf ↦ ecE list]
  specs [callW_spec p n "io_neutral", ecbE_spec p hb ht n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model sectE_spec (p : Prog) (hf : p.lookup "struct_eta_cert_tail" = some structEtaCertTailL)
  fns [hf ↦ sectE list]
  specs [callW_spec p n "lvls_eq_c", callW_spec p n "eta_projs"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model secgE_spec (p : Prog) (hf : p.lookup "struct_eta_cert_go" = some structEtaCertGoL)
    (ht : p.lookup "struct_eta_cert_tail" = some structEtaCertTailL)
  fns [hf ↦ secgE list]
  specs [callW_spec p n "er_slice_eq", callW_spec p n "reserved_contains_w", callW_spec p n "ls_node", callW_spec p n "tower_slots_all", sectE_spec p ht n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model secwtbE_spec (p : Prog) (hf : p.lookup "struct_eta_cert_wtb" = some structEtaCertWtbL)
    (hg : p.lookup "struct_eta_cert_go" = some structEtaCertGoL) (ht : p.lookup "struct_eta_cert_tail" = some structEtaCertTailL)
  fns [hf ↦ secwtbE list]
  specs [callW_spec p n "get_app_fn", callW_spec p n "env_find", callW_spec p n "get_app_args", secgE_spec p hg ht n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model secwE_spec (p : Prog) (hf : p.lookup "struct_eta_cert_with" = some structEtaCertWithL)
    (hb : p.lookup "struct_eta_cert_wtb" = some structEtaCertWtbL)
    (hg : p.lookup "struct_eta_cert_go" = some structEtaCertGoL) (ht : p.lookup "struct_eta_cert_tail" = some structEtaCertTailL)
  fns [hf ↦ secwE list]
  specs [callW_spec p n "get_app_fn", callW_spec p n "env_find", callW_spec p n "get_app_args", secwtbE_spec p hb hg ht n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model secE_spec (p : Prog) (hf : p.lookup "struct_eta_cert" = some structEtaCertL)
    (hw : p.lookup "struct_eta_cert_with" = some structEtaCertWithL) (hb : p.lookup "struct_eta_cert_wtb" = some structEtaCertWtbL)
    (hg : p.lookup "struct_eta_cert_go" = some structEtaCertGoL) (ht : p.lookup "struct_eta_cert_tail" = some structEtaCertTailL)
  fns [hf ↦ secE list]
  specs [callW_spec p n "eta_ctor_shape", secwE_spec p hw hb hg ht n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model sutE_spec (p : Prog) (hf : p.lookup "struct_unit_tail" = some structUnitTailL)
  fns [hf ↦ sutE list]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model suhE_spec (p : Prog) (hf : p.lookup "struct_unit_head" = some structUnitHeadL)
    (ht : p.lookup "struct_unit_tail" = some structUnitTailL)
  fns [hf ↦ suhE list]
  specs [callW_spec p n "get_app_fn", callW_spec p n "env_find", callW_spec p n "get_app_args", callW_spec p n "ls_node", callW_spec p n "reserved_contains_w", sutE_spec p ht n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model sucE_spec (p : Prog) (hf : p.lookup "struct_unit_cert" = some structUnitCertL)
    (hh : p.lookup "struct_unit_head" = some structUnitHeadL)
    (ht : p.lookup "struct_unit_tail" = some structUnitTailL)
  fns [hf ↦ sucE list]
  specs [suhE_spec p hh ht n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

end L.Arena
