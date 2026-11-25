module

public import ConAgua.Checker.PreLoopWSBase
meta import ConAgua.Checker.PreLoopWSBase
import all ConAgua.Arena.Abs1
import all ConAgua.Arena.AppStore
import all ConAgua.Arena.ArRange
import all ConAgua.Arena.ArRangeSpec
import all ConAgua.Arena.BVarStore
import all ConAgua.Arena.BasisL
import all ConAgua.Arena.BvarB
import all ConAgua.Arena.CheckerL
import all ConAgua.Arena.ConsLib
import all ConAgua.Arena.ConsPresize
import all ConAgua.Arena.ConstStore
import all ConAgua.Arena.ConstsResolveF
import all ConAgua.Arena.CoreCaches
import all ConAgua.Arena.CoreLevels
import all ConAgua.Arena.DeclAndPin
import all ConAgua.Arena.DeclApd
import all ConAgua.Arena.DeclArms
import all ConAgua.Arena.DeclArmsCanon
import all ConAgua.Arena.DeclArmsNat
import all ConAgua.Arena.DeclStep
import all ConAgua.Arena.DefEq
import all ConAgua.Arena.Env
import all ConAgua.Arena.ExprMk
import all ConAgua.Arena.FVarRange
import all ConAgua.Arena.FVarStore
import all ConAgua.Arena.ForallStore
import all ConAgua.Arena.Freeze
import all ConAgua.Arena.FreezeCmp
import all ConAgua.Arena.HasFvar
import all ConAgua.Arena.ImaxStore
import all ConAgua.Arena.IndDeclConsts
import all ConAgua.Arena.IndIface
import all ConAgua.Arena.IndInstall
import all ConAgua.Arena.IndParts
import all ConAgua.Arena.IndPos
import all ConAgua.Arena.IndPos2
import all ConAgua.Arena.IndStream
import all ConAgua.Arena.IndSum
import all ConAgua.Arena.Infer
import all ConAgua.Arena.Inst1
import all ConAgua.Arena.Inst1Spec
import all ConAgua.Arena.InstLP
import all ConAgua.Arena.InstList
import all ConAgua.Arena.InstListSpec
import all ConAgua.Arena.IotaFrame
import all ConAgua.Arena.IotaRel
import all ConAgua.Arena.Justify
import all ConAgua.Arena.JustifyIface
import all ConAgua.Arena.JustifySide
import all ConAgua.Arena.Knot
import all ConAgua.Arena.LamStore
import all ConAgua.Arena.LetStore
import all ConAgua.Arena.LevelApd
import all ConAgua.Arena.LevelEquiv
import all ConAgua.Arena.LevelHeap
import all ConAgua.Arena.LevelIntern
import all ConAgua.Arena.LevelLeq
import all ConAgua.Arena.LevelSimp
import all ConAgua.Arena.LevelStore
import all ConAgua.Arena.LevelSubst
import all ConAgua.Arena.LevelSubstL
import all ConAgua.Arena.LevelSubstLP
import all ConAgua.Arena.LevelZero
import all ConAgua.Arena.LiftL
import all ConAgua.Arena.LsStore
import all ConAgua.Arena.MaxStore
import all ConAgua.Arena.MemoLib
import all ConAgua.Arena.NAnonStore
import all ConAgua.Arena.NNumStore
import all ConAgua.Arena.NStrStore
import all ConAgua.Arena.NatAdd
import all ConAgua.Arena.NatArms
import all ConAgua.Arena.NatBits
import all ConAgua.Arena.NatCmp
import all ConAgua.Arena.NatDiv
import all ConAgua.Arena.NatDivKstep
import all ConAgua.Arena.NatDivSubmul
import all ConAgua.Arena.NatDivWord
import all ConAgua.Arena.NatGcd
import all ConAgua.Arena.NatLeaf
import all ConAgua.Arena.NatMul
import all ConAgua.Arena.NatPow
import all ConAgua.Arena.NatShl
import all ConAgua.Arena.NatShr
import all ConAgua.Arena.NatSized
import all ConAgua.Arena.NatSub
import all ConAgua.Arena.Needs
import all ConAgua.Arena.ParamStore
import all ConAgua.Arena.Pins
import all ConAgua.Arena.Prelude
import all ConAgua.Arena.ProjStore
import all ConAgua.Arena.PropRead
import all ConAgua.Arena.RecCheck
import all ConAgua.Arena.RecClass
import all ConAgua.Arena.RecGen
import all ConAgua.Arena.Refine
import all ConAgua.Arena.Rom
import all ConAgua.Arena.RomCI
import all ConAgua.Arena.RomExpr
import all ConAgua.Arena.RomItems
import all ConAgua.Arena.RomLevel
import all ConAgua.Arena.RomLevels
import all ConAgua.Arena.RomPins
import all ConAgua.Arena.Scratch
import all ConAgua.Arena.SortStore
import all ConAgua.Arena.Store
import all ConAgua.Arena.StrLit
import all ConAgua.Arena.StripTele
import all ConAgua.Arena.StubInd
import all ConAgua.Arena.StubNames
import all ConAgua.Arena.TeleLift
import all ConAgua.Arena.Walk
import all ConAgua.Arena.WalkLeaves
import all ConAgua.Arena.WalkLift
import all ConAgua.Arena.WalkScope
import all ConAgua.Arena.WhnfCore
import all ConAgua.Arena.WhnfDelta
import all ConAgua.Arena.WhnfEntry
import all ConAgua.Arena.WhnfIota
import all ConAgua.Arena.WhnfIotaRec
import all ConAgua.Arena.WhnfM2C
import all ConAgua.Arena.WhnfProj
import all ConAgua.Arena.WhnfSpineArgs
import all ConAgua.Arena.WhnfSpineRefine
import all ConAgua.Arena.ZeroStore
import all ConAgua.Checker.CmpSeqEntry
import all ConAgua.Checker.CompareEntry
import all ConAgua.Checker.Entry
import all ConAgua.Checker.Hoist
import all ConAgua.Checker.Prelude
import all ConAgua.Checker.Presize
import all ConAgua.Front.Apply
import all ConAgua.Front.ApplyDecl
import all ConAgua.Front.ApplyExpr
import all ConAgua.Front.Driver
import all ConAgua.Front.Fields
import all ConAgua.Front.FieldsDecl
import all ConAgua.Front.IdTable
import all ConAgua.Front.IndApply
import all ConAgua.Front.IndFields
import all ConAgua.Front.Line
import all ConAgua.Front.LineRec
import all ConAgua.Front.NatDec
import all ConAgua.Front.Unescape
import all ConAgua.L.Examples
import all ConAgua.Rom.CIConst
import all ConAgua.Rom.CIRead
import all ConAgua.Rom.PinRead
import all ConAgua.Rom.PinReadSpec
import all ConAgua.Scan.Key
import all ConAgua.Scan.Leaves
import all ConAgua.Scan.Line
import all ConAgua.Scan.Lit
import all ConAgua.Scan.Member
import all ConAgua.Scan.Records
import all ConAgua.Scan.Str
import all ConAgua.Scan.Utf8
import all ConAgua.Scan.Values

@[expose] public section

/-!
# The pre-loop stages' write sets, part 2 (lane `pipeline`)

The stages `front_run`, `prepare_prelude` of `PreLoopWSStages.lean` (generated by
`scripts/preloop_ws.py`). Do not edit by hand: rerun the script.
-/

namespace L.Checker

open L L.Arena L.Compiler
open Std.WP
open scoped Lean.Order

/-! ## `front_run` -/

/-- The call closure of `front_run` in `checkerProg` (250 functions). -/
def stageFns_front_run : List FnName := [
  "add_1", "add_n", "app_find", "app_push", "apply_decl", "apply_dline", "apply_expr", "apply_ind",
  "apply_level", "apply_nnum", "apply_nstr", "apply_rec", "apply_str", "bvar_find", "bvar_push",
  "byte_in", "const_find", "const_push", "ctl_sum", "d_member", "dec_chunk", "decl_code",
  "decl_cv", "decl_kind", "decl_push", "decl_val", "der_b", "dind_alloc", "e_view", "esc_one",
  "esc_sur", "esp_find", "esp_put", "expr_fresh", "expr_get", "expr_node", "expr_put", "fld_alloc",
  "fld_put", "forall_find", "forall_push", "front_init", "front_line", "front_run", "has_escape",
  "hex3", "hex4", "hex_val", "hints_num", "hints_obj", "hints_val", "if_reset", "ifl_alloc",
  "ifl_contains", "ifl_find_last", "ifl_ids", "ifl_nodup", "ifl_push", "ifr_alloc", "imax_find",
  "imax_push", "ind_bool", "ind_caps", "ind_ctor", "ind_cv", "ind_fields", "ind_list",
  "ind_member", "ind_nlist", "ind_num", "ind_obj", "ind_pi_tele_len", "ind_rec", "ind_rules",
  "ind_rules_go", "ind_size", "ind_slot", "ind_type", "inst_ctors", "inst_recs", "inst_types",
  "install_ind_d", "intern_app", "intern_bvar", "intern_const", "intern_forall", "intern_imax",
  "intern_lam", "intern_letE", "intern_lit", "intern_lit_str", "intern_ls", "intern_max",
  "intern_nanon", "intern_nnum", "intern_nstr", "intern_param", "intern_proj", "intern_sort",
  "intern_succ", "intern_zero", "kara_mid", "kara_prods", "kara_sum", "key_at", "key_at_g1",
  "key_at_g2", "key_at_g3", "key_at_g4", "key_at_g5", "key_at_g6", "key_end", "lam_find",
  "lam_push", "letE_find", "letE_push", "level_fresh", "level_get", "level_put", "limbs_eq",
  "line_rec", "lit_find", "lit_find_str", "lit_hash", "lit_match", "lit_match_str", "lit_push",
  "lit_push_str", "lp_put", "ls_find", "ls_match", "ls_push", "ls_put", "lsp_find", "lsp_put",
  "match_dlit", "match_lit", "match_word", "max_find", "max_push", "mk_app", "mk_forall", "mk_lam",
  "mk_let", "mk_proj", "mul_row", "mul_win", "mul_zeros", "name_fresh", "name_get", "name_put",
  "name_rec_pre", "nanon_find", "nanon_push", "nat_add", "nat_dec", "nat_dec_big",
  "nat_dec_chunks", "nat_dec_split", "nat_mad", "nat_mul", "nat_trim", "next_member", "nnum_find",
  "nnum_push", "node_bin", "node_const", "node_let", "node_lit", "node_lit_str", "node_proj",
  "nsp_find", "nsp_put", "nstr_find", "nstr_match", "nstr_push", "num_end", "param_find",
  "param_push", "parse_rule_d", "pi_sort_tele_len", "proj_find", "proj_push", "read_nat",
  "rec_decl_line", "rec_decl_obj", "rec_nat_list", "scan_axiom", "scan_binder_info", "scan_bool",
  "scan_def", "scan_hints", "scan_ind_ctor", "scan_ind_ctors", "scan_ind_decl", "scan_ind_rec",
  "scan_ind_recs", "scan_ind_type", "scan_ind_types", "scan_nat_list", "scan_opaque", "scan_quot",
  "scan_quoted_nat", "scan_rule", "scan_rules", "scan_string", "scan_thm", "skip_braced",
  "skip_digits", "skip_ws", "slot_nat", "sort_find", "sort_push", "store_fuel", "str_close",
  "str_code", "str_put_esc", "sub_bit", "sub_rec", "sub_row", "sub_val", "succ_find", "succ_push",
  "u_next", "unescape", "utf8_char", "utf8_put", "utf8_valid", "validate_ind_d", "value_at",
  "vi_ctor", "vi_ids_go", "vi_listed", "vi_listed_go", "vi_map", "vi_map_go", "vi_nested",
  "vi_np_go", "vi_nparams", "vi_order", "vi_order_go", "vi_order_in", "vi_rec", "vi_rec_idx",
  "vi_recs", "vi_recs_go", "vi_tail", "vi_unsafe", "zero_find", "zero_push"]

/-- The word arrays (other than `CTL`) the functions of `stageFns_front_run` store
into. -/
def stageA_front_run : List TieredArray :=
  tier0s [
  POOL, REC, SLOT, AREC, ASLOT, SREC, SSLOT, ZREC, ZSLOT, MREC, MSLOT, IREC, ISLOT, PREC, PSLOT,
  SOREC, SOSLOT, CREC, CSLOT, LEREC, LESLOT, BREC, BSLOT, LAREC, LASLOT, FAREC, FASLOT, PJREC,
  PJSLOT, NAREC, NASLOT, NSREC, NSSLOT, NNREC, NNSLOT, LSREC, LSSLOT, ADER, LADER, FADER, LEDER,
  PJDER, SHP, MHP, IHP, LSHP, SOLP, CLP, Front.NID, Front.LID, Front.EID, Front.DECL, Front.DLP,
  Front.Ind.IFR, Front.Ind.IFL, Front.NIDS, Front.LIDS, Front.EIDS] ++
  tier1s [
  POOL, REC, SLOT, AREC, ASLOT, SREC, SSLOT, ZREC, ZSLOT, MREC, MSLOT, IREC, ISLOT, PREC, PSLOT,
  SOREC, SOSLOT, CREC, CSLOT, LEREC, LESLOT, BREC, BSLOT, LAREC, LASLOT, FAREC, FASLOT, PJREC,
  PJSLOT, NAREC, NASLOT, NSREC, NSSLOT, NNREC, NNSLOT, LSREC, LSSLOT, ADER, LADER, FADER, LEDER,
  PJDER, SHP, MHP, IHP, LSHP, SOLP, CLP, Front.NID, Front.LID, Front.EID]

/-- The `CTL` words the functions of `stageFns_front_run` store into. -/
def stageC_front_run : List Word := [
  0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 28, 29, 30,
  31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 65, 67, 69, 70, 71, 72]

names_tree stageTree_front_run : stageFns_front_run

prog_all checkerProg_stageChk_front_run : checkerProg
  (wsChk CTL (fun a => stageA_front_run.contains a)
    (fun w => stageC_front_run.contains w) stageTree_front_run)

theorem checkerProg_stageClosed_front_run :
    closedA checkerProg stageA_front_run stageC_front_run
      stageFns_front_run = true :=
  closedW_of_all stageTree_front_run.eq (fun _ h => List.contains_iff_mem.mp h)
    (fun _ h => List.contains_iff_mem.mp h) checkerProg_stageChk_front_run

/-- **A run of `front_run` is a frame of its own write set.** -/
theorem stageFrame_front_run (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) "front_run" []
    ⦃fun _ s' =>
      MemFrame stageA_front_run stageC_front_run s₀.mem s'.mem; ⊤⦄ :=
  memFrame_of_closed checkerProg_stageClosed_front_run n
    (mem_of_tree stageTree_front_run.eq "front_run" (by decide +kernel)) s₀

theorem stageA_front_run_pins : (PINS : TieredArray) ∉ stageA_front_run := by decide +kernel

/-- Of the `CTL` words 131, 132, 148, 149, 150, 151, 240, `front_run` writes
none. -/
theorem stageC_front_run_off :
    ∀ w : Word, w.toNat ∈ ([131, 132, 148, 149, 150, 151, 240] : List Nat) →
      w ∉ stageC_front_run :=
  not_mem_of_toNat (by decide +kernel)

/-! ## `prepare_prelude` -/

/-- The call closure of `prepare_prelude` in `checkerProg` (58 functions). -/
def stageFns_prepare_prelude : List FnName := [
  "decl_declares", "decl_declares_go", "decl_key", "hn_clear", "hn_find", "hn_put", "hoist_any",
  "hoist_app", "hoist_apply", "hoist_block_go", "hoist_bucket", "hoist_chain", "hoist_close_go",
  "hoist_closure", "hoist_deps", "hoist_deps_of", "hoist_emit", "hoist_forall", "hoist_fvar",
  "hoist_index_go", "hoist_ins", "hoist_ix", "hoist_lam", "hoist_let", "hoist_names",
  "hoist_names_go", "hoist_nat_op_ground", "hoist_note", "hoist_proj", "hoist_rules_go",
  "hoist_targets_go", "hoist_walk", "hoist_zero", "hs_clear", "hs_find", "hs_put", "intern_nanon",
  "iw_alloc", "nanon_find", "nanon_push", "nat_div_mod_names", "nat_op_deps", "nat_op_names",
  "nat_op_pins", "nat_op_pins_a", "nat_op_pins_b", "nat_op_pins_c", "nat_op_record", "pin_at",
  "prep_back", "prep_back_rec", "prep_copy", "prep_copy_rec", "prep_find", "prep_front",
  "prep_rest", "prepare_prelude", "slice_has"]

/-- The word arrays (other than `CTL`) the functions of `stageFns_prepare_prelude` store
into. -/
def stageA_prepare_prelude : List TieredArray :=
  tier0s [
  NAREC, NASLOT, Front.DECL, HSEEN, HNIX, Ind.IW] ++
  tier1s [
  NAREC, NASLOT]

/-- The `CTL` words the functions of `stageFns_prepare_prelude` store into. -/
def stageC_prepare_prelude : List Word := [
  34, 35, 73, 74, 75, 76, 200]

names_tree stageTree_prepare_prelude : stageFns_prepare_prelude

prog_all checkerProg_stageChk_prepare_prelude : checkerProg
  (wsChk CTL (fun a => stageA_prepare_prelude.contains a)
    (fun w => stageC_prepare_prelude.contains w) stageTree_prepare_prelude)

theorem checkerProg_stageClosed_prepare_prelude :
    closedA checkerProg stageA_prepare_prelude stageC_prepare_prelude
      stageFns_prepare_prelude = true :=
  closedW_of_all stageTree_prepare_prelude.eq (fun _ h => List.contains_iff_mem.mp h)
    (fun _ h => List.contains_iff_mem.mp h) checkerProg_stageChk_prepare_prelude

/-- **A run of `prepare_prelude` is a frame of its own write set.** -/
theorem stageFrame_prepare_prelude (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) "prepare_prelude" []
    ⦃fun _ s' =>
      MemFrame stageA_prepare_prelude stageC_prepare_prelude s₀.mem s'.mem; ⊤⦄ :=
  memFrame_of_closed checkerProg_stageClosed_prepare_prelude n
    (mem_of_tree stageTree_prepare_prelude.eq "prepare_prelude" (by decide +kernel)) s₀

theorem stageA_prepare_prelude_pins : (PINS : TieredArray) ∉ stageA_prepare_prelude := by decide +kernel

/-- Of the `CTL` words 131, 132, 148, 149, 150, 151, 240, `prepare_prelude` writes
none. -/
theorem stageC_prepare_prelude_off :
    ∀ w : Word, w.toNat ∈ ([131, 132, 148, 149, 150, 151, 240] : List Nat) →
      w ∉ stageC_prepare_prelude :=
  not_mem_of_toNat (by decide +kernel)

end L.Checker
