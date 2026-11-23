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
import all ConAgua.Arena.JustifyIface
import all ConAgua.Arena.Needs
import all ConAgua.Arena.Justify
import all ConAgua.Arena.JustifySide
import all ConAgua.Checker.CompareEntry
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
# The pre-loop stages' write sets, part 1 (lane `pipeline`)

The stages `builtin_prelude` of `PreLoopWSStages.lean` (generated by
`scripts/preloop_ws.py`). Do not edit by hand: rerun the script.
-/

namespace L.Checker

open L L.Arena L.Compiler
open Std.WP
open scoped Lean.Order

/-! ## `builtin_prelude` -/

/-- The call closure of `builtin_prelude` in `checkerProg` (255 functions). -/
def stageFns_builtin_prelude : List FnName := [
  "add_1", "add_n", "app_find", "app_push", "apply_level", "apply_nnum", "apply_nstr",
  "builtin_prelude", "bvar_find", "bvar_push", "const_find", "const_push", "ctl_sum", "decl_code",
  "decl_kind", "decl_push", "der_b", "dind_alloc", "e_view", "eid_sp_clear", "esp_find", "esp_put",
  "expr_fresh", "expr_get", "expr_put", "fld_alloc", "fld_put", "forall_find", "forall_push",
  "front_init", "front_reset", "hex_val", "if_reset", "ifl_alloc", "ifl_contains", "ifl_find_last",
  "ifl_nodup", "ifl_push", "ifr_alloc", "imax_find", "imax_push", "ind_caps", "ind_pi_tele_len",
  "ind_rules", "ind_rules_go", "ind_size", "ind_slot", "intern_app", "intern_bvar", "intern_const",
  "intern_forall", "intern_imax", "intern_lam", "intern_letE", "intern_lit", "intern_lit_str",
  "intern_ls", "intern_max", "intern_nanon", "intern_nnum", "intern_nstr", "intern_param",
  "intern_proj", "intern_sort", "intern_succ", "intern_zero", "kara_mid", "kara_prods", "kara_sum",
  "lam_find", "lam_push", "letE_find", "letE_push", "level_fresh", "level_get", "level_put",
  "lid_sp_clear", "limbs_eq", "lit_find", "lit_find_str", "lit_hash", "lit_match", "lit_match_str",
  "lit_push", "lit_push_str", "ls_find", "ls_match", "ls_push", "lsp_find", "lsp_put", "max_find",
  "max_push", "mk_app", "mk_forall", "mk_lam", "mk_let", "mk_proj", "mul_row", "mul_win",
  "mul_zeros", "name_fresh", "name_get", "name_put", "name_rec_pre", "nanon_find", "nanon_push",
  "nat_add", "nat_mad", "nat_mul", "nat_trim", "nid_sp_clear", "nnum_find", "nnum_push",
  "node_bin", "node_let", "node_proj", "nsp_find", "nsp_put", "nstr_find", "nstr_match",
  "nstr_push", "param_find", "param_push", "parse_rule_d", "pi_sort_tele_len", "pre_apply_decl",
  "pre_apply_dline", "pre_apply_expr", "pre_apply_ind", "pre_apply_rec", "pre_apply_str",
  "pre_byte_in", "pre_d_member", "pre_dec_chunk", "pre_decl_cv", "pre_decl_val", "pre_esc_one",
  "pre_esc_sur", "pre_expr_node", "pre_front_line", "pre_front_run", "pre_has_escape", "pre_hex3",
  "pre_hex4", "pre_hints_num", "pre_hints_obj", "pre_hints_val", "pre_ifl_ids", "pre_ind_bool",
  "pre_ind_ctor", "pre_ind_cv", "pre_ind_fields", "pre_ind_list", "pre_ind_member",
  "pre_ind_nlist", "pre_ind_num", "pre_ind_obj", "pre_ind_rec", "pre_ind_type", "pre_inst_ctors",
  "pre_inst_recs", "pre_inst_types", "pre_install_ind_d", "pre_key_at", "pre_key_at_g1",
  "pre_key_at_g2", "pre_key_at_g3", "pre_key_at_g4", "pre_key_at_g5", "pre_key_at_g6",
  "pre_key_end", "pre_line_rec", "pre_lp_put", "pre_ls_put", "pre_match_dlit", "pre_match_lit",
  "pre_match_word", "pre_nat_dec", "pre_nat_dec_big", "pre_nat_dec_chunks", "pre_nat_dec_split",
  "pre_next_member", "pre_node_const", "pre_node_lit", "pre_node_lit_str", "pre_num_end",
  "pre_read_nat", "pre_rec_decl_line", "pre_rec_decl_obj", "pre_rec_nat_list", "pre_scan_axiom",
  "pre_scan_binder_info", "pre_scan_bool", "pre_scan_def", "pre_scan_hints", "pre_scan_ind_ctor",
  "pre_scan_ind_ctors", "pre_scan_ind_decl", "pre_scan_ind_rec", "pre_scan_ind_recs",
  "pre_scan_ind_type", "pre_scan_ind_types", "pre_scan_nat_list", "pre_scan_opaque",
  "pre_scan_quot", "pre_scan_quoted_nat", "pre_scan_rule", "pre_scan_rules", "pre_scan_string",
  "pre_scan_thm", "pre_skip_braced", "pre_skip_digits", "pre_skip_ws", "pre_slot_nat",
  "pre_str_close", "pre_str_code", "pre_str_put_esc", "pre_sub_rec", "pre_sub_val", "pre_u_next",
  "pre_unescape", "pre_utf8_char", "pre_utf8_valid", "pre_value_at", "proj_find", "proj_push",
  "sort_find", "sort_push", "store_fuel", "sub_bit", "sub_row", "succ_find", "succ_push",
  "utf8_put", "validate_ind_d", "vi_ctor", "vi_ids_go", "vi_listed", "vi_listed_go", "vi_map",
  "vi_map_go", "vi_nested", "vi_np_go", "vi_nparams", "vi_order", "vi_order_go", "vi_order_in",
  "vi_rec", "vi_rec_idx", "vi_recs", "vi_recs_go", "vi_tail", "vi_unsafe", "zero_find",
  "zero_push"]

/-- The word arrays (other than `CTL`) the functions of `stageFns_builtin_prelude` store
into. -/
def stageA_builtin_prelude : List TieredArray :=
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

/-- The `CTL` words the functions of `stageFns_builtin_prelude` store into. -/
def stageC_builtin_prelude : List Word := [
  0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 28, 29, 30,
  31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 64, 65, 66, 67, 68, 69, 70, 71, 72, 240]

names_tree stageTree_builtin_prelude : stageFns_builtin_prelude

prog_all checkerProg_stageChk_builtin_prelude : checkerProg
  (wsChk CTL (fun a => stageA_builtin_prelude.contains a)
    (fun w => stageC_builtin_prelude.contains w) stageTree_builtin_prelude)

theorem checkerProg_stageClosed_builtin_prelude :
    closedA checkerProg stageA_builtin_prelude stageC_builtin_prelude
      stageFns_builtin_prelude = true :=
  closedW_of_all stageTree_builtin_prelude.eq (fun _ h => List.contains_iff_mem.mp h)
    (fun _ h => List.contains_iff_mem.mp h) checkerProg_stageChk_builtin_prelude

/-- **A run of `builtin_prelude` is a frame of its own write set.** -/
theorem stageFrame_builtin_prelude (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) "builtin_prelude" []
    ⦃fun _ s' =>
      MemFrame stageA_builtin_prelude stageC_builtin_prelude s₀.mem s'.mem; ⊤⦄ :=
  memFrame_of_closed checkerProg_stageClosed_builtin_prelude n
    (mem_of_tree stageTree_builtin_prelude.eq "builtin_prelude" (by decide +kernel)) s₀

theorem stageA_builtin_prelude_pins : (PINS : TieredArray) ∉ stageA_builtin_prelude := by decide +kernel

/-- Of the `CTL` words 131, 132, 148, 149, 150, 151, 240, `builtin_prelude` writes
240. -/
theorem stageC_builtin_prelude_off :
    ∀ w : Word, w.toNat ∈ ([131, 132, 148, 149, 150, 151] : List Nat) →
      w ∉ stageC_builtin_prelude :=
  not_mem_of_toNat (by decide +kernel)

end L.Checker
