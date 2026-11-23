module

public import ConAgua.Checker.Prog
public import ConAgua.Arena.Frame
public import ConAgua.Compiler.WriteSetSplit
meta import ConAgua.Checker.Prog
meta import ConAgua.Arena.Frame
meta import ConAgua.Compiler.WriteSetSplit
import all ConAgua.Arena.Abs1
import all ConAgua.Arena.AppStore
import all ConAgua.Arena.ArRange
import all ConAgua.Arena.ArRangeSpec
import all ConAgua.Arena.BVarStore
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
import all ConAgua.Arena.IndIface
import all ConAgua.Arena.IndInstall
import all ConAgua.Arena.IndParts
import all ConAgua.Arena.IotaFrame
import all ConAgua.Arena.IotaRel
import all ConAgua.Arena.JustifyIface
import all ConAgua.Arena.Needs
import all ConAgua.Arena.Justify
import all ConAgua.Arena.JustifySide
import all ConAgua.Checker.CompareEntry
import all ConAgua.Arena.IndPos
import all ConAgua.Arena.IndPos2
import all ConAgua.Arena.IndSum
import all ConAgua.Arena.Infer
import all ConAgua.Arena.InferFieldSort
import all ConAgua.Arena.Inst1
import all ConAgua.Arena.Inst1Spec
import all ConAgua.Arena.InstLP
import all ConAgua.Arena.InstList
import all ConAgua.Arena.InstListSpec
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
import all ConAgua.Arena.NatLeaf
import all ConAgua.Arena.NatArms
import all ConAgua.Arena.NatBits
import all ConAgua.Arena.NatCmp
import all ConAgua.Arena.NatDiv
import all ConAgua.Arena.NatDivKstep
import all ConAgua.Arena.NatDivSubmul
import all ConAgua.Arena.NatDivWord
import all ConAgua.Arena.NatGcd
import all ConAgua.Arena.NatMul
import all ConAgua.Arena.NatPow
import all ConAgua.Arena.NatShl
import all ConAgua.Arena.NatShr
import all ConAgua.Arena.NatSub
import all ConAgua.Arena.ParamStore
import all ConAgua.Arena.Pins
import all ConAgua.Arena.ProjStore
import all ConAgua.Arena.PropRead
import all ConAgua.Arena.RecCheck
import all ConAgua.Arena.RecClass
import all ConAgua.Arena.RecGen
import all ConAgua.Arena.Refine
import all ConAgua.Arena.Rom
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
import all ConAgua.Rom.CIRead
import all ConAgua.Rom.PinRead
import all ConAgua.Scan.Key
import all ConAgua.Scan.Leaves
import all ConAgua.Scan.Lit
import all ConAgua.Scan.Member
import all ConAgua.Scan.Records
import all ConAgua.Scan.Str
import all ConAgua.Scan.Utf8
import all ConAgua.Scan.Values
import all ConAgua.Arena.NatSized

@[expose] public section

/-!
# The write set of everything `check` runs before the declaration loop (lane `pipeline`)

`check_a` (`Entry.lean`) runs the stages `cap_check`, `pb_check`, `intern_reserved_pins`,
`builtin_prelude`, `front_run`, `prepare_prelude` and `intern_all_pins` before
phase A's fold; the compared run's mode `4` (`check_c1`, `CompareEntry.lean`) runs the first five,
then `cmp_stash`, which is a stage here as well. `preLoopFns` is their call closure in `checkerProg` (447 functions, computed
by `scripts/preloop_ws.py`), `preLoopA` the word arrays and `preLoopC` the `CTL` words their bodies
store into (every `CTL` index in the closure is a literal or `k + (e &&& 1)`). Per-chunk kernel
checks as `LoopCore.lean`. Corollaries: every stage's run is a `MemFrame preLoopA preLoopC`
(`preLoopFrame_*`), and the set misses the arrays and words the declaration loop needs zero at its
start (`preLoopA_loopZero`, `preLoopC_loopZero`).
-/

namespace L.Checker

open L L.Arena L.Compiler
open Std.WP
open scoped Lean.Order

/-- The call closure of the pre-loop stages in `checkerProg` (`scripts/preloop_ws.py`). -/
def preLoopFns : List FnName := [
  "add_1", "add_n", "app_find", "app_push", "apply_decl", "apply_dline", "apply_expr", "apply_ind",
  "apply_level", "apply_nnum", "apply_nstr", "apply_rec", "apply_str", "builtin_prelude",
  "bvar_find", "bvar_push", "byte_in", "cap_check", "cmp_stash", "const_find", "const_push",
  "ctl_sum", "d_member", "dec_chunk", "decl_code", "decl_cv", "decl_declares", "decl_declares_go",
  "decl_key", "decl_kind", "decl_push", "decl_val", "der_b", "dind_alloc", "e_view",
  "eid_sp_clear", "erec_alloc", "erec_put", "esc_one", "esc_sur", "esp_find", "esp_put",
  "expr_fresh", "expr_get", "expr_node", "expr_put", "fld_alloc", "fld_put", "forall_find",
  "forall_push", "front_init", "front_line", "front_reset", "front_run", "fvar_find", "fvar_push",
  "has_escape", "hex3", "hex4", "hex_val", "hints_num", "hints_obj", "hints_val", "hn_clear",
  "hn_find", "hn_put", "hoist_any", "hoist_app", "hoist_apply", "hoist_block_go", "hoist_bucket",
  "hoist_chain", "hoist_close_go", "hoist_closure", "hoist_deps", "hoist_deps_of", "hoist_emit",
  "hoist_forall", "hoist_fvar", "hoist_index_go", "hoist_ins", "hoist_ix", "hoist_lam",
  "hoist_let", "hoist_names", "hoist_names_go", "hoist_nat_op_ground", "hoist_note", "hoist_proj",
  "hoist_rules_go", "hoist_targets_go", "hoist_walk", "hoist_zero", "hs_clear", "hs_find",
  "hs_put", "if_reset", "ifl_alloc", "ifl_contains", "ifl_find_last", "ifl_ids", "ifl_nodup",
  "ifl_push", "ifr_alloc", "imax_find", "imax_push", "ind_bool", "ind_caps", "ind_ctor", "ind_cv",
  "ind_fields", "ind_list", "ind_member", "ind_nlist", "ind_num", "ind_obj", "ind_pi_tele_len",
  "ind_rec", "ind_rules", "ind_rules_go", "ind_size", "ind_slot", "ind_type", "inst_ctors",
  "inst_recs", "inst_types", "install_ind_d", "intern_all_pins", "intern_app", "intern_bvar",
  "intern_const", "intern_forall", "intern_fvar", "intern_imax", "intern_lam", "intern_letE",
  "intern_lit", "intern_lit_str", "intern_ls", "intern_max", "intern_nanon", "intern_nnum",
  "intern_nstr", "intern_param", "intern_pin_sets", "intern_proj", "intern_reserved_pins",
  "intern_sort", "intern_succ", "intern_zero", "iw_alloc", "kara_mid", "kara_prods", "kara_sum",
  "key_at", "key_at_g1", "key_at_g2", "key_at_g3", "key_at_g4", "key_at_g5", "key_at_g6",
  "key_end", "lam_find", "lam_push", "letE_find", "letE_push", "level_fresh", "level_get",
  "level_put", "lid_sp_clear", "limbs_eq", "line_rec", "lit_find", "lit_find_str", "lit_hash",
  "lit_match", "lit_match_str", "lit_push", "lit_push_str", "lp_put", "ls_find", "ls_match",
  "ls_push", "ls_put", "lsp_find", "lsp_put", "match_dlit", "match_lit", "match_word", "max_find",
  "max_push", "memo_get", "memo_push", "mk_app", "mk_forall", "mk_lam", "mk_let", "mk_proj",
  "mul_row", "mul_win", "mul_zeros", "name_fresh", "name_get", "name_put", "name_rec_pre",
  "nanon_find", "nanon_push", "nat_add", "nat_dec", "nat_dec_big", "nat_dec_chunks",
  "nat_dec_split", "nat_div_mod_names", "nat_mad", "nat_mul", "nat_op_deps", "nat_op_names",
  "nat_op_pins", "nat_op_pins_a", "nat_op_pins_b", "nat_op_pins_c", "nat_op_record", "nat_trim",
  "next_member", "nid_sp_clear", "nnum_find", "nnum_push", "node_bin", "node_const", "node_let",
  "node_lit", "node_lit_str", "node_proj", "nsp_find", "nsp_put", "nstr_find", "nstr_match",
  "nstr_push", "num_end", "param_find", "param_push", "parse_rule_d", "pb_check",
  "pi_sort_tele_len", "pin_at", "pre_apply_decl", "pre_apply_dline", "pre_apply_expr",
  "pre_apply_ind", "pre_apply_rec", "pre_apply_str", "pre_byte_in", "pre_d_member",
  "pre_dec_chunk", "pre_decl_cv", "pre_decl_val", "pre_esc_one", "pre_esc_sur", "pre_expr_node",
  "pre_front_line", "pre_front_run", "pre_has_escape", "pre_hex3", "pre_hex4", "pre_hints_num",
  "pre_hints_obj", "pre_hints_val", "pre_ifl_ids", "pre_ind_bool", "pre_ind_ctor", "pre_ind_cv",
  "pre_ind_fields", "pre_ind_list", "pre_ind_member", "pre_ind_nlist", "pre_ind_num",
  "pre_ind_obj", "pre_ind_rec", "pre_ind_type", "pre_inst_ctors", "pre_inst_recs",
  "pre_inst_types", "pre_install_ind_d", "pre_key_at", "pre_key_at_g1", "pre_key_at_g2",
  "pre_key_at_g3", "pre_key_at_g4", "pre_key_at_g5", "pre_key_at_g6", "pre_key_end",
  "pre_line_rec", "pre_lp_put", "pre_ls_put", "pre_match_dlit", "pre_match_lit", "pre_match_word",
  "pre_nat_dec", "pre_nat_dec_big", "pre_nat_dec_chunks", "pre_nat_dec_split", "pre_next_member",
  "pre_node_const", "pre_node_lit", "pre_node_lit_str", "pre_num_end", "pre_read_nat",
  "pre_rec_decl_line", "pre_rec_decl_obj", "pre_rec_nat_list", "pre_scan_axiom",
  "pre_scan_binder_info", "pre_scan_bool", "pre_scan_def", "pre_scan_hints", "pre_scan_ind_ctor",
  "pre_scan_ind_ctors", "pre_scan_ind_decl", "pre_scan_ind_rec", "pre_scan_ind_recs",
  "pre_scan_ind_type", "pre_scan_ind_types", "pre_scan_nat_list", "pre_scan_opaque",
  "pre_scan_quot", "pre_scan_quoted_nat", "pre_scan_rule", "pre_scan_rules", "pre_scan_string",
  "pre_scan_thm", "pre_skip_braced", "pre_skip_digits", "pre_skip_ws", "pre_slot_nat",
  "pre_str_close", "pre_str_code", "pre_str_put_esc", "pre_sub_rec", "pre_sub_val", "pre_u_next",
  "pre_unescape", "pre_utf8_char", "pre_utf8_valid", "pre_value_at", "prep_back", "prep_back_rec",
  "prep_copy", "prep_copy_rec", "prep_find", "prep_front", "prep_rest", "prepare_prelude",
  "proj_find", "proj_push", "read_nat", "rec_decl_line", "rec_decl_obj", "rec_nat_list",
  "rom_ex_leaf", "rom_ex_one", "rom_ex_ref", "rom_ex_two", "rom_expr", "rom_exprs_to", "rom_items",
  "rom_level", "rom_levels", "rom_lists_to", "rom_lit", "rom_lvls_go", "rom_name", "rom_names_to",
  "rom_pins_to", "rom_put", "rom_sets_to", "rom_tpairs_to", "rom_tpins_to", "rom_u64",
  "rset_clear", "rset_find", "rset_put", "scan_axiom", "scan_binder_info", "scan_bool", "scan_def",
  "scan_hints", "scan_ind_ctor", "scan_ind_ctors", "scan_ind_decl", "scan_ind_rec",
  "scan_ind_recs", "scan_ind_type", "scan_ind_types", "scan_nat_list", "scan_opaque", "scan_quot",
  "scan_quoted_nat", "scan_rule", "scan_rules", "scan_string", "scan_thm", "skip_braced",
  "skip_digits", "skip_ws", "slice_has", "slot_nat", "sort_find", "sort_push", "stk_pool",
  "stk_push", "store_fuel", "str_close", "str_code", "str_put_esc", "sub_bit", "sub_rec",
  "sub_row", "sub_val", "succ_find", "succ_push", "u_next", "unescape", "utf8_char", "utf8_put",
  "utf8_valid", "validate_ind_d", "value_at", "vi_ctor", "vi_ids_go", "vi_listed", "vi_listed_go",
  "vi_map", "vi_map_go", "vi_nested", "vi_np_go", "vi_nparams", "vi_order", "vi_order_go",
  "vi_order_in", "vi_rec", "vi_rec_idx", "vi_recs", "vi_recs_go", "vi_tail", "vi_unsafe",
  "zero_find", "zero_push"]

/-- The word arrays (other than `CTL`) the functions of `preLoopFns` store into. -/
def preLoopA : List TieredArray :=
  tier0s [
  POOL, REC, SLOT, AREC, ASLOT, SREC, SSLOT, ZREC, ZSLOT, MREC, MSLOT, IREC, ISLOT, PREC, PSLOT,
  SOREC, SOSLOT, CREC, CSLOT, LEREC, LESLOT, BREC, BSLOT, FVREC, FVSLOT, LAREC, LASLOT, FAREC,
  FASLOT, PJREC, PJSLOT, NAREC, NASLOT, NSREC, NSSLOT, NNREC, NNSLOT, LSREC, LSSLOT, ADER, LADER,
  FADER, LEDER, PJDER, SHP, MHP, IHP, LSHP, SOLP, CLP, FVLP, Front.NID, Front.LID, Front.EID,
  Front.DECL, Front.DLP, Front.Ind.IFR, Front.Ind.IFL, Front.NIDS, Front.LIDS, Front.EIDS, HSEEN,
  HNIX, PINS, EREC, Rom.RSTK, Rom.RMEMO, Rom.RSET, Ind.IW, CDECL] ++
  tier1s [
  POOL, REC, SLOT, AREC, ASLOT, SREC, SSLOT, ZREC, ZSLOT, MREC, MSLOT, IREC, ISLOT, PREC, PSLOT,
  SOREC, SOSLOT, CREC, CSLOT, LEREC, LESLOT, BREC, BSLOT, FVREC, FVSLOT, LAREC, LASLOT, FAREC,
  FASLOT, PJREC, PJSLOT, NAREC, NASLOT, NSREC, NSSLOT, NNREC, NNSLOT, LSREC, LSSLOT, ADER, LADER,
  FADER, LEDER, PJDER, SHP, MHP, IHP, LSHP, SOLP, CLP, FVLP, Front.NID, Front.LID, Front.EID, EREC]

/-- The `CTL` words the functions of `preLoopFns` store into. -/
def preLoopC : List Word := [
  0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 26, 27, 28,
  29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74,
  75, 76, 129, 130, 131, 132, 148, 149, 150, 151, 200, 240]

/-- `preLoopFns` as a tree of name codes. -/
names_tree preLoopTree : preLoopFns

theorem preLoop_mem (f : FnName) (h : (preLoopTree.find (nameCode f)).isSome = true) :
    f ∈ preLoopFns := by
  have := namesTree_spec preLoopTree.eq f
  rw [h] at this; exact of_decide_eq_true this.symm

/-- Every function of the checker passes the pre-loop per-function check. -/
prog_all checkerProg_preLoopChk :
  checkerProg (wsChk CTL (fun a => preLoopA.contains a) (fun w => preLoopC.contains w) preLoopTree)

theorem checkerProg_preLoopClosed : closedA checkerProg preLoopA preLoopC preLoopFns = true :=
  closedW_of_all preLoopTree.eq (fun _ h => List.contains_iff_mem.mp h)
    (fun _ h => List.contains_iff_mem.mp h) checkerProg_preLoopChk

/-- **Every run of a pre-loop function is a frame of `(preLoopA, preLoopC)`.** -/
theorem preLoop_frame (n : Nat) {f : FnName} (hf : f ∈ preLoopFns) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) f []
    ⦃fun _ s' => MemFrame preLoopA preLoopC s₀.mem s'.mem; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  exact (M.of_run (P := fun s => s = s₀) hs hrun
    (invoke_memFrame checkerProg_preLoopClosed n hf [] s₀)).1

theorem preLoopFrame_cap_check (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) "cap_check" []
    ⦃fun _ s' => MemFrame preLoopA preLoopC s₀.mem s'.mem; ⊤⦄ :=
  preLoop_frame n (preLoop_mem "cap_check" (by decide +kernel)) s₀

theorem preLoopFrame_pb_check (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) "pb_check" []
    ⦃fun _ s' => MemFrame preLoopA preLoopC s₀.mem s'.mem; ⊤⦄ :=
  preLoop_frame n (preLoop_mem "pb_check" (by decide +kernel)) s₀

theorem preLoopFrame_intern_reserved_pins (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) "intern_reserved_pins" []
    ⦃fun _ s' => MemFrame preLoopA preLoopC s₀.mem s'.mem; ⊤⦄ :=
  preLoop_frame n (preLoop_mem "intern_reserved_pins" (by decide +kernel)) s₀

theorem preLoopFrame_builtin_prelude (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) "builtin_prelude" []
    ⦃fun _ s' => MemFrame preLoopA preLoopC s₀.mem s'.mem; ⊤⦄ :=
  preLoop_frame n (preLoop_mem "builtin_prelude" (by decide +kernel)) s₀

theorem preLoopFrame_front_run (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) "front_run" []
    ⦃fun _ s' => MemFrame preLoopA preLoopC s₀.mem s'.mem; ⊤⦄ :=
  preLoop_frame n (preLoop_mem "front_run" (by decide +kernel)) s₀

theorem preLoopFrame_prepare_prelude (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) "prepare_prelude" []
    ⦃fun _ s' => MemFrame preLoopA preLoopC s₀.mem s'.mem; ⊤⦄ :=
  preLoop_frame n (preLoop_mem "prepare_prelude" (by decide +kernel)) s₀

theorem preLoopFrame_intern_all_pins (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) "intern_all_pins" []
    ⦃fun _ s' => MemFrame preLoopA preLoopC s₀.mem s'.mem; ⊤⦄ :=
  preLoop_frame n (preLoop_mem "intern_all_pins" (by decide +kernel)) s₀

/-- The arrays the declaration loop needs zero at its start are not written before it. -/
theorem preLoopA_loopZero :
    ∀ b ∈ tier0s [ABMEMO, ILMEMO, LPMEMO, LPLMEMO, LPLSMEMO, WSM, FLM, LSM, Stubs.CRM,
      Ind.MAM, Ind.NOM, Ind.DPM, Ind.RFM, Ind.RAM, Ind.TAM, Ind.HBM, Ind.MCM],
      b ∉ preLoopA := by
  decide +kernel

/-- The `CTL` words the declaration loop needs zero at its start (as numbers). -/
def loopZeroC : List Nat :=
  [48, 50, 54, 56, 58, 152, 154, 156, 158, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212,
    213, 214, 215, 216, 217, 218, 219]

/-- `preLoopC_loopZero` by numbers (deciding it on `List Word` membership takes over 3 GB). -/
theorem preLoopC_loopZeroN :
    (preLoopC.map UInt64.toNat).all (fun x => !loopZeroC.contains x) = true := by
  decide +kernel

/-- The `CTL` words the declaration loop needs zero at its start are not written before it. -/
theorem preLoopC_loopZero (w : Word) (hw : w.toNat ∈ loopZeroC) : w ∉ preLoopC := by
  intro h
  have := List.all_eq_true.mp preLoopC_loopZeroN w.toNat (List.mem_map.mpr ⟨w, h, rfl⟩)
  simp [hw] at this

end L.Checker
