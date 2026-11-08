module

public import ConAgua.Compiler.WFSplit
public import ConAgua.Checker.Entry
public import ConAgua.Checker.Prelude
public import ConAgua.Arena.Abs1
public import ConAgua.Arena.AppStore
public import ConAgua.Arena.ArRange
public import ConAgua.Arena.ArRangeSpec
public import ConAgua.Arena.BVarStore
public import ConAgua.Arena.BvarB
public import ConAgua.Arena.CheckerL
public import ConAgua.Arena.ConstStore
public import ConAgua.Arena.ConstsResolveF
public import ConAgua.Arena.CoreCaches
public import ConAgua.Arena.CoreLevels
public import ConAgua.Arena.DeclAndPin
public import ConAgua.Arena.DeclApd
public import ConAgua.Arena.DeclArms
public import ConAgua.Arena.DeclArmsCanon
public import ConAgua.Arena.DeclArmsNat
public import ConAgua.Arena.DeclStep
public import ConAgua.Arena.DefEq
public import ConAgua.Arena.Env
public import ConAgua.Arena.ExprMk
public import ConAgua.Arena.FVarRange
public import ConAgua.Arena.FVarStore
public import ConAgua.Arena.ForallStore
public import ConAgua.Arena.Freeze
public import ConAgua.Arena.HasFvar
public import ConAgua.Arena.ImaxStore
public import ConAgua.Arena.IndIface
public import ConAgua.Arena.IndInstall
public import ConAgua.Arena.IndParts
public import ConAgua.Arena.IndPos
public import ConAgua.Arena.IndPos2
public import ConAgua.Arena.IndSum
public import ConAgua.Arena.Infer
public import ConAgua.Arena.InferFieldSort
public import ConAgua.Arena.Inst1
public import ConAgua.Arena.Inst1Spec
public import ConAgua.Arena.InstLP
public import ConAgua.Arena.InstList
public import ConAgua.Arena.InstListSpec
public import ConAgua.Arena.Knot
public import ConAgua.Arena.LamStore
public import ConAgua.Arena.LetStore
public import ConAgua.Arena.LevelApd
public import ConAgua.Arena.LevelEquiv
public import ConAgua.Arena.LevelHeap
public import ConAgua.Arena.LevelIntern
public import ConAgua.Arena.LevelLeq
public import ConAgua.Arena.LevelSimp
public import ConAgua.Arena.LevelStore
public import ConAgua.Arena.LevelSubst
public import ConAgua.Arena.LevelSubstL
public import ConAgua.Arena.LevelSubstLP
public import ConAgua.Arena.LevelZero
public import ConAgua.Arena.LiftL
public import ConAgua.Arena.LsStore
public import ConAgua.Arena.MaxStore
public import ConAgua.Arena.MemoLib
public import ConAgua.Arena.NAnonStore
public import ConAgua.Arena.NNumStore
public import ConAgua.Arena.NStrStore
public import ConAgua.Arena.NatAdd
public import ConAgua.Arena.NatArms
public import ConAgua.Arena.NatBits
public import ConAgua.Arena.NatCmp
public import ConAgua.Arena.NatDiv
public import ConAgua.Arena.NatGcd
public import ConAgua.Arena.NatMul
public import ConAgua.Arena.NatPow
public import ConAgua.Arena.NatShl
public import ConAgua.Arena.NatShr
public import ConAgua.Arena.NatSub
public import ConAgua.Arena.ParamStore
public import ConAgua.Arena.Pins
public import ConAgua.Arena.ProjStore
public import ConAgua.Arena.PropRead
public import ConAgua.Arena.RecCheck
public import ConAgua.Arena.RecClass
public import ConAgua.Arena.RecGen
public import ConAgua.Arena.Refine
public import ConAgua.Arena.Rom
public import ConAgua.Arena.RomExpr
public import ConAgua.Arena.RomItems
public import ConAgua.Arena.RomLevel
public import ConAgua.Arena.RomLevels
public import ConAgua.Arena.RomPins
public import ConAgua.Arena.Scratch
public import ConAgua.Arena.SortStore
public import ConAgua.Arena.Store
public import ConAgua.Arena.StrLit
public import ConAgua.Arena.StripTele
public import ConAgua.Arena.StubInd
public import ConAgua.Arena.StubNames
public import ConAgua.Arena.TeleLift
public import ConAgua.Arena.Walk
public import ConAgua.Arena.WalkLeaves
public import ConAgua.Arena.WalkLift
public import ConAgua.Arena.WalkScope
public import ConAgua.Arena.WhnfCore
public import ConAgua.Arena.WhnfDelta
public import ConAgua.Arena.WhnfEntry
public import ConAgua.Arena.WhnfIota
public import ConAgua.Arena.WhnfIotaRec
public import ConAgua.Arena.WhnfM2C
public import ConAgua.Arena.WhnfProj
public import ConAgua.Arena.WhnfSpineArgs
public import ConAgua.Arena.WhnfSpineRefine
public import ConAgua.Arena.ZeroStore
public import ConAgua.Checker.Hoist
public import ConAgua.Checker.Presize
public import ConAgua.Front.Apply
public import ConAgua.Front.ApplyDecl
public import ConAgua.Front.ApplyExpr
public import ConAgua.Front.Driver
public import ConAgua.Front.Fields
public import ConAgua.Front.FieldsDecl
public import ConAgua.Front.IdTable
public import ConAgua.Front.IndApply
public import ConAgua.Front.IndFields
public import ConAgua.Front.Line
public import ConAgua.Front.LineRec
public import ConAgua.Front.NatDec
public import ConAgua.Front.Unescape
public import ConAgua.L.Examples
public import ConAgua.L.Syntax
public import ConAgua.Layout
public import ConAgua.Rom.CIRead
public import ConAgua.Rom.PinRead
public import ConAgua.Scan.Key
public import ConAgua.Scan.Leaves
public import ConAgua.Scan.Lit
public import ConAgua.Scan.Member
public import ConAgua.Scan.Records
public import ConAgua.Scan.Str
public import ConAgua.Scan.Utf8
public import ConAgua.Scan.Values

@[expose] public section

/-!
# The checker: one program (generated by `scripts/checker_prog.py`; do not edit)

`checkerProg` is every L function reachable from `check` (`ConAgua/Checker/Entry.lean`), each bound
to the `FunDecl` of the lanes' modules: the one body every non-stub binding of the name agrees on
(`L.Checker.entryProg` first). `checkerStubs` are the called functions with no L code yet: they
abort (the checker declines). DESIGN.md, "The checker as one program (lane `integrate`)".

1819 functions, 0 of them stubs.
-/

namespace L.Checker

open L L.Compiler

/-- The called functions with no L code yet (each aborts). -/
def checkerStubs : List String := []

/-- The frontend functions `builtin_prelude` runs on the prelude's bytes (96; `preFn`,
`ConAgua/Checker/Prelude.lean`), each bound as `pre_<name>`. -/
def preNames : List String := [
  "apply_decl",
  "apply_dline",
  "apply_expr",
  "apply_ind",
  "apply_rec",
  "apply_str",
  "byte_in",
  "d_member",
  "dec_chunk",
  "decl_cv",
  "decl_val",
  "esc_one",
  "esc_sur",
  "expr_node",
  "front_line",
  "front_run",
  "has_escape",
  "hex3",
  "hex4",
  "hints_num",
  "hints_obj",
  "hints_val",
  "ifl_ids",
  "ind_bool",
  "ind_ctor",
  "ind_cv",
  "ind_fields",
  "ind_list",
  "ind_member",
  "ind_nlist",
  "ind_num",
  "ind_obj",
  "ind_rec",
  "ind_type",
  "inst_ctors",
  "inst_recs",
  "inst_types",
  "install_ind_d",
  "key_at",
  "key_at_g1",
  "key_at_g2",
  "key_at_g3",
  "key_at_g4",
  "key_at_g5",
  "key_at_g6",
  "key_end",
  "line_rec",
  "lp_put",
  "ls_put",
  "match_dlit",
  "match_lit",
  "match_word",
  "nat_dec",
  "next_member",
  "node_const",
  "node_lit",
  "node_lit_str",
  "num_end",
  "read_nat",
  "rec_decl_line",
  "rec_decl_obj",
  "rec_nat_list",
  "scan_axiom",
  "scan_binder_info",
  "scan_bool",
  "scan_def",
  "scan_hints",
  "scan_ind_ctor",
  "scan_ind_ctors",
  "scan_ind_decl",
  "scan_ind_rec",
  "scan_ind_recs",
  "scan_ind_type",
  "scan_ind_types",
  "scan_nat_list",
  "scan_opaque",
  "scan_quot",
  "scan_quoted_nat",
  "scan_rule",
  "scan_rules",
  "scan_string",
  "scan_thm",
  "skip_braced",
  "skip_digits",
  "skip_ws",
  "slot_nat",
  "str_close",
  "str_code",
  "str_put_esc",
  "sub_rec",
  "sub_val",
  "u_next",
  "unescape",
  "utf8_char",
  "utf8_valid",
  "value_at"]

def preTree : NTree := nameTree preNames

/-- The functions reachable from `front_run` that are not copied (158): the copies call them
unrenamed (`PreSimProg`, `ConAgua/Checker/PreludeSim.lean`). -/
def preShared : List String := [
  "app_find",
  "app_push",
  "apply_level",
  "apply_nnum",
  "apply_nstr",
  "bvar_find",
  "bvar_push",
  "const_find",
  "const_push",
  "ctl_sum",
  "decl_code",
  "decl_kind",
  "decl_push",
  "der_b",
  "dind_alloc",
  "e_view",
  "esp_find",
  "esp_put",
  "expr_fresh",
  "expr_get",
  "expr_put",
  "fld_alloc",
  "fld_put",
  "forall_find",
  "forall_push",
  "front_init",
  "hex_val",
  "if_reset",
  "ifl_alloc",
  "ifl_contains",
  "ifl_find_last",
  "ifl_nodup",
  "ifl_push",
  "ifr_alloc",
  "imax_find",
  "imax_push",
  "ind_caps",
  "ind_pi_tele_len",
  "ind_rules",
  "ind_rules_go",
  "ind_size",
  "ind_slot",
  "intern_app",
  "intern_bvar",
  "intern_const",
  "intern_forall",
  "intern_imax",
  "intern_lam",
  "intern_letE",
  "intern_lit",
  "intern_lit_str",
  "intern_ls",
  "intern_max",
  "intern_nanon",
  "intern_nnum",
  "intern_nstr",
  "intern_param",
  "intern_proj",
  "intern_sort",
  "intern_succ",
  "intern_zero",
  "lam_find",
  "lam_push",
  "letE_find",
  "letE_push",
  "level_fresh",
  "level_get",
  "level_put",
  "lh_mk",
  "limbs_eq",
  "lit_find",
  "lit_find_str",
  "lit_hash",
  "lit_match",
  "lit_match_str",
  "lit_push",
  "lit_push_str",
  "ls_find",
  "ls_match",
  "ls_push",
  "lsp_find",
  "lsp_put",
  "lv_cases",
  "lv_cases_at",
  "lv_comb",
  "lv_dist1",
  "lv_dist2",
  "lv_eq",
  "lv_equiv",
  "lv_imax",
  "lv_imax_l",
  "lv_imax_r",
  "lv_leq",
  "lv_node",
  "lv_rest",
  "lv_simp",
  "lv_subsimp",
  "lv_subst",
  "max_find",
  "max_push",
  "mk_app",
  "mk_forall",
  "mk_lam",
  "mk_let",
  "mk_proj",
  "name_fresh",
  "name_get",
  "name_put",
  "name_rec_pre",
  "nanon_find",
  "nanon_push",
  "nat_mad",
  "nnum_find",
  "nnum_push",
  "node_bin",
  "node_let",
  "node_proj",
  "nsp_find",
  "nsp_put",
  "nstr_find",
  "nstr_match",
  "nstr_push",
  "param_find",
  "param_push",
  "parse_rule_d",
  "pi_result_d",
  "pi_sort_tele_len",
  "proj_find",
  "proj_push",
  "sort_find",
  "sort_push",
  "store_fuel",
  "sub_bit",
  "succ_find",
  "succ_push",
  "utf8_put",
  "validate_ind_d",
  "vi_ctor",
  "vi_ids_go",
  "vi_k_expected",
  "vi_listed",
  "vi_listed_go",
  "vi_map",
  "vi_map_go",
  "vi_nested",
  "vi_np_go",
  "vi_nparams",
  "vi_order",
  "vi_order_go",
  "vi_order_in",
  "vi_rec",
  "vi_rec_idx",
  "vi_recs",
  "vi_recs_go",
  "vi_tail",
  "vi_unsafe",
  "zero_find",
  "zero_push"]

end L.Checker
