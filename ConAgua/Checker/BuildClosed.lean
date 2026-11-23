module

public import ConAgua.Checker.Prog
meta import ConAgua.Checker.Prog
meta import ConAgua.Arena.Jobs
public import ConAgua.Compiler.WriteSetSplit
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
import all ConAgua.Arena.CoreWalks
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
import all ConAgua.Arena.IotaFrame
import all ConAgua.Arena.IotaRel
import all ConAgua.Arena.JustifyIface
import all ConAgua.Arena.Needs
import all ConAgua.Arena.Justify
import all ConAgua.Arena.JustifySide
import all ConAgua.Checker.CompareEntry
import all ConAgua.Arena.IndPos
import all ConAgua.Arena.IndPos2
import all ConAgua.Arena.IndStream
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
import all ConAgua.Arena.WhnfCoreApp
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
import all ConAgua.Arena.NatSized

@[expose] public section

/-!
# The stream index build's write set at the checker's program

`build_index` with its call closure (`biFns`, 351 functions) stores only where `biA`/`biC`
allow: every word array but `PINS` and `DECL`, every `CTL` word but `150` and `151` (the pin sets' header).
As `Checker/JobsClosed.lean`: name trees, the store sets as predicates, one kernel check per chunk
of the program's functions (`prog_all`), composed by `closedW_of_all`.
-/

namespace L.Checker

open L.Arena L.Compiler

/-- `build_index`'s call closure in the checker's program. -/
def biFns : List FnName :=
  ["build_index", "lit_from", "str_lit_names", "index_freeze", "sl_snoc", "intern_letE", "letE_find", "letE_push", "app_count", "app_fill", "app_find", "app_push", "base_row_get",
   "base_row_set", "basis_name_hit", "basis_name_hit_go", "bb_go", "bb_memo",
   "bb_node", "block_caps_at", "member_never_zero", "former_z", "former_res_sort", "pi_result", "lv_zero", "lh_push", "block_caps_at_er_copy", "block_caps_at_er_copy_go",
   "block_caps_ctor_names", "block_caps_fin", "block_caps_head", "block_caps_one",
   "block_constants", "block_counts", "block_counts_head", "block_counts_pure", "block_ctors",
   "block_ctors_go", "block_ctors_groups", "block_shape_ctor_groups", "block_formers", "block_formers_go", "block_groups", "block_groups_go",
   "block_groups_one", "block_is_rec", "block_is_rec_go", "block_is_rec_member",
   "block_member_counts", "block_member_counts_find", "block_member_counts_go", "block_names_eq",
   "block_rec", "block_recs", "read_block", "block_shape_all_ctors", "block_shape_all_ctors_go",
   "read_block_at", "formers_lps_ok", "ctors_params_ok", "ctors_lps_ok", "block_shape_ctors_copy", "block_shape_ctors_of", "block_shape_declared",
   "block_shape_fin", "block_shape_large", "block_shape_lps", "block_shape_member_names",
   "block_shape_members_of", "block_shape_names_of", "block_shape_pack", "block_shape_recs_of", "block_shape_result_sort", "block_shape_seal", "block_shape_tail",
   "block_split", "block_split_ctors", "block_split_recs", "block_table", "block_tables",
   "bm_clear", "bm_find", "bm_put", "bvar_b", "bvar_find", "bvar_push", "ci_at_lps", "const_find",
   "const_push", "ctor_info_rec", "ctor_member", "cv_at_lps", "decl_constants",
   "decl_constants_axiom", "decl_constants_ind", "decl_tables", "der_b", "der_bv", "dind_copy",
   "dlp_copy", "e_view", "ek_copy", "er_copy", "er_copy_er", "er_from_iw", "er_from_iw_go",
   "er_put_ci", "er_to_iw", "erec_alloc", "erec_ci", "erec_put", "expr_drop_vars",
   "expr_drop_vars_list", "fire_levels_at", "forall_find", "forall_push", "fvar_find", "fvar_push",
   "get_app_args", "get_app_args_f", "get_app_fn", "get_app_fn_f", "i1l_app", "i1l_clear",
   "i1l_find", "i1l_forall", "i1l_go", "i1l_lam", "i1l_let", "i1l_proj", "i1l_put", "idx_add",
   "idx_consts", "idx_tables", "if_clear", "if_find", "if_put", "ilp_clear", "ilp_find", "ilp_put",
   "ilpl_clear", "ilpl_find", "ilpl_put", "ilpls_clear", "ilpls_find", "ilpls_put", "imax_find",
   "imax_push", "ind_block_to_erec", "ind_copy_go", "ind_info_rec", "ind_rec_copy", "inst_app",
   "inst_entry", "inst_forall", "inst_go", "inst_lam", "inst_let", "inst_lp", "inst_lp_core",
   "inst_proj", "instantiate1_fast", "instantiate_lift_fast", "intern_app",
   "intern_bvar", "intern_const", "intern_forall", "intern_fvar", "intern_imax", "intern_lam",
   "intern_lit", "intern_ls", "intern_ls_iw", "intern_max", "intern_nanon", "intern_nnum",
   "intern_nstr", "intern_param", "intern_proj", "intern_sort", "intern_succ", "intern_zero",
   "iw_alloc", "iw_copy", "iw_pool", "iw_reset", "keys_ok", "keys_push", "lam_find", "lam_push",
   "lf_clear", "lf_find", "lf_put", "lh_mk", "lift_app", "lift_entry", "lift_forall", "lift_go",
   "lift_lam", "lift_let", "lift_proj", "limbs_eq", "lit_find", "lit_hash", "lit_match",
   "lit_push", "lp_app", "lp_forall", "lp_fvar", "lp_go", "lp_lam", "lp_let", "lp_let_tail",
   "lp_lookup", "lp_proj", "lp_rb_let", "lp_substl", "lq_find", "lq_put", "ls_find", "ls_match",
   "ls_node", "ls_push", "lv_cases", "lv_cases_at", "lv_comb", "lv_dist1", "lv_dist2", "lv_eq",
   "lv_equiv", "lv_imax", "lv_imax_l", "lv_imax_r", "lv_intern", "lv_leq", "lv_node", "lv_rest",
   "lv_simp", "lv_sub_int", "lv_subsimp", "lv_subst", "lvl_eq", "lvl_eq_c", "lvl_eq_rec",
   "ma_clear", "ma_find", "ma_put", "max_find", "max_push", "member_field_copy", "member_idx_at",
   "member_names_copy", "memo_get", "memo_push", "mentions_any_const", "mentions_any_go",
   "mentions_any_node", "mk_app", "mk_forall", "mk_lam", "mk_let", "mk_proj", "nanon_find",
   "nanon_push", "nnum_find", "nnum_push", "nstr_find", "nstr_match", "nstr_push", "num_ctors_of",
   "param_find", "param_levels", "param_levels_go", "param_push", "pi_binders",
   "pi_doms_mention_any", "pin_at", "pin_word", "pool_copy", "pool_room", "proj_find", "proj_push",
   "quot_at", "quot_pin", "rci_block", "rci_block_to", "rci_caps", "rci_ci", "rci_cv", "rci_fresh",
   "rci_lvls_to", "rci_name_sl", "rci_names_to", "rci_rule", "rci_rules_to", "rci_slot", "rec2",
   "rec3", "rec5", "rec6", "rec7", "rec_fire", "rec_info_rec", "rec_target_of",
   "reserved_contains", "reserved_from", "rom_basis_decls", "rom_ex_leaf_c", "rom_ex_one_c",
   "rom_ex_ref_c", "rom_ex_two_c", "rom_expr_c", "rom_exprs_to_c", "rom_level_c", "rom_levels_c",
   "rom_lit", "rom_lvls_go_c", "rom_name_c", "rom_put_c", "rom_u64_c", "rset_clear", "rset_find",
   "rset_put", "rules_at_lps_go", "rules_refire", "sl_append", "sl_cons", "sl_contains", "sl_eq",
   "sl_find", "sl_get", "sl_getd", "sl_memo", "sl_new1", "sle_go", "sls_go", "sls_memo",
   "sort_find", "sort_push", "spn_ls", "spn_pool", "spn_to_er", "spn_to_iw", "stk_pool",
   "stk_push", "strip_pis", "struct_proj_arg_p", "struct_proj_bodies", "struct_proj_bodies_go",
   "struct_proj_ps", "struct_ps_at", "struct_ps_at_go", "succ_find", "succ_push", "tbl_base_get",
   "tbl_base_set", "view_ls", "zero_find", "zero_push"]

names_tree biTree : biFns

/-- The arrays `build_index` may write: all but the pins, the records `DECL`, their pool `DLP`,
the compared run's kept records `CDECL` (`Checker/CompareEntry.lean`) and the preparation's memos
`HSEEN`, `HNIX`. -/
def biA : List TieredArray := checkerWordArrays.filter fun b =>
  b != PINS && b != L.Front.DECL && b != L.Front.DLP && b != CDECL && b != HSEEN && b != HNIX

/-- The `CTL` words `build_index` may write: all but the pin sets' words, the solution's flag
(`CTL[224]`, `Arena/JustifyIface.lean`), the preparation's memo stamps (`CTL[73]`, `CTL[75]`) and the
prelude's record count (`CTL[240]`). -/
def biC : List Word := ((List.range 1024).filter fun x => x != 150 && x != 151 && x != 224 &&
  x != 73 && x != 75 && x != 240).map UInt64.ofNat

/-- The arrays of `biA`, as a test. -/
def biPa (b : TieredArray) : Bool := checkerWordArrays.contains b && b != PINS && b != L.Front.DECL &&
  b != L.Front.DLP && b != CDECL && b != HSEEN && b != HNIX

/-- The `CTL` words of `biC`, as a test. -/
def biPc (x : Word) : Bool := decide (x.toNat < 1024) && x.toNat != 150 && x.toNat != 151 &&
  x.toNat != 224 && x.toNat != 73 && x.toNat != 75 && x.toNat != 240

theorem biPa_mem (b : TieredArray) (h : biPa b = true) : b ∈ biA := by
  simp only [biPa, Bool.and_eq_true, List.contains_iff_mem] at h
  simp only [biA, List.mem_filter, Bool.and_eq_true]
  exact ⟨h.1.1.1.1.1.1, by simp only [h, and_self]⟩

theorem biPc_mem (x : Word) (h : biPc x = true) : x ∈ biC := by
  simp only [biPc, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
  simp only [biC, List.mem_filter, List.mem_map, List.mem_range]
  refine ⟨x.toNat, ⟨h.1.1.1.1.1.1, ?_⟩, UInt64.ofNat_toNat⟩
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq]
  omega

theorem not_mem_biC {x : Word} (h : x.toNat = 150 ∨ x.toNat = 151 ∨ x.toNat = 224 ∨ x.toNat = 73 ∨
    x.toNat = 75 ∨ x.toNat = 240) : x ∉ biC := by
  intro hm
  simp only [biC, List.mem_map, List.mem_filter, List.mem_range] at hm
  obtain ⟨y, ⟨hy, hb⟩, rfl⟩ := hm
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hb
  rw [UInt64.toNat_ofNat_of_lt' (by simp only [UInt64.size]; omega)] at h
  omega

/-- Every function of the checker passes `build_index`'s per-function check. -/
prog_all checkerProg_biChk : checkerProg (wsChk CTL biPa biPc biTree)

/-- **`build_index`'s write set.** -/
theorem checkerProg_biW : ∃ F, "build_index" ∈ F ∧ closedA checkerProg biA biC F = true :=
  ⟨biFns, List.mem_cons_self, closedW_of_all biTree.eq biPa_mem biPc_mem checkerProg_biChk⟩

end L.Checker
