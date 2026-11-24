module

public import ConAgua.Checker.PhaseBReads
public import ConAgua.Checker.CmpSeqView
public import ConAgua.Checker.CompareChain6
public import ConAgua.Checker.CmpSStash
import ConAgua.Checker.CmpSeqSpec
meta import ConAgua.Checker.PhaseBReads
import ConAgua.Checker.LoopProgTac
meta import ConAgua.Checker.LoopProgTac
meta import ConAgua.Checker.Prog
meta import ConAgua.Arena.Jobs
import all ConAgua.Arena.Abs1
import all ConAgua.Arena.BasisL
import all ConAgua.Arena.IndDeclConsts
import all ConAgua.Arena.IndStream
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
import all ConAgua.Arena.FreezeCmp
import all ConAgua.Checker.CmpSeqEntry
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
public import ConAgua.Arena.Globals

@[expose] public section

/-!
# The solution's stash survives the challenge's preparation (lane compare2, design (i))

`cmp_sstash()` copies what the solution's jobs read into `SDECL`, `SFIRSTS`, `SDLP`, `SCTL`
(arrays `224‥227`); mode `6`'s stages (`index_to_solution`, `cmp_restore`, `prepare_prelude`,
`side_records`, `solution_of`, `build_index`, with their call closure `c3StageFns`) store only into
the other word arrays (`checkerProg_ssW`: one kernel check per chunk of the program's functions,
`prog_all`, composed by `closedW_of_all`). So `CsStash m` (`Checker/CmpSeqView.lean`), true right
after the stash (`csStash_sstash`), holds of the frozen memory (`CsStash.frame`).
-/

open Std.WP
open scoped Lean.Order

namespace L.Checker

open L L.Arena L.Compiler

/-- The call closure of mode `6`'s stages in `checkerProg` (generated by `scripts/c3stage_fns.py`
from the call graph: 422 names; regenerate when the program changes). -/
def c3StageFns : List FnName :=
  ["app_count", "app_fill", "app_find", "app_push", "base_row_get", "base_row_set", "bb_go",
   "bb_memo", "bb_node", "block_caps_at", "block_caps_at_er_copy", "block_caps_at_er_copy_go",
   "block_caps_ctor_names", "block_caps_fin", "block_caps_head", "block_caps_one",
   "block_constants", "block_counts", "block_counts_head", "block_counts_pure", "block_ctors",
   "block_ctors_go", "block_ctors_groups", "block_formers", "block_formers_go", "block_groups",
   "block_groups_go", "block_groups_one", "block_is_rec", "block_is_rec_go", "block_is_rec_member",
   "block_member_counts", "block_member_counts_find", "block_member_counts_go", "block_rec",
   "block_recs", "block_shape_ctor_groups", "block_shape_ctors_of", "block_shape_declared",
   "block_shape_fin", "block_shape_large", "block_shape_lps", "block_shape_member_names",
   "block_shape_members_of", "block_shape_names_of", "block_shape_pack", "block_shape_recs_of",
   "block_shape_result_sort", "block_shape_seal", "block_shape_tail", "block_split",
   "block_split_ctors", "block_split_recs", "block_table", "block_tables", "bm_clear", "bm_find",
   "bm_put", "build_index", "builtin_axiom_name", "bvar_b", "bvar_find", "bvar_push", "ci_at_lps",
   "cmp_restore", "const_find", "const_push", "ctor_info_rec", "ctor_member", "ctors_lps_ok",
   "ctors_params_ok", "cv_at_lps", "decl_constants", "decl_constants_axiom", "decl_constants_ind",
   "decl_declares", "decl_declares_go", "decl_key", "decl_tables", "der_b", "der_bv", "dind_copy",
   "dlp_copy", "e_view", "ek_copy", "er_copy", "er_copy_er", "er_from_iw", "er_from_iw_go",
   "er_put_ci", "er_to_iw", "erec_alloc", "erec_ci", "erec_put", "expr_drop_vars",
   "expr_drop_vars_list", "fire_levels_at", "forall_find", "forall_push", "former_res_sort",
   "former_z", "formers_lps_ok", "fvar_find", "fvar_push", "get_app_args", "get_app_args_f",
   "get_app_fn", "get_app_fn_f", "hn_clear", "hn_find", "hn_put", "hoist_any", "hoist_app",
   "hoist_apply", "hoist_block_go", "hoist_bucket", "hoist_chain", "hoist_close_go",
   "hoist_closure", "hoist_deps", "hoist_deps_of", "hoist_emit", "hoist_forall", "hoist_fvar",
   "hoist_index_go", "hoist_ins", "hoist_ix", "hoist_lam", "hoist_let", "hoist_names",
   "hoist_names_go", "hoist_nat_op_ground", "hoist_note", "hoist_proj", "hoist_rules_go",
   "hoist_targets_go", "hoist_walk", "hoist_zero", "hs_clear", "hs_find", "hs_put", "i1l_app",
   "i1l_clear", "i1l_find", "i1l_forall", "i1l_go", "i1l_lam", "i1l_let", "i1l_proj", "i1l_put",
   "idx_add", "idx_consts", "idx_tables", "if_clear", "if_find", "if_put", "ilp_clear", "ilp_find",
   "ilp_put", "ilpl_clear", "ilpl_find", "ilpl_put", "ilpls_clear", "ilpls_find", "ilpls_put",
   "imax_find", "imax_push", "ind_block_to_erec", "ind_copy_go", "ind_info_rec", "ind_rec_copy",
   "index_freeze", "index_to_solution", "inst_app", "inst_entry", "inst_forall", "inst_go",
   "inst_lam", "inst_let", "inst_lp", "inst_lp_core", "inst_proj", "instantiate1_fast",
   "instantiate_lift_fast", "intern_app", "intern_bvar", "intern_const", "intern_forall",
   "intern_fvar", "intern_imax", "intern_lam", "intern_letE", "intern_lit", "intern_ls",
   "intern_ls_iw", "intern_max", "intern_nanon", "intern_nnum", "intern_nstr", "intern_param",
   "intern_proj", "intern_sort", "intern_succ", "intern_zero", "iw_alloc", "iw_copy", "iw_pool",
   "iw_reset", "keys_ok", "keys_push", "lam_find", "lam_push", "letE_find", "letE_push",
   "lf_clear", "lf_find", "lf_put", "lh_mk", "lh_push", "lift_app", "lift_entry", "lift_forall",
   "lift_go", "lift_lam", "lift_let", "lift_proj", "limbs_eq", "lit_find", "lit_from", "lit_hash",
   "lit_match", "lit_push", "lp_app", "lp_forall", "lp_fvar", "lp_go", "lp_lam", "lp_let",
   "lp_let_tail", "lp_lookup", "lp_proj", "lp_rb_let", "lp_substl", "lq_find", "lq_put", "ls_find",
   "ls_match", "ls_node", "ls_push", "lv_cases", "lv_cases_at", "lv_comb", "lv_dist1", "lv_dist2",
   "lv_eq", "lv_equiv", "lv_imax", "lv_imax_l", "lv_imax_r", "lv_intern", "lv_leq", "lv_node",
   "lv_rest", "lv_simp", "lv_sub_int", "lv_subsimp", "lv_subst", "lv_zero", "lvl_eq", "lvl_eq_c",
   "lvl_eq_rec", "ma_clear", "ma_find", "ma_put", "mates_get", "mates_insert", "mates_set",
   "max_find", "max_push", "mc_clear", "mc_find", "mc_put", "member_field_copy", "member_idx_at",
   "member_names_copy", "member_never_zero", "memo_get", "memo_push", "mentions_any_const",
   "mentions_any_go", "mentions_any_node", "mentions_const", "mentions_const_go", "mk_app",
   "mk_forall", "mk_lam", "mk_let", "mk_proj", "nanon_find", "nanon_push", "nat_div_mod_names",
   "nat_op_deps", "nat_op_names", "nat_op_pins", "nat_op_pins_a", "nat_op_pins_b", "nat_op_pins_c",
   "nat_op_record", "nnum_find", "nnum_push", "nstr_find", "nstr_match", "nstr_push", "param_find",
   "param_levels", "param_levels_go", "param_push", "pi_binders", "pi_doms_mention_any",
   "pi_result", "pin_at", "pin_word", "pool_copy", "pool_room", "prep_back", "prep_back_rec",
   "prep_copy", "prep_copy_rec", "prep_find", "prep_front", "prep_rest", "prepare_prelude",
   "proj_find", "proj_push", "quot_at", "quot_pin", "rci_block", "rci_block_to", "rci_caps",
   "rci_ci", "rci_cv", "rci_fresh", "rci_lvls_to", "rci_name_sl", "rci_names_to", "rci_rule",
   "rci_rules_to", "rci_slot", "read_block", "read_block_at", "rec2", "rec3", "rec5", "rec6",
   "rec7", "rec_fire", "rec_info_rec", "rec_target_of", "rom_basis_decls", "rom_ex_leaf_c",
   "rom_ex_one_c", "rom_ex_ref_c", "rom_ex_two_c", "rom_expr_c", "rom_exprs_to_c", "rom_level_c",
   "rom_levels_c", "rom_lit", "rom_lvls_go_c", "rom_name_c", "rom_put_c", "rom_u64_c",
   "rset_clear", "rset_find", "rset_put", "rules_at_lps_go", "rules_refire", "sd_copy_names",
   "sd_copy_prev", "sd_move_a", "sd_move_n", "sd_move_s", "side_record", "side_records",
   "sl_append", "sl_cons", "sl_contains", "sl_eq", "sl_find", "sl_get", "sl_getd", "sl_memo",
   "sl_new1", "sl_snoc", "sle_go", "slice_has", "sls_go", "sls_memo", "solution_of", "sort_find",
   "sort_push", "spn_ls", "spn_pool", "spn_to_er", "spn_to_iw", "stk_pool", "stk_push",
   "str_lit_names", "strip_pis", "struct_proj_arg_p", "struct_proj_bodies",
   "struct_proj_bodies_go", "struct_proj_ps", "struct_ps_at", "struct_ps_at_go", "succ_find",
   "succ_push", "tbl_base_get", "tbl_base_set", "view_ls", "zero_find", "zero_push"]

names_tree c3StageTree : c3StageFns

/-- The arrays the stages may store into: every word array but the stash `224‥227`. -/
def ssA : List TieredArray := checkerWordArrays.filter fun b => !(decide (224 ≤ b.arr) && decide (b.arr ≤ 227))

/-- `ssA` as a test. -/
def ssPa (b : TieredArray) : Bool := checkerWordArrays.contains b && !(decide (224 ≤ b.arr) && decide (b.arr ≤ 227))

/-- The `CTL` words the stages may store into: those below `1024`. -/
def ssC : List Word := (List.range 1024).map UInt64.ofNat

def ssPc (x : Word) : Bool := decide (x.toNat < 1024)

theorem ssPa_mem (b : TieredArray) (h : ssPa b = true) : b ∈ ssA := by
  simp only [ssPa, Bool.and_eq_true, List.contains_iff_mem] at h
  exact List.mem_filter.mpr ⟨h.1, h.2⟩

theorem ssPc_mem (x : Word) (h : ssPc x = true) : x ∈ ssC := by
  simp only [ssPc, decide_eq_true_eq] at h
  exact List.mem_map.mpr ⟨x.toNat, List.mem_range.mpr h, by simp⟩

/-- Every function of the checker passes the stages' per-function check. -/
prog_all checkerProg_ssChk : checkerProg (wsChk CTL ssPa ssPc c3StageTree)

/-- **Mode `6`'s stages miss the stash arrays.** -/
theorem checkerProg_ssW : closedA checkerProg ssA ssC c3StageFns = true :=
  closedW_of_all c3StageTree.eq ssPa_mem ssPc_mem checkerProg_ssChk

theorem not_mem_ssA {b : TieredArray} (h1 : 224 ≤ b.arr) (h2 : b.arr ≤ 227) : b ∉ ssA := fun hm => by
  have := (List.mem_filter.mp hm).2
  simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not] at this
  omega

/-- `CsStash m` reads only the stash arrays of its second memory. -/
theorem CsStash.of_eq {m x x' : Mem} (h : CsStash m x) (e1 : x'.arr64 SDECL = x.arr64 SDECL)
    (e2 : x'.arr64 SFIRSTS = x.arr64 SFIRSTS) (e3 : x'.arr64 SDLP = x.arr64 SDLP)
    (e4 : x'.arr64 SCTL = x.arr64 SCTL) : CsStash m x' :=
  ⟨fun j hj => by rw [e1]; exact h.decl j hj, fun j hj => by rw [e2]; exact h.firsts j hj,
    fun j hj => by rw [e3]; exact h.dlp j hj, fun x hx => by rw [e4]; exact h.frz x hx⟩

/-- **A frame of the stages keeps the stash.** -/
theorem CsStash.frame {m x x' : Mem} (h : CsStash m x) (hf : MemFrame ssA ssC x x') : CsStash m x' :=
  h.of_eq (hf.arr _ (not_mem_ssA (by decide) (by decide)) (by decide))
    (hf.arr _ (not_mem_ssA (by decide) (by decide)) (by decide))
    (hf.arr _ (not_mem_ssA (by decide) (by decide)) (by decide))
    (hf.arr _ (not_mem_ssA (by decide) (by decide)) (by decide))

theorem CsStash.setCtl {m x : Mem} (h : CsStash m x) (c v : Word) : CsStash m (x.set64 CTL c v) :=
  h.of_eq (Mem.arr64_set64_ne _ _ _ _ _ (by decide)) (Mem.arr64_set64_ne _ _ _ _ _ (by decide))
    (Mem.arr64_set64_ne _ _ _ _ _ (by decide)) (Mem.arr64_set64_ne _ _ _ _ _ (by decide))

end L.Checker
