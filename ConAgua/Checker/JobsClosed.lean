module

public import ConAgua.Checker.Prog
public import ConAgua.Arena.Jobs
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

@[expose] public section

/-!
# The jobs' write sets at the checker's program

`JobProg`'s `apW` and `cdW` (`Arena/Jobs.lean`): `and_pin_ok` and `check_decl`, with their
call closures (`apFns`, 143 functions; `cdFns`, 1328), store only where `apA`/`apC` and
`cdA`/`cdC` allow. As `Checker/CoreErec.lean`: the function sets as name trees, the store sets as
predicates, one kernel check per chunk of the program's functions (`prog_all`), composed by
`closedW_of_all`.
-/

namespace L.Checker

open L.Arena L.Compiler

/-- `and_pin_ok`'s call closure in the checker's program. -/
def apFns : List FnName :=
  ["and_pin_ok",
    "and_block_named", "app_find", "app_push", "b_eq", "bvar_find", "bvar_push", "canon_ctx",
    "canon_eq_list", "canon_expr_eq", "canon_level_eq", "canon_level_list_eq", "canon_levels_eq",
    "canon_name_map", "canon_names", "canon_names_go", "canon_rules_eq", "ci_canon_defn",
    "ci_canon_eq", "ci_canon_rec", "const_find", "const_push", "cv_canon_eq", "cv_lps", "der_b",
    "dind_copy", "e_view", "er_copy", "er_sl_at", "er_sl_eq", "er_to_iw", "erec_alloc", "erec_put",
    "forall_find", "forall_push", "fvar_find", "fvar_push", "hint_eq", "imax_find", "imax_push",
    "ind_block_to_erec", "ind_copy_go", "ind_rec_copy", "intern_app", "intern_bvar", "intern_const",
    "intern_forall", "intern_fvar", "intern_imax", "intern_lam", "intern_letE", "intern_lit",
    "intern_ls", "intern_max", "intern_nanon", "intern_nnum", "intern_nstr", "intern_param",
    "intern_proj", "intern_sort", "intern_succ", "intern_zero", "iw_alloc", "iw_copy", "lam_find",
    "lam_push", "letE_find", "letE_push", "limbs_eq", "lit_find", "lit_hash", "lit_match",
    "lit_push", "ls_find", "ls_match", "ls_node", "ls_push", "lv_node", "max_find", "max_push",
    "memo_get", "memo_push", "mk_app", "mk_forall", "mk_lam", "mk_let", "mk_proj", "nanon_find",
    "nanon_push", "nnum_find", "nnum_push", "nstr_find", "nstr_match", "nstr_push", "param_find",
    "param_push", "pool_copy", "proj_find", "proj_push", "rci_block", "rci_block_to", "rci_caps",
    "rci_ci", "rci_cv", "rci_fresh", "rci_lvls_to", "rci_name_sl", "rci_names_to", "rci_rule",
    "rci_rules_to", "rci_slot", "rom_and_pin", "rom_ex_leaf_c", "rom_ex_one_c", "rom_ex_ref_c",
    "rom_ex_two_c", "rom_expr_c", "rom_exprs_to_c", "rom_level_c", "rom_levels_c", "rom_lit",
    "rom_lvls_go_c", "rom_name_c", "rom_put_c", "rom_u64_c", "rset_clear", "rset_find", "rset_put",
    "rule_eq_a", "rule_eq_b", "rule_eq_but_rhs", "sl_cons", "sl_find", "sl_getd", "sort_find",
    "sort_push", "stk_pool", "stk_push", "succ_find", "succ_push", "view_ls", "zero_find",
    "zero_push"]

/-- `check_decl`'s call closure in the checker's program. -/
def cdFns : List FnName :=
  ["check_decl", "close_lams_go", "close_telescope_go", "formers_lps_ok", "ctors_params_ok", "ctors_lps_ok", "check_decl_kind", "basis_names_ok", "basis_names_error", "basis_name_unreserved", "block_names_unreserved", "nat_ind_at_cv", "nat_zero_at_cv", "nat_succ_at_cv",
    "ab_clear", "ab_find", "ab_fvb", "ab_node", "ab_put", "abs_app", "abs_entry", "abs_forall",
    "abs_go", "abs_lam", "abs_let", "abs_proj", "abstract1_fast", "abstract_prefix",
    "abstract_prefix_list", "all_level_params_defined", "alpd_go", "alpd_ls",
    "and_rescue_slots", "apd_clear", "apd_find", "apd_put", "app_count", "app_count_at", "app_fill",
    "app_fill_n", "app_find", "app_hole", "app_push", "ar_app", "ar_entry", "ar_forall", "ar_go",
    "ar_lam", "ar_let", "ar_node", "ar_proj", "aux_rule_fire", "b_eq",
    "base_row_get", "basis_name_hit", "basis_name_hit_go", "bb_go", "bb_memo",
    "bb_node", "beta_peel", "binder_dom", "block_caps_at", "member_never_zero", "block_caps_at_er_copy",
    "block_caps_at_er_copy_go", "block_caps_ctor_names", "block_caps_fin", "block_caps_head",
    "block_caps_one", "block_counts", "block_counts_head", "block_counts_pure", "block_groups",
    "block_groups_go", "block_groups_one", "block_is_rec", "block_is_rec_go", "block_is_rec_member",
    "block_large_elim_allowed", "block_link_ok_at", "block_links_ok", "block_links_ok_go",
    "block_member_counts", "block_member_counts_find", "block_member_counts_go", "block_names_eq",
    "block_nest_ctx", "block_nested_bit", "block_nested_bit_go", "block_rec", "block_rec_got",
    "block_rec_infos_tf", "block_rec_lps_ok", "block_rec_lps_ok_go", "block_rec_lps_one",
    "block_rec_name_set_ok", "block_rec_names_unreserved", "block_rec_split_own_aux",
    "block_rec_want", "block_rec_want_aux_names", "block_recs", "read_block",
    "block_shape_all_ctors", "block_shape_all_ctors_go", "read_block_at",
    "block_shape_ctors_copy", "block_shape_ctors_of", "block_shape_declared", "block_shape_fin",
    "block_shape_formers", "block_shape_large", "block_shape_lps", "block_shape_major_idx_at",
    "block_shape_member_ctors", "block_shape_member_names", "block_shape_members_of",
    "block_shape_n_idxs", "block_shape_names_of", "block_shape_nest_ctx", "block_shape_num_ctors",
    "block_shape_pack", "block_shape_recs_of", "block_shape_result_sort",
    "block_shape_rule_prefix_at", "block_shape_seal", "block_shape_tail",
    "block_shape_with_members", "block_shape_with_sort", "block_split", "block_split_ctors",
    "block_split_recs", "block_table", "block_tables", "bm_clear", "bm_find", "bm_put",
    "bool_ctor_ok", "bool_ctor_typed", "bvar_b", "bvar_find", "bvar_push",
    "canon_name_map", "caps_eq", "caps_eq_a", "caps_eq_b", "caps_eq_c", "cert_ctx", "cert_ctx_main",
    "cert_ctx_pins", "cert_div_mod", "cert_div_mod_eqs", "cert_div_mod_guards", "cert_eq",
    "cert_gcd", "cert_guard", "cert_halves", "cert_land", "cert_lor", "cert_lor_rhs",
    "cert_rec_rhs", "cert_shift_left", "cert_shift_right", "cert_two_eqs", "cert_xor",
    "cert_xor_rhs", "certify_nat_eqs", "char_of_nat_ty_ok", "char_ty_ok", "check_abs_ctor_sorts",
    "check_abs_ctor_sorts_all", "check_abs_ctor_sorts_one", "check_block",
    "check_block_agree", "check_block_agree_one", "check_block_classes",
    "check_block_classes_count", "check_block_classes_keys", "check_block_classes_one_per_member",
    "check_block_ctors", "check_block_doms_at", "check_block_idx_sorts", "check_block_inds",
    "check_block_names", "check_block_pass", "check_block_pass_rec", "check_block_positivity",
    "check_block_positivity_init", "check_block_rec", "check_block_tables", "check_block_tail",
    "check_block_tail_stream", "check_block_tele", "check_block_teles", "check_constant_val",
    "check_decl_axiom", "check_decl_defn", "check_decl_opaque", "check_decl_quot", "check_decl_thm",
    "check_defn_val", "check_div_mod_certs", "check_div_mod_pin", "check_div_mod_pin_at",
    "check_div_mod_pin_at_fe2", "check_div_mod_pin_loop", "check_div_mod_pin_value",
    "check_field_sort_bound", "check_guard_rows", "check_ind_decl", "check_opaque_val",
    "check_proj_guard", "check_quot_record", "check_reduce_pin", "check_reduce_pin_pre",
    "check_spine_at", "check_struct_doms_at",
    "check_struct_field_sorts_i", "check_struct_proj_table", "check_struct_proj_table_scoped",
    "check_structural_nat_pin", "check_structural_nat_pin_at_fe2", "check_sum_ctor",
    "check_sum_ctor_tail", "check_sum_ctors", "check_sum_tele", "check_thm_val", "check_type_pins",
    "ci_at_lps", "ci_eq", "ci_eq_rest", "ci_to_cv", "class_const_ok", "class_const_ok_header",
    "class_const_ok_lit", "class_ctor_of", "class_ctor_of_nfs", "class_ctors_of", "class_fe_r",
    "class_fe_r_go", "class_fe_r_rec", "class_fields_agree", "class_fields_of",
    "class_fields_of_go", "class_fields_of_hits", "class_former_ty", "class_gen_ih_parts",
    "class_gen_major", "class_gen_major_ci", "class_gen_major_open", "class_gen_major_tail",
    "class_gen_minor_ci", "class_gen_minor_ty", "class_gen_minor_ty_body",
    "class_gen_minor_ty_close", "class_gen_minor_ty_concl", "class_gen_minor_ty_concl2",
    "class_gen_minor_ty_ih1", "class_gen_minor_ty_ih1_close", "class_gen_minor_ty_ih1_tail",
    "class_gen_minor_ty_ihs_go", "class_gen_mot_var", "class_gen_motive_ty",
    "class_gen_prefix_binders", "class_gen_prefix_binders_find_ctor",
    "class_gen_prefix_binders_find_ctor_go", "class_gen_prefix_binders_slot_minor",
    "class_gen_prefix_binders_slot_motive", "class_gen_prefix_binders_slots_go", "class_gen_rec_ty",
    "class_gen_rec_ty_tail", "class_gen_rule", "class_gen_rule_body", "class_gen_rule_call1",
    "class_gen_rule_call1_close", "class_gen_rule_call1_tail", "class_gen_rule_calls_go",
    "class_gen_rule_close", "class_gen_rule_find_slot", "class_gen_rule_find_slot_go",
    "class_gen_rule_pvars_go", "class_gen_slot_var", "class_key_canon", "class_key_canon_go",
    "class_key_of", "class_key_of_closed", "class_leaf_at", "class_majors", "class_minor_slot",
    "class_minor_slot_go", "class_n_pc_of", "class_nodes_agree", "class_of_motive_var",
    "class_read", "class_read_classes", "class_read_finish", "class_read_minor",
    "class_read_minor_finish", "class_read_minor_ih1", "class_read_minor_ihs",
    "class_read_minor_tail", "class_read_mot_pos", "class_read_motive_slot", "class_read_n_slots",
    "class_read_rec_cls", "class_read_slot", "class_read_slot_motive", "class_read_slots",
    "class_read_slots_next", "class_read_slots_snoc", "class_rec_of", "class_rec_ty_check",
    "class_rec_ty_ok", "class_rec_ty_ok_guards", "class_rec_tys_ok", "class_recs_rules_ok",
    "class_recs_rules_ok_go", "class_rule_check", "class_rule_check_domains",
    "class_rule_check_guards", "class_rule_ok", "class_rules_ok", "class_rules_ok_one",
    "class_seeds", "class_slot_is_minor", "class_stream_recs", "classes_ctors", "classes_nfs",
    "close_lams", "close_telescope", "cons_block_ctors", "block_shape_ctor_groups", "cons_block_inds", "cons_block_recs_temp",
    "cons_sum_ctors", "const_e", "const_find", "const_named", "const_push",
    "const_ty_at", "const_val_at", "consts_resolve_all", "consts_resolve_ffast", "cr_leaf",
    "cr_lit_pins", "crf_go", "crm_clear", "crm_find", "crm_put", "ct_clear", "ct_find", "ct_put",
    "ctl_get", "ctor_family", "iota_no_cert", "rec_fire_level_count", "ctor_info_rec", "ctor_member", "ctors_have_name", "cv_at_lps",
    "cv_clear", "cv_eq", "cv_find", "cv_lps", "cv_new", "cv_put", "de_clear", "de_find", "de_put",
    "dec_len", "declined_at_definition", "defeq", "defeq_arg", "defeq_binders", "defeq_domain",
    "defeq_binders_inner", "binder_pair", "quick_binders", "defeq_body", "defeq_lazy",
    "ctor_head_against", "ctor_target", "ctor_target_for",
    "defeq_e", "defeq_list", "defeq_list_rev", "defeq_lst",
    "defeq_no_fvars", "defeq_offset", "defeq_proj_pair", "defeq_spine",
    "defeq_spine2", "defeq_stuck", "defeq_tail", "delta_quick", "depth", "depth_go", "depth_node",
    "der_b", "der_bv", "dind_copy", "div_add", "div_mod_cert_applied", "div_mod_cert_guard",
    "div_mod_cert_proofs", "div_mod_cert_stmts", "div_mod_cert_stmts_at", "div_mod_certs_guard",
    "div_mod_certs_guard_go", "div_mod_decl_pin", "div_mod_env_guard", "div_mod_pin_guard",
    "div_mod_slot", "div_mod_type_pins", "div_2by1", "div_kstep", "div_mod1", "div_modk", "div_norm", "div_recip", "div_submul", "dlp_copy", "dp_clear",
    "dp_find", "dp_put", "e_view", "ek_copy", "ensure_sort", "ensure_sort_core", "env_find",
    "env_pop_temp", "env_push", "lit_name_at", "lits_stored", "env_set_flags", "env_push_table", "env_row_get", "env_row_set", "eq_at1",
    "eq_stored", "er_copy", "er_copy_er", "er_from_iw", "er_from_iw_go", "er_put_ci", "er_sl_at",
    "er_sl_eq", "er_slice_eq", "er_to_iw", "erase_each", "erase_fvar_tys", "erec_alloc", "erec_ci",
    "erec_push", "erec_put", "eta_cert", "eta_cert_body", "eta_cert_ty", "eta_ctor_shape",
    "eta_fab_args", "eta_projs", "eta_rescue_table", "expr_drop_vars", "expr_drop_vars_list",
    "expr_get_d", "expr_view_ok", "fab_scope_ok", "family_key_check", "family_key_checks",
    -- the ι reading rule (ronsync8)
    "pi_tele", "motive_level", "iota_frame", "is_minor_at", "minors_from", "iota_read_major", "iota_rec_of", "lift_field_doms", "lift_idx_args", "iota_parts_of_at", "ctor_levels_at", "iota_bvars", "iota_params_at", "iota_parts_at_body", "iota_parts_at", "expr_lvl_eq", "name_opt_param", "name_auto_param", "name_out_param", "name_semi_out_param", "name_missing", "ann_witness", "ann_ident_body", "ann_ident_val", "ann_ident", "ann_eq", "list_lvl_eq", "list_ann_eq", "params_ann_eq", "iota_parts_rel", "rule_reads", "rules_read", "rec_reads", "recs_read", "block_reads_at", "family_telescope",
    "field_doms_resolve", "find_pinned", "find_pinned_cv", "find_proj", "find_rule", "find_table",
    "fire_levels_at", "fl_clear", "fl_find", "fl_go", "fl_node", "fl_put", "flush_caches",
    "fm_clear", "fm_find", "fm_put", "forall_find", "forall_push", "former_def_headed",
    "former_never_zero", "former_never_zero_at", "family_never_zero_at", "former_res_sort", "former_sort_loop", "former_z",
    "fr_go", "fr_memo", "fr_node", "fv_map_at", "fvar_b", "fvar_find", "fvar_head", "fvar_push",
    "fvar_type_d", "fvar_type_ds", "gcd_step", "gen_rec_check", "gen_rec_check_any_no_member",
    "gen_rec_check_former_tys", "gen_rec_check_former_tys_c", "gen_rec_check_minor_ok",
    "gen_rec_check_pop_all", "gen_rec_check_prep", "generated_fire", "generated_rule_nested",
    "generated_rules", "generated_rules_remap", "get_app_args", "get_app_args_f", "get_app_fn",
    "get_app_fn_f", "get_app_spine", "ground_guards", "has_fvar", "has_fvar_fast",
    "has_loose_b_var_b_fast", "has_loose_b_var_b_go", "has_loose_b_var_b_ins", "has_loose_bvar_in", "has_loose_bvar_in_go", "has_str_lit_go",
    "hb_clear", "hb_find", "hb_put", "head_and_args", "head_hint", "head_is_proj",
    "head_proof_const", "head_proof_proj", "head_proof_pw", "head_type_const", "head_type_pw",
    "head_type_res", "hint_eq", "hint_lt", "i1l_app", "i1l_clear", "i1l_find", "i1l_forall",
    "i1l_go", "i1l_lam", "i1l_let", "i1l_proj", "i1l_put", "idx_args_resolve", "if_clear",
    "if_find", "if_put", "ifenv_push_all", "ifenv_push_delta", "ifenv_push_tables", "ik_copy",
    "il_app", "il_bvar", "il_forall", "il_go", "il_lam", "il_let", "il_proj", "ilg_app",
    "ilg_forall", "ilg_go", "ilg_lam", "ilg_let", "ilg_proj", "ilm_clear", "ilm_find", "ilm_fit",
    "ilm_put", "ilp_clear", "ilp_find", "ilp_put", "ilpl_clear", "ilpl_find", "ilpl_put",
    "ilpls_clear", "ilpls_find", "ilpls_put", "imax_find", "imax_push", "in_clear", "in_find",
    "in_put", "ind_block_to_erec", "ind_copy_go", "ind_info_rec", "ind_params_ok", "ind_rec_copy",
    "infer", "infer_app", "infer_app_io", "infer_body", "infer_body_io", "infer_const",
    "infer_forall", "infer_forall_io", "infer_io", "infer_lam", "infer_lam_io", "infer_lam_result",
    "infer_lams", "infer_lams_leaf", "infer_let", "infer_lit", "infer_pis", "infer_pis_leaf",
    "infer_proj", "infer_proj_at", "infer_spine", "infer_spine_arg", "infer_spine_io",
    "infer_type_core", "inst1", "inst_app", "inst_entry", "inst_forall", "inst_go", "inst_lam",
    "inst_let", "inst_list", "inst_lp", "inst_lp_core", "inst_lp_fast",
    "inst_pis_with", "inst_proj", "inst_spine", "inst_spine_pins", "install_basis_decl",
    "instantiate1_fast", "instantiate_lift_fast", "intern_app",
    "intern_bvar", "intern_const", "intern_forall", "intern_fvar", "intern_imax", "intern_lam",
    "intern_letE", "intern_lit", "intern_ls", "intern_ls_iw", "intern_max", "intern_nanon",
    "intern_nnum", "intern_nstr", "intern_param", "intern_proj", "intern_sort", "intern_succ",
    "intern_zero", "io_clear", "io_find", "io_neutral", "io_put", "iota_case3_at",
    "iota_certs_full", "iota_certs_full_aux", "iota_certs_full_check", "iota_certs_full_flush",
    "iota_certs_full_forall", "iota_certs_full_parts", "iota_index_ok", "iota_rec_at", "iota_rec_cmp", "iota_rec_fam", "iota_rec_fire", "iota_rec_fire2", "eidx_copy_upto", "iota_rec_major", "iota_rec_vck", "is_def_eq_core",
    "is_eager_reduce", "is_nat_zero", "is_proof_fast", "is_str_lit", "iw_alloc", "iw_copy",
    "iw_pool", "iw_to_spn", "keys_ok", "keys_push", "keys_push_iw", "lam_find", "lam_proj", "lam_push", "lazy_delta_proj_reduction",
    "lazy_delta_reduction", "lazy_delta_step", "lazy_fold_ok", "lazy_iter", "lazy_nat", "ldpr_exit",
    "lds_both", "lds_left", "lds_right", "lds_same", "lds_unfold2", "leaf_guard", "leaf_mem",
    "letE_find", "letE_push", "lf_clear", "lf_find", "lf_put", "lh_contains", "lh_mk", "lh_push",
    "lift_app", "lift_entry", "lift_forall", "lift_go", "lift_lam", "lift_let", "lift_proj",
    "limbs_eq", "list_cons_ty_ok", "list_nil_ty_ok", "list_ty_ok", "lit_eq", "lit_find",
    "lit_guard_has", "lit_hash", "lit_major_to_ctor", "lit_match", "lit_push", "lit_shape_ok",
    "lit_to_ctor_if_nat", "loose_bvars_bounded_fast", "lp_app", "lp_forall", "lp_fvar", "lp_go",
    "lp_lam", "lp_let", "lp_let_tail", "lp_lookup", "lp_proj", "lp_rb_let", "lp_substl", "lq_clear",
    "lq_find", "lq_put", "ls_find", "ls_match", "ls_node", "ls_push", "lsb_clear", "lsb_find",
    "lsb_go", "lsb_node", "lsb_put", "lsq_clear", "lsq_find", "lsq_put", "lv_always_zero", "lv_apd",
    "lv_cases", "lv_cases_at", "lv_comb", "lv_dist1", "lv_dist2", "lv_eq", "lv_equiv", "lv_equivs",
    "lv_imax", "lv_imax_l", "lv_imax_r", "lv_intern", "lv_leq", "lv_leq_top", "lv_lookup", "lv_mem",
    "lv_never", "lv_node", "lv_nz", "lv_rest", "lv_simp", "lv_spw", "lv_sub_int", "lv_subsimp",
    "lv_subst", "lv_zero", "lv_zero_where_zero", "lvl_eq", "lvl_eq_c", "lvl_eq_fueled",
    "lvl_eq_rec", "lvl_eq_true", "lvls_eq", "lvls_eq_c", "lvls_eq_rec", "m2c_and", "m2c_and2",
    "m2c_arms", "m2c_check", "m2c_const_view", "m2c_ctor", "m2c_eta", "m2c_eta2", "m2c_head",
    "m2c_k", "m2c_k2", "m2c_pre", "ma_clear", "ma_find", "ma_put", "mul_row", "sub_row", "mul_zeros", "kara_sum", "kara_prods", "kara_mid", "mul_win", "major_to_ctor", "major_to_ctor_rescue", "ctor_view", "prepare_major_whnf", "is_nat_succ_app",
    "matches_pin", "max_find", "max_push", "member_ctors_copy", "member_field_copy",
    "member_idx_at", "member_names_copy", "memo_get", "memo_push", "mentions_any_const",
    "mentions_any_go", "mentions_any_node", "mk_app", "mk_app_n", "mk_app_n_f", "mk_app_n_from",
    "mk_forall", "mk_lam", "mk_let", "mk_proj", "mk_target_major", "n_idxs_copy", "name_rec",
    "name_rec_i", "nanon_find", "nanon_push", "nat_add", "add_n", "add_1", "nat_add_lit", "nat_ap1", "nat_ap2",
    "nat_beq_lit", "nat_bin_op_of_name", "nat_bin_op_result", "nat_ble_lit", "nat_cmp", "nat_div_lit", "nat_div_mod_names",
    "nat_divmod", "nat_eq_be", "nat_eq_bl", "nat_eq_ctx", "nat_eq_disp", "nat_eq_list2",
    "nat_eq_list3", "nat_eq_list4", "nat_eq_mu", "nat_eq_po", "nat_eq_pr", "nat_eq_un", "nat_gcd",
    "nat_gcd_lit", "nat_ind_ok", "nat_land", "and_n", "nat_land_lit", "nat_lit_supported", "nat_lit_to_ctor", "nat_lor", "or_n", "copy_n", "nat_lor_lit", "nat_mod_lit", "nat_mul",
    "nat_mul_lit", "nat_one", "nat_op_bool_ctors", "nat_op_cod", "nat_op_deps",
    "nat_op_deps_stored", "nat_op_equations", "nat_op_guard", "nat_op_name",
    "nat_op_names", "nat_op_pins", "nat_op_pins_a", "nat_op_pins_b", "nat_op_pins_c",
    "nat_op_stored_ok", "nat_op_ty_pinned", "nat_pow",
    "nat_pow_lit", "nat_pred", "nat_pred_lit", "nat_shl", "shl_n", "zero_n", "nat_shl_lit", "nat_shr", "shr_n", "nat_shr_lit",
    "limb_push", "lit_nat_sized", "nat_size_refused", "pow_nat", "pow_refused", "shift_left_refused", "size_bytes",
    "nat_sub", "sub_n", "sub_1", "nat_sub_lit", "nat_succ_lit", "nat_succ_ok", "nat_trim", "nat_var", "nat_xor", "xor_n", "copy_n",
    "nat_xor_lit", "nat_zero_ok", "nest_accept_group", "nest_block_of", "nest_canon_crest",
    "nest_canon_sub", "nest_cont", "nest_cont_checks", "nest_cont_key", "nest_cont_new",
    "nest_cont_new_active", "nest_cont_new_finish", "nest_cont_params_closed", "nest_container",
    "nest_container_ctors", "nest_container_ctors_go", "nest_crest", "nest_ctor_entry",
    "nest_ctor_entry_strip", "nest_ctor_nf", "nest_ctors", "nest_ctors_crest", "nest_ctors_one",
    "nest_ctors_res_ok", "nest_ctors_u4", "nest_ctors_walk", "nest_ctx_hi_at",
    "nest_ctx_root_holes", "nest_ctx_root_holes_go", "nest_ds_closed", "nest_ds_closed_go",
    "nest_field_kind_flat", "nest_fields", "nest_frame", "nest_frame_grp", "nest_frame_holes",
    "nest_frame_mates", "nest_frame_mates_go", "nest_group_ctors", "nest_grow_group",
    "nest_hole_at", "nest_hole_img", "nest_hole_img_ds", "nest_hole_img_ds_go",
    "nest_hole_img_frame", "nest_hole_img_root", "nest_holes", "nest_holes_go", "nest_inst_type",
    "nest_inst_type_ty", "nest_key_eq", "nest_key_map", "nest_keys_contains", "nest_kinds_flat",
    "nest_kinds_flat_inner", "nest_kinds_flat_mid", "nest_occ", "nest_occ_any", "nest_occ_go",
    "nest_occ_node", "nest_out_kinds", "nest_phs", "nest_phs_go", "nest_pos", "nest_pos_app",
    "nest_pos_bind", "nest_pos_fvar", "nest_pos_hole_kind", "nest_res_head", "nest_root",
    "nest_root_canon", "nest_seed_of", "nest_seed_of_go", "nest_seeds", "nest_seeds_fuel",
    "nest_uniform", "nest_uniform_cs", "nest_uniform_ok", "nest_walk_stack", "nnum_find",
    "nnum_push", "no_clear", "no_find", "no_put", "not_proof_fast", "nstr_find", "nstr_match",
    "nstr_push", "num_ctors_of", "of_reduce_ax_ok", "of_reduce_op", "of_reduce_pin_a", "opa_go",
    "open_pis_at_fvars", "open_pis_at_fvars_f", "opf_go", "param_find", "param_levels",
    "param_levels_go", "param_push", "peel_pis", "peel_pis_w", "ph_app", "pi_binders", "pi_doms_mention_any", "pi_doms_occ",
    "pi_residual", "pi_result", "pi_result_f", "pi_sort_tele_len", "pin_agrees", "pin_at",
    "pin_copies_ok", "pin_copy_ok", "pin_found", "pin_link_go", "pin_link_ok", "pin_list_ok",
    "pin_range_has", "pin_word", "pool_copy", "pool_room", "prepare_major", "proj_cert",
    "proj_find", "proj_guard_fast", "proj_guard_row", "proj_guard_rows", "proj_guard_rows_at", "proj_guard_rows_go", "proj_guard_sort", "proj_lit_to_ctor",
    "proj_push", "proj_type_at", "proof_irrel", "proof_irrel_half", "proof_pw", "prop_irrel",
    "ptr_list_names", "ptr_names_copy", "quick_defeq", "quick_sort",
    "quot_at", "quot_pin", "quot_pin_hit", "quot_preds_ok", "ra_clear", "ra_find", "ra_put",
    "raw_nat_lit", "raw_table", "rci_block", "rci_block_to", "rci_caps", "rci_ci", "rci_cv",
    "rci_fresh", "rci_lvls_to", "rci_name_sl", "rci_names_to", "rci_rule", "rci_rules_to",
    "rci_slot", "rec2", "rec3", "rec4", "rec5", "rec6", "rec7", "rec_doms_at", "rec_fire",
    "rec_fire_args", "rec_fire_levels", "rec_info_rec", "rec_k_expected", "rec_target_of",
    "rec_ty_check", "rec_ty_opened", "reduce_cert_var", "reduce_decl_pin", "reduce_elem_ok",
    "reduce_member", "reduce_members", "reduce_nat", "reduce_nat_ap", "reduce_nat_head",
    "reduce_nat_k", "reduce_nat_op", "reduce_nat_succ", "reduce_op_cv_a",
    "reduce_pin_guard", "reduce_proj_arg", "reduce_proj_core", "reduce_proj_fire",
    "reduce_proj_head", "reduce_stored_ok", "reduced_former", "replace_apps", "replace_apps_go",
    "replace_apps_node", "replace_fvars", "replace_fvars_go", "replace_fvars_node",
    "reserved_contains", "reserved_from", "reserved_rec_bool",
    "reserved_rec_name", "residual_pw", "rf_bank_enter", "rf_bank_leave", "rf_clear", "rf_find",
    "rf_put", "rom_basis_decls", "rom_ci", "rom_cv", "rom_ex_leaf_c", "rom_ex_one_c",
    "rom_ex_ref_c", "rom_ex_two_c", "rom_expr_c", "rom_expr_pin", "rom_exprs_to_c", "rom_level_c",
    "rom_levels_c", "rom_lit", "rom_lvls_go_c", "rom_name_c", "rom_pin_sets", "rom_put_c",
    "rom_u64_c", "rr_clear", "rr_find", "rr_put", "rset_clear", "rset_find", "rset_put",
    "rule_agree", "rule_copy", "rule_eq_a", "rule_eq_b", "rule_eq_but_rhs", "rule_body_at", "lam_body",
    "rules_at_lps_go", "rules_eq", "rules_link_ok", "rules_refire", "rules_to_erec",
    "rules_to_erec_go", "same_const_heads", "sl_all_in", "sl_append", "sl_cons", "sl_contains",
    "sl_eq", "sl_find", "sl_get", "sl_getd", "sl_memo", "sl_new1", "sl_nodup", "sl_set_eq",
    "sl_snoc", "sle_go", "slp_go", "sls_go", "sls_memo", "sort_find", "sort_push", "spine_cmp",
    "spine_head", "spn_get", "spn_ls", "spn_pool", "spn_push", "spn_to_er", "spn_to_iw",
    "stack_cover", "std_ax_family", "std_axiom_ok", "stk_pool", "stk_push", "stmt1",
    "str_cons_spine", "str_ctor_pre", "str_cv", "str_lit_ctor", "str_ls1",
    "str_param_sort", "str_utf8_char", "stream_closed", "stream_k_check", "stream_nested_bvars",
    "stream_nested_dom", "stream_nested_ok", "stream_nested_pins", "stream_rec_check",
    "stream_rec_compare", "stream_recs_check", "stream_rules_check", "rule_binds",
    "stream_rules_shape",
    "string_of_list_ty_ok", "string_ty_ok", "strip_lams", "strip_pis", "struct_ctor_resid_ok",
    "struct_elim_level", "struct_eta_cert", "struct_eta_cert_go", "struct_eta_cert_tail",
    "struct_eta_cert_with", "struct_eta_cert_wtb", "struct_proj_arg_p", "struct_proj_bodies",
    "struct_proj_bodies_go", "struct_proj_ps", "struct_ps_at", "struct_ps_at_go",
    "struct_unit_cert", "eta_ctor_partial_fam", "eta_ctor_partial", "struct_eta_full_at", "struct_eta_full", "struct_eta_expand", "struct_eta_cert_partial", "is_prop_type", "unit_like_fields", "unit_like_shape_at", "unit_like_shape", "unit_like_struct", "unit_like_loop", "struct_unit_tail", "struct_used_later", "stuck_app",
    "stuck_app_cong", "stuck_irrel", "stuck_rest", "stuck_str", "subst_const0",
    "subst_const0_list", "subst_const0_pairs", "subst_const_all", "subst_pw_at", "succ_find",
    "succ_push", "sum_rules", "sum_rules_go", "ta_clear", "ta_find", "ta_put", "target_abs",
    "target_abs_const", "target_abs_go", "target_abs_node", "target_canon_params",
    "target_class_match", "target_ctor_at", "target_ctors_of", "target_holes", "target_k53",
    "target_k53_args", "target_k53_heads", "target_k53_tele", "target_major_at",
    "target_major_default", "target_major_nfs", "target_major_of", "target_major_of_const",
    "target_major_of_member", "target_major_of_outside", "target_major_of_outside_closed",
    "target_major_of_outside_occ", "target_major_of_outside_tail", "target_major_pins",
    "target_outside_inst", "target_params_def_eq", "target_params_def_eq_step",
    "target_pi_doms_with", "target_pin_tys", "target_rec_pins", "target_rec_pins_names",
    "target_rec_pins_split", "tbl_base_get", "tbl_own_get", "tbl_own_set",
    "trust_compiler_ok", "try_unfold_proj_app", "type_pin_guard", "type_pin_stored",
    "type_pins_guard", "type_sort_pw", "ue_mentions_go", "unfold_definition", "unfold_defn_at",
    "unfoldable_head", "unresolved_consts_error", "unwrap_id_defs", "unwrap_step", "value_guards",
    "view_ls", "view_ls_len", "wc_clear", "wc_find", "wc_put", "wh_clear", "wh_find", "wh_put",
    "whnf", "whnf_app", "whnf_app_iota", "whnf_core", "whnf_core_app", "whnf_core_app2", "whnf_core_lookup_at", "whnf_core_store_chain", "whnf_core_store_keys",
    "whnf_core_store_cheap_keys", "whnf_stuck", "whnf_core_step", "whnf_core_step_proj", "whnf_loop", "whnf_step", "whnf_telescope", "whnf_top",
    "whnf_walk_fuel", "wk_clear", "wk_find", "wk_put", "ws_clear", "ws_find", "ws_go", "ws_node",
    "ws_put", "wscoped_bfast", "zero_find", "zero_push"]

names_tree apTree : apFns
names_tree cdTree : cdFns

/-- The arrays of `apA`, as a test. -/
def apPa (b : TieredArray) : Bool :=
  checkerWordArrays.contains b && b != PINS && b != ABMEMO && b != ILMEMO && b != LPMEMO &&
    b != LPLMEMO && b != LPLSMEMO && b != WSM && b != FLM && b != LSM && b != L.Ind.HBM && apP b

/-- The `CTL` words of `apC`, as a test. -/
def apPc (x : Word) : Bool :=
  decide (x.toNat < 1024) && x.toNat != 48 && x.toNat != 50 && x.toNat != 54 && x.toNat != 56 &&
    x.toNat != 58 && x.toNat != 152 && x.toNat != 154 && x.toNat != 156 && x.toNat != 214 && apQ x

/-- The arrays of `cdA`, as a test. -/
def cdPa (b : TieredArray) : Bool := checkerWordArrays.contains b && !IdxArr b && b != PINS

/-- The `CTL` words of `cdC`, as a test. -/
def cdPc (x : Word) : Bool :=
  decide (x.toNat < 1024) && ((decide (x.toNat < 162) || decide (173 < x.toNat)) && x.toNat != 128)

theorem apPa_mem (b : TieredArray) (h : apPa b = true) : b ∈ apA := by
  simp only [apPa, Bool.and_eq_true, bne_iff_ne, ne_eq, List.contains_iff_mem] at h
  simp only [apA, leafA, List.mem_filter, decide_eq_true_eq]
  grind

theorem apPc_mem (x : Word) (h : apPc x = true) : x ∈ apC := by
  simp only [apPc, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
  simp only [apC, leafC, List.mem_filter, List.mem_map, List.mem_range, decide_eq_true_eq]
  refine ⟨⟨x.toNat, ⟨h.1.1.1.1.1.1.1.1.1.1, ?_⟩, UInt64.ofNat_toNat⟩, h.2⟩
  omega

theorem cdPa_mem (b : TieredArray) (h : cdPa b = true) : b ∈ cdA := by
  simp only [cdPa, Bool.and_eq_true, List.contains_iff_mem] at h
  simp only [cdA, List.mem_filter, Bool.and_eq_true]
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem cdPc_mem (x : Word) (h : cdPc x = true) : x ∈ cdC := by
  simp only [cdPc, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [cdC, List.mem_filter, List.mem_map, List.mem_range]
  exact ⟨x.toNat, ⟨h.1, by rw [Bool.and_eq_true]; exact h.2⟩, UInt64.ofNat_toNat⟩

/-- Every function of the checker passes `and_pin_ok`'s per-function check. -/
prog_all checkerProg_apChk : checkerProg (wsChk CTL apPa apPc apTree)

/-- Every function of the checker passes `check_decl`'s per-function check. -/
prog_all checkerProg_cdChk : checkerProg (wsChk CTL cdPa cdPc cdTree)

/-- **`and_pin_ok`'s write set.** -/
theorem checkerProg_apW : ∃ F, "and_pin_ok" ∈ F ∧ closedA checkerProg apA apC F = true :=
  ⟨apFns, List.mem_cons_self, closedW_of_all apTree.eq apPa_mem apPc_mem checkerProg_apChk⟩

/-- **`check_decl`'s write set.** -/
theorem checkerProg_cdW : ∃ F, "check_decl" ∈ F ∧ closedA checkerProg cdA cdC F = true :=
  ⟨cdFns, List.mem_cons_self, closedW_of_all cdTree.eq cdPa_mem cdPc_mem checkerProg_cdChk⟩

end L.Checker
