module

public import ConAgua.Checker.IndArmTests
public import ConAgua.Arena.IotaRelRefK
public import ConAgua.Arena.IotaFrameBase
meta import ConAgua.Checker.IndArmTests
meta import ConAgua.Arena.IotaRelRefK
meta import ConAgua.Arena.IotaFrameBase

@[expose] public section

/-!
# The ι reading rule's write sets in `checkerProg`: the function sets and their tests (lane ronsync8)

The call closures (computed from the checker's program) and the store tests of the four write
sets `Checker/IotaArmClosed.lean` decides: `block_reads_at`'s with three leaves (`briFns`, the
stage's memos kept: `BrMem`), the readings' (`iotaRFns`, `IotaFrameProg.rclosed`), the closure of
the callees `blockReadsAt_rel` takes `AbsKeep` of (`iotaKeepFns`, outside the walk memos) and of
`recs_read` (`iotaOwnFns`, the own rows' counters kept). The `CTL` tests reach word 1023.
-/

namespace L.Checker

open L.Arena L.Ind L.Compiler

/-- `block_reads_at`'s call closure without the leaves `briLeaves` and what only they reach. -/
def briFns : List FnName :=
  ["ann_eq", "ann_ident", "ann_ident_body", "ann_ident_val", "ann_witness", "app_count",
   "app_fill", "app_find", "app_push", "base_row_get", "block_caps_at", "block_caps_at_er_copy",
   "block_caps_at_er_copy_go", "block_caps_ctor_names", "block_caps_fin", "block_caps_head",
   "block_caps_one", "block_constants", "block_ctors", "block_ctors_go", "block_ctors_groups",
   "block_formers", "block_formers_go", "block_is_rec", "block_is_rec_go", "block_is_rec_member",
   "block_reads_at", "block_rec", "block_recs", "block_shape_ctor_groups", "block_shape_declared",
   "block_shape_member_names", "bvar_find", "bvar_push", "cons_block_recs_temp", "ctor_info_rec",
   "ctor_levels_at", "cv_lps", "der_b", "der_bv", "e_view", "env_find", "env_pop_temp", "env_push",
   "env_row_get", "env_row_set", "env_set_flags", "er_copy", "er_from_iw", "er_from_iw_go",
   "er_put_ci", "er_to_iw", "erec_alloc", "erec_put", "expr_drop_vars", "expr_drop_vars_list",
   "expr_get_d", "expr_lvl_eq", "forall_find", "forall_push", "former_res_sort", "former_z",
   "gen_rec_check_pop_all", "get_app_args", "get_app_args_f", "get_app_fn", "get_app_fn_f",
   "if_clear", "if_find", "if_put", "ik_copy", "ind_info_rec", "inst_app", "inst_entry",
   "inst_forall", "inst_go", "inst_lam", "inst_let", "inst_lp_fast", "inst_proj",
   "instantiate1_fast", "intern_app", "intern_bvar", "intern_forall", "intern_lam", "intern_letE",
   "intern_ls", "intern_ls_iw", "intern_nanon", "intern_nstr", "intern_param", "intern_proj",
   "intern_sort", "iota_bvars", "iota_frame", "iota_params_at", "iota_parts_at",
   "iota_parts_at_body", "iota_parts_of_at", "iota_parts_rel", "iota_read_major", "iota_rec_of",
   "is_minor_at", "iw_alloc", "iw_copy", "iw_pool", "keys_push_iw", "lam_find", "lam_push",
   "letE_find", "letE_push", "lf_clear", "lf_find", "lf_put", "lh_mk", "lh_push", "lift_app",
   "lift_entry", "lift_field_doms", "lift_forall", "lift_go", "lift_idx_args", "lift_lam",
   "lift_let", "lift_proj", "limbs_eq", "list_ann_eq", "list_lvl_eq", "lit_hash", "lit_name_at",
   "lits_stored", "ls_find", "ls_match", "ls_node", "ls_push", "lv_cases", "lv_cases_at",
   "lv_comb", "lv_dist1", "lv_dist2", "lv_eq", "lv_equiv", "lv_equivs", "lv_imax", "lv_imax_l",
   "lv_imax_r", "lv_leq", "lv_node", "lv_rest", "lv_simp", "lv_subsimp", "lv_subst", "lv_zero",
   "lvl_eq", "lvls_eq", "member_field_copy", "member_names_copy", "member_never_zero",
   "minors_from", "mk_app", "mk_forall", "mk_lam", "mk_let", "mk_proj", "motive_level",
   "name_auto_param", "name_missing", "name_opt_param", "name_out_param", "name_semi_out_param",
   "nanon_find", "nanon_push", "nstr_find", "nstr_match", "nstr_push", "param_find",
   "param_levels", "param_levels_go", "param_push", "params_ann_eq", "pi_doms_mention_any",
   "pi_result", "pi_result_f", "pi_tele", "pin_word", "pool_copy", "pool_room", "proj_find",
   "proj_push", "rec3", "rec_fire", "rec_info_rec", "rec_reads", "recs_read", "rule_reads",
   "rules_read", "rules_refire", "sl_append", "sl_cons", "sl_eq", "sl_get", "sl_snoc", "sort_find",
   "sort_push", "spn_to_iw", "strip_pis", "view_ls", "view_ls_len"]

/-- The call closure of `iota_parts_rel`, `block_constants`, `block_recs`, `cons_block_recs_temp`,
`gen_rec_check_pop_all`, `env_set_flags`. -/
def iotaKeepFns : List FnName :=
  ["ann_eq", "ann_ident", "ann_ident_body", "ann_ident_val", "ann_witness", "app_count",
   "app_fill", "app_find", "app_push", "base_row_get", "block_caps_at", "block_caps_at_er_copy",
   "block_caps_at_er_copy_go", "block_caps_ctor_names", "block_caps_fin", "block_caps_head",
   "block_caps_one", "block_constants", "block_ctors", "block_ctors_go", "block_ctors_groups",
   "block_formers", "block_formers_go", "block_is_rec", "block_is_rec_go", "block_is_rec_member",
   "block_rec", "block_recs", "block_shape_ctor_groups", "block_shape_declared",
   "block_shape_member_names", "bvar_find", "bvar_push", "cons_block_recs_temp", "ctor_info_rec",
   "der_b", "der_bv", "e_view", "env_find", "env_pop_temp", "env_push", "env_row_get",
   "env_row_set", "env_set_flags", "er_from_iw", "er_from_iw_go", "er_put_ci", "erec_alloc",
   "erec_put", "expr_drop_vars", "expr_drop_vars_list", "expr_lvl_eq", "forall_find",
   "forall_push", "former_res_sort", "former_z", "gen_rec_check_pop_all", "get_app_args",
   "get_app_args_f", "get_app_fn", "get_app_fn_f", "if_clear", "if_find", "if_put", "ind_info_rec",
   "inst_app", "inst_entry", "inst_forall", "inst_go", "inst_lam", "inst_let", "inst_proj",
   "instantiate1_fast", "intern_app", "intern_bvar", "intern_forall", "intern_lam", "intern_letE",
   "intern_nanon", "intern_nstr", "intern_proj", "intern_sort", "iota_parts_rel", "iw_alloc",
   "iw_copy", "lam_find", "lam_push", "letE_find", "letE_push", "lh_mk", "lh_push", "limbs_eq",
   "list_ann_eq", "list_lvl_eq", "lit_hash", "lit_name_at", "lits_stored", "ls_node", "lv_cases",
   "lv_cases_at", "lv_comb", "lv_dist1", "lv_dist2", "lv_eq", "lv_equiv", "lv_equivs", "lv_imax",
   "lv_imax_l", "lv_imax_r", "lv_leq", "lv_node", "lv_rest", "lv_simp", "lv_subsimp", "lv_subst",
   "lv_zero", "lvl_eq", "lvls_eq", "ma_clear", "ma_find", "ma_put", "member_field_copy",
   "member_names_copy", "member_never_zero", "mentions_any_const", "mentions_any_go",
   "mentions_any_node", "mk_app", "mk_forall", "mk_lam", "mk_let", "mk_proj", "name_auto_param",
   "name_missing", "name_opt_param", "name_out_param", "name_semi_out_param", "nanon_find",
   "nanon_push", "nstr_find", "nstr_match", "nstr_push", "params_ann_eq", "pi_doms_mention_any",
   "pi_result", "pin_word", "pool_copy", "pool_room", "proj_find", "proj_push", "rec3", "rec_fire",
   "rec_info_rec", "rules_refire", "sl_append", "sl_cons", "sl_contains", "sl_eq", "sl_snoc",
   "sort_find", "sort_push", "spn_to_iw", "strip_pis", "view_ls", "view_ls_len"]

/-- `recs_read`'s call closure. -/
def iotaOwnFns : List FnName :=
  ["ann_eq", "ann_ident", "ann_ident_body", "ann_ident_val", "ann_witness", "app_count",
   "app_fill", "app_find", "app_push", "base_row_get", "bb_go", "bb_memo", "bb_node", "bm_clear",
   "bm_find", "bm_put", "bvar_b", "bvar_find", "bvar_push", "const_find", "const_push",
   "ctor_levels_at", "cv_lps", "der_b", "der_bv", "e_view", "env_find", "env_row_get", "er_copy",
   "er_to_iw", "expr_drop_vars", "expr_drop_vars_list", "expr_get_d", "expr_lvl_eq", "forall_find",
   "forall_push", "fvar_find", "fvar_push", "get_app_args", "get_app_args_f", "get_app_fn",
   "get_app_fn_f", "i1l_app", "i1l_clear", "i1l_find", "i1l_forall", "i1l_go", "i1l_lam",
   "i1l_let", "i1l_proj", "i1l_put", "if_clear", "if_find", "if_put", "ik_copy", "ilp_clear",
   "ilp_find", "ilp_put", "ilpl_clear", "ilpl_find", "ilpl_put", "ilpls_clear", "ilpls_find",
   "ilpls_put", "imax_find", "imax_push", "inst_app", "inst_entry", "inst_forall", "inst_go",
   "inst_lam", "inst_let", "inst_lp_core", "inst_lp_fast", "inst_proj", "instantiate1_fast",
   "instantiate_lift_fast", "intern_app", "intern_bvar", "intern_const", "intern_forall",
   "intern_fvar", "intern_imax", "intern_lam", "intern_letE", "intern_ls", "intern_ls_iw",
   "intern_max", "intern_nanon", "intern_nstr", "intern_param", "intern_proj", "intern_sort",
   "intern_succ", "intern_zero", "iota_bvars", "iota_frame", "iota_params_at", "iota_parts_at",
   "iota_parts_at_body", "iota_parts_of_at", "iota_parts_rel", "iota_read_major", "iota_rec_of",
   "is_minor_at", "iw_alloc", "iw_copy", "iw_pool", "keys_ok", "keys_push_iw", "lam_find",
   "lam_push", "letE_find", "letE_push", "lf_clear", "lf_find", "lf_put", "lh_mk", "lift_app",
   "lift_entry", "lift_field_doms", "lift_forall", "lift_go", "lift_idx_args", "lift_lam",
   "lift_let", "lift_proj", "limbs_eq", "list_ann_eq", "list_lvl_eq", "lit_hash", "lp_app",
   "lp_forall", "lp_fvar", "lp_go", "lp_lam", "lp_let", "lp_let_tail", "lp_lookup", "lp_proj",
   "lp_rb_let", "lp_substl", "ls_find", "ls_match", "ls_node", "ls_push", "lv_cases",
   "lv_cases_at", "lv_comb", "lv_dist1", "lv_dist2", "lv_eq", "lv_equiv", "lv_equivs", "lv_imax",
   "lv_imax_l", "lv_imax_r", "lv_intern", "lv_leq", "lv_node", "lv_rest", "lv_simp", "lv_sub_int",
   "lv_subsimp", "lv_subst", "lvl_eq", "lvls_eq", "max_find", "max_push", "minors_from", "mk_app",
   "mk_forall", "mk_lam", "mk_let", "mk_proj", "motive_level", "name_auto_param", "name_missing",
   "name_opt_param", "name_out_param", "name_semi_out_param", "nanon_find", "nanon_push",
   "nstr_find", "nstr_match", "nstr_push", "param_find", "param_levels", "param_levels_go",
   "param_push", "params_ann_eq", "pi_result", "pi_result_f", "pi_tele", "pin_word", "pool_room",
   "proj_find", "proj_push", "rec_reads", "recs_read", "rule_reads", "rules_read", "sl_cons",
   "sl_eq", "sl_get", "sl_memo", "sls_go", "sls_memo", "sort_find", "sort_push", "spn_ls",
   "spn_pool", "spn_to_iw", "strip_pis", "succ_find", "succ_push", "view_ls_len", "zero_find",
   "zero_push"]

/-- A `CTL` word test: below 1024 and `g`. -/
def tC1 (g : Nat → Bool) (w : Word) : Bool := decide (w.toNat < 1024) && g w.toNat

theorem tC1_mem {g : Nat → Bool} {w : Word} (h : tC1 g w = true) :
    w ∈ ((List.range 1024).filter g).map Nat.toUInt64 := by
  simp only [tC1, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [List.mem_map, List.mem_filter, List.mem_range]
  exact ⟨w.toNat, ⟨h.1, h.2⟩, UInt64.ofNat_toNat⟩

names_tree briTree : briFns
names_tree briCallTree : briFns ++ briLeaves
def briT : ArmTest :=
  (tA fun b => decide ((b.arr < 201 ∨ 208 < b.arr) ∧ b ≠ Stubs.CRM),
    tC1 fun c => decide ((c < 202 ∨ 219 < c) ∧ c ≠ 158), briTree, briCallTree)

names_tree iotaRTree : iotaRFns
def iotaRT : ArmTest :=
  (tA fun b => memoFreeA [b], tC1 fun c => memoFreeC [UInt64.ofNat c], iotaRTree, iotaRTree)

names_tree iotaKeepTree : iotaKeepFns
def iotaKeepT : ArmTest :=
  (tA fun b => memoFreeA [b], tC1 fun c => memoFreeC [UInt64.ofNat c], iotaKeepTree, iotaKeepTree)

names_tree iotaOwnTree : iotaOwnFns
def iotaOwnT : ArmTest :=
  (tA fun b => decide (b ∉ ([OIXA, OIXS, OIXN, tier1 OIXA, tier1 OIXS, tier1 OIXN] : List TieredArray)),
    tC1 fun c => decide (c ≠ 133), iotaOwnTree, iotaOwnTree)

end L.Checker
