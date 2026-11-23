module

public import ConAgua.Arena.LoopFns
public import ConAgua.Compiler.WriteSetSplit
meta import ConAgua.Arena.LoopFns
meta import ConAgua.Compiler.WriteSetSplit

@[expose] public section

/-!
# The declaration loop's leaves: the functions that leave the core's memos alone (lane `loopt2`)

`leafFns`: every function of `loopFns` whose call closure stores neither into the pin table nor
into the core's walk memos (`CoreMemos`: arrays 49, 50, 52‥54, 151‥153, 207 and `CTL` words 48, 50,
54, 56, 58, 152, 154, 156, 214) nor bytes — the record writers, the environment's index, the ROM
readers, the interning functions, … but not the walks or the core. Computed from `checkerProg`'s
call graph by `scripts/leaf_fns.py` (the decided check in `ConAgua/Checker/LeafAll.lean` fails if
it is stale). A leaf call keeps `CoreMemos` and the pin flag by its frame (`LeafClosed`), which is
what carries `StageC` across it.
-/

namespace L.Arena

/-- The arrays a leaf may write (both tiers): all but the pin table and the core's memos. -/
def leafA : List TieredArray :=
  checkerWordArrays.filter fun b => b ≠ PINS ∧ b ≠ ABMEMO ∧ b ≠ ILMEMO ∧ b ≠ LPMEMO ∧
    b ≠ LPLMEMO ∧ b ≠ LPLSMEMO ∧ b ≠ WSM ∧ b ≠ FLM ∧ b ≠ LSM ∧ b ≠ L.Ind.HBM

/-- The `CTL` words a leaf may write: all but the core memos' stamps. -/
def leafC : List Word :=
  ((List.range 1024).filter fun x => x ≠ 48 ∧ x ≠ 50 ∧ x ≠ 54 ∧ x ≠ 56 ∧ x ≠ 58 ∧ x ≠ 152 ∧
    x ≠ 154 ∧ x ≠ 156 ∧ x ≠ 214).map UInt64.ofNat

/-- The functions of `loopFns` that leave the pins and the core's memos alone. -/
def leafFns : List FnName :=
  ["ab_find", "ab_fvb", "add_1", "add_n", "alpd_ls", "and_block_named", "and_n", "and_pin_ok",
   "and_rescue_slots", "apd_find", "app_count", "app_count_at", "app_fill", "app_fill_n",
   "app_find", "app_hole", "app_push", "b_eq", "base_row_get", "basis_name_hit",
   "basis_name_hit_go", "basis_name_unreserved", "basis_names_error", "bb_go", "bb_memo",
   "bb_node", "binder_dom", "binder_pair", "block_caps_at", "block_caps_at_er_copy",
   "block_caps_at_er_copy_go", "block_caps_ctor_names", "block_caps_fin", "block_caps_head",
   "block_caps_one", "block_counts", "block_counts_head", "block_counts_pure", "block_groups",
   "block_groups_go", "block_groups_one", "block_is_rec", "block_is_rec_go", "block_is_rec_member",
   "block_large_elim_allowed", "block_link_ok_at", "block_links_ok", "block_links_ok_go",
   "block_member_counts", "block_member_counts_find", "block_member_counts_go", "block_names_eq",
   "block_names_unreserved", "block_nested_bit", "block_nested_bit_go", "block_rec",
   "block_rec_got", "block_rec_lps_ok", "block_rec_lps_ok_go", "block_rec_lps_one",
   "block_rec_name_set_ok", "block_rec_names_unreserved", "block_rec_split_own_aux",
   "block_rec_want", "block_rec_want_aux_names", "block_recs", "block_shape_all_ctors",
   "block_shape_all_ctors_go", "block_shape_ctor_groups", "block_shape_ctors_copy",
   "block_shape_ctors_of", "block_shape_declared", "block_shape_fin", "block_shape_formers",
   "block_shape_large", "block_shape_lps", "block_shape_major_idx_at", "block_shape_member_ctors",
   "block_shape_member_names", "block_shape_members_of", "block_shape_n_idxs",
   "block_shape_names_of", "block_shape_nest_ctx", "block_shape_num_ctors", "block_shape_pack",
   "block_shape_recs_of", "block_shape_result_sort", "block_shape_rule_prefix_at",
   "block_shape_seal", "block_shape_tail", "block_shape_with_members", "block_shape_with_sort",
   "block_split", "block_split_ctors", "block_split_recs", "block_table", "block_tables",
   "bm_clear", "bm_find", "bm_put", "bool_ctor_ok", "bool_ctor_typed", "bvar_b", "bvar_find",
   "bvar_push", "canon_ctx", "canon_eq_list", "canon_expr_eq", "canon_level_eq",
   "canon_level_list_eq", "canon_levels_eq", "canon_name_map", "canon_names", "canon_names_go",
   "canon_rules_eq", "caps_eq", "caps_eq_a", "caps_eq_b", "caps_eq_c", "cert_ctx", "cert_ctx_main",
   "cert_ctx_pins", "cert_div_mod", "cert_div_mod_eqs", "cert_div_mod_guards", "cert_eq",
   "cert_gcd", "cert_guard", "cert_halves", "cert_land", "cert_lor", "cert_lor_rhs",
   "cert_rec_rhs", "cert_shift_left", "cert_shift_right", "cert_two_eqs", "cert_xor",
   "cert_xor_rhs", "char_of_nat_ty_ok", "char_ty_ok", "check_block_classes_count",
   "check_block_classes_keys", "check_block_classes_one_per_member", "check_block_names",
   "check_block_pass_rec", "check_block_positivity_init", "check_div_mod_pin_at_fe2",
   "check_field_sort_bound", "check_structural_nat_pin_at_fe2", "check_sum_tele", "ci_canon_defn",
   "ci_canon_eq", "ci_canon_rec", "ci_eq", "ci_eq_rest", "ci_to_cv", "class_const_ok_lit",
   "class_ctor_of_nfs", "class_fe_r", "class_fe_r_go", "class_fe_r_rec", "class_fields_of",
   "class_fields_of_go", "class_fields_of_hits", "class_gen_major_ci", "class_gen_major_tail",
   "class_gen_minor_ci", "class_gen_mot_var", "class_gen_prefix_binders_find_ctor",
   "class_gen_prefix_binders_find_ctor_go", "class_gen_rule_find_slot",
   "class_gen_rule_find_slot_go", "class_gen_rule_pvars_go", "class_gen_slot_var",
   "class_key_canon", "class_key_canon_go", "class_key_of", "class_key_of_closed", "class_leaf_at",
   "class_minor_slot", "class_minor_slot_go", "class_n_pc_of", "class_of_motive_var",
   "class_read_classes", "class_read_minor_finish", "class_read_minor_ih1", "class_read_minor_ihs",
   "class_read_minor_tail", "class_read_mot_pos", "class_read_motive_slot", "class_read_n_slots",
   "class_read_slot_motive", "class_read_slots_snoc", "class_rec_of", "class_rec_ty_ok_guards",
   "class_rule_check_domains", "class_seeds", "class_slot_is_minor", "cons_block_ctors",
   "cons_block_inds", "cons_block_recs_temp", "cons_sum_ctors", "const_e", "const_find",
   "const_named", "const_push", "consts_resolve_all", "consts_resolve_ffast", "copy_n", "cr_leaf",
   "cr_lit_pins", "crf_go", "crm_clear", "crm_find", "crm_put", "ct_clear", "ct_find", "ct_put",
   "ctl_get", "ctor_family", "ctor_head_against", "ctor_info_rec", "ctor_member", "ctor_target",
   "ctor_target_for", "ctor_view", "ctors_have_name", "ctors_lps_ok", "ctors_params_ok",
   "cv_canon_eq", "cv_clear", "cv_eq", "cv_find", "cv_lps", "cv_new", "cv_put", "de_clear",
   "de_find", "de_put", "dec_len", "declined_at_definition", "defeq_no_fvars", "depth", "depth_go",
   "depth_node", "der_b", "der_bv", "dind_copy", "div_2by1", "div_add", "div_kstep", "div_mod1",
   "div_mod_cert_applied", "div_mod_cert_proofs", "div_mod_cert_stmts", "div_mod_cert_stmts_at",
   "div_mod_decl_pin", "div_mod_env_guard", "div_mod_slot", "div_mod_type_pins", "div_modk",
   "div_norm", "div_recip", "div_submul", "dlp_copy", "dp_clear", "dp_find", "dp_put", "e_view",
   "eidx_copy_upto", "ek_copy", "env_find", "env_pop_temp", "env_push", "env_push_table",
   "env_row_get", "env_row_set", "env_set_flags", "eq_at1", "eq_stored", "er_copy", "er_copy_er",
   "er_from_iw", "er_from_iw_go", "er_put_ci", "er_sl_at", "er_sl_eq", "er_slice_eq", "er_to_iw",
   "erase_each", "erase_fvar_tys", "erec_alloc", "erec_ci", "erec_push", "erec_put",
   "eta_ctor_partial", "eta_ctor_partial_fam", "eta_ctor_shape", "eta_fab_args", "eta_projs",
   "eta_rescue_table", "expr_drop_vars", "expr_drop_vars_list", "expr_get_d", "expr_view_ok",
   "field_doms_resolve", "find_pinned", "find_pinned_cv", "find_proj", "find_rule", "find_table",
   "fire_levels_at", "fl_find", "flush_caches", "fm_clear", "fm_find", "fm_put", "forall_find",
   "forall_push", "former_def_headed", "former_never_zero", "former_res_sort", "former_z",
   "formers_lps_ok", "fr_go", "fr_memo", "fr_node", "from_le", "fv_map_at", "fvar_b", "fvar_find",
   "fvar_head", "fvar_push", "fvar_type_d", "fvar_type_ds", "gcd_step",
   "gen_rec_check_any_no_member", "gen_rec_check_former_tys", "gen_rec_check_minor_ok",
   "gen_rec_check_pop_all", "generated_rule_nested", "generated_rules_remap", "get_app_args",
   "get_app_args_f", "get_app_fn", "get_app_fn_f", "get_app_spine", "has_fvar", "has_fvar_fast",
   "has_str_lit_go", "hb_find", "head_and_args", "head_hint", "head_is_proj", "head_proof_const",
   "head_proof_proj", "head_proof_pw", "head_type_const", "head_type_pw", "head_type_res",
   "hint_eq", "hint_lt", "i1l_app", "i1l_clear", "i1l_find", "i1l_forall", "i1l_go", "i1l_lam",
   "i1l_let", "i1l_proj", "i1l_put", "idx_args_resolve", "if_clear", "if_find", "if_put",
   "ifenv_push_all", "ifenv_push_delta", "ifenv_push_tables", "ik_copy", "il_app", "il_bvar",
   "il_forall", "il_go", "il_lam", "il_let", "il_proj", "ilm_find", "ilp_find", "ilpl_find",
   "ilpls_find", "imax_find", "imax_push", "in_clear", "in_find", "in_put", "ind_block_to_erec",
   "ind_copy_go", "ind_info_rec", "ind_params_ok", "ind_rec_copy", "infer_lit", "inst1",
   "inst_app", "inst_entry", "inst_forall", "inst_go", "inst_lam", "inst_let", "inst_pis_with",
   "inst_proj", "inst_spine", "install_basis_decl", "instantiate1_fast", "instantiate_lift_fast",
   "intern_app", "intern_bvar", "intern_const", "intern_forall", "intern_fvar", "intern_imax",
   "intern_lam", "intern_letE", "intern_lit", "intern_ls", "intern_ls_iw", "intern_max",
   "intern_nanon", "intern_nnum", "intern_nstr", "intern_param", "intern_proj", "intern_sort",
   "intern_succ", "intern_zero", "io_clear", "io_find", "io_neutral", "io_put",
   "iota_certs_full_parts", "iota_no_cert", "is_eager_reduce", "is_nat_succ_app", "is_nat_zero",
   "is_proof_fast", "is_str_lit", "iw_alloc", "iw_copy", "iw_pool", "iw_reset", "iw_to_spn",
   "kara_mid", "kara_prods", "kara_sum", "keys_ok", "keys_push", "keys_push_iw", "lam_body",
   "lam_find", "lam_proj", "lam_push", "lazy_fold_ok", "leaf_mem", "letE_find", "letE_push",
   "lf_clear", "lf_find", "lf_put", "lh_contains", "lh_mk", "lh_push", "lift_app", "lift_entry",
   "lift_forall", "lift_go", "lift_lam", "lift_let", "lift_proj", "limb_push", "limbs_eq",
   "list_cons_ty_ok", "list_nil_ty_ok", "list_ty_ok", "lit_eq", "lit_find", "lit_guard_has",
   "lit_hash", "lit_match", "lit_name_at", "lit_nat_sized", "lit_push", "lit_shape_ok",
   "lit_to_ctor_if_nat", "lits_stored", "loose_bvars_bounded_fast", "lp_lookup", "lp_rb_let",
   "lp_substl", "lq_clear", "lq_find", "lq_put", "ls_find", "ls_match", "ls_node", "ls_push",
   "lsb_find", "lsq_clear", "lsq_find", "lsq_put", "lv_always_zero", "lv_apd", "lv_cases",
   "lv_cases_at", "lv_comb", "lv_dist1", "lv_dist2", "lv_eq", "lv_equiv", "lv_equivs", "lv_imax",
   "lv_imax_l", "lv_imax_r", "lv_intern", "lv_leq", "lv_leq_top", "lv_lookup", "lv_mem",
   "lv_never", "lv_node", "lv_nz", "lv_rest", "lv_simp", "lv_spw", "lv_sub_int", "lv_subsimp",
   "lv_subst", "lv_zero", "lv_zero_where_zero", "lvl_eq", "lvl_eq_c", "lvl_eq_fueled",
   "lvl_eq_rec", "lvl_eq_true", "lvls_eq", "lvls_eq_c", "lvls_eq_rec", "m2c_const_view",
   "ma_clear", "ma_find", "ma_put", "matches_pin", "max_find", "max_push", "member_ctors_copy",
   "member_field_copy", "member_idx_at", "member_names_copy", "member_never_zero", "memo_get",
   "memo_push", "mentions_any_const", "mentions_any_go", "mentions_any_node", "mk_app", "mk_app_n",
   "mk_app_n_f", "mk_app_n_from", "mk_forall", "mk_lam", "mk_let", "mk_proj", "mk_target_major",
   "mul_row", "mul_win", "mul_zeros", "n_idxs_copy", "name_rec", "name_rec_i", "nanon_find",
   "nanon_push", "nat_add", "nat_add_lit", "nat_ap1", "nat_ap2", "nat_beq_lit",
   "nat_bin_op_of_name", "nat_bin_op_result", "nat_ble_lit", "nat_cmp", "nat_div_lit",
   "nat_div_mod_names", "nat_divmod", "nat_eq_be", "nat_eq_bl", "nat_eq_ctx", "nat_eq_disp",
   "nat_eq_list2", "nat_eq_list3", "nat_eq_list4", "nat_eq_mu", "nat_eq_po", "nat_eq_pr",
   "nat_eq_un", "nat_gcd", "nat_gcd_lit", "nat_ind_at_cv", "nat_ind_ok", "nat_land",
   "nat_land_lit", "nat_lit_supported", "nat_lit_to_ctor", "nat_lor", "nat_lor_lit", "nat_mod_lit",
   "nat_mul", "nat_mul_lit", "nat_one", "nat_op_bool_ctors", "nat_op_cod", "nat_op_deps",
   "nat_op_deps_stored", "nat_op_equations", "nat_op_guard", "nat_op_name", "nat_op_names",
   "nat_op_pins", "nat_op_pins_a", "nat_op_pins_b", "nat_op_pins_c", "nat_op_stored_ok",
   "nat_op_ty_pinned", "nat_pow", "nat_pow_lit", "nat_pred",
   "nat_pred_lit", "nat_shl", "nat_shl_lit", "nat_shr", "nat_shr_lit", "nat_size_refused",
   "nat_sub", "nat_sub_lit", "nat_succ_at_cv", "nat_succ_lit", "nat_succ_ok", "nat_trim",
   "nat_var", "nat_xor", "nat_xor_lit", "nat_zero_at_cv", "nat_zero_ok", "nest_accept_group",
   "nest_block_of", "nest_canon_crest", "nest_canon_sub", "nest_cont_checks",
   "nest_cont_new_active", "nest_cont_new_finish", "nest_cont_params_closed", "nest_container",
   "nest_container_ctors", "nest_container_ctors_go", "nest_crest", "nest_ctor_entry",
   "nest_ctor_entry_strip", "nest_ctor_nf", "nest_ctors_res_ok", "nest_ctx_hi_at",
   "nest_ctx_root_holes", "nest_ctx_root_holes_go", "nest_ds_closed", "nest_ds_closed_go",
   "nest_field_kind_flat", "nest_frame_grp", "nest_frame_holes", "nest_frame_mates",
   "nest_frame_mates_go", "nest_group_ctors", "nest_hole_at", "nest_hole_img", "nest_hole_img_ds",
   "nest_hole_img_ds_go", "nest_hole_img_frame", "nest_hole_img_root", "nest_holes",
   "nest_holes_go", "nest_key_eq", "nest_key_map", "nest_keys_contains", "nest_kinds_flat",
   "nest_kinds_flat_inner", "nest_kinds_flat_mid", "nest_occ", "nest_occ_any", "nest_occ_go",
   "nest_occ_node", "nest_out_kinds", "nest_phs", "nest_phs_go", "nest_pos_fvar",
   "nest_pos_hole_kind", "nest_res_head", "nest_seed_of", "nest_seed_of_go", "nest_seeds_fuel",
   "nest_walk_stack", "nnum_find", "nnum_push", "no_clear", "no_find", "no_put", "not_proof_fast",
   "nstr_find", "nstr_match", "nstr_push", "num_ctors_of", "of_reduce_ax_ok", "of_reduce_op",
   "of_reduce_pin_a", "opa_go", "open_pis_at_fvars", "or_n", "param_find", "param_levels",
   "param_levels_go", "param_push", "peel_pis", "peel_pis_w", "ph_app", "pi_binders",
   "pi_doms_mention_any", "pi_doms_occ", "pi_residual", "pi_result", "pi_result_f",
   "pi_sort_tele_len", "pin_agrees", "pin_at", "pin_found", "pin_link_go", "pin_link_ok",
   "pin_range_has", "pin_word", "pool_copy", "pool_room", "pow_nat", "pow_refused", "proj_cert",
   "proj_find", "proj_guard_row", "proj_push", "proof_pw", "ptr_list_names", "ptr_names_copy",
   "quick_sort", "quot_pin", "quot_preds_ok", "ra_clear", "ra_find", "ra_put", "raw_nat_lit",
   "raw_table", "rci_block", "rci_block_to", "rci_caps", "rci_ci", "rci_cv", "rci_fresh",
   "rci_lvls_to", "rci_name_sl", "rci_names_to", "rci_rule", "rci_rules_to", "rci_slot",
   "read_block", "read_block_at", "rec2", "rec3", "rec4", "rec5", "rec6", "rec7", "rec_fire",
   "rec_fire_level_count", "rec_fire_levels", "rec_info_rec", "rec_k_expected", "rec_target_of",
   "reduce_cert_var", "reduce_decl_pin", "reduce_elem_ok", "reduce_op_cv_a", "reduce_proj_arg",
   "reduce_proj_fire", "reduce_proj_head", "reduce_stored_ok", "replace_apps", "replace_apps_go",
   "replace_apps_node", "replace_fvars", "replace_fvars_go", "replace_fvars_node",
   "reserved_contains", "reserved_from", "reserved_rec_bool", "reserved_rec_name", "residual_pw",
   "rf_bank_enter", "rf_bank_leave", "rf_clear", "rf_find", "rf_put", "rom_and_pin",
   "rom_basis_decls", "rom_ci", "rom_cv", "rom_ex_leaf_c", "rom_ex_one_c", "rom_ex_ref_c",
   "rom_ex_two_c", "rom_expr_c", "rom_expr_pin", "rom_exprs_to_c", "rom_level_c", "rom_levels_c",
   "rom_lit", "rom_lvls_go_c", "rom_name_c", "rom_pin_sets", "rom_put_c", "rom_u64_c", "rr_clear",
   "rr_find", "rr_put", "rset_clear", "rset_find", "rset_put", "rule_binds", "rule_copy",
   "rule_eq_a", "rule_eq_b", "rule_eq_but_rhs", "rules_eq", "rules_link_ok", "rules_refire",
   "rules_to_erec", "rules_to_erec_go", "same_const_heads", "scratch_drop", "scratch_enter",
   "scratch_reset", "shift_left_refused", "shl_n", "shr_n", "size_bytes", "sl_all_in", "sl_append",
   "sl_cons", "sl_contains", "sl_eq", "sl_find", "sl_get", "sl_getd", "sl_new1", "sl_nodup",
   "sl_set_eq", "sl_snoc", "sle_go", "slp_go", "sls_go", "sort_find", "sort_push", "spine_head",
   "spn_get", "spn_ls", "spn_pool", "spn_push", "spn_to_er", "spn_to_iw", "stack_cover",
   "std_ax_family", "std_axiom_ok", "stk_pool", "stk_push", "stmt1", "str_cons_spine",
   "str_ctor_pre", "str_cv", "str_lit_ctor", "str_ls1", "str_param_sort", "str_utf8_char",
   "stream_closed", "stream_k_check", "stream_nested_bvars", "stream_nested_dom",
   "stream_nested_ok", "stream_nested_pins", "stream_rules_shape", "string_of_list_ty_ok",
   "string_ty_ok", "strip_lams", "strip_pis", "struct_ctor_resid_ok", "struct_elim_level",
   "struct_proj_arg_p", "struct_proj_bodies", "struct_proj_bodies_go", "struct_proj_ps",
   "struct_ps_at", "struct_ps_at_go", "sub_1", "sub_n", "sub_row", "subst_const0",
   "subst_const0_list", "subst_const0_pairs", "subst_const_all", "subst_pw_at", "succ_find",
   "succ_push", "sum_rules", "sum_rules_go", "ta_clear", "ta_find", "ta_put", "target_abs",
   "target_abs_const", "target_abs_go", "target_abs_node", "target_canon_params",
   "target_ctors_of", "target_holes", "target_k53_tele", "target_major_at", "target_major_default",
   "target_major_of_member", "target_major_of_outside_closed", "target_major_of_outside_occ",
   "target_pi_doms_with", "target_rec_pins", "target_rec_pins_names", "target_rec_pins_split",
   "tbl_base_get", "tbl_own_get", "tbl_own_set", "trust_compiler_ok", "type_pin_guard",
   "type_pin_stored", "type_pins_guard", "type_sort_pw", "ue_mentions_go", "unfoldable_head",
   "unresolved_consts_error", "unwrap_id_defs", "unwrap_step", "view_ls", "view_ls_len",
   "wc_clear", "wc_find", "wc_put", "wh_clear", "wh_find", "wh_put", "whnf_core_lookup_at",
   "whnf_core_store_chain", "whnf_core_store_cheap_keys", "whnf_core_store_keys", "whnf_walk_fuel",
   "wk_clear", "wk_find", "wk_put", "ws_find", "xor_n", "zero_find", "zero_n", "zero_push"]

/-- `leafFns` as a tree of name codes (membership of a name by evaluating its code's lookup). -/
names_tree leafTree : leafFns

theorem leaf_mem (f : FnName) (h : (leafTree.find (L.Compiler.nameCode f)).isSome = true) :
    f ∈ leafFns := by
  have := L.Compiler.namesTree_spec leafTree.eq f
  rw [h] at this; exact of_decide_eq_true this.symm

/-- `loopFns` as a tree of name codes: membership by name, stable under a regenerated list. -/
names_tree loopTree : loopFns

theorem loop_mem (f : FnName) (h : (loopTree.find (L.Compiler.nameCode f)).isSome = true) :
    f ∈ loopFns := by
  have := L.Compiler.namesTree_spec loopTree.eq f
  rw [h] at this; exact of_decide_eq_true this.symm

theorem leafA_pins : (PINS : TieredArray) ∉ leafA := by decide +kernel
theorem leafA_memo : (ILMEMO : TieredArray) ∉ leafA ∧ (ABMEMO : TieredArray) ∉ leafA := by
  decide +kernel
theorem leafA_walk : (WSM : TieredArray) ∉ leafA ∧ (FLM : TieredArray) ∉ leafA ∧
    (LSM : TieredArray) ∉ leafA := by
  decide +kernel
theorem leafA_lp : (LPMEMO : TieredArray) ∉ leafA ∧ (LPLMEMO : TieredArray) ∉ leafA ∧
    (LPLSMEMO : TieredArray) ∉ leafA := by
  decide +kernel
theorem leafC_memo : (50 : Word) ∉ leafC ∧ (48 : Word) ∉ leafC := by decide +kernel
theorem leafC_walk : (152 : Word) ∉ leafC ∧ (154 : Word) ∉ leafC ∧ (156 : Word) ∉ leafC := by
  decide +kernel
theorem leafC_lp : (54 : Word) ∉ leafC ∧ (56 : Word) ∉ leafC ∧ (58 : Word) ∉ leafC := by
  decide +kernel
theorem leafA_hb : (L.Ind.HBM : TieredArray) ∉ leafA := fun h => by
  simp [leafA, List.mem_filter] at h
theorem leafC_hb : (214 : Word) ∉ leafC := fun h => by
  simp only [leafC, List.mem_map, List.mem_filter, List.mem_range] at h
  obtain ⟨x, ⟨hx, hp⟩, e⟩ := h
  have : x = 214 := by
    have := congrArg UInt64.toNat e
    rw [UInt64.toNat_ofNat] at this; simp at this; omega
  subst this; simp at hp

/-- **The leaves' write set.** -/
def LeafClosed (p : Prog) : Prop := closedA p leafA leafC leafFns = true

end L.Arena
