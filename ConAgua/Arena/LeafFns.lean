import ConAgua.Arena.LoopFns
import ConAgua.Compiler.WriteSetSplit

/-!
# The declaration loop's leaves: the functions that leave the core's memos alone (lane `loopt2`)

`leafFns`: every function of `loopFns` whose call closure stores neither into the pin table nor
into the core's walk memos (`CoreMemos`: arrays 49, 50, 52‥54, 151‥153 and `CTL` words 48, 50,
54, 56, 58, 152, 154, 156) nor bytes — the record writers, the environment's index, the ROM
readers, the interning functions, … but not the walks or the core. Computed from `checkerProg`'s
call graph by `scripts/leaf_fns.py` (the decided check in `ConAgua/Checker/LeafAll.lean` fails if
it is stale). A leaf call keeps `CoreMemos` and the pin flag by its frame (`LeafClosed`), which is
what carries `StageC` across it.
-/

namespace L.Arena

/-- The arrays a leaf may write (both tiers): all but the pin table and the core's memos. -/
def leafA : List ArrId :=
  (List.range 388).filter fun b => b ≠ PINS ∧ b ≠ 49 ∧ b ≠ 50 ∧ b ≠ 52 ∧ b ≠ 53 ∧ b ≠ 54 ∧
    b ≠ 151 ∧ b ≠ 152 ∧ b ≠ 153

/-- The `CTL` words a leaf may write: all but the core memos' stamps. -/
def leafC : List Word :=
  ((List.range 1024).filter fun x => x ≠ 48 ∧ x ≠ 50 ∧ x ≠ 54 ∧ x ≠ 56 ∧ x ≠ 58 ∧ x ≠ 152 ∧
    x ≠ 154 ∧ x ≠ 156).map UInt64.ofNat

/-- The functions of `loopFns` that leave the pins and the core's memos alone. -/
def leafFns : List FnName :=
  ["ab_find", "ab_fvb", "add_carry", "alpd_ls", "and_block_named", "and_pin_ok",
   "and_rescue_slots", "apd_find", "app_count", "app_count_at", "app_fill", "app_fill_n",
   "app_find", "app_hole", "app_push", "b_eq", "basis_pin_hit", "bb_go", "bb_memo", "bb_node",
   "binder_dom", "block_caps_at", "block_caps_at_er_copy", "block_caps_at_er_copy_go",
   "block_caps_ctor_names", "block_caps_fin", "block_caps_head", "block_caps_one", "block_counts",
   "block_counts_head", "block_counts_pure", "block_groups", "block_groups_go", "block_groups_one",
   "block_large_elim_allowed", "block_member_counts", "block_member_counts_find",
   "block_member_counts_go", "block_nested_bit", "block_nested_bit_go", "block_parts",
   "block_raw_rec", "block_raw_rec_go", "block_raw_rec_member", "block_rec_got",
   "block_rec_lps_ok", "block_rec_lps_ok_go", "block_rec_lps_one", "block_rec_name_set_ok",
   "block_rec_names_unreserved", "block_rec_split_own_aux", "block_rec_want",
   "block_rec_want_aux_names", "block_shape", "block_shape_all_ctors", "block_shape_all_ctors_go",
   "block_shape_build", "block_shape_ctors_copy", "block_shape_ctors_of", "block_shape_fin",
   "block_shape_large", "block_shape_lps", "block_shape_major_idx_at", "block_shape_member_names",
   "block_shape_members_of", "block_shape_n_idxs", "block_shape_names_of", "block_shape_nest_ctx",
   "block_shape_num_ctors", "block_shape_pack", "block_shape_pins_ctors",
   "block_shape_pins_formers", "block_shape_pins_ok", "block_shape_pins_recs",
   "block_shape_recs_of", "block_shape_result_sort", "block_shape_rhss_of",
   "block_shape_rule_prefix_at", "block_shape_seal", "block_shape_tail", "block_shape_with_sort",
   "block_split", "block_split_ctors", "block_split_recs", "bm_clear", "bm_find", "bm_put",
   "bool_ctor_ok", "bool_ctor_typed", "bvar_b", "bvar_find", "bvar_push", "canon_ctx",
   "canon_eq_list", "canon_expr_eq", "canon_level_eq", "canon_level_list_eq", "canon_levels_eq",
   "canon_name_map", "canon_names", "canon_names_go", "canon_rules_eq", "caps_eq", "caps_eq_a",
   "caps_eq_b", "caps_eq_c", "caps_never_zero", "caps_parts", "caps_wr", "cert_ctx",
   "cert_ctx_main", "cert_ctx_pins", "cert_div_mod", "cert_div_mod_eqs", "cert_div_mod_guards",
   "cert_eq", "cert_gcd", "cert_guard", "cert_halves", "cert_land", "cert_lor", "cert_lor_rhs",
   "cert_rec_rhs", "cert_shift_left", "cert_shift_right", "cert_two_eqs", "cert_xor",
   "cert_xor_rhs", "char_of_nat_ty_ok", "char_ty_ok", "check_basis_decl",
   "check_block_classes_count", "check_block_classes_keys", "check_block_classes_one_per_member",
   "check_block_inds_cv_tas", "check_block_inds_cv_tas_go", "check_block_pass_rec",
   "check_block_positivity_init", "check_block_positivity_nfs",
   "check_block_positivity_nfs_member", "check_decl_quot", "check_field_sort_bound",
   "ci_canon_defn", "ci_canon_eq", "ci_canon_rec", "ci_eq", "ci_eq_rest", "ci_to_cv",
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
   "class_rule_ok_domains", "class_seeds", "class_slot_is_minor", "cons_block_ctors",
   "cons_block_inds", "cons_block_recs_push", "cons_sum_ctors", "const_e", "const_find",
   "const_name_of", "const_push", "consts_resolve_all", "consts_resolve_ffast", "cr_leaf",
   "cr_lit_pins", "crf_go", "crm_clear", "crm_find", "crm_put", "ct_clear", "ct_find", "ct_put",
   "ctl_get", "ctor_family", "ctor_info_rec", "ctor_member", "ctors_have_name", "cv_canon_eq",
   "cv_clear", "cv_eq", "cv_find", "cv_lps", "cv_new", "cv_put", "cv_rd", "cv_wr", "de_clear",
   "de_find", "de_put", "dec_len", "defeq_no_fvars", "depth", "depth_go", "depth_node", "der_b",
   "dind_copy", "div_add", "div_mod_cert_applied", "div_mod_cert_proofs", "div_mod_cert_stmts",
   "div_mod_cert_stmts_at", "div_mod_decl_pin", "div_mod_env_guard", "div_mod_slot",
   "div_mod_type_pins", "div_shl1", "div_step", "div_sub", "dlp_copy", "dp_clear", "dp_find",
   "dp_put", "e_rec_get", "e_view", "ek_copy", "env_erase", "env_find", "env_ix", "env_pop_temp",
   "env_push", "env_push_table", "env_row_get", "env_row_set", "eq_at1", "er_copy", "er_from_iw",
   "er_from_iw_go", "er_put5", "er_sl_at", "er_sl_eq", "er_slice_eq", "er_to_iw", "erase_each",
   "erase_fvar_tys", "erase_installed", "erase_installed_tables", "erec_alloc", "erec_ci",
   "erec_cp", "erec_push", "erec_rd1", "erec_rd2", "erec_rd3", "erec_rd4", "erec_rd5", "erec_vg",
   "erec_wr1", "erec_wr2", "erec_wr3", "erec_wr4", "erec_wr5", "eta_ctor_shape", "eta_fab_args",
   "eta_projs", "expr_get_d", "expr_view_ok", "field_doms_resolve", "field_sort_zero", "find_is",
   "find_pinned", "find_pinned_cv", "find_proj", "find_rule", "find_table", "fire_ok", "fl_find",
   "flush_caches", "fm_clear", "fm_find", "fm_put", "forall_find", "forall_push", "fr_go",
   "fr_memo", "fr_node", "fv_map_at", "fvar_b", "fvar_find", "fvar_head", "fvar_push",
   "fvar_type_d", "fvar_type_ds", "gcd_step", "gen_rec_check_any_no_member",
   "gen_rec_check_former_tys", "gen_rec_check_minor_ok", "gen_rec_check_pop_all", "get_app_args",
   "get_app_args_f", "get_app_fn", "get_app_fn_f", "get_app_spine", "has_fvar", "has_fvar_fast",
   "has_loose_b_var_b_fast", "has_loose_b_var_b_go", "has_loose_b_var_b_ins", "has_str_lit_go",
   "hb_clear", "hb_find", "hb_put", "head_and_args", "head_hint", "head_is_proj",
   "head_proof_const", "head_proof_proj", "head_proof_pw", "head_type_const", "head_type_pw",
   "head_type_res", "hint_eq", "hint_lt", "i1l_app", "i1l_clear", "i1l_find", "i1l_forall",
   "i1l_go", "i1l_lam", "i1l_let", "i1l_proj", "i1l_put", "idx_args_resolve", "if_clear",
   "if_find", "if_put", "ik_copy", "il_app", "il_bvar", "il_forall", "il_go", "il_lam", "il_let",
   "il_proj", "ilm_find", "ilp_find", "ilpl_find", "ilpls_find", "imax_find", "imax_push",
   "in_clear", "in_find", "in_put", "ind_block_to_erec", "ind_caps_check", "ind_copy_go",
   "ind_info_rec", "ind_params_ok", "ind_rec_copy", "index_promoted", "index_promoted_tables",
   "infer_lit", "inst1", "inst_app", "inst_entry", "inst_forall", "inst_go", "inst_lam",
   "inst_let", "inst_pis_at_lift", "inst_pis_with", "inst_proj", "inst_spine",
   "install_basis_decl", "install_basis_decls", "instantiate1_fast", "instantiate1_lift_fast",
   "intern_app", "intern_bvar", "intern_const", "intern_forall", "intern_fvar", "intern_imax",
   "intern_lam", "intern_letE", "intern_lit", "intern_lit_str", "intern_ls", "intern_ls_iw",
   "intern_max", "intern_nanon", "intern_nnum", "intern_nstr", "intern_param", "intern_proj",
   "intern_sort", "intern_succ", "intern_zero", "io_clear", "io_find", "io_neutral", "io_put",
   "iota_case3", "iota_certs_full_parts", "iota_ctor_never_prop", "iota_rec_head", "is_bool_true",
   "is_ctor_app", "is_eager_reduce", "is_nat_zero", "is_none", "is_proof_fast", "is_some",
   "is_str_lit", "iw_alloc", "iw_copy", "iw_pool", "iw_reset", "iw_to_spn", "keys_ok", "keys_push",
   "keys_push_iw", "lam_find", "lam_pair", "lam_proj", "lam_push", "lams_inst", "lazy_fold_ok",
   "leaf_mem", "letE_find", "letE_push", "lf_clear", "lf_find", "lf_put", "lh_er_copy", "lh_mk",
   "lh_push", "lift_app", "lift_entry", "lift_forall", "lift_go", "lift_lam", "lift_let",
   "lift_proj", "limbs_eq", "list_cons_ty_ok", "list_nil_ty_ok", "list_ty_ok", "lit_eq",
   "lit_find", "lit_find_str", "lit_guard_has", "lit_hash", "lit_match", "lit_match_str",
   "lit_push", "lit_push_str", "lit_to_ctor_if_nat", "loose_bvars_bounded_fast", "lp_lookup",
   "lp_rb_let", "lp_spw", "lp_substl", "lp_substpw", "lq_clear", "lq_find", "lq_put", "ls_find",
   "ls_match", "ls_node", "ls_push", "lsb_find", "lsq_clear", "lsq_find", "lsq_put", "lv_apd",
   "lv_cases", "lv_cases_at", "lv_comb", "lv_dist1", "lv_dist2", "lv_eq", "lv_equiv", "lv_equivs",
   "lv_imax", "lv_imax_l", "lv_imax_r", "lv_intern", "lv_leq", "lv_leq_top", "lv_lookup", "lv_mem",
   "lv_node", "lv_nz", "lv_rest", "lv_simp", "lv_spw", "lv_sub_int", "lv_subsimp", "lv_subst",
   "lv_substl", "lv_zero", "lv_zero_caps", "lvl_eq", "lvl_eq_c", "lvl_eq_fueled", "lvl_eq_rec",
   "lvl_eq_true", "lvls_eq", "lvls_eq_c", "lvls_eq_rec", "m2c_const_view", "ma_clear", "ma_find",
   "ma_put", "mac_hi", "matches_pin", "max_find", "max_push", "mc_clear", "mc_find", "mc_put",
   "member_idx_at", "member_names_copy", "memo_get", "memo_push", "mentions_any_const",
   "mentions_any_go", "mentions_any_node", "mentions_const", "mentions_const_go", "mk_app",
   "mk_app_n", "mk_app_n_f", "mk_app_n_from", "mk_forall", "mk_lam", "mk_let", "mk_proj",
   "mk_target_major", "n_idxs_copy", "name_rec", "name_rec_i", "nanon_find", "nanon_push",
   "nat_add", "nat_add_lit", "nat_ap1", "nat_ap2", "nat_beq_lit", "nat_bin_op_name", "nat_ble_lit",
   "nat_cmp", "nat_div_lit", "nat_div_mod_names", "nat_divmod", "nat_eq_be", "nat_eq_bl",
   "nat_eq_ctx", "nat_eq_disp", "nat_eq_list2", "nat_eq_list3", "nat_eq_list4", "nat_eq_mu",
   "nat_eq_po", "nat_eq_pr", "nat_eq_un", "nat_gcd", "nat_gcd_lit", "nat_ind_ok", "nat_land",
   "nat_land_lit", "nat_limb", "nat_lit_supported", "nat_lit_to_ctor", "nat_lor", "nat_lor_lit",
   "nat_mod_lit", "nat_mul", "nat_mul_lit", "nat_one", "nat_op_bool_ctors", "nat_op_cod",
   "nat_op_deps", "nat_op_deps_stored", "nat_op_equations", "nat_op_guard", "nat_op_is_wf",
   "nat_op_names", "nat_op_pins", "nat_op_pins_a", "nat_op_pins_b", "nat_op_pins_c",
   "nat_op_result", "nat_op_stored", "nat_op_stored_ok", "nat_op_stored_ok_all",
   "nat_op_ty_pinned", "nat_pow", "nat_pow_lit", "nat_pred", "nat_pred_lit", "nat_shl",
   "nat_shl_lit", "nat_shr", "nat_shr_lit", "nat_sub", "nat_sub_lit", "nat_succ_lit",
   "nat_succ_ok", "nat_trim", "nat_var", "nat_xor", "nat_xor_lit", "nat_zero_ok",
   "nest_accept_group", "nest_arity", "nest_block_of", "nest_canon_crest", "nest_canon_sub",
   "nest_cont_checks", "nest_cont_new_active", "nest_cont_new_finish", "nest_cont_params_closed",
   "nest_container", "nest_container_ctors", "nest_container_ctors_go", "nest_crest",
   "nest_ctor_entry", "nest_ctor_entry_strip", "nest_ctor_nf", "nest_ctors_res_ok",
   "nest_ctors_u4", "nest_ctx_hi_at", "nest_ctx_root_holes", "nest_ctx_root_holes_go",
   "nest_ds_closed", "nest_ds_closed_go", "nest_field_kind_flat", "nest_frame_grp",
   "nest_frame_holes", "nest_frame_mates", "nest_frame_mates_go", "nest_group_ctors",
   "nest_hole_at", "nest_hole_img", "nest_hole_img_ds", "nest_hole_img_ds_go",
   "nest_hole_img_frame", "nest_hole_img_root", "nest_holes", "nest_holes_go", "nest_key_eq",
   "nest_key_map", "nest_keys_contains", "nest_kinds_flat", "nest_kinds_flat_inner",
   "nest_kinds_flat_mid", "nest_occ", "nest_occ_any", "nest_occ_go", "nest_occ_node", "nest_phs",
   "nest_phs_go", "nest_pos_fvar", "nest_pos_hole_kind", "nest_res_head", "nest_seed_of",
   "nest_seed_of_go", "nest_seeds_fuel", "nest_walk_stack", "nnum_find", "nnum_push", "no_clear",
   "no_find", "no_put", "not_proof_fast", "nstr_find", "nstr_match", "nstr_push", "num_ctors_of",
   "of_reduce_ax_ok", "of_reduce_op", "of_reduce_pin_a", "opa_go", "param_find", "param_levels",
   "param_levels_go", "param_push", "pci_ctor", "pci_defn", "pci_ind", "pci_mk", "pci_plain",
   "pci_rec", "pe_app", "pe_arm", "pe_at", "pe_clear", "pe_const", "pe_find", "pe_forall",
   "pe_lam", "pe_let", "pe_lit", "pe_proj", "pe_put", "peel_pis", "peel_pis_w", "peel_push",
   "pend_push", "ph_app", "pi_app", "pi_binders", "pi_bvar", "pi_const", "pi_doms_mention_any",
   "pi_doms_occ", "pi_forall", "pi_fvar", "pi_imax", "pi_lam", "pi_let", "pi_lit", "pi_lit_str",
   "pi_ls", "pi_max", "pi_nanon", "pi_nnum", "pi_nstr", "pi_param", "pi_proj", "pi_residual",
   "pi_result", "pi_result_f", "pi_sort", "pi_sort_tele_len", "pi_succ", "pi_zero", "pin_at",
   "pin_found", "pin_in", "pin_range_has", "pin_word", "pl_arm", "pl_at", "pl_clear", "pl_find",
   "pl_put", "pls_arm", "pls_clear", "pls_find", "pls_put", "pn_arm", "pn_at", "pn_clear",
   "pn_find", "pn_put", "pool_alloc0", "pool_copy", "pool_copy0", "pool_room", "proj_a", "proj_b",
   "proj_cert", "proj_find", "proj_push", "proj_wr", "promote_caps", "promote_ci",
   "promote_ci_list", "promote_clear", "promote_cv", "promote_e", "promote_e_list", "promote_fire",
   "promote_l", "promote_l_list", "promote_l_pool", "promote_ls", "promote_n", "promote_n_list",
   "promote_new", "promote_new_consts", "promote_new_tables", "promote_proj_table",
   "promote_proj_tables", "promote_rule", "promote_rules", "promote_slice", "promote_vg",
   "proof_pw", "ps_at", "ptr_list_names", "ptr_names_copy", "pw_eq", "quick_sort", "quot_pin_hit",
   "ra_clear", "ra_find", "ra_put", "raw_nat_lit", "rci_block", "rci_block_to", "rci_caps",
   "rci_ci", "rci_cv", "rci_fresh", "rci_lvls_to", "rci_name_sl", "rci_names_to", "rci_rule",
   "rci_rules_to", "rci_slot", "rec2", "rec3", "rec4", "rec5", "rec6", "rec_block",
   "rec_fire_levels", "rec_info_rec", "rec_rule_bits", "rec_rule_eta_of", "rec_rule_k",
   "rec_rule_k_of", "rec_target_of", "reduce_cert_var", "reduce_decl_pin", "reduce_elem_ok",
   "reduce_op_cv_a", "reduce_proj_arg", "reduce_proj_fire", "reduce_proj_head", "reduce_stored_ok",
   "replace_apps", "replace_apps_go", "replace_apps_node", "replace_fvars", "replace_fvars_go",
   "replace_fvars_node", "reserved_contains", "reserved_contains_w", "reserved_from",
   "reserved_rec_name", "residual_pw", "rf_bank_enter", "rf_bank_leave", "rf_find", "rf_put",
   "rom_and_pin", "rom_basis_decls", "rom_basis_decls_a", "rom_ci", "rom_cv", "rom_ex_leaf",
   "rom_ex_one", "rom_ex_ref", "rom_ex_two", "rom_expr", "rom_expr_pin", "rom_exprs_to",
   "rom_level", "rom_levels", "rom_lit", "rom_lvls_go", "rom_name", "rom_pin_sets", "rom_put",
   "rom_u64", "rr_clear", "rr_find", "rr_put", "rset_clear", "rset_find", "rset_put", "rule_copy",
   "rule_eq_a", "rule_eq_b", "rule_eq_but_rhs", "rule_wr", "rules_eq", "rules_to_erec",
   "rules_to_erec_go", "same_const_heads", "scratch_drop", "scratch_enter", "scratch_reset",
   "sl_all_in", "sl_append", "sl_cons", "sl_contains", "sl_eq", "sl_find", "sl_get", "sl_getd",
   "sl_new1", "sl_nodup", "sl_set_eq", "sl_snoc", "sle_go", "slp_go", "sls_go", "sort_find",
   "sort_push", "spine_head", "spn_get", "spn_ls", "spn_pool", "spn_push", "spn_to_iw",
   "stack_cover", "std_ax_family", "std_axiom_ok", "stk_pool", "stk_push", "stmt1",
   "str_cons_spine", "str_ctor_pre", "str_cv", "str_lit_ctor", "str_lit_supported", "str_ls1",
   "str_param_sort", "str_sup_1", "str_sup_2", "str_sup_3", "str_sup_4", "str_sup_5", "str_sup_6",
   "str_sup_7", "str_utf8_char", "string_of_list_ty_ok", "string_ty_ok", "strip_lams", "strip_pis",
   "struct_ctor_resid_ok", "struct_elim_level", "struct_proj_arg_p", "struct_proj_bodies",
   "struct_proj_bodies_go", "struct_proj_guards", "struct_proj_guards_col",
   "struct_proj_guards_row", "struct_proj_ps", "struct_ps_at", "struct_ps_at_go",
   "struct_used_later", "struct_used_later_go", "struct_used_later_list", "sub_borrow",
   "subst_const0", "subst_const0_list", "subst_const0_pairs", "subst_const_all", "subst_pw_at",
   "succ_find", "succ_push", "sum_rules", "sum_rules_go", "ta_clear", "ta_find", "ta_put",
   "target_abs", "target_abs_const", "target_abs_go", "target_abs_node", "target_canon_params",
   "target_ctors_of", "target_holes", "target_k53_tele", "target_major_at", "target_major_default",
   "target_major_of_member", "target_major_of_outside_closed", "target_major_of_outside_occ",
   "target_pi_doms_with", "target_rec_pins", "target_rec_pins_names", "target_rec_pins_split",
   "tbl_at", "tbl_cnt", "tbl_grown", "tbl_ix", "tbl_put", "tbl_row_get", "tbl_row_set",
   "tgt_rule_nested", "tgt_stored_rules_remap", "tower_slots_all", "trust_compiler_ok",
   "type_pin_guard", "type_pin_stored", "type_pins_guard", "type_sort_pw", "unfoldable_head",
   "unresolved_consts_error", "unwrap_id_defs", "unwrap_step", "vg_rd", "vg_wr", "view_ls",
   "view_ls_len", "wc_clear", "wc_find", "wc_put", "wh_clear", "wh_find", "wh_put",
   "whnf_walk_fuel", "wk_clear", "wk_find", "wk_put", "ws_find", "zero_find", "zero_push"]

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

theorem leafA_pins : PINS ∉ leafA := by decide +kernel
theorem leafA_memo : (50 : ArrId) ∉ leafA ∧ (49 : ArrId) ∉ leafA := by decide +kernel
theorem leafA_walk : (151 : ArrId) ∉ leafA ∧ (152 : ArrId) ∉ leafA ∧ (153 : ArrId) ∉ leafA := by
  decide +kernel
theorem leafA_lp : (52 : ArrId) ∉ leafA ∧ (53 : ArrId) ∉ leafA ∧ (54 : ArrId) ∉ leafA := by
  decide +kernel
theorem leafC_memo : (50 : Word) ∉ leafC ∧ (48 : Word) ∉ leafC := by decide +kernel
theorem leafC_walk : (152 : Word) ∉ leafC ∧ (154 : Word) ∉ leafC ∧ (156 : Word) ∉ leafC := by
  decide +kernel
theorem leafC_lp : (54 : Word) ∉ leafC ∧ (56 : Word) ∉ leafC ∧ (58 : Word) ∉ leafC := by
  decide +kernel

/-- **The leaves' write set.** -/
def LeafClosed (p : Prog) : Prop := closedA p leafA leafC leafFns = true

end L.Arena
