module

public import ConAgua.Arena.LeafFrame
meta import ConAgua.Arena.LeafFrame

@[expose] public section

/-!
# The loop's callees outside the inductive arm (lane `indproofs4`, helper `lm`)

The inductive arm `check_ind_decl` needs its stage's memos well formed (`IndMemos`, `LoopT.lean`:
the stage memos, arrays 201‥208 and `CTL` 202‥219; `instantiate1Lift`'s, array 51 and `CTL[52]`;
`consts_resolve_ffast`'s, array 155 and `CTL[158]`). The loop's other callees leave them alone but
for `consts_resolve_ffast`, which the declaration arms call (the gates' `install_value_guards`)
and which keeps its own memo well formed: `imFns` is the call closure of those callees in the
checker's program with `consts_resolve_ffast` a leaf, and `IndMemoClosed` its write set away from
the three memos' words (decided for the checker's program in `Checker/IndMemoClosed.lean`).
-/

namespace L.Arena

/-- The arrays the loop's non-inductive callees may write: all but the inductive stage's memos. -/
def imA : List TieredArray :=
  checkerWordArrays.filter fun b => b ≠ ILFM ∧ b ≠ Stubs.CRM ∧ (b.arr < 201 ∨ 208 < b.arr)

/-- The `CTL` words the loop's non-inductive callees may write: all but the memos' epochs. -/
def imC : List Word :=
  ((List.range 1024).filter fun x => x ≠ 52 ∧ x ≠ 158 ∧ (x < 202 ∨ 219 < x)).map UInt64.ofNat

theorem imA_spec : ∀ b ∈ imA, b ≠ ILFM ∧ b ≠ Stubs.CRM ∧ (b.arr < 201 ∨ 208 < b.arr) := by
  intro b hb; simp only [imA, List.mem_filter, decide_eq_true_eq] at hb; exact hb.2

theorem imC_spec : ∀ x ∈ imC, x.toNat ≠ 52 ∧ x.toNat ≠ 158 ∧ (x.toNat < 202 ∨ 219 < x.toNat) := by
  intro x hx
  simp only [imC, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at hx
  obtain ⟨n, ⟨h1, h2⟩, rfl⟩ := hx
  have : (UInt64.ofNat n).toNat = n := by simp; omega
  rw [this]; exact h2

/-- The leaves of `imFns`: `consts_resolve_ffast` and `struct_used_later` (infer_proj's field check,
which clears and walks the stage's `hb` memo), each writing its own memo. -/
def imLeaves : List FnName :=
  ["consts_resolve_ffast", "struct_used_later", "has_loose_b_var_b_fast", "has_loose_bvar_in"]

/-- **The loop's callees outside the inductive arm**: the call closure in the checker's program
of the declaration arms but the inductive one, `install_value`, `and_pin_ok`, `is_none`,
`is_some`, `ind_block_to_erec`, `flush_caches`, `scratch_enter`, `reduce_members` (`check_block`'s
member reduction) and `check_block_inds`, `check_block_ctors`, `block_nest_ctx` (`check_block_pass`'s
first steps, which write no memo), with `consts_resolve_ffast` and
`struct_used_later` leaves (`imLeaves`). It does not contain `check_ind_decl`. -/
def imFns : List FnName :=
  ["ab_clear", "ab_find", "ab_fvb", "ab_node", "ab_put", "abs_app", "abs_entry", "abs_forall",
   "abs_go", "abs_lam", "abs_let", "abs_proj", "abstract1_fast",
   "all_level_params_defined", "alpd_go", "alpd_ls", "and_block_named", "and_pin_ok",
   "and_rescue_slots", "apd_clear", "apd_find", "apd_put", "app_count", "app_count_at", "app_fill",
   "app_fill_n", "app_find", "app_push", "ar_app", "ar_entry", "ar_forall", "ar_go", "ar_lam",
   "ar_let", "ar_node", "ar_proj", "b_eq", "base_row_get", "bb_go", "bb_memo", "bb_node",
   "beta_peel", "binder_dom", "block_caps_at", "member_never_zero", "block_caps_at_er_copy", "block_caps_at_er_copy_go",
   "block_caps_ctor_names", "block_caps_fin", "block_caps_head", "block_caps_one", "block_nest_ctx",
   "block_shape_declared", "block_shape_formers", "block_shape_lps", "block_shape_member_names",
   "block_shape_n_idxs", "block_shape_nest_ctx", "block_shape_with_sort", "bm_clear", "bm_find",
   "bm_put", "bool_ctor_ok", "bool_ctor_typed", "bvar_b", "bvar_find",
   "bvar_push", "canon_ctx", "canon_eq_list", "canon_expr_eq", "canon_level_eq",
   "canon_level_list_eq", "canon_levels_eq", "canon_name_map", "canon_names", "canon_names_go",
   "canon_rules_eq", "caps_eq", "caps_eq_a", "caps_eq_b", "caps_eq_c", "caps_never_zero",
   "caps_parts", "caps_wr", "cert_ctx", "cert_ctx_main", "cert_ctx_pins", "cert_div_mod",
   "cert_div_mod_eqs", "cert_div_mod_guards", "cert_eq", "cert_gcd", "cert_guard", "cert_halves",
   "cert_land", "cert_lor", "cert_lor_rhs", "cert_rec_rhs", "cert_shift_left", "cert_shift_right",
   "cert_two_eqs", "cert_xor", "cert_xor_rhs", "certify_nat_eqs", "char_of_nat_ty_ok", "char_ty_ok",
   "check_basis_decl", "check_block_agree", "check_block_agree_one", "check_block_ctors",
   "check_block_doms_at", "check_block_inds", "check_block_tele", "check_block_teles",
   "check_constant_val", "check_decl_axiom", "check_decl_defn", "check_decl_opaque",
   "check_decl_quot", "check_decl_thm", "check_defn_val", "check_div_mod_certs",
   "check_div_mod_pin", "check_div_mod_pin_at", "check_div_mod_pin_at_fe2",
   "check_div_mod_pin_loop", "check_div_mod_pin_value", "check_field_sort_bound",
   "check_guard_rows", "check_opaque_val", "check_proj_guard", "check_quot_record",
   "check_reduce_pin", "check_reduce_pin_pre", "check_struct_doms_at", "check_struct_field_sorts_i",
   "check_structural_nat_pin", "check_structural_nat_pin_at_fe2", "check_sum_ctor",
   "check_sum_ctor_tail", "check_sum_ctors", "check_sum_tele", "check_thm_val", "check_type_pins",
   "ci_at_lps", "ci_canon_defn", "ci_canon_eq", "ci_canon_rec", "ci_eq", "ci_eq_rest", "ci_to_cv",
   "close_telescope", "close_telescope_go", "cons_block_inds", "const_e", "const_find", "const_push",
   "const_ty_at", "const_val_at", "consts_resolve_all", "ct_clear", "ct_find", "ct_put", "ctl_get",
   "ctor_family", "iota_no_cert", "rec_fire_level_count", "cv_at_lps", "cv_canon_eq", "cv_clear", "cv_eq", "cv_find", "cv_lps", "cv_new",
   "cv_put", "cv_rd", "cv_wr", "de_clear", "de_find", "de_put", "declined_at_definition", "defeq",
   "defeq_arg", "defeq_binders", "defeq_domain", "defeq_binders_inner", "binder_pair",
   "quick_binders", "defeq_body", "defeq_lazy", "ctor_head_against", "ctor_target",
   "ctor_target_for", "defeq_e", "defeq_list", "defeq_list_rev", "defeq_lst", "defeq_no_fvars",
   "defeq_offset", "defeq_proj_pair", "defeq_spine", "defeq_spine2", "defeq_stuck", "defeq_tail",
   "defn_div_gate",
   "defn_nat_cert", "defn_nat_gate", "delta_quick", "der_b", "der_bv", "dind_copy", "div_add",
   "div_mod_cert_applied", "div_mod_cert_guard", "div_mod_cert_proofs", "div_mod_cert_stmts",
   "div_mod_cert_stmts_at", "div_mod_certs_guard", "div_mod_certs_guard_go", "div_mod_decl_pin",
   "div_mod_env_guard", "div_mod_pin_guard", "div_mod_slot", "div_mod_type_pins", "div_2by1", "div_kstep", "div_mod1", "div_modk", "div_norm", "div_recip", "div_submul", "dlp_copy", "e_rec_get", "e_view", "ek_copy", "ensure_sort",
   "ensure_sort_core", "env_erase", "env_find", "env_ix", "env_pop_temp", "env_push", "lit_name_at", "lits_stored", "env_set_flags", "env_row_get",
   "env_row_set", "eq_at1", "eq_stored", "er_copy", "er_copy_er", "er_put_ci", "er_sl_at", "er_sl_eq",
   "er_slice_eq", "er_to_iw", "erase_installed", "erase_installed_tables", "erec_alloc", "erec_ci",
   "erec_cp", "erec_push", "erec_put", "erec_rd1", "erec_rd2", "erec_rd3", "erec_rd4", "erec_rd5",
   "erec_vg", "erec_wr1", "erec_wr2", "erec_wr3", "erec_wr4", "erec_wr5", "eta_cert",
   "eta_cert_body", "eta_cert_ty", "eta_ctor_shape", "eta_fab_args", "eta_projs", "eta_rescue_table",
   "expr_view_ok", "fab_scope_ok", "field_doms_resolve", "field_sort_zero", "find_is",
   "find_pinned", "find_pinned_cv", "find_proj", "find_rule", "find_table", "fire_levels_at",
   "fire_ok", "fl_clear", "fl_find", "fl_go", "fl_node", "fl_put", "flush_caches", "fm_clear",
   "fm_find", "fm_put", "forall_find", "forall_push", "former_def_headed", "former_never_zero",
   "former_never_zero_at", "family_never_zero_at", "former_res_sort", "former_sort_loop", "former_z", "fr_go", "fr_memo",
   "fr_node", "fvar_find", "fvar_push", "fvar_type_d", "fvar_type_ds", "gcd_step", "get_app_args",
   "get_app_args_f", "get_app_fn", "get_app_fn_f", "get_app_spine", "ground_guards", "has_fvar",
   "has_fvar_fast", "has_str_lit_go", "head_and_args", "head_hint", "head_is_proj",
   "head_proof_const", "head_proof_proj", "head_proof_pw", "head_type_const", "head_type_pw",
   "head_type_res", "hint_eq", "hint_lt", "idx_args_resolve", "if_clear", "if_find", "if_put",
   "il_app", "il_bvar", "il_forall", "il_go", "il_lam", "il_let", "il_proj", "ilg_app",
   "ilg_forall", "ilg_go", "ilg_lam", "ilg_let", "ilg_proj", "ilm_clear", "ilm_find", "ilm_fit",
   "ilm_put", "ilp_clear", "ilp_find", "ilp_put", "ilpl_clear", "ilpl_find", "ilpl_put",
   "ilpls_clear", "ilpls_find", "ilpls_put", "imax_find", "imax_push", "in_clear", "in_find",
   "in_put", "ind_block_to_erec", "ind_caps_check", "ind_copy_go", "ind_info_rec", "ind_rec_copy",
   "infer", "infer_app", "infer_app_io", "infer_body", "infer_body_io", "infer_const",
   "infer_forall", "infer_forall_io", "infer_io", "infer_lam", "infer_lam_io", "infer_lam_result",
   "infer_lams", "infer_lams_leaf", "infer_let", "infer_lit", "infer_pis", "infer_pis_leaf",
   "infer_proj", "infer_proj_at", "infer_spine", "infer_spine_arg", "infer_spine_io",
   "infer_type_core", "inst1", "inst_app", "inst_entry", "inst_forall", "inst_go", "inst_lam",
   "inst_let", "inst_list", "inst_lp", "inst_lp_core", "inst_pis_with", "inst_proj", "inst_spine",
   "inst_spine_pins", "install_basis_decl", "install_header",
   "install_value", "install_value_guards", "instantiate1_fast", "intern_app", "intern_bvar",
   "intern_const", "intern_forall", "intern_fvar", "intern_imax", "intern_lam", "intern_letE",
   "intern_lit", "intern_lit_str", "intern_ls", "intern_ls_iw", "intern_max", "intern_nanon",
   "intern_nnum", "intern_nstr", "intern_param", "intern_proj", "intern_sort", "intern_succ",
   "intern_zero", "io_clear", "io_find", "io_neutral", "io_put", "iota_case3", "iota_case3_at",
   "iota_certs_full", "iota_certs_full_aux", "iota_certs_full_check", "iota_certs_full_flush",
   "iota_certs_full_forall", "iota_certs_full_parts", "iota_ctor_never_prop", "iota_index_ok",
   "iota_rec_at", "iota_rec_cmp", "iota_rec_fam", "iota_rec_fire", "iota_rec_fire2", "eidx_copy_upto",
   "iota_rec_major", "iota_rec_vck", "is_def_eq_core", "is_eager_reduce", "is_nat_zero", "is_none", "is_proof_fast", "is_some",
   "is_str_lit", "iw_alloc", "iw_copy", "iw_pool", "keys_ok", "keys_push", "lam_find", "lam_proj", "lam_push", "lazy_delta_proj_reduction",
   "lazy_delta_reduction", "lazy_delta_step", "lazy_fold_ok", "lazy_iter", "lazy_nat", "ldpr_exit",
   "lds_both", "lds_left", "lds_right", "lds_same", "lds_unfold2", "leaf_guard", "leaf_mem",
   "letE_find", "letE_push", "lf_clear", "lh_contains", "lh_mk", "lh_push", "limbs_eq",
   "list_cons_ty_ok", "list_nil_ty_ok", "list_ty_ok", "lit_eq", "lit_find", "lit_find_str",
   "lit_hash", "lit_major_to_ctor", "lit_match", "lit_match_str", "lit_push", "lit_push_str",
   "lit_shape_ok", "lit_to_ctor_if_nat", "loose_bvars_bounded_fast", "lp_app", "lp_forall",
   "lp_fvar", "lp_go", "lp_lam", "lp_let", "lp_let_tail", "lp_lookup", "lp_proj", "lp_rb_let",
   "lp_substl", "lq_clear", "lq_find", "lq_put", "ls_find", "ls_match", "ls_node", "ls_push",
   "lsb_clear", "lsb_find", "lsb_go", "lsb_node", "lsb_put", "lsq_clear", "lsq_find", "lsq_put",
   "lv_always_zero", "lv_apd", "lv_cases", "lv_cases_at", "lv_comb", "lv_dist1", "lv_dist2",
   "lv_eq", "lv_equiv", "lv_equivs", "lv_imax", "lv_imax_l", "lv_imax_r", "lv_intern", "lv_leq",
   "lv_leq_top", "lv_lookup", "lv_mem", "lv_never", "lv_node", "lv_rest", "lv_simp", "lv_spw",
   "lv_sub_int", "lv_subsimp", "lv_subst", "lv_substl", "lv_zero", "lv_zero_where_zero", "lvl_eq",
   "lvl_eq_c", "lvl_eq_fueled", "lvl_eq_rec", "lvl_eq_true", "lvls_eq", "lvls_eq_c", "lvls_eq_rec",
   "m2c_and", "m2c_and2", "m2c_arms", "m2c_check", "m2c_const_view", "m2c_ctor", "m2c_eta",
   "m2c_eta2", "m2c_head", "m2c_k", "m2c_k2", "m2c_pre", "mul_row", "sub_row", "mul_zeros", "kara_sum", "kara_prods", "kara_mid", "mul_win", "major_to_ctor", "major_to_ctor_rescue", "ctor_view", "prepare_major_whnf", "is_nat_succ_app", "matches_pin",
   "max_find", "max_push", "member_field_copy", "member_names_copy", "memo_get", "memo_push",
   "mk_app", "mk_app_n", "mk_app_n_from", "mk_forall", "mk_lam", "mk_let", "mk_proj", "n_idxs_copy",
   "nanon_find", "nanon_push", "nat_add", "add_n", "add_1", "nat_add_lit", "nat_ap1", "nat_ap2", "nat_beq_lit",
   "nat_bin_op_of_name", "nat_bin_op_result", "nat_ble_lit", "nat_cmp", "nat_div_lit", "nat_div_mod_names", "nat_divmod",
   "nat_eq_be", "nat_eq_bl", "nat_eq_ctx", "nat_eq_disp", "nat_eq_list2", "nat_eq_list3",
   "nat_eq_list4", "nat_eq_mu", "nat_eq_po", "nat_eq_pr", "nat_eq_un", "nat_gcd", "nat_gcd_lit",
   "nat_ind_ok", "nat_ind_at_cv", "nat_zero_at_cv", "nat_succ_at_cv", "nat_land", "and_n", "nat_land_lit", "nat_limb", "nat_lit_supported",
   "nat_lit_to_ctor", "nat_lor", "or_n", "copy_n", "nat_lor_lit", "nat_mod_lit", "nat_mul", "nat_mul_lit", "nat_one",
   "nat_op_bool_ctors", "nat_op_cod", "nat_op_deps", "nat_op_deps_stored", "nat_op_equations",
   "nat_op_guard", "nat_op_name", "nat_op_names", "nat_op_pins", "nat_op_pins_a",
   "nat_op_pins_b", "nat_op_pins_c", "nat_op_stored", "nat_op_stored_ok",
   "nat_op_ty_pinned", "nat_pow", "nat_pow_lit", "nat_pred", "nat_pred_lit",
   "limb_push", "lit_nat_sized", "nat_size_refused", "pow_nat", "pow_refused", "shift_left_refused", "size_bytes",
   "nat_shl", "shl_n", "zero_n", "nat_shl_lit", "nat_shr", "shr_n", "nat_shr_lit", "nat_sub", "sub_n", "sub_1", "nat_sub_lit", "nat_succ_lit",
   "nat_succ_ok", "nat_trim", "nat_var", "nat_xor", "xor_n", "copy_n", "nat_xor_lit", "nat_zero_ok", "nest_holes",
   "nest_holes_go", "nnum_find", "nnum_push", "not_proof_fast", "nstr_find", "nstr_match",
   "nstr_push", "of_reduce_ax_ok", "of_reduce_op", "of_reduce_pin_a", "opa_go",
   "open_pis_at_fvars_f", "opf_go", "param_find", "param_levels", "param_levels_go", "param_push",
   "pci_ctor", "pci_defn", "pci_ind", "pci_mk", "pci_plain", "pci_rec", "pe_app", "pe_arm", "pe_at",
   "pe_clear", "pe_const", "pe_find", "pe_forall", "pe_lam", "pe_let", "pe_lit", "pe_proj",
   "pe_put", "peel_pis", "peel_pis_w", "pend_push", "pi_app", "pi_bvar", "pi_const", "pi_forall", "pi_fvar", "pi_imax",
   "pi_lam", "pi_let", "pi_lit", "pi_lit_str", "pi_ls", "pi_max", "pi_nanon", "pi_nnum", "pi_nstr",
   "pi_param", "pi_proj", "pi_residual", "pi_result", "pi_sort", "pi_succ", "pi_zero", "pin_at",
   "pin_range_has", "pin_word", "pl_arm", "pl_at", "pl_clear", "pl_find", "pl_put", "pls_arm",
   "pls_clear", "pls_find", "pls_put", "pn_arm", "pn_at", "pn_clear", "pn_find", "pn_put",
   "pool_alloc0", "pool_copy", "pool_copy0", "pool_room", "prepare_major", "proj_a", "proj_b",
   "proj_cert", "proj_find", "proj_guard_fast", "proj_guard_row", "proj_guard_rows", "proj_guard_rows_at", "proj_guard_rows_go", "proj_guard_sort",
   "proj_lit_to_ctor", "proj_push", "proj_type_at", "proj_wr", "proof_irrel", "proof_irrel_half",
   "proof_pw", "prop_irrel", "ps_at", "pw_eq", "quick_defeq", "quick_sort", "quot_at", "quot_pin", "quot_pin_hit", "quot_preds_ok", "raw_nat_lit", "raw_table",
   "rci_block", "rci_block_to", "rci_caps", "rci_ci", "rci_cv", "rci_fresh", "rci_lvls_to",
   "rci_name_sl", "rci_names_to", "rci_rule", "rci_rules_to", "rci_slot", "rec2", "rec3", "rec5",
   "rec_block", "rec_fire_args", "rec_fire_levels", "rec_rule_k", "reduce_cert_var",
   "reduce_decl_pin", "reduce_elem_ok", "reduce_member", "reduce_members", "reduce_nat",
   "reduce_nat_ap", "reduce_nat_head", "reduce_nat_k", "reduce_nat_op", "reduce_nat_succ",
   "reduce_op_cv_a", "reduce_pin_guard", "reduce_proj_arg", "reduce_proj_core",
   "reduce_proj_fire", "reduce_proj_head", "reduce_stored_ok", "reduced_former",
   "reserved_contains", "reserved_from", "residual_pw", "rom_and_pin",
   "rom_basis_decls", "rom_basis_decls_a", "rom_ci", "rom_cv", "rom_ex_leaf", "rom_ex_leaf_c",
   "rom_ex_one", "rom_ex_one_c", "rom_ex_ref", "rom_ex_ref_c", "rom_ex_two", "rom_ex_two_c",
   "rom_expr", "rom_expr_c", "rom_expr_pin", "rom_exprs_to", "rom_exprs_to_c", "rom_level",
   "rom_level_c", "rom_levels", "rom_levels_c", "rom_lit", "rom_lvls_go", "rom_lvls_go_c",
   "rom_name", "rom_name_c", "rom_pin_sets", "rom_put", "rom_put_c", "rom_u64", "rom_u64_c",
   "rr_clear", "rr_find", "rr_put", "rset_clear", "rset_find", "rset_put", "rule_eq_a", "rule_eq_b",
   "rule_eq_but_rhs", "rule_body_at", "lam_body", "rule_wr", "rules_at_lps_go", "rules_eq", "same_const_heads",
   "scratch_drop", "scratch_enter", "scratch_reset", "sl_cons", "sl_contains", "sl_eq", "sl_find",
   "sl_get", "sl_getd", "sl_memo", "sl_new1", "sl_nodup", "sl_snoc", "sle_go", "slp_go", "sls_go",
   "sls_memo", "sort_find", "sort_push", "spine_cmp", "spine_head", "spn_get", "spn_ls", "spn_pool",
   "spn_push", "spn_to_er", "spn_to_iw", "stack_cover", "std_ax_family", "std_axiom_ok", "stk_pool",
   "stk_push", "stmt1", "str_cons_spine", "str_ctor_pre", "str_cv", "str_lit_ctor",
   "str_lit_supported", "str_ls1", "str_param_sort", "str_sup_1", "str_sup_2",
   "str_sup_3", "str_sup_4", "str_sup_5", "str_sup_6", "str_sup_7", "str_utf8_char",
   "string_of_list_ty_ok", "string_ty_ok", "strip_pis", "struct_ctor_resid_ok", "struct_eta_cert",
   "struct_eta_cert_go", "struct_eta_cert_tail", "struct_eta_cert_with", "struct_eta_cert_wtb",
   "struct_ps_at", "struct_ps_at_go", "struct_unit_cert", "eta_ctor_partial_fam", "eta_ctor_partial", "struct_eta_full_at", "struct_eta_full", "struct_eta_expand", "struct_eta_cert_partial", "is_prop_type", "unit_like_fields", "unit_like_shape_at", "unit_like_shape", "unit_like_struct", "unit_like_loop", "struct_unit_tail",
   "stuck_app", "stuck_app_cong", "stuck_irrel", "stuck_rest", "stuck_str",
   "subst_const0", "subst_const0_list", "subst_const0_pairs", "subst_const_all", "subst_pw_at",
   "succ_find", "succ_push", "tbl_at", "tbl_base_get", "tbl_cnt", "tbl_grown", "tbl_ix",
   "tbl_own_get", "tbl_put", "tbl_row_get", "tbl_row_set", "trust_compiler_ok",
   "try_unfold_proj_app", "type_pin_guard", "type_pin_stored", "type_pins_guard", "type_sort_pw",
   "ue_mentions_go", "unfold_definition", "unfold_defn_at", "unfoldable_head",
   "unresolved_consts_error", "unwrap_id_defs", "unwrap_step", "value_guards", "vg_rd", "vg_wr",
   "view_ls", "wc_clear", "wc_find", "wc_put", "wh_clear", "wh_find", "wh_put", "whnf", "whnf_app", "whnf_app_iota",
   "whnf_core", "whnf_core_app", "whnf_core_app2", "whnf_core_lookup_at", "whnf_core_store_chain", "whnf_core_store_keys",
    "whnf_core_store_cheap_keys", "whnf_stuck", "whnf_core_step",
   "whnf_core_step_proj", "whnf_loop", "whnf_step", "whnf_telescope", "whnf_top", "wk_clear",
   "wk_find", "wk_put", "ws_clear", "ws_find", "ws_go", "ws_node", "ws_put", "wscoped_bfast",
   "zero_find", "zero_push",
   "basis_names_ok", "basis_names_error", "basis_name_unreserved",
   "block_names_unreserved", "basis_name_hit", "basis_name_hit_go", "block_names_eq",
   "pin_list_ok", "block_links_ok", "block_links_ok_go", "block_link_ok_at", "rules_link_ok",
   "pin_link_ok", "pin_link_go", "const_named", "pin_copies_ok", "pin_copy_ok", "pin_agrees"]

/-- `imFns` as a tree of name codes. -/
names_tree imTree : imFns

theorem im_mem (f : FnName) (h : (imTree.find (L.Compiler.nameCode f)).isSome = true) :
    f ∈ imFns := by
  have := L.Compiler.namesTree_spec imTree.eq f
  rw [h] at this; exact of_decide_eq_true this.symm

/-- **The program hypothesis**: the loop's callees outside the inductive arm write none of the
inductive stage's memos but through `consts_resolve_ffast`. -/
def IndMemoClosed (p : Prog) : Prop := closedAL p imA imC imFns imLeaves = true

end L.Arena
