import ConAgua.Checker.Prog
import ConAgua.Arena.Freeze
import ConAgua.Compiler.ReadSetSplit
import ConAgua.Arena.Globals

/-!
# Phase B's read set in the checker's program (lane parmode)

`phaseBFns`: every function `check_pending_go` (phase B's loop) reaches in `checkerProg`, as a
literal computed from the program's call graph (577 names; `scripts/phaseb_fns.py` regenerates
it, and the check below fails if a callee is missing). None of them names the frozen buffer's
arrays `OUT`, `HDRF`, `CTLF` (`Arena/Freeze.lean`) or any byte array: `checkerProg_phaseBReads`,
so by `L.invoke_agree` (`L/Agree.lean`) a worker's run of `check_pending_go` is the run on any
memory that agrees with it on every other word array (docs/design/parmode.md, Step 4 (b2)).
Also, none of them writes the globals `MODE`, `PLO`, `INIT`, `PHI` (`Arena/Globals.lean`):
`checkerProg_phaseBGlobs`, so a run of `check_pending_go` keeps them (`check_pending_go_keepsG`,
by `L.invoke_keepsG`, `L/GKeep.lean`). Per-chunk kernel checks as `LoopAll.lean`.
-/

namespace L.Checker

open L.Arena L.Compiler

/-- The functions `check_pending_go` reaches in the checker's program. -/
def phaseBFns : List FnName :=
  ["ab_clear", "ab_find", "ab_fvb", "ab_node", "ab_put", "abs_app", "abs_entry", "abs_forall",
   "abs_go", "abs_lam", "abs_let", "abs_proj", "add_carry", "all_level_params_defined", "alpd_go",
   "alpd_ls", "and_rescue_slots", "apd_clear", "apd_find", "apd_put", "app_count", "app_count_at",
   "app_fill", "app_fill_n", "app_find", "app_push", "ar_app", "ar_entry", "ar_forall", "ar_go",
   "ar_lam", "ar_let", "ar_node", "ar_proj", "bb_go", "bb_memo", "bb_node", "beta_peel",
   "binder_dom", "bm_clear", "bm_find", "bm_put", "bool_true_shortcut", "bvar_b", "bvar_find",
   "bvar_push", "caps_never_zero", "char_of_nat_ty_ok", "char_ty_ok", "check_pending",
   "check_pending_go", "check_pending_next", "check_value_group", "const_e", "const_find",
   "const_name_of", "const_push", "const_ty_at", "const_val_at", "consts_resolve_ffast", "cr_leaf",
   "cr_lit_pins", "crf_go", "crm_clear", "crm_find", "crm_put", "ct_clear", "ct_find", "ct_put",
   "ctl_get", "cv_clear", "cv_find", "cv_lps", "cv_put", "de_clear", "de_find", "de_put", "defeq",
   "defeq_arg", "defeq_binders", "defeq_body", "defeq_e", "defeq_lams", "defeq_lams_inner",
   "defeq_list", "defeq_list_rev", "defeq_lst", "defeq_no_fvars", "defeq_offset", "defeq_peel",
   "defeq_proj_pair", "defeq_spine", "defeq_spine2", "defeq_stuck", "defeq_tail", "delta_quick",
   "der_b", "div_add", "div_shl1", "div_step", "div_sub", "e_rec_get", "e_view", "ek_copy",
   "ensure_sort", "ensure_sort_core", "env_find", "env_ix", "env_row_get", "er_copy",
   "er_slice_eq", "er_to_iw", "erec_push", "eta_cert", "eta_cert_body", "eta_cert_ty",
   "eta_ctor_shape", "eta_fab_args", "eta_projs", "expr_view_ok", "fab_scope_ok",
   "field_sort_zero", "find_proj", "find_rule", "find_table", "fire_ok", "fl_clear", "fl_find",
   "fl_go", "fl_node", "fl_put", "flush_caches", "fm_clear", "fm_find", "fm_put", "forall_find",
   "forall_push", "fr_go", "fr_memo", "fr_node", "fvar_find", "fvar_push", "gcd_step",
   "get_app_args", "get_app_fn", "get_app_spine", "has_fvar", "has_fvar_fast", "head_and_args",
   "head_hint", "head_is_proj", "head_proof_const", "head_proof_proj", "head_proof_pw",
   "head_type_const", "head_type_pw", "head_type_res", "hint_lt", "if_clear", "if_find", "if_put",
   "il_app", "il_bvar", "il_forall", "il_go", "il_lam", "il_let", "il_proj", "ilg_app",
   "ilg_forall", "ilg_go", "ilg_lam", "ilg_let", "ilg_proj", "ilm_clear", "ilm_find", "ilm_put",
   "ilp_clear", "ilp_find", "ilp_put", "ilpl_clear", "ilpl_find", "ilpl_put", "ilpls_clear",
   "ilpls_find", "ilpls_put", "imax_find", "imax_push", "in_clear", "in_find", "in_put",
   "ind_caps_check", "infer", "infer_app", "infer_app_io", "infer_body", "infer_body_io",
   "infer_const", "infer_forall", "infer_forall_io", "infer_io", "infer_lam", "infer_lam_io",
   "infer_lam_result", "infer_lams", "infer_lams_leaf", "infer_let", "infer_lit", "infer_pis",
   "infer_pis_leaf", "infer_proj", "infer_proj_at", "infer_spine", "infer_spine_arg",
   "infer_spine_io", "infer_type_core", "inst1", "inst_app", "inst_entry", "inst_forall",
   "inst_go", "inst_lam", "inst_let", "inst_list", "inst_lp", "inst_lp_core", "inst_proj",
   "inst_spine", "inst_spine_pins", "install_value_guards", "intern_app", "intern_bvar",
   "intern_const", "intern_forall", "intern_fvar", "intern_imax", "intern_lam", "intern_letE",
   "intern_lit", "intern_ls", "intern_max", "intern_param", "intern_proj", "intern_sort",
   "intern_succ", "intern_zero", "io_clear", "io_find", "io_neutral", "io_put", "iota_case3",
   "iota_certs_full", "iota_certs_full_aux", "iota_certs_full_check", "iota_certs_full_flush",
   "iota_certs_full_forall", "iota_certs_full_parts", "iota_ctor_never_prop", "iota_index_ok",
   "iota_rec_at", "iota_rec_c", "iota_rec_cmp", "iota_rec_fam", "iota_rec_fire", "iota_rec_fire2",
   "iota_rec_head", "iota_rec_major", "iota_rec_vck", "is_bool_true", "is_ctor_app",
   "is_def_eq_core", "is_eager_reduce", "is_nat_zero", "is_proof_fast", "is_str_lit", "iw_alloc",
   "iw_reset", "keys_ok", "keys_push", "lam_find", "lam_pair", "lam_proj", "lam_push", "lams_inst",
   "lams_open", "lazy_delta_proj_reduction", "lazy_delta_reduction", "lazy_delta_step",
   "lazy_fold_ok", "lazy_iter", "lazy_nat", "ldpr_exit", "lds_both", "lds_left", "lds_right",
   "lds_same", "lds_unfold2", "leaf_guard", "leaf_mem", "letE_find", "letE_push", "lf_clear",
   "lh_mk", "lh_push", "limbs_eq", "list_cons_ty_ok", "list_nil_ty_ok", "list_ty_ok", "lit_eq",
   "lit_find", "lit_hash", "lit_major_to_ctor", "lit_match", "lit_push", "lit_to_ctor_if_nat",
   "loose_bvars_bounded_fast", "lp_app", "lp_forall", "lp_fvar", "lp_go", "lp_lam", "lp_let",
   "lp_let_tail", "lp_lookup", "lp_proj", "lp_rb_let", "lp_spw", "lp_substl", "lp_substpw",
   "lq_clear", "lq_find", "lq_put", "ls_find", "ls_match", "ls_node", "ls_push", "lsb_clear",
   "lsb_find", "lsb_go", "lsb_node", "lsb_put", "lsq_clear", "lsq_find", "lsq_put", "lv_apd",
   "lv_cases", "lv_cases_at", "lv_comb", "lv_dist1", "lv_dist2", "lv_eq", "lv_equiv", "lv_equivs",
   "lv_imax", "lv_imax_l", "lv_imax_r", "lv_intern", "lv_leq", "lv_lookup", "lv_mem", "lv_node",
   "lv_rest", "lv_simp", "lv_spw", "lv_sub_int", "lv_subsimp", "lv_subst", "lv_substl", "lv_zero",
   "lvl_eq", "lvl_eq_c", "lvl_eq_rec", "lvls_eq", "lvls_eq_c", "lvls_eq_rec", "m2c_and",
   "m2c_and2", "m2c_arms", "m2c_check", "m2c_const_view", "m2c_ctor", "m2c_eta", "m2c_eta2",
   "m2c_head", "m2c_k", "m2c_k2", "m2c_pre", "mac_hi", "major_to_ctor", "max_find", "max_push",
   "mk_app", "mk_app_n", "mk_app_n_from", "mk_forall", "mk_lam", "mk_let", "mk_proj", "nat_add",
   "nat_add_lit", "nat_beq_lit", "nat_bin_op_name", "nat_ble_lit", "nat_cmp", "nat_div_lit",
   "nat_divmod", "nat_gcd", "nat_gcd_lit", "nat_ind_ok", "nat_land", "nat_land_lit", "nat_limb",
   "nat_lit_supported", "nat_lit_to_ctor", "nat_lor", "nat_lor_lit", "nat_mod_lit", "nat_mul",
   "nat_mul_lit", "nat_op_is_wf", "nat_op_result", "nat_op_stored", "nat_pow", "nat_pow_lit",
   "nat_pred", "nat_pred_lit", "nat_shl", "nat_shl_lit", "nat_shr", "nat_shr_lit", "nat_sub",
   "nat_sub_lit", "nat_succ_lit", "nat_succ_ok", "nat_trim", "nat_xor", "nat_xor_lit",
   "nat_zero_ok", "not_proof_fast", "param_find", "param_push", "peel_dom", "peel_leaf",
   "peel_pis", "peel_pis_w", "peel_push", "peel_step", "peel_step2", "pi_residual", "pi_result",
   "pin_at", "pin_found", "pin_word", "prepare_major", "proj_cert", "proj_find",
   "proj_lit_to_ctor", "proj_push", "proj_type_at", "proof_irrel", "proof_irrel_half", "proof_pw",
   "prop_irrel", "quick_defeq", "quick_forall", "quick_lam", "quick_sort", "raw_nat_lit",
   "rec_fire_args", "rec_fire_levels", "rec_rule_k", "reduce_nat", "reduce_nat_ap",
   "reduce_nat_head", "reduce_nat_k", "reduce_nat_op", "reduce_nat_succ", "reduce_nat_wf",
   "reduce_proj_arg", "reduce_proj_core", "reduce_proj_fire", "reduce_proj_head",
   "reserved_contains_w", "residual_pw", "rom_lit", "rr_clear", "rr_find", "rr_put", "rule_rhs_at",
   "same_const_heads", "scratch_drop", "scratch_enter", "scratch_reset", "sl_memo", "sle_go",
   "slp_go", "sls_go", "sls_memo", "sort_find", "sort_push", "spine_cmp", "spine_head", "spn_get",
   "spn_ls", "spn_pool", "stack_cover", "str_cons_spine", "str_ctor_pre", "str_cv", "str_lit_ctor",
   "str_lit_supported", "str_ls1", "str_param_sort", "str_sup_1", "str_sup_2", "str_sup_3",
   "str_sup_4", "str_sup_5", "str_sup_6", "str_sup_7", "str_utf8_char", "string_of_list_ty_ok",
   "string_ty_ok", "struct_eta_cert", "struct_eta_cert_go", "struct_eta_cert_tail",
   "struct_eta_cert_with", "struct_eta_cert_wtb", "struct_unit_cert", "struct_unit_head",
   "struct_unit_tail", "stuck_app", "stuck_app_cong", "stuck_irrel", "stuck_rest", "stuck_str",
   "sub_borrow", "subst_pw_at", "succ_find", "succ_push", "tbl_ix", "tbl_row_get",
   "tower_slots_all", "try_unfold_proj_app", "type_sort_pw", "unfold_definition", "unfold_defn_at",
   "unfoldable_head", "unwrap_id_defs", "unwrap_step", "wc_clear", "wc_find", "wc_put", "wh_clear",
   "wh_find", "wh_put", "whnf", "whnf_app", "whnf_core", "whnf_core_app", "whnf_core_app2",
   "whnf_core_loop", "whnf_core_step", "whnf_core_step_proj", "whnf_loop", "whnf_step", "wk_clear",
   "wk_find", "wk_put", "ws_clear", "ws_find", "ws_go", "ws_node", "ws_put", "wscoped_bfast",
   "zero_find", "zero_push"]

/-- The word arrays phase B may name: all but the frozen buffer's (`OUT`, `HDRF`, `CTLF`). -/
def phaseBPa (a : ArrId) : Bool := a != 240 && a != 241 && a != 242

theorem phaseBPa_frozen : OUT = 240 ∧ HDRF = 241 ∧ CTLF = 242 := ⟨rfl, rfl, rfl⟩

/-- `phaseBFns` as a tree of name codes. -/
names_tree phaseBTree : phaseBFns

/-- Every function of the checker passes phase B's per-function read check. -/
prog_all checkerProg_phaseBReadsChk : checkerProg (rdChk phaseBPa (fun _ => false) phaseBTree)

/-- **Phase B's read set**: the call closure of `check_pending_go` names only word arrays other
than `OUT`, `HDRF`, `CTLF`, no byte array, and calls only into itself. -/
theorem checkerProg_phaseBReads :
    readsIn checkerProg (fun a => a != 240 && a != 241 && a != 242) (fun _ => false) phaseBFns =
      true :=
  readsIn_of_all phaseBTree.eq checkerProg_phaseBReadsChk

theorem check_pending_go_mem_phaseBFns : "check_pending_go" ∈ phaseBFns :=
  of_decide_eq_true ((namesTree_spec phaseBTree.eq _).symm.trans (by decide +kernel))

/-- The globals phase B never writes: `MODE` (8), `PLO` (9), `INIT` (10), `PHI` (11). -/
def phaseBG (g : GVar) : Bool := g.id == 8 || g.id == 9 || g.id == 10 || g.id == 11

/-- Every function of the checker passes phase B's per-function kept-globals check. -/
prog_all checkerProg_phaseBGlobsChk : checkerProg (gsChk phaseBG phaseBTree)

/-- **Phase B's kept globals**: the call closure of `check_pending_go` writes none of `MODE`,
`PLO`, `INIT`, `PHI`. -/
theorem checkerProg_phaseBGlobs : globsIn checkerProg phaseBG phaseBFns = true :=
  globsIn_of_all phaseBTree.eq checkerProg_phaseBGlobsChk

/-- A successful run of `check_pending_go` keeps `INIT`, `MODE`, `PLO` and `PHI`. -/
theorem check_pending_go_keepsG {n : Nat} {vs : List Word} {s : St} {r : List Word} {s' : St}
    (h : (invoke checkerProg (exec checkerProg n) "check_pending_go" vs).run s = .ok (r, s')) :
    s'.mem.glob INIT = s.mem.glob INIT ∧ s'.mem.glob MODE = s.mem.glob MODE ∧
      s'.mem.glob PLO = s.mem.glob PLO ∧ s'.mem.glob PHI = s.mem.glob PHI :=
  ⟨invoke_keepsG checkerProg_phaseBGlobs check_pending_go_mem_phaseBFns h rfl,
   invoke_keepsG checkerProg_phaseBGlobs check_pending_go_mem_phaseBFns h rfl,
   invoke_keepsG checkerProg_phaseBGlobs check_pending_go_mem_phaseBFns h rfl,
   invoke_keepsG checkerProg_phaseBGlobs check_pending_go_mem_phaseBFns h rfl⟩

end L.Checker
