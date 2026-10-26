import ConAgua.Checker.Prog
import ConAgua.Arena.Frame
import ConAgua.Compiler.WriteSetSplit

/-!
# The write set of everything `check` runs before the declaration loop (lane `pipeline`)

`check_a` (`Entry.lean`) runs the stages `cap_check`, `pb_check`, `intern_reserved_pins`,
`builtin_prelude`, `front_run`, `prepare_prelude` and `intern_all_pins` before
phase A's fold. `preLoopFns` is their call closure in `checkerProg` (473 functions, computed
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
  "app_find", "app_push", "apply_any", "apply_decl", "apply_dline", "apply_expr", "apply_ind",
  "apply_level", "apply_nnum", "apply_nstr", "apply_rec", "apply_str", "builtin_prelude",
  "bvar_find", "bvar_push", "byte_in", "cap_check", "const_find", "const_push", "ctl_sum",
  "d_member", "dec_chunk", "decl_code", "decl_cv", "decl_declares", "decl_declares_go", "decl_key",
  "decl_kind", "decl_push", "decl_val", "der_b", "dind_alloc", "e_view", "eid_sp_clear",
  "erec_alloc", "esc_one", "esc_sur", "esp_find", "esp_put", "expr_fresh", "expr_get", "expr_node",
  "expr_put", "expr_val", "fld_alloc", "fld_put", "forall_find", "forall_push", "front_init",
  "front_line", "front_reset", "front_run", "fvar_find", "fvar_push", "has_escape", "hex3", "hex4",
  "hex_val", "hints_num", "hints_obj", "hints_val", "hn_clear", "hn_find", "hn_put", "hoist_any",
  "hoist_app", "hoist_apply", "hoist_block_go", "hoist_bucket", "hoist_chain", "hoist_close_go",
  "hoist_closure", "hoist_deps", "hoist_deps_of", "hoist_emit", "hoist_forall", "hoist_fvar",
  "hoist_index_go", "hoist_ins", "hoist_ix", "hoist_lam", "hoist_let", "hoist_names",
  "hoist_names_go", "hoist_nat_op_ground", "hoist_note", "hoist_proj", "hoist_rules_go",
  "hoist_targets_go", "hoist_walk", "hoist_zero", "hs_clear", "hs_find", "hs_put", "if_reset",
  "ifl_alloc", "ifl_contains", "ifl_find_last", "ifl_ids", "ifl_nodup", "ifl_push", "ifr_alloc",
  "imax_find", "imax_push", "ind_bool", "ind_caps", "ind_ctor", "ind_cv", "ind_fields", "ind_list",
  "ind_member", "ind_nlist", "ind_num", "ind_obj", "ind_pi_tele_len", "ind_rec", "ind_rules",
  "ind_rules_go", "ind_size", "ind_slot", "ind_type", "inst_ctors", "inst_recs", "inst_types",
  "install_ind_d", "intern_all_pins", "intern_app", "intern_bvar", "intern_const", "intern_forall",
  "intern_fvar", "intern_imax", "intern_lam", "intern_letE", "intern_lit", "intern_lit_str",
  "intern_ls", "intern_max", "intern_nanon", "intern_nnum", "intern_nstr", "intern_param",
  "intern_pin_sets", "intern_proj", "intern_reserved_pins", "intern_sort", "intern_succ",
  "intern_zero", "iw_alloc", "key_at", "key_at_g1", "key_at_g2", "key_at_g3", "key_at_g4",
  "key_at_g5", "key_at_g6", "key_end", "lam_find", "lam_push", "letE_find", "letE_push",
  "level_fresh", "level_get", "level_put", "lh_mk", "lid_sp_clear", "limbs_eq", "lit_find",
  "lit_find_str", "lit_hash", "lit_match", "lit_match_str", "lit_push", "lit_push_str", "lp_put",
  "ls_find", "ls_match", "ls_push", "ls_put", "lsp_find", "lsp_put", "lv_cases", "lv_cases_at",
  "lv_comb", "lv_dist1", "lv_dist2", "lv_eq", "lv_equiv", "lv_imax", "lv_imax_l", "lv_imax_r",
  "lv_leq", "lv_node", "lv_rest", "lv_simp", "lv_subsimp", "lv_subst", "match_dlit", "match_lit",
  "match_word", "max_find", "max_push", "memo_get", "memo_push", "mk_app", "mk_forall", "mk_lam",
  "mk_let", "mk_proj", "name_fresh", "name_get", "name_put", "name_rec_pre", "nanon_find",
  "nanon_push", "nat_dec", "nat_div_mod_names", "nat_mad", "nat_op_deps", "nat_op_names",
  "nat_op_pins", "nat_op_pins_a", "nat_op_pins_b", "nat_op_pins_c", "nat_op_record", "next_member",
  "nid_sp_clear", "nnum_find", "nnum_push", "node_bin", "node_const", "node_let", "node_lit",
  "node_lit_str", "node_proj", "nsp_find", "nsp_put", "nstr_find", "nstr_match", "nstr_push",
  "num_end", "obj_val", "param_find", "param_push", "parse_rule_d", "pb_check", "pi_result_d",
  "pi_sort_tele_len", "pin_at", "pre_apply_any", "pre_apply_decl", "pre_apply_dline",
  "pre_apply_expr", "pre_apply_ind", "pre_apply_rec", "pre_apply_str", "pre_byte_in",
  "pre_d_member", "pre_dec_chunk", "pre_decl_cv", "pre_decl_val", "pre_esc_one", "pre_esc_sur",
  "pre_expr_node", "pre_expr_val", "pre_front_line", "pre_front_run", "pre_has_escape", "pre_hex3",
  "pre_hex4", "pre_hints_num", "pre_hints_obj", "pre_hints_val", "pre_ifl_ids", "pre_ind_bool",
  "pre_ind_ctor", "pre_ind_cv", "pre_ind_fields", "pre_ind_list", "pre_ind_member",
  "pre_ind_nlist", "pre_ind_num", "pre_ind_obj", "pre_ind_rec", "pre_ind_type", "pre_inst_ctors",
  "pre_inst_recs", "pre_inst_types", "pre_install_ind_d", "pre_key_at", "pre_key_at_g1",
  "pre_key_at_g2", "pre_key_at_g3", "pre_key_at_g4", "pre_key_at_g5", "pre_key_at_g6",
  "pre_key_end", "pre_lp_put", "pre_ls_put", "pre_match_dlit", "pre_match_lit", "pre_match_word",
  "pre_nat_dec", "pre_next_member", "pre_node_const", "pre_node_lit", "pre_node_lit_str",
  "pre_num_end", "pre_obj_val", "pre_read_nat", "pre_rec_decl_line", "pre_rec_decl_obj",
  "pre_rec_expr_loop", "pre_rec_line_loop", "pre_rec_nat_list", "pre_rec_num_name", "pre_rec_obj",
  "pre_rec_str_name", "pre_scan_app", "pre_scan_axiom", "pre_scan_binder", "pre_scan_binder_info",
  "pre_scan_bool", "pre_scan_const", "pre_scan_def", "pre_scan_hints", "pre_scan_ind_ctor",
  "pre_scan_ind_ctors", "pre_scan_ind_decl", "pre_scan_ind_rec", "pre_scan_ind_recs",
  "pre_scan_ind_type", "pre_scan_ind_types", "pre_scan_let", "pre_scan_line", "pre_scan_line_loop",
  "pre_scan_nat_list", "pre_scan_num_name", "pre_scan_opaque", "pre_scan_proj", "pre_scan_quot",
  "pre_scan_quoted_nat", "pre_scan_rule", "pre_scan_rules", "pre_scan_str_name", "pre_scan_string",
  "pre_scan_thm", "pre_skip_braced", "pre_skip_digits", "pre_skip_ws", "pre_slot_nat",
  "pre_str_close", "pre_str_code", "pre_str_put_esc", "pre_u_next", "pre_unescape",
  "pre_utf8_char", "pre_utf8_valid", "pre_value_at", "prep_back", "prep_back_rec", "prep_copy",
  "prep_copy_rec", "prep_find", "prep_front", "prep_rest", "prepare_prelude", "proj_find",
  "proj_push", "read_nat", "rec_decl_line", "rec_decl_obj", "rec_expr_loop", "rec_line_loop",
  "rec_nat_list", "rec_num_name", "rec_obj", "rec_str_name", "rom_ex_leaf", "rom_ex_one",
  "rom_ex_ref", "rom_ex_two", "rom_expr", "rom_exprs_to", "rom_items", "rom_level", "rom_levels",
  "rom_lists_to", "rom_lit", "rom_lvls_go", "rom_name", "rom_names_to", "rom_pins_to", "rom_put",
  "rom_sets_to", "rom_tpairs_to", "rom_tpins_to", "rom_u64", "rset_clear", "rset_find", "rset_put",
  "scan_app", "scan_axiom", "scan_binder", "scan_binder_info", "scan_bool", "scan_const",
  "scan_def", "scan_hints", "scan_ind_ctor", "scan_ind_ctors", "scan_ind_decl", "scan_ind_rec",
  "scan_ind_recs", "scan_ind_type", "scan_ind_types", "scan_let", "scan_line", "scan_line_loop",
  "scan_nat_list", "scan_num_name", "scan_opaque", "scan_proj", "scan_quot", "scan_quoted_nat",
  "scan_rule", "scan_rules", "scan_str_name", "scan_string", "scan_thm", "skip_braced",
  "skip_digits", "skip_ws", "slice_has", "slot_nat", "sort_find", "sort_push", "stk_pool",
  "stk_push", "store_fuel", "str_close", "str_code", "str_put_esc", "succ_find", "succ_push",
  "u_next", "unescape", "utf8_char", "utf8_put", "utf8_valid", "validate_ind_d", "value_at",
  "vi_ctor", "vi_ids_go", "vi_k_expected", "vi_listed", "vi_listed_go", "vi_map", "vi_map_go",
  "vi_nested", "vi_np_go", "vi_nparams", "vi_order", "vi_order_go", "vi_order_in", "vi_rec",
  "vi_rec_idx", "vi_recs", "vi_recs_go", "vi_tail", "vi_unsafe", "zero_find", "zero_push"]

/-- The word arrays (other than `CTL`) the functions of `preLoopFns` store into. -/
def preLoopA : List ArrId := [
  0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 25, 26, 27,
  28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 42, 43, 44, 45, 46, 55, 56, 57, 58, 59, 60,
  61, 64, 65, 66, 67, 68, 70, 71, 72, 73, 74, 75, 76, 128, 136, 138, 139, 150, 192, 200, 256, 258,
  259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277,
  278, 279, 281, 282, 283, 284, 285, 286, 287, 288, 289, 290, 291, 292, 293, 294, 295, 296, 298,
  299, 300, 301, 302, 311, 312, 313, 314, 315, 316, 317]

/-- The `CTL` words the functions of `preLoopFns` store into. -/
def preLoopC : List Word := [
  0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 26, 27, 28,
  29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74,
  75, 76, 129, 131, 132, 148, 149, 150, 151, 192, 200, 240]

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
    ∀ b ∈ ([49, 50, 52, 53, 54, 151, 152, 153, 155, 201, 202, 203, 204, 205, 206, 207, 208] :
      List ArrId), b ∉ preLoopA := by
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
