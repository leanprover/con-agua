import ConAgua.Checker.Prog
import ConAgua.Front.FrontRun

/-!
# `checkerProg` agrees with `frontAllProg` on what `front_run` reaches (lane `pipeline`)

The 267 functions reachable from `front_run` in `checkerProg` (`frontFns`): each is bound in
`checkerProg` as in `L.Front.frontAllProg`, one lookup each, by `rfl`, in chunks of twelve (as in
`LoopDeclAgree.lean`). `frontAllProg` binds three more functions that `checkerProg` does not
(`validate`, `str_put`, `apply_ind_line`: nothing reachable from `check` calls them), so the
lookup bundles of `frontRun_refines` do not hold at `checkerProg`; `FrontProg.lean` transfers the
run instead (`invoke_exec_agree`).
-/

namespace L.Checker

open L L.Compiler

set_option Elab.async false

/-- The functions reachable from `front_run`, part 0. -/
def frontFns0 : List FnName :=
  ["front_run", "front_init", "front_line", "intern_nanon", "name_put", "intern_zero", "level_put", "scan_line", "skip_ws", "apply_any", "nanon_find", "nanon_push"]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem checkerProg_front0 :
    ∀ f ∈ frontFns0, checkerProg.lookup f = L.Front.frontAllProg.lookup f :=
  List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- The functions reachable from `front_run`, part 1. -/
def frontFns1 : List FnName :=
  ["nsp_find", "nsp_put", "zero_find", "zero_push", "lsp_find", "lsp_put", "scan_line_loop", "rec_line_loop", "apply_rec", "rec_expr_loop", "apply_expr", "apply_dline"]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem checkerProg_front1 :
    ∀ f ∈ frontFns1, checkerProg.lookup f = L.Front.frontAllProg.lookup f :=
  List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- The functions reachable from `front_run`, part 2. -/
def frontFns2 : List FnName :=
  ["next_member", "slot_nat", "scan_nat_list", "scan_str_name", "scan_num_name", "scan_app", "scan_binder", "scan_let", "scan_const", "scan_proj", "scan_quoted_nat", "scan_string"]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem checkerProg_front2 :
    ∀ f ∈ frontFns2, checkerProg.lookup f = L.Front.frontAllProg.lookup f :=
  List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- The functions reachable from `front_run`, part 3. -/
def frontFns3 : List FnName :=
  ["scan_axiom", "scan_def", "scan_thm", "scan_opaque", "scan_quot", "scan_ind_decl", "skip_braced", "read_nat", "rec_nat_list", "rec_str_name", "rec_num_name", "apply_str"]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem checkerProg_front3 :
    ∀ f ∈ frontFns3, checkerProg.lookup f = L.Front.frontAllProg.lookup f :=
  List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- The functions reachable from `front_run`, part 4. -/
def frontFns4 : List FnName :=
  ["apply_nnum", "apply_level", "expr_val", "expr_fresh", "expr_node", "expr_put", "rec_decl_line", "apply_ind", "apply_decl", "key_end", "value_at", "key_at"]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem checkerProg_front4 :
    ∀ f ∈ frontFns4, checkerProg.lookup f = L.Front.frontAllProg.lookup f :=
  List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- The functions reachable from `front_run`, part 5. -/
def frontFns5 : List FnName :=
  ["num_end", "scan_binder_info", "scan_bool", "skip_digits", "str_close", "has_escape", "unescape", "utf8_valid", "scan_hints", "scan_ind_ctors", "scan_ind_recs", "scan_ind_types"]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem checkerProg_front5 :
    ∀ f ∈ frontFns5, checkerProg.lookup f = L.Front.frontAllProg.lookup f :=
  List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- The functions reachable from `front_run`, part 6. -/
def frontFns6 : List FnName :=
  ["str_put_esc", "apply_nstr", "name_get", "name_fresh", "intern_nnum", "level_fresh", "level_get", "intern_succ", "intern_max", "intern_imax", "intern_param", "rec_obj"]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem checkerProg_front6 :
    ∀ f ∈ frontFns6, checkerProg.lookup f = L.Front.frontAllProg.lookup f :=
  List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- The functions reachable from `front_run`, part 7. -/
def frontFns7 : List FnName :=
  ["esp_find", "intern_bvar", "intern_sort", "node_bin", "node_let", "node_proj", "node_const", "node_lit", "node_lit_str", "esp_put", "decl_val", "ind_fields"]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem checkerProg_front7 :
    ∀ f ∈ frontFns7, checkerProg.lookup f = L.Front.frontAllProg.lookup f :=
  List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- The functions reachable from `front_run`, part 8. -/
def frontFns8 : List FnName :=
  ["validate_ind_d", "install_ind_d", "decl_kind", "decl_cv", "key_at_g1", "key_at_g2", "key_at_g3", "key_at_g4", "key_at_g5", "key_at_g6", "match_word", "match_lit"]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem checkerProg_front8 :
    ∀ f ∈ frontFns8, checkerProg.lookup f = L.Front.frontAllProg.lookup f :=
  List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- The functions reachable from `front_run`, part 9. -/
def frontFns9 : List FnName :=
  ["byte_in", "hex4", "u_next", "utf8_char", "hints_obj", "scan_ind_ctor", "scan_ind_rec", "scan_ind_type", "esc_one", "utf8_put", "intern_nstr", "nnum_find"]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem checkerProg_front9 :
    ∀ f ∈ frontFns9, checkerProg.lookup f = L.Front.frontAllProg.lookup f :=
  List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- The functions reachable from `front_run`, part 10. -/
def frontFns10 : List FnName :=
  ["nnum_push", "succ_find", "succ_push", "max_find", "max_push", "imax_find", "imax_push", "param_find", "param_push", "obj_val", "bvar_find", "bvar_push"]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem checkerProg_front10 :
    ∀ f ∈ frontFns10, checkerProg.lookup f = L.Front.frontAllProg.lookup f :=
  List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- The functions reachable from `front_run`, part 11. -/
def frontFns11 : List FnName :=
  ["sort_find", "sort_push", "expr_get", "mk_app", "mk_lam", "mk_forall", "mk_let", "mk_proj", "ls_put", "intern_ls", "intern_const", "nat_dec"]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem checkerProg_front11 :
    ∀ f ∈ frontFns11, checkerProg.lookup f = L.Front.frontAllProg.lookup f :=
  List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- The functions reachable from `front_run`, part 12. -/
def frontFns12 : List FnName :=
  ["intern_lit", "intern_lit_str", "rec_decl_obj", "decl_code", "if_reset", "ifr_alloc", "ind_obj", "vi_unsafe", "vi_nparams", "vi_map", "vi_listed", "ifl_nodup"]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem checkerProg_front12 :
    ∀ f ∈ frontFns12, checkerProg.lookup f = L.Front.frontAllProg.lookup f :=
  List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- The functions reachable from `front_run`, part 13. -/
def frontFns13 : List FnName :=
  ["vi_tail", "dind_alloc", "inst_types", "inst_ctors", "inst_recs", "decl_push", "lp_put", "hex_val", "hex3", "hints_num", "scan_rules", "esc_sur"]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem checkerProg_front13 :
    ∀ f ∈ frontFns13, checkerProg.lookup f = L.Front.frontAllProg.lookup f :=
  List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- The functions reachable from `front_run`, part 14. -/
def frontFns14 : List FnName :=
  ["lit_hash", "nstr_find", "nstr_push", "der_b", "intern_app", "intern_lam", "intern_forall", "intern_letE", "intern_proj", "ls_find", "ls_push", "const_find"]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem checkerProg_front14 :
    ∀ f ∈ frontFns14, checkerProg.lookup f = L.Front.frontAllProg.lookup f :=
  List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- The functions reachable from `front_run`, part 15. -/
def frontFns15 : List FnName :=
  ["const_push", "dec_chunk", "nat_mad", "lit_find", "lit_push", "lit_find_str", "lit_push_str", "d_member", "ind_member", "vi_np_go", "ifl_alloc", "vi_map_go"]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem checkerProg_front15 :
    ∀ f ∈ frontFns15, checkerProg.lookup f = L.Front.frontAllProg.lookup f :=
  List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- The functions reachable from `front_run`, part 16. -/
def frontFns16 : List FnName :=
  ["vi_listed_go", "ifl_contains", "store_fuel", "vi_order", "vi_k_expected", "vi_recs", "ind_type", "ind_ctor", "ind_rec", "scan_rule", "nstr_match", "app_find"]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem checkerProg_front16 :
    ∀ f ∈ frontFns16, checkerProg.lookup f = L.Front.frontAllProg.lookup f :=
  List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- The functions reachable from `front_run`, part 17. -/
def frontFns17 : List FnName :=
  ["app_push", "lam_find", "lam_push", "forall_find", "forall_push", "letE_find", "letE_push", "proj_find", "proj_push", "ls_match", "lit_match", "lit_match_str"]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem checkerProg_front17 :
    ∀ f ∈ frontFns17, checkerProg.lookup f = L.Front.frontAllProg.lookup f :=
  List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- The functions reachable from `front_run`, part 18. -/
def frontFns18 : List FnName :=
  ["hints_val", "str_code", "ind_slot", "ind_num", "ind_bool", "ind_nlist", "ind_list", "fld_put", "ifl_push", "vi_ids_go", "ctl_sum", "vi_order_go"]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem checkerProg_front18 :
    ∀ f ∈ frontFns18, checkerProg.lookup f = L.Front.frontAllProg.lookup f :=
  List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- The functions reachable from `front_run`, part 19. -/
def frontFns19 : List FnName :=
  ["pi_result_d", "e_view", "lh_mk", "lv_equiv", "vi_nested", "vi_recs_go", "ind_cv", "ind_caps", "ind_rules", "limbs_eq", "match_dlit", "ifl_ids"]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem checkerProg_front19 :
    ∀ f ∈ frontFns19, checkerProg.lookup f = L.Front.frontAllProg.lookup f :=
  List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- The functions reachable from `front_run`, part 20. -/
def frontFns20 : List FnName :=
  ["ind_size", "fld_alloc", "vi_order_in", "lv_eq", "lv_simp", "lv_leq", "vi_rec", "ind_rules_go", "vi_ctor", "lv_node", "lv_comb", "lv_rest"]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem checkerProg_front20 :
    ∀ f ∈ frontFns20, checkerProg.lookup f = L.Front.frontAllProg.lookup f :=
  List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- The functions reachable from `front_run`, part 21. -/
def frontFns21 : List FnName :=
  ["name_rec_pre", "vi_rec_idx", "parse_rule_d", "ifl_find_last", "ind_pi_tele_len", "lv_imax", "pi_sort_tele_len", "lv_cases", "lv_imax_l", "lv_cases_at", "lv_dist1", "lv_dist2"]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem checkerProg_front21 :
    ∀ f ∈ frontFns21, checkerProg.lookup f = L.Front.frontAllProg.lookup f :=
  List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- The functions reachable from `front_run`, part 22. -/
def frontFns22 : List FnName :=
  ["lv_imax_r", "lv_subsimp", "lv_subst"]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem checkerProg_front22 :
    ∀ f ∈ frontFns22, checkerProg.lookup f = L.Front.frontAllProg.lookup f :=
  List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩⟩⟩

/-- The functions reachable from `front_run` in `checkerProg` (267). -/
def frontFns : List FnName :=
  frontFns0 ++ (frontFns1 ++ (frontFns2 ++ (frontFns3 ++ (frontFns4 ++ (frontFns5 ++ (frontFns6 ++ (frontFns7 ++ (frontFns8 ++ (frontFns9 ++ (frontFns10 ++ (frontFns11 ++ (frontFns12 ++ (frontFns13 ++ (frontFns14 ++ (frontFns15 ++ (frontFns16 ++ (frontFns17 ++ (frontFns18 ++ (frontFns19 ++ (frontFns20 ++ (frontFns21 ++ frontFns22)))))))))))))))))))))

theorem checkerProg_frontAgree :
    ∀ f ∈ frontFns, checkerProg.lookup f = L.Front.frontAllProg.lookup f :=
  List.forall_mem_append.2 ⟨checkerProg_front0, List.forall_mem_append.2 ⟨checkerProg_front1, List.forall_mem_append.2 ⟨checkerProg_front2, List.forall_mem_append.2 ⟨checkerProg_front3, List.forall_mem_append.2 ⟨checkerProg_front4, List.forall_mem_append.2 ⟨checkerProg_front5, List.forall_mem_append.2 ⟨checkerProg_front6, List.forall_mem_append.2 ⟨checkerProg_front7, List.forall_mem_append.2 ⟨checkerProg_front8, List.forall_mem_append.2 ⟨checkerProg_front9, List.forall_mem_append.2 ⟨checkerProg_front10, List.forall_mem_append.2 ⟨checkerProg_front11, List.forall_mem_append.2 ⟨checkerProg_front12, List.forall_mem_append.2 ⟨checkerProg_front13, List.forall_mem_append.2 ⟨checkerProg_front14, List.forall_mem_append.2 ⟨checkerProg_front15, List.forall_mem_append.2 ⟨checkerProg_front16, List.forall_mem_append.2 ⟨checkerProg_front17, List.forall_mem_append.2 ⟨checkerProg_front18, List.forall_mem_append.2 ⟨checkerProg_front19, List.forall_mem_append.2 ⟨checkerProg_front20, List.forall_mem_append.2 ⟨checkerProg_front21, checkerProg_front22⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end L.Checker
