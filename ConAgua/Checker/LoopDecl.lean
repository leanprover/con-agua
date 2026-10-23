import ConAgua.Checker.Prog
import ConAgua.Arena.LoopT
import ConAgua.Compiler.WriteSetSplit

/-!
# The declaration texts' write set in the checker's program (lane `loopt2`)

The declaration loop's program hypotheses (`CvgProg`, `IvProg`, `ArmProg`, `CheckDeclProg`'s
`natText` and `dgClosed`) ask for a step's write set (`stepA`, `stepC`: no `PEND`, `DECL`, `DLP`,
promotion memos, `CTL[130]`, `CTL[140‥147]`, `CTL[150]`, `CTL[151]`) on a call-closed superset of
their function lists (`StepIn`). In the checker's program the texts' open callees (`openFns`: the
core's entry points, the walks, the ROM readers) are real code, so the superset is the texts'
lists, the core's (`stageCoreFns`) and the open callees' own callees (`declExtFns`). Decided by
per-chunk kernel checks as `LoopCore.lean`.
-/

namespace L.Checker

open L.Arena L.Ind L.Compiler
open L.Front (DECL DLP)

/-- The functions the declaration texts reach in the checker's program outside the texts' lists
and `stageCoreFns`: the callees of the walks, of the ROM readers and of the `Nat.div`-family gate's
certificate checks (computed from `checkerProg`'s call graph; the check below fails if one is
missing). -/
def declExtFns : List FnName :=
  ["apd_clear", "alpd_go", "apd_find", "lv_apd", "lv_mem", "alpd_ls", "apd_put", "rci_slot",
   "rom_u64", "rci_fresh", "rset_clear", "rci_cv", "rom_name", "rom_put", "rci_name_sl",
   "rci_names_to", "rom_expr", "rom_ex_ref", "memo_get", "rom_ex_leaf", "rom_level", "rom_levels",
   "rom_lvls_go", "stk_push", "stk_pool", "rom_ex_one", "memo_push", "rset_find", "rset_put",
   "rom_ex_two", "rci_ci", "rci_caps", "rci_rules_to", "rci_rule", "rci_lvls_to", "rom_exprs_to",
   "rci_block", "rci_block_to", "div_mod_env_guard", "bool_ctor_typed", "check_div_mod_pin_loop",
   "div_mod_pin_guard", "div_mod_decl_pin", "div_mod_slot", "div_mod_certs_guard",
   "div_mod_cert_stmts", "cert_ctx", "nat_var", "nat_one", "cert_ctx_pins", "cert_ctx_main",
   "div_mod_cert_stmts_at", "cert_gcd", "cert_guard", "eq_at1", "sl_new1", "intern_ls_iw",
   "cert_two_eqs", "cert_eq", "stmt1", "rec3", "cert_shift_left", "cert_shift_right", "cert_land",
   "cert_halves", "cert_lor", "cert_lor_rhs", "cert_xor", "cert_xor_rhs", "cert_div_mod",
   "cert_rec_rhs", "cert_div_mod_guards", "cert_div_mod_eqs", "div_mod_cert_proofs",
   "div_mod_certs_guard_go", "div_mod_cert_guard", "subst_const_all", "subst_const0_list",
   "consts_resolve_all", "check_div_mod_pin_at", "check_div_mod_certs", "div_mod_cert_applied",
   -- lane `stubs`: the callees of `intern_ls_iw` and `consts_resolve_ffast`
   "pool_room", "iw_pool", "crf_go", "cr_leaf", "cr_lit_pins", "pin_found", "crm_find", "crm_put",
   "crm_clear", "is_str_lit"]

/-- The call-closed superset: the texts' lists, their open callees' callees and the core. -/
def declLoopFns : List FnName :=
  cvgFns ++ ivFns ++ armFns ++ natGateFns ++ dgFns ++ declExtFns ++ stageCoreFns

/-- `declLoopFns` as a tree of name codes. -/
names_tree declLoopTree : declLoopFns

/-- The arrays of `stepA`, as a test. -/
def stepPa (a : ArrId) : Bool :=
  decide (a < 256) && a != PEND && a != DECL && a != DLP && (decide (a < 146) || decide (149 < a))

/-- The `CTL` words of `stepC`, as a test. -/
def stepPc (w : Word) : Bool :=
  decide (w.toNat < 1024) && w.toNat != 130 && w.toNat != 150 && w.toNat != 151 &&
    (decide (w.toNat < 140) || decide (147 < w.toNat))

theorem stepPa_mem (a : ArrId) (h : stepPa a = true) : a ∈ stepA := by
  simp only [stepPa, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne,
    ne_eq] at h
  simp [stepA, List.mem_filter, List.mem_range, h]

theorem stepPc_mem (w : Word) (h : stepPc w = true) : w ∈ stepC := by
  simp only [stepPc, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne,
    ne_eq] at h
  simp only [stepC, List.mem_map, List.mem_filter, List.mem_range]
  refine ⟨w.toNat, ⟨h.1.1.1.1, ?_⟩, UInt64.ofNat_toNat⟩
  simp only [decide_eq_true_eq]
  exact ⟨h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- Every function of the checker passes the declaration texts' per-function check. -/
prog_all checkerProg_declChk : checkerProg (wsChk CTL stepPa stepPc declLoopTree)

theorem checkerProg_declClosed : closedA checkerProg stepA stepC declLoopFns = true :=
  closedW_of_all declLoopTree.eq stepPa_mem stepPc_mem checkerProg_declChk

theorem checkerProg_stepIn {fs : List FnName} (h : ∀ f ∈ fs, f ∈ declLoopFns) :
    StepIn checkerProg fs :=
  ⟨_, h, checkerProg_declClosed⟩

theorem checkerProg_cvgIn : StepIn checkerProg cvgFns :=
  checkerProg_stepIn fun _ h => by simp only [declLoopFns, List.mem_append]; simp [h]

theorem checkerProg_ivIn : StepIn checkerProg ivFns :=
  checkerProg_stepIn fun _ h => by simp only [declLoopFns, List.mem_append]; simp [h]

theorem checkerProg_armIn : StepIn checkerProg armFns :=
  checkerProg_stepIn fun _ h => by simp only [declLoopFns, List.mem_append]; simp [h]

theorem checkerProg_natGateIn : StepIn checkerProg natGateFns :=
  checkerProg_stepIn fun _ h => by simp only [declLoopFns, List.mem_append]; simp [h]

theorem checkerProg_dgIn : StepIn checkerProg dgFns :=
  checkerProg_stepIn fun _ h => by simp only [declLoopFns, List.mem_append]; simp [h]

/-! ## The texts' agreement halves

`checkerProg` agrees with the texts on their functions but `openFns`: one lookup each, by `rfl`
(the elaborator and the kernel compare the names along `checkerProg`'s list), in chunks. -/

/-- `cvgFns` but `openFns`, part 0. -/
def cvgOwn0 : List FnName :=
  ["check_value_group", "iw_reset", "pin_word", "lvl_eq_c", "lq_find", "lvl_eq_rec", "lvl_eq",
   "lv_equiv", "lv_eq", "lv_node", "lv_simp", "lh_mk"]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem checkerProg_cvgOwn0 : ∀ f ∈ cvgOwn0, checkerProg.lookup f = cvgProg.lookup f :=
  List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- `cvgFns` but `openFns`, part 1. -/
def cvgOwn1 : List FnName :=
  ["lv_comb", "lv_leq", "lv_rest", "lv_imax", "lv_cases", "lv_cases_at", "lv_subsimp", "lv_subst",
   "lv_imax_l", "lv_dist1", "lv_dist2", "lv_imax_r"]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem checkerProg_cvgOwn1 : ∀ f ∈ cvgOwn1, checkerProg.lookup f = cvgProg.lookup f :=
  List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- `cvgFns` but `openFns`, part 2. -/
def cvgOwn2 : List FnName :=
  ["lq_put", "install_value_guards", "cv_lps", "er_to_iw", "iw_alloc", "er_copy",
   "consts_resolve_ffast"]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem checkerProg_cvgOwn2 : ∀ f ∈ cvgOwn2, checkerProg.lookup f = cvgProg.lookup f :=
  List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩

set_option maxRecDepth 100000 in
theorem cvgOwn_of : ∀ f ∈ cvgFns, f ∉ openFns →
    f ∈ cvgOwn0 ++ (cvgOwn1 ++ cvgOwn2) := by
  decide +kernel

theorem checkerProg_cvgAgree : ∀ f ∈ cvgFns, f ∉ openFns → checkerProg.lookup f = cvgProg.lookup f := by
  intro f hf ho
  have h := cvgOwn_of f hf ho
  rcases List.mem_append.1 h with h | h
  · exact checkerProg_cvgOwn0 f h
  rcases List.mem_append.1 h with h | h
  · exact checkerProg_cvgOwn1 f h
  exact checkerProg_cvgOwn2 f h

/-- `ivFns` but `openFns`, part 0. -/
def ivOwn0 : List FnName :=
  ["install_value", "erec_ci", "erec_alloc", "dlp_copy", "install_header", "env_find",
   "env_row_get", "env_ix", "reserved_contains", "reserved_from", "cv_lps", "er_to_iw"]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem checkerProg_ivOwn0 : ∀ f ∈ ivOwn0, checkerProg.lookup f = ivProg.lookup f :=
  List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- `ivFns` but `openFns`, part 1. -/
def ivOwn1 : List FnName :=
  ["iw_alloc", "er_copy", "sl_nodup", "sl_contains", "consts_resolve_ffast",
   "install_value_guards", "env_push", "env_row_set", "erec_vg"]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem checkerProg_ivOwn1 : ∀ f ∈ ivOwn1, checkerProg.lookup f = ivProg.lookup f :=
  List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩

set_option maxRecDepth 100000 in
theorem ivOwn_of : ∀ f ∈ ivFns, f ∉ openFns →
    f ∈ ivOwn0 ++ ivOwn1 := by
  decide +kernel

theorem checkerProg_ivAgree : ∀ f ∈ ivFns, f ∉ openFns → checkerProg.lookup f = ivProg.lookup f := by
  intro f hf ho
  have h := ivOwn_of f hf ho
  rcases List.mem_append.1 h with h | h
  · exact checkerProg_ivOwn0 f h
  exact checkerProg_ivOwn1 f h

/-- `armFns` but `openFns`, part 0. -/
def armOwn0 : List FnName :=
  ["check_decl_thm", "erec_ci", "erec_alloc", "dlp_copy", "check_constant_val", "install_header",
   "env_find", "env_row_get", "env_ix", "reserved_contains", "reserved_from", "cv_lps"]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem checkerProg_armOwn0 : ∀ f ∈ armOwn0, checkerProg.lookup f = armText.lookup f :=
  List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- `armFns` but `openFns`, part 1. -/
def armOwn1 : List FnName :=
  ["er_to_iw", "iw_alloc", "er_copy", "sl_nodup", "sl_contains", "consts_resolve_ffast",
   "check_thm_val", "pin_word", "lvl_eq_fueled", "lvl_eq_c", "lq_find", "lvl_eq_rec"]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem checkerProg_armOwn1 : ∀ f ∈ armOwn1, checkerProg.lookup f = armText.lookup f :=
  List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- `armFns` but `openFns`, part 2. -/
def armOwn2 : List FnName :=
  ["lvl_eq", "lv_equiv", "lv_eq", "lv_node", "lv_simp", "lh_mk", "lv_comb", "lv_leq", "lv_rest",
   "lv_imax", "lv_cases", "lv_cases_at"]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem checkerProg_armOwn2 : ∀ f ∈ armOwn2, checkerProg.lookup f = armText.lookup f :=
  List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- `armFns` but `openFns`, part 3. -/
def armOwn3 : List FnName :=
  ["lv_subsimp", "lv_subst", "lv_imax_l", "lv_dist1", "lv_dist2", "lv_imax_r", "lq_put",
   "install_value_guards", "env_push", "env_row_set", "check_decl_opaque", "check_opaque_val"]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem checkerProg_armOwn3 : ∀ f ∈ armOwn3, checkerProg.lookup f = armText.lookup f :=
  List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- `armFns` but `openFns`, part 4. -/
def armOwn4 : List FnName :=
  ["pin_at", "check_reduce_pin", "reduce_stored_ok", "reduce_op_cv_a", "matches_pin", "cv_eq",
   "er_sl_eq", "reduce_elem_ok", "ci_eq", "tbl_eq", "tbl_eq_a", "er_sl_at"]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem checkerProg_armOwn4 : ∀ f ∈ armOwn4, checkerProg.lookup f = armText.lookup f :=
  List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- `armFns` but `openFns`, part 5. -/
def armOwn5 : List FnName :=
  ["ci_eq_rest", "hint_eq", "caps_eq", "caps_eq_a", "b_eq", "caps_eq_b", "pw_eq", "caps_eq_c",
   "rules_eq", "rule_eq_but_rhs", "rule_eq_a", "rule_eq_b"]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem checkerProg_armOwn5 : ∀ f ∈ armOwn5, checkerProg.lookup f = armText.lookup f :=
  List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- `armFns` but `openFns`, part 6. -/
def armOwn6 : List FnName :=
  ["reduce_pin_guard", "reduce_decl_pin", "reduce_cert_var", "const_e", "intern_const",
   "const_find", "const_push", "intern_fvar", "fvar_find", "fvar_push", "mk_app", "der_b"]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem checkerProg_armOwn6 : ∀ f ∈ armOwn6, checkerProg.lookup f = armText.lookup f :=
  List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- `armFns` but `openFns`, part 7. -/
def armOwn7 : List FnName :=
  ["intern_app", "app_find", "app_push", "check_decl_quot", "quot_pin_hit", "ci_to_cv",
   "intern_zero", "zero_find", "zero_push", "intern_succ", "succ_find", "succ_push"]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem checkerProg_armOwn7 : ∀ f ∈ armOwn7, checkerProg.lookup f = armText.lookup f :=
  List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- `armFns` but `openFns`, part 8. -/
def armOwn8 : List FnName :=
  ["intern_sort", "sort_find", "sort_push", "cv_new", "cv_canon_eq", "canon_ctx", "canon_names",
   "canon_names_go", "intern_nanon", "nanon_find", "nanon_push", "intern_nnum"]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem checkerProg_armOwn8 : ∀ f ∈ armOwn8, checkerProg.lookup f = armText.lookup f :=
  List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- `armFns` but `openFns`, part 9. -/
def armOwn9 : List FnName :=
  ["nnum_find", "nnum_push", "sl_cons", "iw_copy", "canon_expr_eq", "e_view", "canon_level_eq",
   "canon_name_map", "sl_find", "sl_getd", "canon_levels_eq", "view_ls"]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem checkerProg_armOwn9 : ∀ f ∈ armOwn9, checkerProg.lookup f = armText.lookup f :=
  List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- `armFns` but `openFns`, part 10. -/
def armOwn10 : List FnName :=
  ["ls_node", "pool_copy", "canon_level_list_eq", "check_basis_decl", "find_is",
   "install_basis_decls", "install_basis_decl", "check_decl_axiom", "ci_canon_eq", "ci_canon_defn",
   "ci_canon_rec", "canon_rules_eq"]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem checkerProg_armOwn10 : ∀ f ∈ armOwn10, checkerProg.lookup f = armText.lookup f :=
  List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- `armFns` but `openFns`, part 11. -/
def armOwn11 : List FnName :=
  ["std_axiom_ok", "std_ax_family", "find_pinned", "trust_compiler_ok", "find_pinned_cv",
   "of_reduce_ax_ok", "of_reduce_op", "of_reduce_pin_a", "check_defn_val"]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem checkerProg_armOwn11 : ∀ f ∈ armOwn11, checkerProg.lookup f = armText.lookup f :=
  List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, List.forall_mem_cons.2 ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩

set_option maxRecDepth 100000 in
theorem armOwn_of : ∀ f ∈ armFns, f ∉ openFns →
    f ∈ armOwn0 ++ (armOwn1 ++ (armOwn2 ++ (armOwn3 ++ (armOwn4 ++ (armOwn5 ++ (armOwn6 ++ (armOwn7 ++ (armOwn8 ++ (armOwn9 ++ (armOwn10 ++ armOwn11)))))))))) := by
  decide +kernel

theorem checkerProg_armAgree : ∀ f ∈ armFns, f ∉ openFns → checkerProg.lookup f = armText.lookup f := by
  intro f hf ho
  have h := armOwn_of f hf ho
  rcases List.mem_append.1 h with h | h
  · exact checkerProg_armOwn0 f h
  rcases List.mem_append.1 h with h | h
  · exact checkerProg_armOwn1 f h
  rcases List.mem_append.1 h with h | h
  · exact checkerProg_armOwn2 f h
  rcases List.mem_append.1 h with h | h
  · exact checkerProg_armOwn3 f h
  rcases List.mem_append.1 h with h | h
  · exact checkerProg_armOwn4 f h
  rcases List.mem_append.1 h with h | h
  · exact checkerProg_armOwn5 f h
  rcases List.mem_append.1 h with h | h
  · exact checkerProg_armOwn6 f h
  rcases List.mem_append.1 h with h | h
  · exact checkerProg_armOwn7 f h
  rcases List.mem_append.1 h with h | h
  · exact checkerProg_armOwn8 f h
  rcases List.mem_append.1 h with h | h
  · exact checkerProg_armOwn9 f h
  rcases List.mem_append.1 h with h | h
  · exact checkerProg_armOwn10 f h
  exact checkerProg_armOwn11 f h

theorem checkerProg_cvg : CvgProg checkerProg := ⟨⟨checkerProg_cvgAgree, checkerProg_cvgIn⟩⟩

theorem checkerProg_iv : IvProg checkerProg := ⟨⟨checkerProg_ivAgree, checkerProg_ivIn⟩⟩

theorem checkerProg_arm : ArmProg checkerProg := ⟨⟨checkerProg_armAgree, checkerProg_armIn⟩⟩

end L.Checker
