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
   "ground_guards", "div_mod_type_pins", "type_pins_guard", "type_pin_guard", "type_pin_stored",
   "check_type_pins", "check_div_mod_pin_value", "intern_nstr", "nstr_find", "nstr_match",
   "nstr_push",
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
  decide (a < 388) && a != PEND && a != DECL && a != DLP && (decide (a < 146) || decide (149 < a))

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

end L.Checker
