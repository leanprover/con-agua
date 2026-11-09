module

public import ConAgua.Arena.DeclStepGo
public import ConAgua.Arena.WhnfDelta
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr

@[expose] public section

/-!
# The `checkDecl` arms at the loop's relation: the text (lane `decls3`)

`check_decl`'s arms run on the stage relation; the loop's relation `LoopR` adds the pending checks
and the declaration records, which no callee spec mentions, so they come from the program text
(`closedA`, as `check_value_group`'s and `install_value`'s do, `DeclCvg.lean`, `DeclStepGo.lean`).

* `armText`: the arms' modules, then lane `decls2`'s texts (`cvgProg`, `ivProg`, whose real master
  callees come before the stage's stubs), then the step's program; `armFns`: every function the
  five arms reach. A program `p` with that text (`ArmProg p`, a `TextProg`: agreeing there but
  on `openFns`) has a step's write set on them (`StepIn`); the arms' specs take their callees' lookup structures
  (`ValProg`, `RecProg`, …) beside it, as `DeclCallees` does.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

open L.Ind
open L.Front (DECL DLP DeclsF DeclAt CVAt dw)

/-! ## The text -/

/-- Master functions the arms reach that the stage's program has only as stubs. -/
def armMasterFns : Prog :=
  [("pin_at", pinAtL), ("const_e", constEL), ("const_find", constFind), ("const_push", constPush),
   ("intern_const", internConst), ("fvar_find", fvarFind), ("fvar_push", fvarPush),
   ("intern_fvar", internFVar), ("mk_app", mkApp), ("app_find", appFind), ("app_push", appPush),
   ("intern_app", internApp), ("der_b", derB), ("intern_zero", internZero), ("zero_find", zeroFind),
   ("zero_push", zeroPush), ("intern_succ", internSucc), ("succ_find", succFind),
   ("succ_push", succPush), ("intern_sort", internSort), ("sort_find", sortFind),
   ("sort_push", sortPush), ("intern_nanon", internNAnon), ("nanon_find", nanonFind),
   ("nanon_push", nanonPush), ("intern_nnum", internNNum), ("nnum_find", nnumFind),
   ("nnum_push", nnumPush), ("lv_node", lvNode), ("ls_node", lsNode)]

/-- **The arms' text.** -/
def armText : Prog :=
  declArmsFns ++ declArmsNatFns ++ declArmsCanonFns ++ armMasterFns ++ cvgProg ++ ivProg ++
    declStepProg

/-- The functions the theorem arm reaches. -/
def thmArmFns : List FnName :=
  ["check_decl_thm", "erec_ci", "erec_alloc", "dlp_copy", "check_constant_val", "env_find", "env_row_get", "reserved_contains", "reserved_from",
   "cv_lps", "er_to_iw", "iw_alloc", "er_copy", "sl_nodup", "sl_contains",
   "loose_bvars_bounded_fast", "has_fvar_fast", "all_level_params_defined", "consts_resolve_ffast",
   "infer_type_core", "ensure_sort_core", "check_thm_val", "pin_word", "lvl_eq_fueled", "lvl_eq_c",
   "lq_find", "lvl_eq_rec", "lvl_eq", "lv_equiv", "lv_eq", "lv_node", "lv_simp", "lh_mk", "lv_comb",
   "lv_leq", "lv_rest", "lv_imax", "lv_cases", "lv_cases_at", "lv_subsimp", "lv_subst",
   "lv_imax_l", "lv_dist1", "lv_dist2", "lv_imax_r", "lq_put", "is_def_eq_core", "env_push", "env_row_set"]

/-- The functions the opaque arm reaches beyond the theorem arm's. -/
def opqArmFns : List FnName :=
  ["check_decl_opaque", "check_opaque_val", "pin_at", "check_reduce_pin", "reduce_stored_ok",
   "reduce_op_cv_a", "rom_cv", "matches_pin", "cv_eq", "er_sl_eq", "reduce_elem_ok", "rom_ci", "ci_eq",
   "er_sl_at", "ci_eq_rest", "hint_eq", "caps_eq", "caps_eq_a", "b_eq",
   "caps_eq_b", "caps_eq_c", "rules_eq", "rule_eq_but_rhs", "rule_eq_a", "rule_eq_b",
   "reduce_pin_guard", "reduce_decl_pin", "rom_expr_pin", "reduce_cert_var", "const_e", "intern_const",
   "const_find", "const_push", "intern_fvar", "fvar_find", "fvar_push", "mk_app", "der_b",
   "intern_app", "app_find", "app_push"]

/-- The functions the quotient and axiom arms reach beyond the others'. -/
def qaxArmFns : List FnName :=
  ["check_decl_quot", "quot_pin_hit", "rom_basis_decls", "ci_to_cv", "intern_zero", "zero_find",
   "zero_push", "intern_succ", "succ_find", "succ_push", "intern_sort", "sort_find", "sort_push",
   "cv_new", "cv_canon_eq", "canon_ctx", "canon_names", "canon_names_go", "intern_nanon",
   "nanon_find", "nanon_push", "intern_nnum", "nnum_find", "nnum_push", "sl_cons", "iw_copy",
   "canon_expr_eq", "e_view", "canon_level_eq", "canon_name_map", "sl_find", "sl_getd",
   "canon_levels_eq", "view_ls", "ls_node", "pool_copy", "canon_level_list_eq", "install_basis_decls", "install_basis_decl", "check_decl_axiom",
   "ci_canon_eq", "ci_canon_defn", "ci_canon_rec", "canon_rules_eq", "std_axiom_ok",
   "std_ax_family", "find_pinned", "trust_compiler_ok", "find_pinned_cv", "of_reduce_ax_ok",
   "of_reduce_op", "of_reduce_pin_a"]

/-- The definition check (the definition arm's gates are specified, not closed here). -/
def defnArmFns : List FnName := ["check_defn_val"]

/-- The functions the arms reach. -/
def armFns : List FnName := thmArmFns ++ opqArmFns ++ qaxArmFns ++ defnArmFns

/-- A program with the arms' text. -/
structure ArmProg (p : Prog) : Prop extends TextProg p armText armFns

end L.Arena
