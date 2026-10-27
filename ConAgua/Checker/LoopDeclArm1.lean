import ConAgua.Arena.DeclArmLoop
import ConAgua.Checker.LoopProgTac

/-!
# The arms' text agreement for the checker's program, parts 0‥5 (lane `loopt2`)

The first half of `LoopDeclArm.lean`'s lookups (split to keep each module's elaboration small).
-/

namespace L.Checker

open L.Arena L.Ind L.Compiler

/-- `armFns` but `openFns`, part 0. -/
def armOwn0 : List FnName :=
  ["check_decl_thm", "erec_ci", "erec_alloc", "dlp_copy", "check_constant_val", "install_header",
   "env_find", "env_row_get", "env_ix", "reserved_contains", "reserved_from", "cv_lps"]

set_option maxRecDepth 100000 in
theorem checkerProg_armOwn0 : ∀ f ∈ armOwn0, checkerProg.lookup f = armText.lookup f :=
  List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- `armFns` but `openFns`, part 1. -/
def armOwn1 : List FnName :=
  ["er_to_iw", "iw_alloc", "er_copy", "sl_nodup", "sl_contains", "check_thm_val", "pin_word",
   "lvl_eq_fueled", "lvl_eq_c", "lq_find", "lvl_eq_rec"]

set_option maxRecDepth 100000 in
theorem checkerProg_armOwn1 : ∀ f ∈ armOwn1, checkerProg.lookup f = armText.lookup f :=
  List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- `armFns` but `openFns`, part 2. -/
def armOwn2 : List FnName :=
  ["lvl_eq", "lv_equiv", "lv_eq", "lv_node", "lv_simp", "lh_mk", "lv_comb", "lv_leq", "lv_rest",
   "lv_imax", "lv_cases", "lv_cases_at"]

set_option maxRecDepth 100000 in
theorem checkerProg_armOwn2 : ∀ f ∈ armOwn2, checkerProg.lookup f = armText.lookup f :=
  List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- `armFns` but `openFns`, part 3. -/
def armOwn3 : List FnName :=
  ["lv_subsimp", "lv_subst", "lv_imax_l", "lv_dist1", "lv_dist2", "lv_imax_r", "lq_put",
   "install_value_guards", "env_push", "env_row_set", "check_decl_opaque", "check_opaque_val"]

set_option maxRecDepth 100000 in
theorem checkerProg_armOwn3 : ∀ f ∈ armOwn3, checkerProg.lookup f = armText.lookup f :=
  List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- `armFns` but `openFns`, part 4. -/
def armOwn4 : List FnName :=
  ["pin_at", "check_reduce_pin", "reduce_stored_ok", "reduce_op_cv_a", "matches_pin", "cv_eq",
   "er_sl_eq", "reduce_elem_ok", "ci_eq", "er_sl_at"]

set_option maxRecDepth 100000 in
theorem checkerProg_armOwn4 : ∀ f ∈ armOwn4, checkerProg.lookup f = armText.lookup f :=
  List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- `armFns` but `openFns`, part 5. -/
def armOwn5 : List FnName :=
  ["ci_eq_rest", "hint_eq", "caps_eq", "caps_eq_a", "b_eq", "caps_eq_b", "pw_eq", "caps_eq_c",
   "rules_eq", "rule_eq_but_rhs", "rule_eq_a", "rule_eq_b"]

set_option maxRecDepth 100000 in
theorem checkerProg_armOwn5 : ∀ f ∈ armOwn5, checkerProg.lookup f = armText.lookup f :=
  List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end L.Checker
