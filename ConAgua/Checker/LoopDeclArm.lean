import ConAgua.Checker.LoopDeclArm1

/-!
# The arms' text agreement for the checker's program (lane `loopt2`)

As `LoopDeclAgree.lean`, for `armText` on `armFns` (split off to keep each module's elaboration
small; parts 0‥5 in `LoopDeclArm1.lean`): `ArmProg checkerProg`.
-/

namespace L.Checker

open L.Arena L.Ind L.Compiler

/-- `armFns` but `openFns`, part 6. -/
def armOwn6 : List FnName :=
  ["reduce_pin_guard", "reduce_decl_pin", "reduce_cert_var", "const_e", "intern_const",
   "const_find", "const_push", "intern_fvar", "fvar_find", "fvar_push", "mk_app", "der_b"]

set_option maxRecDepth 100000 in
theorem checkerProg_armOwn6 : ∀ f ∈ armOwn6, checkerProg.lookup f = armText.lookup f :=
  List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- `armFns` but `openFns`, part 7. -/
def armOwn7 : List FnName :=
  ["intern_app", "app_find", "app_push", "check_decl_quot", "quot_pin_hit", "ci_to_cv",
   "intern_zero", "zero_find", "zero_push", "intern_succ", "succ_find", "succ_push"]

set_option maxRecDepth 100000 in
theorem checkerProg_armOwn7 : ∀ f ∈ armOwn7, checkerProg.lookup f = armText.lookup f :=
  List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- `armFns` but `openFns`, part 8. -/
def armOwn8 : List FnName :=
  ["intern_sort", "sort_find", "sort_push", "cv_new", "cv_canon_eq", "canon_ctx", "canon_names",
   "canon_names_go", "intern_nanon", "nanon_find", "nanon_push", "intern_nnum"]

set_option maxRecDepth 100000 in
theorem checkerProg_armOwn8 : ∀ f ∈ armOwn8, checkerProg.lookup f = armText.lookup f :=
  List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- `armFns` but `openFns`, part 9. -/
def armOwn9 : List FnName :=
  ["nnum_find", "nnum_push", "sl_cons", "iw_copy", "canon_expr_eq", "e_view", "canon_level_eq",
   "canon_name_map", "sl_find", "sl_getd", "canon_levels_eq", "view_ls"]

set_option maxRecDepth 100000 in
theorem checkerProg_armOwn9 : ∀ f ∈ armOwn9, checkerProg.lookup f = armText.lookup f :=
  List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- `armFns` but `openFns`, part 10. -/
def armOwn10 : List FnName :=
  ["ls_node", "pool_copy", "canon_level_list_eq", "check_basis_decl", "find_is",
   "install_basis_decls", "install_basis_decl", "check_decl_axiom", "ci_canon_eq", "ci_canon_defn",
   "ci_canon_rec", "canon_rules_eq"]

set_option maxRecDepth 100000 in
theorem checkerProg_armOwn10 : ∀ f ∈ armOwn10, checkerProg.lookup f = armText.lookup f :=
  List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- `armFns` but `openFns`, part 11. -/
def armOwn11 : List FnName :=
  ["std_axiom_ok", "std_ax_family", "find_pinned", "trust_compiler_ok", "find_pinned_cv",
   "of_reduce_ax_ok", "of_reduce_op", "of_reduce_pin_a", "check_defn_val"]

set_option maxRecDepth 100000 in
theorem checkerProg_armOwn11 : ∀ f ∈ armOwn11, checkerProg.lookup f = armText.lookup f :=
  List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), List.forall_mem_cons.2 ⟨lk_agree rfl (by chk_lk), fun _ h => absurd h List.not_mem_nil⟩⟩⟩⟩⟩⟩⟩⟩⟩

set_option maxRecDepth 100000 in
theorem armOwn_of : ∀ f ∈ armFns, f ∉ openFns →
    f ∈ armOwn0 ++ (armOwn1 ++ (armOwn2 ++ (armOwn3 ++ (armOwn4 ++ (armOwn5 ++ (armOwn6 ++ (armOwn7 ++ (armOwn8 ++ (armOwn9 ++ (armOwn10 ++ armOwn11)))))))))) := by
  decide +kernel

theorem checkerProg_armAgree : ∀ f ∈ armFns, f ∉ openFns → checkerProg.lookup f = armText.lookup f := by
  intro f hf ho
  have h := armOwn_of f hf ho
  simp only [List.mem_append] at h
  exact h.elim (checkerProg_armOwn0 f) fun h => h.elim (checkerProg_armOwn1 f) fun h =>
    h.elim (checkerProg_armOwn2 f) fun h => h.elim (checkerProg_armOwn3 f) fun h =>
    h.elim (checkerProg_armOwn4 f) fun h => h.elim (checkerProg_armOwn5 f) fun h =>
    h.elim (checkerProg_armOwn6 f) fun h => h.elim (checkerProg_armOwn7 f) fun h =>
    h.elim (checkerProg_armOwn8 f) fun h => h.elim (checkerProg_armOwn9 f) fun h =>
    h.elim (checkerProg_armOwn10 f) (checkerProg_armOwn11 f)

end L.Checker
