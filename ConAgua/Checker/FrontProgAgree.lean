import ConAgua.Checker.LoopProgTac
import ConAgua.Front.FrontRun

/-!
# `checkerProg` agrees with `frontAllProg` on what `front_run` reaches (lane `pipeline`)

The 267 functions reachable from `front_run` in `checkerProg` (`frontFns`): each is bound in
`checkerProg` as in `L.Front.frontAllProg`, one lookup each, by position (`front_agree`, below). `frontAllProg` binds three more functions that `checkerProg` does not
(`validate`, `str_put`, `apply_ind_line`: nothing reachable from `check` calls them), so the
lookup bundles of `frontRun_refines` do not hold at `checkerProg`; `FrontProg.lean` transfers the
run instead (`invoke_exec_agree`).
-/

namespace L.Checker

open L L.Compiler

set_option Elab.async false

/-! ## Lookups by position

`rfl` on `checkerProg.lookup f = frontAllProg.lookup f` compares `f` with the names before it as
`String`s, in the elaborator and again in the kernel (~10 s per chunk of twelve, 264 s in all).
Here both sides are lookups by position (`lk_of_idx`, `LoopProgTac.lean`): the names of both
programs are distinct (`checkerProg_nodup`; `frontAll_nodup`, one kernel check over name codes),
and the kernel walks to the position, comparing no `String`. `frontAllProg` is a computed list
(`filter` on names), so its positions are read off its evaluation once (`frontAll_lit`). -/

theorem frontAll_nodup : (L.Front.frontAllProg.map (·.1)).Nodup := by
  have h : (L.Compiler.progTree L.Front.frontAllProg).isSome = true := by decide +kernel
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp h
  exact (L.Compiler.progTree_spec ht).1

theorem lkF_of_idx {i : Nat} {f : FnName} {fd : FunDecl}
    (h : L.Front.frontAllProg[i]? = some (f, fd)) : L.Front.frontAllProg.lookup f = some fd :=
  lookup_of_mem frontAll_nodup (List.mem_of_getElem? h)

open Lean Meta Elab Tactic in
/-- The positions of a program's names (first binding), by compiled code. -/
unsafe def progPos (p : Lean.Expr) : MetaM (Std.HashMap String Nat) := do
  let e := mkApp3 (mkConst ``List.map [0, 0]) (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``String)
    (mkConst ``FunDecl)) (mkConst ``String) (mkApp2 (mkConst ``Prod.fst [0, 0]) (mkConst ``String)
    (mkConst ``FunDecl))
  let ns ← evalExpr (List String) (mkApp (mkConst ``List [0]) (mkConst ``String)) (mkApp e p)
  let mut m : Std.HashMap String Nat := {}
  for (n, i) in ns.zipIdx do
    unless m.contains n do m := m.insert n i
  return m

open Lean Meta Elab Tactic in
/-- The element at position `n` of a program, by `whnf`. -/
def progElem (p : Lean.Expr) (n : Nat) : MetaM Lean.Expr := do
  let mut l ← whnfD p
  for _ in [0:n] do l ← whnfD l.appArg!
  unless l.isAppOfArity ``List.cons 3 do throwError "front_lk: no element {n}"
  return l.appFn!.appArg!

open Lean Meta Elab Tactic in
/-- Close `checkerProg.lookup "f" = frontAllProg.lookup "f"`: both sides by position (`lk_of_idx`,
`lkF_of_idx`), the body taken from `checkerProg`'s element. -/
def frontLk (pc pf : Std.HashMap String Nat) (g : MVarId) : MetaM Unit := do
  let ty := (← instantiateMVars (← g.getType)).cleanupAnnotations.headBeta
  let some (_, lhs, rhs) := ty.eq? | throwError "front_agree: not an equation: {ty}"
  let fE := lhs.appFn!.appArg!
  let .lit (.strVal f) := fE | throwError "front_agree: not a literal name: {fE}"
  let some i := pc[f]? | throwError "front_agree: {f} is not in checkerProg"
  let some j := pf[f]? | throwError "front_agree: {f} is not in frontAllProg"
  let fd := (← progElem (mkConst ``checkerProg) i).appArg!
  let elemTy := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``String) (mkConst ``FunDecl)
  let refl := mkApp2 (mkConst ``Eq.refl [1]) (mkApp (mkConst ``Option [0]) elemTy)
    (mkApp2 (mkConst ``Option.some [0]) elemTy
      (mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``String) (mkConst ``FunDecl) fE fd))
  let hc := mkApp4 (mkConst ``lk_of_idx) (mkNatLit i) fE fd refl
  let hf := mkApp4 (mkConst ``lkF_of_idx) (mkNatLit j) fE fd refl
  let optTy := mkApp (mkConst ``Option [0]) (mkConst ``FunDecl)
  let some_ := mkApp2 (mkConst ``Option.some [0]) (mkConst ``FunDecl) fd
  g.assign (mkApp6 (mkConst ``Eq.trans [1]) optTy lhs some_ rhs hc
    (mkApp4 (mkConst ``Eq.symm [1]) optTy rhs some_ hf))

open Lean Meta Elab Tactic in
/-- `front_agree` closes `∀ f ∈ l, checkerProg.lookup f = frontAllProg.lookup f` for a list `l`
that unfolds to a literal, one `frontLk` per name. -/
elab "front_agree" : tactic => do
  let pc ← unsafe progPos (mkConst ``checkerProg)
  let pf ← unsafe progPos (mkConst ``L.Front.frontAllProg)
  repeat
    let gs ← getGoals
    let some g := gs.head? | break
    let ty ← instantiateMVars (← g.getType)
    if ty.isForall then
      try evalTactic (← `(tactic| refine List.forall_mem_cons.2 ⟨?_, ?_⟩))
      catch _ => evalTactic (← `(tactic| exact fun _ h => absurd h List.not_mem_nil))
    else
      frontLk pc pf g
      setGoals gs.tail

/-- The functions reachable from `front_run` in `checkerProg` (267). -/
def frontFns : List FnName :=
  ["front_run", "front_init", "front_line", "intern_nanon", "name_put", "intern_zero", "level_put", "scan_line", "skip_ws", "apply_any", "nanon_find", "nanon_push",
   "nsp_find", "nsp_put", "zero_find", "zero_push", "lsp_find", "lsp_put", "scan_line_loop", "rec_line_loop", "apply_rec", "rec_expr_loop", "apply_expr", "apply_dline",
   "next_member", "slot_nat", "scan_nat_list", "scan_str_name", "scan_num_name", "scan_app", "scan_binder", "scan_let", "scan_const", "scan_proj", "scan_quoted_nat", "scan_string",
   "scan_axiom", "scan_def", "scan_thm", "scan_opaque", "scan_quot", "scan_ind_decl", "skip_braced", "read_nat", "rec_nat_list", "rec_str_name", "rec_num_name", "apply_str",
   "apply_nnum", "apply_level", "expr_val", "expr_fresh", "expr_node", "expr_put", "rec_decl_line", "apply_ind", "apply_decl", "key_end", "value_at", "key_at",
   "num_end", "scan_binder_info", "scan_bool", "skip_digits", "str_close", "has_escape", "unescape", "utf8_valid", "scan_hints", "scan_ind_ctors", "scan_ind_recs", "scan_ind_types",
   "str_put_esc", "apply_nstr", "name_get", "name_fresh", "intern_nnum", "level_fresh", "level_get", "intern_succ", "intern_max", "intern_imax", "intern_param", "rec_obj",
   "esp_find", "intern_bvar", "intern_sort", "node_bin", "node_let", "node_proj", "node_const", "node_lit", "node_lit_str", "esp_put", "decl_val", "ind_fields",
   "validate_ind_d", "install_ind_d", "decl_kind", "decl_cv", "key_at_g1", "key_at_g2", "key_at_g3", "key_at_g4", "key_at_g5", "key_at_g6", "match_word", "match_lit",
   "byte_in", "hex4", "u_next", "utf8_char", "hints_obj", "scan_ind_ctor", "scan_ind_rec", "scan_ind_type", "esc_one", "utf8_put", "intern_nstr", "nnum_find",
   "nnum_push", "succ_find", "succ_push", "max_find", "max_push", "imax_find", "imax_push", "param_find", "param_push", "obj_val", "bvar_find", "bvar_push",
   "sort_find", "sort_push", "expr_get", "mk_app", "mk_lam", "mk_forall", "mk_let", "mk_proj", "ls_put", "intern_ls", "intern_const", "nat_dec",
   "intern_lit", "intern_lit_str", "rec_decl_obj", "decl_code", "if_reset", "ifr_alloc", "ind_obj", "vi_unsafe", "vi_nparams", "vi_map", "vi_listed", "ifl_nodup",
   "vi_tail", "dind_alloc", "inst_types", "inst_ctors", "inst_recs", "decl_push", "lp_put", "hex_val", "hex3", "hints_num", "scan_rules", "esc_sur",
   "lit_hash", "nstr_find", "nstr_push", "der_b", "intern_app", "intern_lam", "intern_forall", "intern_letE", "intern_proj", "ls_find", "ls_push", "const_find",
   "const_push", "dec_chunk", "nat_mad", "lit_find", "lit_push", "lit_find_str", "lit_push_str", "d_member", "ind_member", "vi_np_go", "ifl_alloc", "vi_map_go",
   "vi_listed_go", "ifl_contains", "store_fuel", "vi_order", "vi_k_expected", "vi_recs", "ind_type", "ind_ctor", "ind_rec", "scan_rule", "nstr_match", "app_find",
   "app_push", "lam_find", "lam_push", "forall_find", "forall_push", "letE_find", "letE_push", "proj_find", "proj_push", "ls_match", "lit_match", "lit_match_str",
   "hints_val", "str_code", "ind_slot", "ind_num", "ind_bool", "ind_nlist", "ind_list", "fld_put", "ifl_push", "vi_ids_go", "ctl_sum", "vi_order_go",
   "pi_result_d", "e_view", "lh_mk", "lv_equiv", "vi_nested", "vi_recs_go", "ind_cv", "ind_caps", "ind_rules", "limbs_eq", "match_dlit", "ifl_ids",
   "ind_size", "fld_alloc", "vi_order_in", "lv_eq", "lv_simp", "lv_leq", "vi_rec", "ind_rules_go", "vi_ctor", "lv_node", "lv_comb", "lv_rest",
   "name_rec_pre", "vi_rec_idx", "parse_rule_d", "ifl_find_last", "ind_pi_tele_len", "lv_imax", "pi_sort_tele_len", "lv_cases", "lv_imax_l", "lv_cases_at", "lv_dist1", "lv_dist2",
   "lv_imax_r", "lv_subsimp", "lv_subst"]

theorem checkerProg_frontAgree :
    ∀ f ∈ frontFns, checkerProg.lookup f = L.Front.frontAllProg.lookup f := by
  front_agree

end L.Checker
