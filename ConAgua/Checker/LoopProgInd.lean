import ConAgua.Checker.LoopDecl
import ConAgua.Arena.LoopFns
import ConAgua.Arena.CheckerT

/-!
# The inductive records' path has a step's write set in the checker's program (lane `loopt3`)

`StepIn checkerProg indFns` (`Arena/CheckerT.lean`'s `LoopCallees.indIn`): the call closure of
`and_pin_ok`, `ind_block_to_erec`, `check_ind_decl` and `check_decl_defn` (1252 functions) writes
only a step's write set (`stepA`, `stepC`). The call-closed superset is `loopFns` (the loop's
closure, `Arena/LoopFns.lean`, generated) without the functions that reach a write of the pending
list, the promotion memos or the declaration index (`loopStepOut`: phase A's fold and its step,
phase B, the pending list's and the promotion's functions). Decided by per-chunk kernel checks as
`LoopDecl.lean`; if `loopFns` gains a function that reaches such a write, the check fails: add it
to `loopStepOut`.
-/

namespace L.Checker

open L.Arena L.Compiler

/-- The functions of `loopFns` that reach a store outside a step's write set (by `checkerProg`'s
call graph): the fold and its step, the pending list, the promotion. -/
def loopStepOut : List FnName :=
  ["caps_parts", "install_decl_step", "install_fold_go", "install_fold_next", "install_step",
   "is_none", "is_some", "pci_ctor", "pci_defn", "pci_ind", "pci_plain",
   "pci_rec", "pe_app", "pe_arm", "pe_at", "pe_clear", "pe_const", "pe_forall", "pe_lam",
   "pe_let", "pe_proj", "pe_put", "pend_push", "pl_arm", "pl_at", "pl_clear", "pl_put", "pls_arm",
   "pls_clear", "pls_put", "pn_arm", "pn_at", "pn_clear", "pn_put", "proj_a", "proj_b",
   "promote_caps", "promote_ci", "promote_ci_list", "promote_clear", "promote_cv", "promote_e",
   "promote_e_list", "promote_fire", "promote_l", "promote_l_list", "promote_l_pool",
   "promote_ls", "promote_n", "promote_n_list", "promote_new", "promote_new_consts",
   "promote_new_tables", "promote_proj_table", "promote_proj_tables",
   "promote_rule", "promote_rules", "promote_slice", "promote_vg", "ps_at"]

/-- The loop's functions with a step's write set: `loopFns` but `loopStepOut` (compared by name
codes, so the kernel compares no `String`s). -/
def loopStepFns : List FnName :=
  let out := loopStepOut.map nameCode
  loopFns.filter fun f => !out.contains (nameCode f)

/-- `loopStepFns` as a tree of name codes. -/
names_tree loopStepTree : loopStepFns

/-- Every function of the checker passes the step's per-function check on `loopStepFns`. -/
prog_all checkerProg_loopStepChk : checkerProg (wsChk CTL stepPa stepPc loopStepTree)

theorem checkerProg_loopStepClosed : closedA checkerProg stepA stepC loopStepFns = true :=
  closedW_of_all loopStepTree.eq stepPa_mem stepPc_mem checkerProg_loopStepChk

theorem indFns_sub : ∀ f ∈ indFns, f ∈ loopStepFns := by
  have h : indFns.all (fun f => (loopStepTree.find (nameCode f)).isSome) = true := by
    decide +kernel
  intro f hf
  have := List.all_eq_true.mp h f hf
  rw [namesTree_spec loopStepTree.eq] at this
  exact of_decide_eq_true this

/-- **The inductive records' path and the definition arm have a step's write set.** -/
theorem checkerProg_indIn : StepIn checkerProg indFns :=
  ⟨_, indFns_sub, checkerProg_loopStepClosed⟩

end L.Checker
