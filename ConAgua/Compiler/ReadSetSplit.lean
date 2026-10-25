import ConAgua.L.Agree
import ConAgua.Compiler.WriteSetSplit

/-!
# Read sets of a large program, one function at a time (lane parmode)

`readsIn p S S8 fs` (`L/Agree.lean`) by `decide` looks up every `f ∈ fs` in `p` and every callee
in `fs` by `String` comparison: far too big for the checker's program. As `closedW_of_all`
(`WriteSetSplit.lean`) does for write sets, `readsIn_of_all` splits it: the function set as a
tree of name codes (`names_tree`), the per-function check `rdChk S S8 t x` (not in the tree, or
its body passes `Stmt.rdOk` with the callees tested in the tree), and `prog_all` for one kernel
check per chunk of functions.
-/

namespace L.Compiler

open L

/-- One function's read-set check: not in the set `t`, or its body names only word arrays of `S`
and byte arrays of `S8` and calls only functions of `t`. -/
def rdChk (S S8 : ArrId → Bool) (t : NTree) (x : FnName × FunDecl) : Bool :=
  !(t.find (nameCode x.1)).isSome || x.2.body.rdOk S S8 fun g => (t.find (nameCode g)).isSome

/-- **A program's read set from per-function checks** (`rdChk` for every function of `p`, by
`prog_all`). -/
theorem readsIn_of_all {p : Prog} {S S8 : ArrId → Bool} {fs : List FnName} {t : NTree}
    (ht : namesTree fs = some t) (h : ∀ x ∈ p, rdChk S S8 t x = true) :
    readsIn p S S8 fs = true := by
  simp only [readsIn, List.all_eq_true]
  intro f hf
  split
  · rename_i fd hfd
    obtain ⟨_, _, hp, -⟩ := List.lookup_eq_some_iff.mp hfd
    have hx := h _ (hp ▸ List.mem_append_right _ List.mem_cons_self)
    simp only [rdChk, namesTree_spec ht, hf, decide_true, Bool.not_true, Bool.false_or] at hx
    exact hx
  · rfl

end L.Compiler
