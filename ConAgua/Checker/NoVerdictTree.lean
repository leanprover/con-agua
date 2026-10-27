import ConAgua.Checker.NoVerdictFns
import ConAgua.Compiler.WriteSetSplit

/-!
# Membership in `nvFns` by its name tree

`f ∈ nvFns` by `decide +kernel` compares `f` with the names before it (1537 `String`
comparisons at most, ~2–13 s each check; 280 such checks in the error claims). `nvTree` is the
list as a search tree of name codes (`names_tree`, one kernel check); `nv_mem`/`nv_sub` answer a
membership by a lookup in it.
-/

namespace L.Checker

open L.Compiler

names_tree nvTree : nvFns

/-- `f ∈ nvFns` by a lookup in `nvTree` (use with `by decide +kernel`). -/
theorem nv_mem {f : FnName} (h : (nvTree.find (nameCode f)).isSome = true) : f ∈ nvFns := by
  rw [namesTree_spec nvTree.eq] at h
  exact of_decide_eq_true h

/-- `∀ f ∈ l, f ∈ nvFns` by lookups in `nvTree` (use with `by decide +kernel`). -/
theorem nv_sub {l : List FnName} (h : l.all (fun f => (nvTree.find (nameCode f)).isSome) = true) :
    ∀ f ∈ l, f ∈ nvFns := fun f hf => nv_mem (List.all_eq_true.mp h f hf)

end L.Checker
