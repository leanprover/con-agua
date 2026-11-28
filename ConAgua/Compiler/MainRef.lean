module

public import ConAgua.L.Semantics

@[expose] public section

/-!
# Target-independent compiler refinement (`Refines`) and `mem_of_lookup`

The compiler compiles `q`, the program after the L → L passes (the inliner,
`Compiler/Inline.lean`); the final theorems speak of `p`, the program as written. `Refines q p`:
a run of `q` with fuel `N` that does not run out of fuel is a run of `p` with fuel `N + abiInl`
(the same results and memory, or the same error), and `q` has `p`'s functions with their
parameter counts.
-/

namespace L.Compiler

open L

/-- The rounds of inlining before code generation (`Compiler/Inline.lean`). -/
def abiInl : Nat := 1

/-- **`q` refines `p`** (fuel `abiInl` apart). -/
structure Refines (q p : Prog) : Prop where
  run : ∀ N f vs m r, L.run q N f vs m = r → r ≠ .error .outOfFuel → L.run p (N + abiInl) f vs m = r
  lookup : ∀ f fd, p.lookup f = some fd → ∃ fd', q.lookup f = some fd' ∧ fd'.nparams = fd.nparams

theorem mem_of_lookup {p : Prog} {f : FnName} {fd : FunDecl} (h : p.lookup f = some fd) : (f, fd) ∈ p := by
  induction p with
  | nil => simp at h
  | cons q p ih =>
    obtain ⟨f', fd'⟩ := q
    simp only [List.lookup_cons] at h
    split at h
    · rename_i heq; cases h; have : f = f' := by simpa using heq
      subst this; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

end L.Compiler
