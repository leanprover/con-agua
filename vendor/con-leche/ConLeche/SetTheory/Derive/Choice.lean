module

public import ConLeche.SetTheory.Derive.Graphs

@[expose] public section

/-!
# Choice: the global selector

A first-order development of Tarski–Grothendieck set theory asserts (or
derives from Axiom A) an axiom of choice, because it cannot reach the
meta-level.  Here the meta-logic is Lean with `Classical.choice`, so
choice over `V` is *derived*:

* `schoice : V → V` — a global selector, `schoice A ∈ A` whenever `A`
  is inhabited (Lean-level choice on the membership predicate).
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

open Classical in
/-- Global choice: a uniform selection from nonempty sets.  On sets
without members (and only there) it returns the set itself. -/
noncomputable def schoice (A : V) : V :=
  if h : ∃ x, x ∈ˢ A then Classical.choose h else A

theorem schoice_mem {A x : V} (hx : x ∈ˢ A) : schoice A ∈ˢ A := by
  unfold schoice
  rw [dite_eq_left ⟨x, hx⟩]
  exact Classical.choose_spec (⟨x, hx⟩ : ∃ x, x ∈ˢ A)

attribute [irreducible] schoice

end ConLeche.SetTheory
