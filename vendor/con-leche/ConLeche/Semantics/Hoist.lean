module

public import ConLeche.Semantics.WellDenoted
public import ConLeche.Semantics.Sat

@[expose] public section

/-!
# The `WellDenoted` hoist at a `∀`

`hoist_pi` splits a hoisted `∀ ρ, Sat V Δa ρ → WellDenoted …` fact of a
`Π` node into its domain's and its codomain's (in the extended
context).  It mentions no fuel, no run and no environment.
-/

namespace ConLeche.Semantics
open ConLeche.Term (Term)
open ConLeche.SetModel

open SetTheory

universe w

variable {V : Type w} [SetTheory V]

/-- **The positive half: the hoist is self-propagating at a `∀`.**  A
hoisted `WellDenoted` of the node gives the domain's hoisted form and the
codomain's *in the extended context*, which is exactly the pair the
recursive call needs.  So paying the repair at the congruence costs
nothing beyond restating it. -/
theorem WellDenoted.hoist_pi {Δa : List Term} {A B : Term}
    (h : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenoted V ρ (.pi A B)) :
    (∀ ρ : Nat → V, Sat V Δa ρ → WellDenoted V ρ A) ∧
      (∀ ρ : Nat → V, Sat V (A :: Δa) ρ → WellDenoted V ρ B) := by
  refine ⟨fun ρ hρ => ((WellDenoted_pi V ρ A B) ▸ h ρ hρ).1,
    fun ρ hρ => ?_⟩
  have hcons : cons (ρ 0) (fun j => ρ (j + 1)) = ρ := by
    funext i; cases i with | zero => rfl | succ i => rfl
  have := ((WellDenoted_pi V _ A B) ▸ h _ (Sat_tail hρ)).2.2.1
    (ρ 0) (hρ 0 A rfl)
  rwa [hcons] at this

end ConLeche.Semantics
