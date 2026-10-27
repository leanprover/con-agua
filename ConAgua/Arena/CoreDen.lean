import ConAgua.Arena.WhnfBase

/-!
# `CoreDen`: stored levels read back under `CoreS` (lane `defeq2`)

The one assumption on the store that the knot's level readers make (`StoreDen.lean`), now the
field `CoreS.den` (`coreDen_of`); `CoreDen` stays the name the callee bundles use.
-/

open ConRon.Arena

namespace L.Arena

/-- **Stored levels read back under `CoreS`.** -/
def CoreDen : Prop :=
  ∀ (dn : NIdx → Option ConLeche.Name) (m : Mem) (a : AState) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb : Word), CoreS dn m a vis fe M eb → StoreDen dn m a fe

/-- **`CoreDen` holds**: it is the field `CoreS.den`. -/
theorem coreDen_of : CoreDen := fun _ _ _ _ _ _ _ hS => hS.den

end L.Arena
