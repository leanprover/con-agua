import ConAgua.Arena.StoreDen
import ConAgua.Arena.WhnfBase

/-!
# `CoreDen`: stored levels read back under `CoreS` (lane `defeq2`)

The one assumption on the store that the knot's level readers make (`StoreDen.lean`), stated over
`CoreS` until it is a field of it (then `CoreDen` is `fun … hS => hS.den`).
-/

open ConRon.Arena

namespace L.Arena

/-- **Stored levels read back under `CoreS`.** -/
def CoreDen : Prop :=
  ∀ (dn : NIdx → Option ConLeche.Name) (m : Mem) (a : AState) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb : Word), CoreS dn m a vis fe M eb → StoreDen m a fe

end L.Arena
