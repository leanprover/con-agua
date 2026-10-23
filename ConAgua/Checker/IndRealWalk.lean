import ConAgua.Checker.Prog
import ConAgua.Arena.IndRealWalk

/-!
# The walk reads' program bundles for the checker's program (lane `indproofs4`)

`Arena/IndRealWalk.lean`'s bundles (`BvbProg` for `bvar_b`, `loose_bvars_bounded_fast`; `HfF`
for `fvar_b`, `has_fvar_fast`) for `checkerProg`, one `rfl` lookup per function.
-/

namespace L.Checker

open L.Arena L.Ind

set_option maxRecDepth 100000 in
theorem checkerProg_bvb : BvbProg checkerProg :=
  .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <|
  .cons rfl <| .cons rfl .nil

set_option maxRecDepth 100000 in
theorem checkerProg_hf : HfF checkerProg :=
  .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <|
  .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <|
  .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <|
  .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <|
  .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <|
  .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <|
  .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <|
  .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .nil

end L.Checker
