import ConAgua.Checker.Prog
import ConAgua.Arena.IndRealMemo

/-!
# The walk-memo callees' program bundles for the checker's program (lane `indproofs4`, helper `memo`)

`Arena/IndRealMemo.lean`'s bundle `I1lF` (`instantiate1_lift_fast`'s walk, `bvar_b`'s and
`lift_entry`'s programs) for `checkerProg`, one `rfl` lookup per function.
-/

namespace L.Checker

open L.Arena L.Ind

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem checkerProg_i1l : I1lF checkerProg :=
  .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <|
  .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <|
  .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <|
  .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <|
  .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <|
  .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <|
  .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <|
  .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .nil

end L.Checker
