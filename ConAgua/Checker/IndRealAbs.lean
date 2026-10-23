import ConAgua.Checker.Prog
import ConAgua.Arena.IndRealAbs

/-!
# `abstract1_fast`'s program bundle for the checker's program (lane `indproofs4`, helper `abs`)

`Arena/IndRealAbs.lean`'s bundle `AbF` (the adapter, the `abstract1` walk and `abs_entry`) for
`checkerProg`, one `rfl` lookup per function.
-/

namespace L.Checker

open L.Arena L.Ind

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem checkerProg_ab : AbF checkerProg :=
  .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <|
  .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <|
  .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <|
  .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <|
  .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <|
  .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <|
  .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <|
  .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .nil

end L.Checker
