import ConAgua.Checker.Prog
import ConAgua.Arena.IndReal

/-!
# The real stub replacements' program bundles for the checker's program (lane `indproofs4`)

`Arena/IndReal.lean`'s bundles (`RrnF`, `RrbF`, …: `ProgHas p P` for a callee's call-closed list
`P`) for `checkerProg`, one `rfl` lookup per function (no decision over the whole program).
-/

namespace L.Checker

open L.Arena L.Ind

set_option maxRecDepth 100000 in
theorem checkerProg_rrn : RrnF checkerProg :=
  .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl .nil

set_option maxRecDepth 100000 in
theorem checkerProg_rrb : RrbF checkerProg :=
  .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <|
  .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl .nil

end L.Checker
