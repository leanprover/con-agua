import ConAgua.Checker.Prog
import ConAgua.Arena.IndRealSpine

/-!
# The spine adapters' program bundles for the checker's program (lane `indproofs4`, helper `spine`)

`Arena/IndRealSpine.lean`'s bundles (`GafF`, …: `ProgHas p P` for an adapter's call-closed list
`P`) for `checkerProg`, one `rfl` lookup per function.
-/

namespace L.Checker

open L.Arena L.Ind

set_option maxRecDepth 100000 in
theorem checkerProg_gaf : GafF checkerProg :=
  .cons rfl <| .cons rfl .nil

end L.Checker
