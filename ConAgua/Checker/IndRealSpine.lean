import ConAgua.Checker.Prog
import ConAgua.Arena.IndRealSpine
import ConAgua.Checker.IndRealFvt

/-!
# The spine adapters' program bundle for the checker's program (lane `indproofs4`, helper `spine`)

`Arena/IndRealSpine.lean`'s bundle `AdF` (`ProgHas p P` for each adapter's call-closed list `P`)
for `checkerProg`, one `rfl` lookup per function.
-/

namespace L.Checker

open L.Arena L.Ind

set_option maxRecDepth 100000 in
theorem checkerProg_ad : AdF checkerProg :=
  ⟨.cons rfl <| .cons rfl .nil, .cons rfl <| .cons rfl .nil,
    .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <|
    .cons rfl .nil, checkerProg_gaa, checkerProg_ftd, checkerProg_ftds⟩

end L.Checker
