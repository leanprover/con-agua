import ConAgua.Checker.Prog
import ConAgua.Arena.IndRealNames
import ConAgua.Arena.IndRealIpf

/-!
# The name and level-list stubs' program bundles for the checker's program (lane `indproofs4`)

`Arena/IndRealNames.lean`'s and `Arena/IndRealIpf.lean`'s bundles (`NaF`, `NrF`, `IlF`, `PtF`,
`IpfF`: `ProgHas p P` for a callee's call-closed list `P`) for `checkerProg`, one `rfl` lookup per
function.
-/

namespace L.Checker

open L.Arena L.Ind

set_option maxRecDepth 100000 in
theorem checkerProg_na : NaF checkerProg :=
  .cons rfl <| .cons rfl <| .cons rfl .nil

set_option maxRecDepth 100000 in
theorem checkerProg_nr : NrF checkerProg :=
  .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <|
  .cons rfl .nil

set_option maxRecDepth 100000 in
theorem checkerProg_il : IlF checkerProg :=
  .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <|
  .cons rfl <| .cons rfl .nil

set_option maxRecDepth 100000 in
theorem checkerProg_pt : PtF checkerProg :=
  .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <|
  .cons rfl <| .cons rfl <| .cons rfl .nil

set_option maxRecDepth 100000 in
theorem checkerProg_ipf : IpfF checkerProg :=
  .cons rfl .nil

end L.Checker
