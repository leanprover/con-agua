import ConAgua.Checker.Prog
import ConAgua.Arena.IndRealFvt

/-!
# `fvar_type_d`, `fvar_type_ds`, `get_app_args_f`: program bundles for the checker's program (lane `indproofs4`, helper `fvt`)

`Arena/IndRealFvt.lean`'s bundles (`ProgHas p P` for each function's call-closed list `P`) for
`checkerProg`, one `rfl` lookup per function. They are fields of `AdF` (`Checker/IndRealSpine.lean`).
-/

namespace L.Checker

open L.Arena L.Ind

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem checkerProg_ftd : FtdF checkerProg := .cons rfl <| .cons rfl .nil

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem checkerProg_ftds : FtdsF checkerProg :=
  .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl .nil

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem checkerProg_gaa : GaaF checkerProg :=
  .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl .nil

end L.Checker
