import ConAgua.Checker.Prog
import ConAgua.Arena.IndRealOpf

/-!
# `open_pis_at_fvars_f`'s program bundle for the checker's program (lane `indproofs4`, helper `opf`)

`Arena/IndRealOpf.lean`'s bundle `OpfF` (the entry, `opf_go`, `opa_go`, the stack and pool
helpers, `e_view`, the `fvar` store, the `inst_list` and `inst_entry` walks) for `checkerProg`,
one `rfl` lookup per function.
-/

namespace L.Checker

open L.Arena L.Ind

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checkerProg_opf : OpfF checkerProg :=
  .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <|
  .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <|
  .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <|
  .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <|
  .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <|
  .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <|
  .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <|
  .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <|
  .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <|
  .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <|
  .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <|
  .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <|
  .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <|
  .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <|
  .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .nil

end L.Checker
