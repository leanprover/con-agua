import ConAgua.Checker.Prog
import ConAgua.Arena.IndRealLvlZ

/-!
# `lv_zero_caps`' program bundle for the checker's program (lane `indproofs4`, helper `lvl`)

`Arena/IndRealLvlZ.lean`'s `LzcF` (`ProgHas p lzcP`) for `checkerProg`, one `rfl` lookup per
function.
-/

namespace L.Checker

open L.Arena L.Ind

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem checkerProg_lzc : LzcF checkerProg :=
  .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl <| .cons rfl .nil

end L.Checker
