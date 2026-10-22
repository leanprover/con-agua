import ConAgua.Checker.Prog
import ConAgua.Arena.LoopT

/-!
# The core leaves the declaration loop's state alone (lane `loopt`)

`ConAgua/Arena/LoopT.lean`'s program hypothesis `CoreLoopClosed`, for the checker's program: every
function the stage's core entry points reach (`stageCoreFns`) stores only into arrays a step may
write (`stepA`) other than `EREC`, `IW`, `PINS`, and into `CTL` words a step may write (`stepC`)
other than `129`, `200`. So a core call keeps `LoopT` (`LoopT.of_core`).
-/

namespace L.Checker

open L.Arena L.Ind

theorem checkerProg_coreLoop : CoreLoopClosed checkerProg := by
  unfold CoreLoopClosed; decide +kernel

end L.Checker
