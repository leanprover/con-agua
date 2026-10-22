import ConAgua.Checker.Prog
import ConAgua.Arena.IndTwin

/-!
# The core leaves the stage's pools and the pins alone (lane `indproofs3`)

`ConAgua/Arena/IndTwin.lean`'s program hypothesis `CoreStageClosed`, for the checker's program:
every function the stage's core entry points reach (`stageCoreFns`) stores into arrays other than
`IW`, `EREC`, `PINS`, and into `CTL` words other than `129`, `200`.
-/

namespace L.Checker

open L.Arena L.Ind

theorem checkerProg_coreStage : CoreStageClosed checkerProg := by
  unfold CoreStageClosed; decide +kernel

end L.Checker
