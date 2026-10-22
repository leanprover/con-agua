import ConAgua.Checker.Prog
import ConAgua.Arena.CoreErec

/-!
# The checker's core leaves `EREC` alone (lane `whnf3`)

`ConAgua/Arena/CoreErec.lean`'s program hypothesis, for the checker's program: every function the
core reaches (`coreFns`) stores into arrays other than the record pool. Discharges the
`ErecKept*` hypotheses of the ι refinements at `checkerProg`.
-/

namespace L.Checker

open L.Arena

theorem checkerProg_coreErec : closedA checkerProg coreErecA coreErecC coreFns = true := by
  decide +kernel

end L.Checker
