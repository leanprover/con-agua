import ConAgua.Verdict.DeclValE
import ConAgua.Checker.NoVerdictTree

/-!
# What the error claims assume about the program

The error half of a unified refinement (`RefE`, `Arena/Verdict.lean`) holds under `VerdictCtx p`:
the program's no-verdict functions are closed (`closedNV`, their errors claim nothing) and the
core stubs claim the twin's failures (`CoreStubsE`). The ok half does not need it.
-/

namespace L.Arena

/-- **What the error claims assume about the program.** -/
structure VerdictCtx (p : Prog) : Prop where
  nv : closedNV p L.Checker.nvFns = true
  core : CoreStubsE p

end L.Arena
