import ConAgua.Checker.Inl2Part0
import ConAgua.Checker.Inl2Part1

namespace L.Checker

open L L.Compiler

/-- **The program the compiler compiles**: `checkerProg` with its small leaves inlined, two rounds
(`checkerProgI_inline`), as a literal. -/
inl_round checkerProgI : 80 checkerIdx checkerProg1 via (inlRound 80 checkerIdx checkerProg)

theorem checkerProgI_inline : inlineProg 80 checkerIdx 2 checkerProg = checkerProgI := by
  rw [inlineProg, checkerProg1_eq, inlineProg, checkerProgI_eq, inlineProg]

end L.Checker
