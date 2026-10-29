import ConAgua.Checker.ProgIPart0
import ConAgua.Checker.ProgIPart1
import ConAgua.Checker.ProgIPart2
import ConAgua.Checker.ProgIPart3

/-!
# The program the compiler compiles

`checkerProgI`: `checkerProg` with its leaves of at most 80 nodes inlined (one round of
`inlRound`, `ConAgua/Compiler/Inline.lean`), as a literal whose functions the kernel checked one
at a time (`ProgIPart0` … `ProgIPart3`). The whole-program checks of the compiled code
(`ProgNrtI`, `ProgSktI`, `ProgWfI`, the asm parts) read the literal. That it is the inliner's
output, `checkerProgI_eq`, and that it refines `checkerProg` are in `Checker/ProgIRef.lean`.
-/

namespace L.Checker

open L L.Compiler

/-- **The program the compiler compiles**: `checkerProg` with its small leaves inlined. -/
inl_round checkerProgI : 80 checkerIdx checkerProg

end L.Checker
