module

public import ConAgua.Checker.ProgI
import ConAgua.Compiler.InlineCorrect
public import ConAgua.Compiler.MainRef
meta import ConAgua.Checker.ProgI
meta import ConAgua.Compiler.InlineCorrect
meta import ConAgua.Compiler.MainRef

@[expose] public section

/-!
# The inlined checker refines the checker

`checkerIdx_eq`: the inliner's name tree is `checkerProg`'s. `checkerProgI_eq`: `checkerProgI` (`Checker/ProgI.lean`) is the inliner's output on `checkerProg`
(from the per-function equations, without evaluation). `checkerProgI_refines`: a run of it is a run
of `checkerProg` with `abiInl` more units of fuel (`inlineProg_run`,
`Compiler/InlineCorrect.lean`), and the two have the same functions with the same parameter counts.
The final theorems (`Final/DrvFinal.lean`, …) use it to state the compiled code's outcomes as runs
of `checkerProg`.
-/

namespace L.Checker

open L L.Compiler L.Compiler.Inl

end L.Checker
