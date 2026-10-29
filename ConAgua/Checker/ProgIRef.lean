import ConAgua.Checker.ProgI
import ConAgua.Compiler.InlineCorrect
import ConAgua.Compiler.MainRef

/-!
# The inlined checker refines the checker

`checkerProgI_eq`: `checkerProgI` (`Checker/ProgI.lean`) is the inliner's output on `checkerProg`
(from the per-function equations, without evaluation). `checkerProgI_refines`: a run of it is a run
of `checkerProg` with `abiInl` more units of fuel (`inlineProg_run`,
`Compiler/InlineCorrect.lean`), and the two have the same functions with the same parameter counts.
The final theorems (`Final/DrvFinal.lean`, …) use it to state the compiled code's outcomes as runs
of `checkerProg`.
-/

namespace L.Checker

open L L.Compiler L.Compiler.Inl

inl_round_eq checkerProgI : 80 checkerIdx checkerProg

theorem checkerProgI_inline : inlineProg 80 checkerIdx 1 checkerProg = checkerProgI := by
  rw [inlineProg, checkerProgI_eq, inlineProg]

theorem checkerProgI_refines : Refines checkerProgI checkerProg where
  run N f vs m r h hr := inlineProg_run 1 checkerProg checkerIdx_eq N f vs m r (checkerProgI_inline ▸ h) hr
  lookup f fd h := checkerProgI_inline ▸ inlineProg_lookup 1 checkerProg f fd h

end L.Checker
