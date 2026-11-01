module

public import ConAgua.Checker.ProgI
public import ConAgua.Compiler.InlineCorrect
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

set_option maxRecDepth 100000 in
idx_lit_eq checkerIdx : checkerProg

inl_round_eq checkerProgI : 80 checkerIdx checkerProg

theorem checkerProgI_inline : inlineProg 80 checkerIdx 1 checkerProg = checkerProgI := by
  rw [inlineProg, checkerProgI_eq, inlineProg]

theorem checkerProgI_refines : Refines checkerProgI checkerProg where
  run N f vs m r h hr := inlineProg_run 1 checkerProg checkerIdx_eq N f vs m r (checkerProgI_inline ▸ h) hr
  lookup f fd h := checkerProgI_inline ▸ inlineProg_lookup 1 checkerProg f fd h

end L.Checker
