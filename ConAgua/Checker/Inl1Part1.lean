import ConAgua.Checker.ProgIdx

/-! Part 1 of `checkerProg1` (`ConAgua/Checker/Inl1.lean`): the kernel-checked first inlining round
of functions 392 … 783 of `checkerProg`. -/

namespace L.Checker

open L L.Compiler

inl_round_fns checkerProg1 : 80 checkerIdx checkerProg 392 784

end L.Checker
