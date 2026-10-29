import ConAgua.Checker.ProgIdx

/-! Part 0 of `checkerProg1` (`ConAgua/Checker/Inl1.lean`): the kernel-checked first inlining round
of functions 0 … 391 of `checkerProg`. -/

namespace L.Checker

open L L.Compiler

inl_round_fns checkerProg1 : 80 checkerIdx checkerProg 0 392

end L.Checker
