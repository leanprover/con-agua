import ConAgua.Checker.ProgIdx

/-! Part 2 of `checkerProg1` (`ConAgua/Checker/Inl1.lean`): the kernel-checked first inlining round
of functions 784 … 1175 of `checkerProg`. -/

namespace L.Checker

open L L.Compiler

inl_round_fns checkerProg1 : 80 checkerIdx checkerProg 784 1176

end L.Checker
