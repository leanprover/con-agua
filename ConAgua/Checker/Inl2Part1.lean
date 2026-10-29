import ConAgua.Checker.Inl1

/-! Part 1 of `checkerProgI` (`ConAgua/Checker/ProgI.lean`): the kernel-checked second inlining
round of functions 784 … 1567 of `checkerProg1`. -/

namespace L.Checker

open L L.Compiler

inl_round_fns checkerProgI : 80 checkerIdx checkerProg1 via (inlRound 80 checkerIdx checkerProg) 784 1568

end L.Checker
