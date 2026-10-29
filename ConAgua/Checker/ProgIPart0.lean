import ConAgua.Checker.ProgIdx

/-! Part 0 of `checkerProgI` (`ConAgua/Checker/ProgI.lean`): functions 0 … 454 of `checkerProg`
with their small leaves inlined, as literals, each with its kernel-checked equation
(`inl_round_fns`, `ConAgua/Compiler/InlineLit.lean`). -/

namespace L.Checker

open L L.Compiler

inl_round_fns checkerProgI : 80 checkerIdx checkerProg 0 455

end L.Checker
