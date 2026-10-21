import ConAgua.Compiler.WF
import ConAgua.Arena.Inst1Bench
import ConAgua.Arena.Inst1BenchComp
import ConAgua.Arena.LiftBench
import ConAgua.Arena.LiftBenchComp

/-! The benchmark programs pass the compiler's static check (see `WFAll.lean`). -/

open L.Compiler

#guard Prog.wfAuto L.Arena.instTestProg
#guard Prog.wfAuto L.Arena.inst1BenchProg
#guard Prog.wfAuto L.Arena.liftTestProg
#guard Prog.wfAuto L.Arena.liftBenchProg
