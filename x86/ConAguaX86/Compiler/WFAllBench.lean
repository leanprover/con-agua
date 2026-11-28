module

public import ConAgua.Compiler.WF
public import ConAgua.Arena.Inst1Bench
public import ConAgua.Arena.Inst1BenchComp
public import ConAgua.Arena.LiftBench
public import ConAgua.Arena.LiftBenchComp
meta import ConAgua.Compiler.WF
meta import ConAgua.Arena.Inst1Bench
meta import ConAgua.Arena.Inst1BenchComp
meta import ConAgua.Arena.LiftBench
meta import ConAgua.Arena.LiftBenchComp

@[expose] public section

/-! The benchmark programs pass the compiler's static check (see `WFAll.lean`). -/

open L.Compiler

#guard Prog.wfAuto L.Arena.instTestProg
#guard Prog.wfAuto L.Arena.inst1BenchProg
#guard Prog.wfAuto L.Arena.liftTestProg
#guard Prog.wfAuto L.Arena.liftBenchProg
