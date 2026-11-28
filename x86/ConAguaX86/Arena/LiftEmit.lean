module

public import ConAguaX86.Compiler.Run
public import ConAgua.Compiler.WF
public import ConAgua.Arena.LiftBenchComp
meta import ConAguaX86.Compiler.Run
meta import ConAgua.Compiler.WF
meta import ConAgua.Arena.LiftBenchComp

@[expose] public section

/-! `lake env lean --run x86/ConAguaX86/Arena/LiftEmit.lean OUT.s` writes the compiled `liftBenchProg`
(entry `lift_bench`, 62 word arrays: the full layout through the level-parameter columns and the
lift memo) for `harness/lift.c`. `WalkEmit.lean`'s doc comment on the compiler's `imul` form
applies here unchanged. -/

open L L.Compiler L.Arena

#guard Prog.wf (Prog.tab liftBenchProg) liftBenchProg

def main (args : List String) : IO Unit := do
  let out := args.headD "lift.s"
  IO.FS.writeFile out (asmText (Prog.tab liftBenchProg) liftBenchProg "lift_bench")
