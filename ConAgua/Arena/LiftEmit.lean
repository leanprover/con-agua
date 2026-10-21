import ConAgua.Compiler.Run
import ConAgua.Compiler.WF
import ConAgua.Arena.LiftBenchComp

/-! `lake env lean --run ConAgua/Arena/LiftEmit.lean OUT.s` writes the compiled `liftBenchProg`
(entry `lift_bench`, 47 word arrays: the full layout through the derived-range arrays and the
lift memo) for `harness/lift.c`. `WalkEmit.lean`'s doc comment on the compiler's `imul` form
applies here unchanged. -/

open L L.Compiler L.Arena

#guard Prog.wf (Prog.tab liftBenchProg 0 47) liftBenchProg

def main (args : List String) : IO Unit := do
  let out := args.headD "lift.s"
  IO.FS.writeFile out (asmText (Prog.tab liftBenchProg 0 47) liftBenchProg "lift_bench")
