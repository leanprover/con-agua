import ConAgua.Compiler.Run
import ConAgua.Compiler.WF
import ConAgua.Arena.Inst1BenchComp

/-! `lake env lean --run ConAgua/Arena/Inst1Emit.lean OUT.s` writes the compiled `inst1BenchProg`
(entry `inst1_bench`, 62 word arrays: the full layout through the level-parameter columns and both
the lift and `inst1` memos) for `harness/inst1.c`. `LiftEmit.lean`'s doc comment on the
compiler's `imul` form applies here unchanged. -/

open L L.Compiler L.Arena

#guard Prog.wf (Prog.tab inst1BenchProg 0 318) inst1BenchProg

def main (args : List String) : IO Unit := do
  let out := args.headD "inst1.s"
  IO.FS.writeFile out (asmText (Prog.tab inst1BenchProg 0 318) inst1BenchProg "inst1_bench")
