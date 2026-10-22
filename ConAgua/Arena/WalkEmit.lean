import ConAgua.Compiler.Run
import ConAgua.Compiler.WF
import ConAgua.Arena.WalkBench

/-! `lake env lean --run ConAgua/Arena/WalkEmit.lean OUT.s` writes the compiled `benchProg`
(entry `bb_bench`, no byte arrays, the 62 word arrays of the arena layout, through the level-parameter columns) for `harness/walk.c`.

The compiler (`ConAgua/Compiler/Compile.lean`) emits the one-destination form of `imul` directly,
so `asmText` (`ConAgua/Compiler/Run.lean`) prints it in the two-operand form every assembler
accepts with no separate normalisation step; see `DESIGN.md`, lane `walk`/`imul`, and
`docs/gaps/kraken-att-imul-three-operand.lean`.
-/

open L L.Compiler L.Arena

#guard Prog.wf (Prog.tab benchProg 0 62) benchProg
#guard Prog.wf (Prog.tab walkProg 0 62) walkProg

def main (args : List String) : IO Unit := do
  let out := args.headD "walk.s"
  IO.FS.writeFile out (asmText (Prog.tab benchProg 0 62) benchProg "bb_bench")
