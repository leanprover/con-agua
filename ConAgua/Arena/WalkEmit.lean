import ConAgua.Compiler.Run
import ConAgua.Compiler.WF
import ConAgua.Arena.WalkBench

/-! `lake env lean --run ConAgua/Arena/WalkEmit.lean OUT.s` writes the compiled `benchProg`
(entry `bb_bench`, no byte arrays, 25 word arrays) for `harness/walk.c`.

`asmText` (`ConAgua/Compiler/Run.lean`) already normalises the compiler's one `imul` to the
two-operand form every assembler accepts (`fixImul`, applied at the `Directive` level, not as a
textual patch); see `DESIGN.md`, lane `walk`, and `docs/gaps/kraken-att-imul-three-operand.lean`.
-/

open L L.Compiler L.Arena

#guard Prog.wf (Prog.tab benchProg 0 25) benchProg
#guard Prog.wf (Prog.tab walkProg 0 25) walkProg

def main (args : List String) : IO Unit := do
  let out := args.headD "walk.s"
  IO.FS.writeFile out (asmText (Prog.tab benchProg 0 25) benchProg "bb_bench")
