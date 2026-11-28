module

public import ConAguaX86.Compiler.Run
public import ConAgua.Compiler.WF
public import ConAgua.Arena.WalkBench
meta import ConAguaX86.Compiler.Run
meta import ConAgua.Compiler.WF
meta import ConAgua.Arena.WalkBench

@[expose] public section

/-! `lake env lean --run x86/ConAguaX86/Arena/WalkEmit.lean OUT.s` writes the compiled `benchProg`
(entry `bb_bench`, no byte arrays, the 318 word arrays of the arena layout, through the level-parameter columns and their tier-1 arrays) for `harness/walk.c`.

The compiler (`ConAgua/Compiler/Compile.lean`) emits the one-destination form of `imul` directly,
so `asmText` (`x86/ConAguaX86/Compiler/Run.lean`) prints it in the two-operand form every assembler
accepts with no separate normalisation step; see `DESIGN.md`, lane `walk`/`imul`, and
`docs/gaps/kraken-att-imul-three-operand.lean`.
-/

open L L.Compiler L.Arena

#guard Prog.wf (Prog.tab benchProg) benchProg
#guard Prog.wf (Prog.tab walkProg) walkProg

def main (args : List String) : IO Unit := do
  let out := args.headD "walk.s"
  IO.FS.writeFile out (asmText (Prog.tab benchProg) benchProg "bb_bench")
