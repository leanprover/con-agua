module

public import ConAguaX86.Compiler.Run
public import ConAgua.Compiler.WF
public import ConAgua.Arena.LitRefine
meta import ConAguaX86.Compiler.Run
meta import ConAgua.Compiler.WF
meta import ConAgua.Arena.LitRefine

@[expose] public section

/-! `lake env lean --run x86/ConAguaX86/Arena/EmitStore.lean OUT.s` writes the compiled `storeProg`
(entry `nat_add_lit`, no byte arrays, 25 word arrays, the same arena layout as the walk) for
`scripts/check-asm.sh`. -/

open L L.Compiler L.Arena

#guard Prog.wf (Prog.tab storeProg) storeProg

def main (args : List String) : IO Unit := do
  let out := args.headD "store.s"
  IO.FS.writeFile out (asmText (Prog.tab storeProg) storeProg "nat_add_lit")
