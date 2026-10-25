import ConAgua.Compiler.Run
import ConAgua.Compiler.WF
import ConAgua.Arena.LitRefine

/-! `lake env lean --run ConAgua/Arena/EmitStore.lean OUT.s` writes the compiled `storeProg`
(entry `nat_add_lit`, no byte arrays, 25 word arrays, the same arena layout as the walk) for
`harness/check-asm.sh`. -/

open L L.Compiler L.Arena

#guard Prog.wf (Prog.tab storeProg 0 260) storeProg

def main (args : List String) : IO Unit := do
  let out := args.headD "store.s"
  IO.FS.writeFile out (asmText (Prog.tab storeProg 0 260) storeProg "nat_add_lit")
