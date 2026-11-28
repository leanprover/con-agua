module

public import ConAguaX86.Compiler.Run
public import ConAgua.L.Examples
meta import ConAguaX86.Compiler.Run
meta import ConAgua.L.Examples

@[expose] public section

/-! `lake env lean --run x86/ConAguaX86/Compiler/EmitScan.lean OUT.s` writes the compiled `scanProg`
(entry `skip_braced`) for `harness/run.c`. -/

open L L.Compiler L.Examples

def main (args : List String) : IO Unit := do
  let out := args.headD "scan.s"
  IO.FS.writeFile out (asmText (Prog.tab scanProg) scanProg "skip_braced")
