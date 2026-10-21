import ConAgua.Compiler.Run
import ConAgua.L.Examples

/-! `lake env lean --run ConAgua/Compiler/EmitScan.lean OUT.s` writes the compiled `scanProg`
(entry `skip_braced`) for `harness/run.c`. -/

open L L.Compiler L.Examples

def main (args : List String) : IO Unit := do
  let out := args.headD "scan.s"
  IO.FS.writeFile out (asmText { nb := 1, nw := 0 } scanProg "skip_braced")
