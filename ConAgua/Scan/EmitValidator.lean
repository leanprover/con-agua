module

public import ConAgua.Compiler.Run
public import ConAgua.Scan.Validator

@[expose] public section

/-! `lake env lean --run ConAgua/Scan/EmitValidator.lean OUT.s` writes the compiled validator
(`L.Scan.Validator.valProg`, entry `validate`) for `ConAgua/Compiler/harness/run.c`:
`run FILE` prints `ok 0` if every line of FILE scans, `ok N` if line `N` is the first that does
not. -/

open L L.Compiler L.Scan.Validator

def main (args : List String) : IO Unit := do
  let out := args.headD "validate.s"
  IO.FS.writeFile out (asmText (Prog.tab valProg) valProg "validate")
