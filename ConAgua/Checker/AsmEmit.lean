module

public import ConAgua.Checker.ProgTab
public import ConAgua.Checker.ProgI
public import ConAgua.Checker.AsmX
public import ConAgua.Compiler.Run
public import ConAgua.Compiler.Abi
public import ConAgua.Compiler.AbiCmp
meta import ConAgua.Checker.ProgTab
meta import ConAgua.Checker.ProgI
meta import ConAgua.Checker.AsmX
meta import ConAgua.Compiler.Run
meta import ConAgua.Compiler.Abi
meta import ConAgua.Compiler.AbiCmp

@[expose] public section

/-! `lake env lean --run ConAgua/Checker/AsmEmit.lean OUT.s` prints the checker's code: the entry
stub (`ConAgua/Compiler/Abi.lean`, lane `abi`), then `compileProgX checkerX checkerTab checkerProgI "check"`
(the checker with its small leaves inlined, `ConAgua/Checker/ProgI.lean`)
(computed by running the compiler), plus the symbols
of `tabSymbols` (`main.c` reads `ca_nw`) and `ca_diag` (no diagnostics
array: `checkerProg`'s stubs just abort). `scripts/asm_file.py` writes the committed file `checker.s` with it. Nothing
here is trusted: the final theorems are about the file as the parser reads it, and the kernel
checks that it is the compiler's output (`checkerFile_eq`, `ConAgua/Checker/AsmFileEq.lean`). -/

open L.Compiler L.Checker

def main (args : List String) : IO Unit := do
  let out := args.headD "checker.s"
  let code := compileProgX checkerX checkerTab checkerProgI "check"
  IO.FS.writeFile out (asmTextAbiPar checkerTab L.Arena.MODE L.Arena.PLO L.Arena.PHI L.Arena.OUT L.Arena.HDRF L.Arena.CTLF L.Arena.hdrHw L.Arena.frozenIdsL
      L.Arena.parOwnedL (code ++ cmpStub checkerTab L.Arena.MODE L.Arena.OUT L.Arena.parOwnedL) ++
    tabSymbols checkerTab ++ cmpSymbols checkerTab L.Arena.parOwnedL ++
    ".globl ca_compare\n.globl ca_diag\nca_diag: .quad -1\n")
  IO.println s!"wrote {out}: {code.length} directives, nb {checkerTab.nb}, nw {checkerTab.nw}"
