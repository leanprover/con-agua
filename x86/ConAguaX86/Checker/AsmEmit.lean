module

public import ConAgua.Checker.ProgTab
public import ConAgua.Checker.ProgI
public import ConAguaX86.Checker.AsmX
public import ConAguaX86.Compiler.Run
public import ConAguaX86.Compiler.Abi
public import ConAguaX86.Compiler.AbiCmp
meta import ConAgua.Checker.ProgTab
meta import ConAgua.Checker.ProgI
meta import ConAguaX86.Checker.AsmX
meta import ConAguaX86.Compiler.Run
meta import ConAguaX86.Compiler.Abi
meta import ConAguaX86.Compiler.AbiCmp

@[expose] public section

/-! `lake env lean --run x86/ConAguaX86/Checker/AsmEmit.lean OUT.s` prints the checker's code: the entry
stub (`x86/ConAguaX86/Compiler/Abi.lean`, lane `abi`), then `compileProgX checkerX checkerTab checkerProgI "check"`
(the checker with its small leaves inlined, `ConAgua/Checker/ProgI.lean`)
(computed by running the compiler), plus the symbols
of `tabSymbols` (`commons/main.c` reads `ca_nw`) and `ca_diag` (no diagnostics
array: `checkerProg`'s stubs just abort). `scripts/asm_file.py` writes the committed file `x86/checker.s` with it. Nothing
here is trusted: the final theorems are about the file as the parser reads it, and the kernel
checks that it is the compiler's output (`checkerFile_eq`, `x86/ConAguaX86/Checker/AsmFileEq.lean`). -/

open L.Compiler L.Checker

def main (args : List String) : IO Unit := do
  let out := args.headD "checker.s"
  let code := compileProgX checkerX checkerTab checkerProgI "check"
  IO.FS.writeFile out (asmTextAbiPar checkerTab L.Arena.MODE L.Arena.PLO L.Arena.PHI L.Arena.OUT L.Arena.HDRF L.Arena.CTLF L.Arena.hdrHw L.Arena.frozenIdsL
      L.Arena.parOwnedL (code ++ cmpStub checkerTab L.Arena.MODE) ++
    tabSymbols checkerTab ++
    ".globl ca_start_c\n.globl ca_start_ac\n.globl ca_diag\nca_diag: .quad -1\n")
  IO.println s!"wrote {out}: {code.length} directives, nb {checkerTab.nb}, nw {checkerTab.nw}"
