import ConAgua.Checker.ProgTab
import ConAgua.Compiler.Run
import ConAgua.Compiler.Abi

/-! `lake env lean --run ConAgua/Checker/AsmEmit.lean OUT.s` prints the checker's code: the entry
stub (`ConAgua/Compiler/Abi.lean`, lane `abi`), then `compileProg checkerTab checkerProg "check"`
(computed by running the compiler), plus the symbols
`ca_nb`, `ca_nw` (the table's array counts; `main.c` reads `ca_nw`) and `ca_diag` (no diagnostics
array: `checkerProg`'s stubs just abort). `scripts/asm_file.py` writes the committed file `checker.s` with it. Nothing
here is trusted: the final theorems are about the file as the parser reads it, and the kernel
checks that it is the compiler's output (`checkerFile_eq`, `ConAgua/Checker/AsmFileEq.lean`). -/

open L.Compiler L.Checker

def main (args : List String) : IO Unit := do
  let out := args.headD "checker.s"
  let code := compileProg checkerTab checkerProg "check"
  IO.FS.writeFile out (asmTextAbiPar checkerTab L.Arena.MODE L.Arena.PLO L.Arena.PHI L.Arena.OUT L.Arena.HDRF L.Arena.CTLF 132 L.Arena.frozenIdsL
      L.Arena.parOwnedL code ++
    s!".section .rodata\n.globl ca_nw\n.globl ca_nb\n.globl ca_diag\nca_nw: .quad {checkerTab.nw}\nca_nb: .quad {checkerTab.nb}\nca_diag: .quad -1\n")
  IO.println s!"wrote {out}: {code.length} directives, nb {checkerTab.nb}, nw {checkerTab.nw}"
