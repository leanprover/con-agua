import ConAgua.Checker.Asm
import ConAgua.Compiler.Run
import ConAgua.Compiler.Abi

/-! `lake env lean --run ConAgua/Checker/AsmEmit.lean OUT.s` prints the checker's code from the
kernel-checked literal `checkerAsm` (`ConAgua/Checker/Asm.lean`; nothing is compiled here: the
printer `asmTextOf` alone), after the entry stub (`ConAgua/Compiler/Abi.lean`, lane `abi`; not yet
part of the literal), plus the symbols `harness/main.c` and `harness/e2e.c` read: `ca_nb`, `ca_nw` (the table's
array counts) and `ca_diag` (no diagnostics array: `checkerProg`'s stubs just abort). -/

open L.Compiler L.Checker

def main (args : List String) : IO Unit := do
  let out := args.headD "checker.s"
  IO.FS.writeFile out (asmTextAbi checkerTab (abiWords checkerProg) checkerAsm ++
    s!".section .rodata\n.globl ca_nw\n.globl ca_nb\n.globl ca_diag\nca_nw: .quad {checkerTab.nw}\nca_nb: .quad {checkerTab.nb}\nca_diag: .quad -1\n")
  IO.println s!"wrote {out}: {checkerAsm.length} directives, nb {checkerTab.nb}, nw {checkerTab.nw}"
