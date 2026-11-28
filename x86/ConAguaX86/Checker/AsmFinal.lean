module

public import ConAgua.Checker.ProgTab
public import ConAguaX86.Final.Abi
meta import ConAgua.Checker.ProgTab
meta import ConAguaX86.Final.Abi

@[expose] public section

/-!
# The committed assembler file `checker.s`: the checker's facts the final theorems use

The final theorems (`ConAgua/Final/EndToEnd.lean`, from `checkerFile_drv_accepts_regs`,
`ConAgua/Final/DrvFinal.lean`) are about `checkerFile`: the code of the committed file
`checker.s` (the parallel mode's entries with the driver `ca_start`, the setup stub, the
trampoline and the functions: exactly what `main.c` is assembled with), as the trusted parser
reads it when `x86/ConAguaAsm/Checker.lean` is elaborated (`include_asm`). The kernel checked
`checkerFile_eq : checkerFile = checkerStub ++ compileProgX checkerX checkerTab checkerProgI "check"`
(`ConAgua/Checker/AsmFileEq.lean`) and `checkerStub_eq` (`ConAgua/Checker/AsmStubEq.lean`), so
neither the Lean compiler that computed the code nor the printer that wrote the file is trusted;
the compiled code that reads the file (`parseAsmFile`, `programTerm`/`labelExpr`, the derived
`ToExpr Directive`), the assembler, the linker (label and branch-target resolution) and the loader
are (`Final/Statement.lean`, "What is trusted"; `scripts/check-asm.sh` checks the assembler's
encodings against the file). DESIGN.md, "Kernel-checked compiler output"; docs/design/asmfile.md.

Here: the entry `check` of `checkerProg`, the table's fit for the setup stub and the ABI's fixed
positions in the layout map (the input and the pin data at descriptor positions `0`, `1`).
-/

namespace ConAgua.Final

open L L.Compiler L.Checker

set_option maxRecDepth 100000 in
theorem checkerProg_lookup_check : checkerProg.lookup "check" = some L.Checker.checkL := rfl

theorem checkerTab_abiOk : abiTabOk checkerTab = true := by decide

theorem checkerTab_abiIO : abiIO checkerTab = true := by decide +kernel

end ConAgua.Final
