/-
# Kraken's AT&T printer: the two-operand `imul` is printed in three-operand form

Toolchain: leanprover/lean4:nightly-2026-10-20; Kraken (sgraf812/kraken) `ba12834`;
GNU assembler 2.46.

Expected: the compiler's `imul rax, rcx` (`.imul (some (.reg rax)) (.reg rax) (rcx)`, i.e.
`rax := rax * rcx`) is printed as `imulq %rcx, %rax`.
Observed: `Kraken.X64.toATT` prints `imulq %rcx, %rax, %rax`. binutils 2.46 accepts it as the
APX "new data destination" form and encodes it with an EVEX prefix
(`62 f4 fc 18 af c1`), which is an illegal instruction on a CPU without APX (SIGILL at the
first multiplication). Older assemblers reject the line. The assembler is in the trusted base,
so the printed text and Kraken's semantics of the instruction must agree.

Found in con-agua: the first compiled program that multiplies (the walk's `homeW`,
`ConAgua/Arena/WalkEmit.lean`). Workaround there: rewrite the text to the two-operand form
(`fixImul`), which is the instruction Kraken's semantics executes.
-/
import ConAgua.Compiler.Run
import ConAgua.L.Notation

open L L.Compiler

def mulProg : Prog := [("mul", lfn (a, b) { return a * b })]

-- Observed: ["imulq %rcx, %rax, %rax"]
#eval ((asmText (Prog.tab mulProg 0 0) mulProg "mul").splitOn "\n").filter
  (fun l => (l.splitOn "imul").length > 1)
