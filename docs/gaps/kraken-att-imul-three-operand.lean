/-
# Kraken's AT&T printer: the two-destination-operand `imul` is printed in three-operand form

For an upstream issue against Kraken (`Kraken.X64.ATT.operation`, the `.imul` case,
`Kraken/X64/PrintATT.lean`).

Toolchain: leanprover/lean4:nightly-2026-10-20; Kraken `sgraf812/kraken` branch `vcgen`,
rev `ba12834902fd19e837c97d0e5ea585d41348ee7e`; GNU assembler (binutils) 2.46.

Checked against upstream (2026-10-21): `AeneasVerif/kraken` `main`
(`72f3a7a3a2d94ac51040815d692cd31a1d240a1d`) has the identical, unfixed three-operand print (same
observed line below); the `vcgen` fork did not diverge from `main` on this file. Not fixed
upstream as of this writing.

Expected: `.imul (some d) a b` with `d = a` (`rax := rax * rcx`, i.e. `.imul (some rax) rax rcx`)
is printed `imulq %rcx, %rax` (two operands): per `Kraken/X64/Semantics.lean`'s `.imul dst src1
src2` case, `(dst?.getD src1) := src1 * src2`, so `.imul (some a) a b` and `.imul none a b` are
*the same instruction*, and Kraken's own printer already writes `.imul none a b` that way
(`Kraken/X64/PrintATT.lean`: `| .imul none a b => two "imul" (operand aw b) (rm aw a)`).
Observed: `Kraken.X64.toATT` prints `.imul (some d) a b` in three-operand form unconditionally,
even when `d = a`: `imulq %rcx, %rax, %rax` below.

```
-- Kraken/X64/PrintATT.lean, current:
| .imul (some d) a b => s!"imul{s} {operand aw b}, {rm aw a}, {rm aw d}"
-- should special-case d = a (`DecidableEq (RegOrMem w)` is already derived):
-- | .imul (some d) a b => if d = a then two "imul" (operand aw b) (rm aw a)
--     else s!"imul{s} {operand aw b}, {rm aw a}, {rm aw d}"
```

binutils 2.46 accepts the observed three-operand line as the APX "new data destination" (`NDD`)
form of `imul` and encodes it with an EVEX prefix, a different instruction, illegal on a CPU
without APX (`SIGILL` at the first multiplication; reproduced below, exit code 132). Kraken's own
two-operand print of the same instruction (`.imul none a b`) assembles to the ordinary REX.W
`0F AF` encoding and runs correctly. The assembler is in the trusted base, so the printed text and
Kraken's semantics of the instruction must agree.

```
$ as --version | head -1
GNU assembler (GNU Binutils) 2.46

$ cat > imul_bug.s <<'EOF'
.text
.globl _start
_start:
imulq %rcx, %rax, %rax
ret
EOF
$ as imul_bug.s -o imul_bug.o && objdump -d imul_bug.o
imul_bug.o:     file format elf64-x86-64

Disassembly of section .text:

0000000000000000 <_start>:
   0:   62 f4 fc 18 af c1       imul   %rcx,%rax,%rax
   6:   c3                      ret

$ cat > imul_bug_run.s <<'EOF'
.text
.globl main
main:
mov $1, %rax
mov $2, %rcx
imulq %rcx, %rax, %rax
ret
EOF
$ as imul_bug_run.s -o imul_bug_run.o && ld imul_bug_run.o -o imul_bug_run -e main
$ ./imul_bug_run; echo $?
Illegal instruction (core dumped)
132

$ cat > imul_fixed.s <<'EOF'      # Kraken's own `.imul none a b` print, same instruction
.text
.globl _start
_start:
mov $3, %rax
mov $4, %rcx
imulq %rcx, %rax
mov %rax, %rdi
mov $60, %rax
syscall
EOF
$ as imul_fixed.s -o imul_fixed.o && objdump -d imul_fixed.o | tail -1
   8:   48 0f af c1             imul   %rcx,%rax
$ ld imul_fixed.o -o imul_fixed && ./imul_fixed; echo $?
12
```

(When `d ≠ a`, the three-operand form is valid legacy x86 only when `b` is an immediate — the
`imul r64, r/m64, imm32` form, `imul $imm, src, dst` in ATT syntax — and wrong, not just APX-only,
for a register `b`. Kraken's printer does not distinguish that case either, but it does not arise
here: see below.)

Found in con-agua: the compiler (`ConAgua/Compiler/Compile.lean`'s `binInstr .mul`) emits exactly
`.imul (some rax) rax rcx`, always `d = a = rax`. The scanner (`scanProg`) never multiplies, so it
was the first compiled program (the arena walk's `homeW`, then the `lit` store's hashing,
`ConAgua/Arena/{WalkEmit,EmitStore}.lean`) to hit it. Fixed on the con-agua side (not here, since
this is Kraken's printer) by rewriting `.imul (some d) a b` to the semantically identical
`.imul none a b` whenever `d = a`, before printing: a `Directive`-level normalisation
(`ConAgua/Compiler/Run.lean`'s `fixImul`), not a textual patch of the printed assembly. See
`DESIGN.md` (lanes `compiler`, `walk`) and `harness/check-asm.sh`, which assembles and disassembles
every compiled program and diffs every instruction against what the compiler intended, to catch
any other such printer/assembler mismatch.
-/
import Kraken.X64.PrintATT

def rax64 : RegOrMem .W64 := .reg (.low .rax .W64)
def rcx64 : Operand .W64 := .regOrMem (.reg (.low .rcx .W64))

/-- `rax := rax * rcx`, i.e. `d = a`: con-agua's compiler's one `imul`. -/
def imulDir : Directive := .instr (.regular .W64 .W64 (.imul (some rax64) rax64 rcx64))

-- Observed: "imulq %rcx, %rax, %rax"
#eval Kraken.X64.ATT.directive imulDir
