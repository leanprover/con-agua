# checkasm: the as/objdump check back in the gates

Lane checkasm, 2026-11-18.

## The failure

`scripts/check-asm.sh` failed on master (b0600fe9c) with 211 mismatches, all in `checker.s`, all one
shape: our `imulq $I, %R` (two operands) against objdump's `imul $I,%R,%R` (three). 23 distinct
(immediate, register) pairs; immediates 2 to 1006632960, registers rax, rbx, rcx, rsi, rdi, r8, r9,
r11, r12, r13. Every one had the same register in both of objdump's register slots. No other kind of
mismatch. The scan/store/walk programs were already OK. No gate or CI step ran the script, so it rotted
when the compiler started to emit `imulq $I, %R`.

## Why the two forms are the same instruction

- Bytes: `as` encodes `imulq $I, %R` as REX.W `6B /r ib` (or `69 /r id` for a 32-bit immediate), ModRM
  mod=11 with reg = r/m = R (e.g. `48 6b c0 03`, `4d 6b ed 02`, `48 69 db 00 00 00 3c`). That is the
  SDM's IMUL r64, r/m64, imm: `R := trunc64(R * sext(I))`, CF = OF = the signed product does not fit,
  SF/ZF/AF/PF undefined. objdump prints the three operands of that encoding (`imul $I,%src,%dst`).
- Kraken: Parse.lean reads `imulq $I, %R` as `.imul none (.reg R) (.imm I)`; Semantics.lean's
  `.imul dst src1 src2` writes `src1 * src2` to `dst.getD src1`, i.e. to R, with
  `cf = of = (v.signed != a.signed * b.signed)` and the other four flags undefined. Same result, same
  flags.
- Immediates outside the signed 32-bit range are rejected by `as` (`operand type mismatch`), and
  objdump prints a negative immediate sign-extended to 64 bits, which the existing mod 2^64 comparison
  matches.

## Fix

`check_asm.py`: `imul_imm_two_operand` folds objdump's `imul $I,%A,%B` to `$I,%B` only when our line
is `imul` with an immediate and a register and A = B; the immediate and the register are then compared
as before. Any other shape still fails the operand count check. Result: checker.s 213320 instructions
OK; scan 156, store 1224, walk 7613 OK.

## The gate

New step `check-asm` (`scripts/check-asm.sh`) in `scripts/gates.sh`, after `warnings` and before
`shake`. `gate_select.py` selects it for `checker.s`, `scripts/check-asm.sh`, `scripts/check_asm.py`,
`ConAgua/AsmFile/**`, `ConAgua/Compiler/{Run,Abi,EmitScan}.lean` and
`ConAgua/Arena/{EmitStore,WalkEmit}.lean` (Kraken's printer is a dependency: a manifest change already
selects everything). It is in `mq.py`'s EXPENSIVE set (it reads built oleans). Runtime: 8.5 s wall
with a warm build (1.8 s of it the checker.s comparison). Also a CI step in the proof job, after
`asm_file.py --check`.
