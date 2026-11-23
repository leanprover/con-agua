module

public import ConAgua.Compiler.Abi

@[expose] public section

/-!
# The compared run's driver `ca_compare` (lane compare)

`ca_compare(c, c_len, pins, pins_len, base, base_len, s, s_len)`: the first six arguments are
`ca_start`'s (the challenge's bytes as the input), the solution's bytes are the two stack
arguments (System V: `[rsp + 8]`, `[rsp + 16]` at the call). The region holds the setup stub's
region `R = [base, base + abiNeed)`, a save area in the slot after it (`cmpSave`), and a worker
region `W` from `cmpW` on (`workerNeed own` bytes). Every page that is never touched stays
virtual.

1. `ca_start_a4` (mode `4`) on `R` with the challenge's bytes: the stages to the challenge's
   parse (`check_c1`); unless it returns `rdx = 0`, `rax ≥ 2^63`, that is the result.
2. `ca_start_a5` (mode `5`) on `R` with the solution's bytes (the setup stub again: it rewrites
   the table, the input's descriptor now the solution's; everything else in `R` stays): the
   solution's parse, preparation, pins, index and frozen buffer (`check_c2`), `2^63 + k`.
3. `ca_check_b(OUT, OUT[1], j, W, workerNeed)` for `j = 0, 1, …, k - 1`: the solution's jobs, in
   order, on one worker region; the first call that does not accept is the result.
4. `ca_start_a6` (mode `6`) on `R` with the solution's bytes again (the input is not read):
   `check_c3`, `2^63 + k'`.
5. `ca_check_seq` on `R` for `[0, k')`: the challenge's jobs in place; its result is the result.

Like `ca_start`, it pops its return address before each `call` (so each callee's machine stack is
the caller's) and keeps it and the caller's `r15` in the save area, `base` in `r15`.
-/

namespace L.Compiler

def abiStartA4L : Label := "ca_start_a4"
def abiStartA5L : Label := "ca_start_a5"
def abiStartA6L : Label := "ca_start_a6"
def abiCompareL : Label := "ca_compare"
def abiCmpLoopL : Label := "ca_cmp_loop"
def abiCmpAfterL : Label := "ca_cmp_after"
def abiCmpDoneL : Label := "ca_cmp_done"
def abiCmpDeclineL : Label := "ca_cmp_decline"

/-- The save area: the slot after the setup stub's region. Words: `0` the caller's `r15`, `1` the
return address, `2`, `3` the solution's buffer and length, `4`, `5` the pin data's, `6` the
solution's job count, `7` the next job. -/
def cmpSave (tab : Tab) : Nat := abiNeed tab
/-- The worker region's start: one slot past the setup stub's region. -/
def cmpW (tab : Tab) : Nat := abiNeed tab + abiSlot
/-- The region size the compared run needs. -/
def cmpNeed (tab : Tab) (own : List TieredArray) : Nat := cmpW tab + workerNeed own

/-- `rax := r15 + cmpSave`. -/
def cmpSaveRax (tab : Tab) : Program :=
  [movRI .rax (cmpSave tab).toUInt64, i64 (.add (.reg (rr .rax)) (oR .r15))]

/-- The arguments of the setup stub for the solution's bytes (from the save area), on `R`. -/
def cmpArgsS (tab : Tab) : Program :=
  cmpSaveRax tab ++
  [movRM .rdi (mb .rax 16), movRM .rsi (mb .rax 24), movRM .rdx (mb .rax 32),
   movRM .rcx (mb .rax 40), movRR .r8 .r15, movRI .r9 (abiNeed tab).toUInt64]

/-- `call l`. -/
def callL (l : Label) : Directive := i64 (.call (.rel (.sub (.label l) .after_current_instruction)))

/-- Unless `rdx = 0` and `rax ≥ 2^63`: to the end (`rcx := 2^63` after). -/
def cmpOkGe : Program :=
  [i64 (.cmp (.reg (rr .rdx)) (oI 0)), jccL .nz abiCmpDoneL,
   movRI .rcx 9223372036854775808, i64 (.cmp (.reg (rr .rax)) (oR .rcx)), jccL .c abiCmpDoneL]

/-- The compared run's entries and driver, for the global `mode`, the buffer array `out` and the
worker's owned arrays `own`. -/
def cmpStub (tab : Tab) (mode : GVar) (out : ArrId) (own : List TieredArray) : Program :=
  -- the entries of modes 4, 5, 6: the mode word, then the setup stub
  [.label abiStartA4L,
   movRI .rax (abiNeed tab).toUInt64, i64 (.cmp (.reg (rr .r9)) (oR .rax)), jccL .c abiSetupL,
   movRI .rax 4, movMR (mb .r8 (tab.globOff mode)) .rax, jmpL abiSetupL,
   .label abiStartA5L,
   movRI .rax (abiNeed tab).toUInt64, i64 (.cmp (.reg (rr .r9)) (oR .rax)), jccL .c abiSetupL,
   movRI .rax 5, movMR (mb .r8 (tab.globOff mode)) .rax, jmpL abiSetupL,
   .label abiStartA6L,
   movRI .rax (abiNeed tab).toUInt64, i64 (.cmp (.reg (rr .r9)) (oR .rax)), jccL .c abiSetupL,
   movRI .rax 6, movMR (mb .r8 (tab.globOff mode)) .rax, jmpL abiSetupL,
  -- the driver
   .label abiCompareL,
   movRI .rax (cmpNeed tab own).toUInt64, i64 (.cmp (.reg (rr .r9)) (oR .rax)), jccL .c abiCmpDeclineL,
   movRI .rax (cmpSave tab).toUInt64, i64 (.add (.reg (rr .rax)) (oR .r8)),
   movMR (mb .rax 0) .r15, i64 (.pop (.reg (rr .r11))), movMR (mb .rax 8) .r11,
   movRM .r11 (mb .rsp 0), movMR (mb .rax 16) .r11, movRM .r11 (mb .rsp 8), movMR (mb .rax 24) .r11,
   movMR (mb .rax 32) .rdx, movMR (mb .rax 40) .rcx, movRR .r15 .r8,
   movRI .r9 (abiNeed tab).toUInt64,
   callL abiStartA4L] ++ cmpOkGe ++
  cmpArgsS tab ++ [callL abiStartA5L] ++ cmpOkGe ++
  [i64 (.sub (.reg (rr .rax)) (oR .rcx)), movRR .rdx .rax] ++ cmpSaveRax tab ++
  [movMR (mb .rax 48) .rdx, movRI .rdx 0, movMR (mb .rax 56) .rdx,
   .label abiCmpLoopL] ++ cmpSaveRax tab ++
  [movRM .rdx (mb .rax 56), i64 (.cmp (.reg (rr .rdx)) (oM (mb .rax 48))), jccL .nc abiCmpAfterL,
   movRI .rdi (abiSlot * abiSlot64 tab out).toUInt64, i64 (.add (.reg (rr .rdi)) (oR .r15)),
   movRM .rsi (mb .rdi 8),
   movRI .rcx (cmpW tab).toUInt64, i64 (.add (.reg (rr .rcx)) (oR .r15)),
   movRI .r8 (workerNeed own).toUInt64,
   callL abiCheckBL,
   i64 (.cmp (.reg (rr .rdx)) (oI 0)), jccL .nz abiCmpDoneL,
   movRI .rcx 71757147230292, i64 (.cmp (.reg (rr .rax)) (oR .rcx)), jccL .nz abiCmpDoneL] ++
  cmpSaveRax tab ++
  [movRM .rdx (mb .rax 56), i64 (.add (.reg (rr .rdx)) (oI 1)), movMR (mb .rax 56) .rdx,
   jmpL abiCmpLoopL,
   .label abiCmpAfterL] ++
  cmpArgsS tab ++ [callL abiStartA6L] ++ cmpOkGe ++
  [i64 (.sub (.reg (rr .rax)) (oR .rcx)), movRR .rdx .rax, movRI .rsi 0, movRR .r8 .r15,
   callL abiCheckSL,
   .label abiCmpDoneL,
   movRR .rcx .rax, movRI .rax (cmpSave tab).toUInt64, i64 (.add (.reg (rr .rax)) (oR .r15)),
   movRM .rsi (mb .rax 8), movRM .r15 (mb .rax 0), movRR .rax .rcx,
   i64 (.push (oR .rsi)), i64 .ret,
   .label abiCmpDeclineL, movRI .rax 0, movRI .rdx 1, i64 .ret]

/-- The entry of mode `7` (`ca_start_a7`, lane compare2: the threaded compared run). -/
def abiStartA7L : Label := "ca_start_a7"

/-- **The threaded compared run's entry** (lane compare2), after `cmpStub` in the file: mode `7`'s
entry, as the entries of modes `4`, `5`, `6` (the mode word, then the setup stub). The threaded
harness calls `ca_start_a4` (the challenge's bytes), `ca_start_a5` (the solution's), the solution's
jobs on its threads, `ca_start_a7` (the solution's bytes again), the challenge's jobs on its
threads; every call on the same region `[base, base + abiNeed)`, as the previous call left it. -/
def ctaStub (tab : Tab) (mode : GVar) : Program :=
  [.label abiStartA7L,
   movRI .rax (abiNeed tab).toUInt64, i64 (.cmp (.reg (rr .r9)) (oR .rax)), jccL .c abiSetupL,
   movRI .rax 7, movMR (mb .r8 (tab.globOff mode)) .rax, jmpL abiSetupL]

/-- The compared run's symbols for the harness: the region size it needs. -/
def cmpSymbols (tab : Tab) (own : List TieredArray) : String :=
  s!".section .rodata\n.globl ca_cmp_region_size\nca_cmp_region_size: .quad {cmpNeed tab own}\n"

end L.Compiler
