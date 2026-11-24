module

public import ConAgua.Compiler.Abi

@[expose] public section

/-!
# The compared run's entries `ca_start_ac`, `ca_start_c` (lanes compare, compare2)

Both take `(c, c_len, pins, pins_len, base, base_len, s, s_len)`: the first six arguments are
`ca_start`'s (the challenge's bytes as the input), the solution's bytes are the two stack
arguments (System V: `[rsp + 8]`, `[rsp + 16]` at the call). They share one front (`ca_cmp_front`)
on the setup stub's region `R = [base, base + abiNeed)`, with a save area in the 64 bytes after it
(`cmpSave`); every page that is never touched stays virtual.

1. `ca_start_a4` (mode `4`) on `R` with the challenge's bytes: the stages to the challenge's
   parse (`check_c1`); unless it returns `rdx = 0`, `rax ≥ 2^63`, that is the result.
2. `ca_start_a5` (mode `5`) on `R` with the solution's bytes (the setup stub again: it rewrites
   the table, the input's descriptor now the solution's; everything else in `R` stays): the
   solution's parse, preparation, pins, index and frozen buffer (`check_c2`), `2^63 + kS`.
3. `ca_start_a7` (mode `7`) on `R` as mode `5` left it, the solution's bytes again (the input is
   not read): the challenge's preparation, index and self-contained frozen buffer right after the
   solution's in `OUT` (`check_c3`), `2^63 + kC`. `OUT` then holds both buffers: the solution's
   header's word `5` is the challenge's buffer's offset, its word `1` the whole length.

`ca_start_ac` (**entry 1 of the threaded compared run**, region `drvNeed`) returns
`rdx = 0`, `rax = 2^63 + kS + kC`; `ca_check_b` over the two buffers is entry 2 for the global job
index `j < kS + kC` (it picks the phase). `ca_start_c` (**the sequential compared run**, region
`cmpNeed`) goes on with `ca_check_b(OUT, OUT[1], j, W, 2 · workerNeed)` for `j = 0, 1, …` on
one worker region `W` from `cmpW` on, in order; the first call that does not accept is the result,
else `ACCEPT`. The two share the front by a flag in save word `7` (`0`: sequential, where the word
then counts the jobs; `1`: threaded).

Like `ca_start`, the front pops its return address before each `call` (so each callee's machine
stack is the caller's) and keeps it and the caller's `r15` in the save area, `base` in `r15`.
-/

namespace L.Compiler

def abiStartA4L : Label := "ca_start_a4"
def abiStartA5L : Label := "ca_start_a5"
def abiStartA7L : Label := "ca_start_a7"
def abiStartCL : Label := "ca_start_c"
def abiStartACL : Label := "ca_start_ac"
def abiCmpFrontL : Label := "ca_cmp_front"
def abiCmpLoopL : Label := "ca_cmp_loop"
def abiCmpAfterL : Label := "ca_cmp_after"
def abiCmpRetL : Label := "ca_cmp_ret"
def abiCmpDoneL : Label := "ca_cmp_done"
def abiCmpDeclineL : Label := "ca_cmp_decline"

/-- The save area: the 64 bytes after the setup stub's region (`drvNeed` covers it). Words: `0`
the caller's `r15`, `1` the return address, `2`, `3` the solution's buffer and length, `4`, `5`
the pin data's, `6` the solution's job count, then all jobs' count, `7` the flag, then the next
job. -/
def cmpSave (tab : Tab) : Nat := abiNeed tab
/-- The worker region's start: one slot past the setup stub's region. -/
def cmpW (tab : Tab) : Nat := abiNeed tab + abiSlot
/-- The region size the sequential compared run needs: the worker region holds both phases'
worker regions (`ca_check_b`'s phase `p` on its `p`-th `workerNeed` bytes). -/
def cmpNeed (tab : Tab) (own : List TieredArray) : Nat := cmpW tab + 2 * workerNeed own

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

/-- A mode entry: the mode word `w`, then the setup stub. -/
def cmpModeEntry (tab : Tab) (mode : GVar) (l : Label) (w : Word) : Program :=
  [.label l,
   movRI .rax (abiNeed tab).toUInt64, i64 (.cmp (.reg (rr .r9)) (oR .rax)), jccL .c abiSetupL,
   movRI .rax w, movMR (mb .r8 (tab.globOff mode)) .rax, jmpL abiSetupL]

/-- The compared run's entries, for the global `mode`, the buffer array `out` and the worker's
owned arrays `own`. -/
def cmpStub (tab : Tab) (mode : GVar) (out : ArrId) (own : List TieredArray) : Program :=
  -- the entries of modes 4, 5, 7: the mode word, then the setup stub
  cmpModeEntry tab mode abiStartA4L 4 ++ cmpModeEntry tab mode abiStartA5L 5 ++
  cmpModeEntry tab mode abiStartA7L 7 ++
  -- the two entries: the region's size, the flag in `r10`
  [.label abiStartCL,
   movRI .rax (cmpNeed tab own).toUInt64, i64 (.cmp (.reg (rr .r9)) (oR .rax)), jccL .c abiCmpDeclineL,
   movRI .r10 0, jmpL abiCmpFrontL,
   .label abiStartACL,
   movRI .rax (drvNeed tab).toUInt64, i64 (.cmp (.reg (rr .r9)) (oR .rax)), jccL .c abiCmpDeclineL,
   movRI .r10 1,
  -- the front: the save area, modes 4, 5, 7
   .label abiCmpFrontL,
   movRI .rax (cmpSave tab).toUInt64, i64 (.add (.reg (rr .rax)) (oR .r8)),
   movMR (mb .rax 0) .r15, i64 (.pop (.reg (rr .r11))), movMR (mb .rax 8) .r11,
   movRM .r11 (mb .rsp 0), movMR (mb .rax 16) .r11, movRM .r11 (mb .rsp 8), movMR (mb .rax 24) .r11,
   movMR (mb .rax 32) .rdx, movMR (mb .rax 40) .rcx, movMR (mb .rax 56) .r10, movRR .r15 .r8,
   movRI .r9 (abiNeed tab).toUInt64,
   callL abiStartA4L] ++ cmpOkGe ++
  cmpArgsS tab ++ [callL abiStartA5L] ++ cmpOkGe ++
  [i64 (.sub (.reg (rr .rax)) (oR .rcx)), movRR .rdx .rax] ++ cmpSaveRax tab ++
  [movMR (mb .rax 48) .rdx] ++
  cmpArgsS tab ++ [callL abiStartA7L] ++ cmpOkGe ++
  [i64 (.sub (.reg (rr .rax)) (oR .rcx)), movRR .rdx .rax] ++ cmpSaveRax tab ++
  [movRM .r11 (mb .rax 48), i64 (.add (.reg (rr .rdx)) (oR .r11)), movMR (mb .rax 48) .rdx,
   movRM .r11 (mb .rax 56), i64 (.cmp (.reg (rr .r11)) (oI 0)), jccL .nz abiCmpRetL,
  -- the sequential run: the jobs `j < kS + kC`
   .label abiCmpLoopL] ++ cmpSaveRax tab ++
  [movRM .rdx (mb .rax 56), i64 (.cmp (.reg (rr .rdx)) (oM (mb .rax 48))), jccL .nc abiCmpAfterL,
   movRI .rdi (abiSlot * abiSlot64 tab out).toUInt64, i64 (.add (.reg (rr .rdi)) (oR .r15)),
   movRM .rsi (mb .rdi 8),
   movRI .rcx (cmpW tab).toUInt64, i64 (.add (.reg (rr .rcx)) (oR .r15)),
   movRI .r8 (2 * workerNeed own).toUInt64,
   callL abiCheckBL,
   i64 (.cmp (.reg (rr .rdx)) (oI 0)), jccL .nz abiCmpDoneL,
   movRI .rcx 71757147230292, i64 (.cmp (.reg (rr .rax)) (oR .rcx)), jccL .nz abiCmpDoneL] ++
  cmpSaveRax tab ++
  [movRM .rdx (mb .rax 56), i64 (.add (.reg (rr .rdx)) (oI 1)), movMR (mb .rax 56) .rdx,
   jmpL abiCmpLoopL,
   .label abiCmpAfterL, movRI .rax 71757147230292, movRI .rdx 0, jmpL abiCmpDoneL,
  -- the threaded run's entry 1: `2^63 + kS + kC`
   .label abiCmpRetL, movRI .rax 9223372036854775808, i64 (.add (.reg (rr .rax)) (oR .rdx)), movRI .rdx 0,
   .label abiCmpDoneL,
   movRR .rcx .rax, movRI .rax (cmpSave tab).toUInt64, i64 (.add (.reg (rr .rax)) (oR .r15)),
   movRM .rsi (mb .rax 8), movRM .r15 (mb .rax 0), movRR .rax .rcx,
   i64 (.push (oR .rsi)), i64 .ret,
   .label abiCmpDeclineL, movRI .rax 0, movRI .rdx 1, i64 .ret]

/-- The compared run's symbols for the harness: the region size the sequential run needs. -/
def cmpSymbols (tab : Tab) (own : List TieredArray) : String :=
  s!".section .rodata\n.globl ca_cmp_region_size\nca_cmp_region_size: .quad {cmpNeed tab own}\n"

end L.Compiler
