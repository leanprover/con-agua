module

public import ConAgua.Compiler.Abi

@[expose] public section

/-!
# The compared run's entries `ca_start_ac`, `ca_start_c` (lanes compare, compare2)

Both take `(c, c_len, pins, pins_len, base, base_len, s, s_len)`: the first six arguments are
`ca_start`'s (the challenge's bytes as the input), the solution's bytes are the two stack
arguments (System V: `[rsp + 8]`, `[rsp + 16]` at the call). Both need `drvNeed` bytes: the setup
stub's region `R = [base, base + abiNeed)` and a save area in the 64 bytes after it (`cmpSave`).
They share one front (`ca_cmp_front`):

1. `ca_start_a4` (mode `4`) on `R` with the challenge's bytes: the stages to the challenge's
   parse; unless it returns `rdx = 0`, `rax ≥ 2^63`, that is the result.
2. `ca_start_a5` (mode `5`) on `R` with the solution's bytes (the setup stub again: it rewrites
   the table, the input's descriptor now the solution's; everything else in `R` stays): the
   solution's parse, preparation, pins and index, `2^63 + kS`.

Then, on `R` as mode `5` left it (the solution's bytes again as the input, not read):

* `ca_start_ac` (**entry 1 of the threaded compared run**): `ca_start_a7` (mode `7`): the
  challenge's preparation and index, and the frozen buffer in `OUT` (one image set, the
  solution's header and the challenge's), `2^63 + kC`; the result `2^63 + kS + kC`.
* `ca_start_c` (**the sequential compared run**): `ca_start_a6` (mode `6`): the same with the
  buffer's header only, `2^63 + kC`; then `ca_check_seq` in place with the mode word `8` for the
  solution's jobs `[0, kS)`, and unless that returns `rdx = 0`, `rax = ACCEPT`, the result; then
  with the mode word `9` for the challenge's jobs `[0, kC)`, whose result is the result.

The two share the front by a flag in save word `7` (`0`: sequential, `1`: threaded). Like
`ca_start`, the front pops its return address before each `call` (so each callee's machine stack
is the caller's) and keeps it and the caller's `r15` in the save area, `base` in `r15`.
-/

namespace L.Compiler

def abiStartA4L : Label := "ca_start_a4"
def abiStartA5L : Label := "ca_start_a5"
def abiStartA6L : Label := "ca_start_a6"
def abiStartA7L : Label := "ca_start_a7"
def abiStartCL : Label := "ca_start_c"
def abiStartACL : Label := "ca_start_ac"
def abiCmpFrontL : Label := "ca_cmp_front"
def abiCmpThrL : Label := "ca_cmp_thr"
def abiCmpDoneL : Label := "ca_cmp_done"
def abiCmpDeclineL : Label := "ca_cmp_decline"

/-- The save area: the 64 bytes after the setup stub's region (`drvNeed` covers them). Words: `0`
the caller's `r15`, `1` the return address, `2`, `3` the solution's buffer and length, `4`, `5`
the pin data's, `6` the solution's job count, `7` the flag, then (sequential) the challenge's job
count. -/
def cmpSave (tab : Tab) : Nat := abiNeed tab

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

/-- The entries of modes `4`, `5`, `6`, `7`: the mode word, then the setup stub. -/
def cmpEntries (tab : Tab) (mode : GVar) : Program :=
  cmpModeEntry tab mode abiStartA4L 4 ++ cmpModeEntry tab mode abiStartA5L 5 ++
  cmpModeEntry tab mode abiStartA6L 6 ++ cmpModeEntry tab mode abiStartA7L 7

/-- The two entries (the flag in `r10`) and the front: the region's size, the save area, modes
`4`, `5`; on to `ca_cmp_thr` for the threaded run. -/
def cmpFront (tab : Tab) : Program :=
  [.label abiStartCL, movRI .r10 0, jmpL abiCmpFrontL,
   .label abiStartACL, movRI .r10 1,
   .label abiCmpFrontL,
   movRI .rax (drvNeed tab).toUInt64, i64 (.cmp (.reg (rr .r9)) (oR .rax)), jccL .c abiCmpDeclineL,
   movRI .rax (cmpSave tab).toUInt64, i64 (.add (.reg (rr .rax)) (oR .r8)),
   movMR (mb .rax 0) .r15, i64 (.pop (.reg (rr .r11))), movMR (mb .rax 8) .r11,
   movRM .r11 (mb .rsp 0), movMR (mb .rax 16) .r11, movRM .r11 (mb .rsp 8), movMR (mb .rax 24) .r11,
   movMR (mb .rax 32) .rdx, movMR (mb .rax 40) .rcx, movMR (mb .rax 56) .r10, movRR .r15 .r8,
   movRI .r9 (abiNeed tab).toUInt64,
   callL abiStartA4L] ++ cmpOkGe ++
  cmpArgsS tab ++ [callL abiStartA5L] ++ cmpOkGe ++
  [i64 (.sub (.reg (rr .rax)) (oR .rcx)), movRR .rdx .rax] ++ cmpSaveRax tab ++
  [movMR (mb .rax 48) .rdx,
   movRM .r11 (mb .rax 56), i64 (.cmp (.reg (rr .r11)) (oI 0)), jccL .nz abiCmpThrL]

/-- The sequential run after the front: mode `6`, the solution's jobs, the challenge's jobs, in
place. -/
def cmpSeqTail (tab : Tab) : Program :=
  cmpArgsS tab ++ [callL abiStartA6L] ++ cmpOkGe ++
  [i64 (.sub (.reg (rr .rax)) (oR .rcx)), movRR .rdx .rax] ++ cmpSaveRax tab ++
  [movMR (mb .rax 56) .rdx,
   movRI .r10 8, movRI .rsi 0, movRM .rdx (mb .rax 48), movRR .r8 .r15, callL abiCheckSML,
   i64 (.cmp (.reg (rr .rdx)) (oI 0)), jccL .nz abiCmpDoneL,
   movRI .rcx 71757147230292, i64 (.cmp (.reg (rr .rax)) (oR .rcx)), jccL .nz abiCmpDoneL] ++
  cmpSaveRax tab ++
  [movRM .rdx (mb .rax 56), movRI .r10 9, movRI .rsi 0, movRR .r8 .r15, callL abiCheckSML,
   jmpL abiCmpDoneL]

/-- The threaded run's entry 1 after the front: mode `7`, `2^63 + kS + kC`. -/
def cmpThrTail (tab : Tab) : Program :=
  [.label abiCmpThrL] ++
  cmpArgsS tab ++ [callL abiStartA7L] ++ cmpOkGe ++
  [i64 (.sub (.reg (rr .rax)) (oR .rcx)), movRR .rdx .rax] ++ cmpSaveRax tab ++
  [movRM .r11 (mb .rax 48), i64 (.add (.reg (rr .rdx)) (oR .r11)),
   movRI .rax 9223372036854775808, i64 (.add (.reg (rr .rax)) (oR .rdx)), movRI .rdx 0]

/-- The exit (the caller's `r15` and the return address back) and the decline. -/
def cmpExit (tab : Tab) : Program :=
  [.label abiCmpDoneL,
   movRR .rcx .rax, movRI .rax (cmpSave tab).toUInt64, i64 (.add (.reg (rr .rax)) (oR .r15)),
   movRM .rsi (mb .rax 8), movRM .r15 (mb .rax 0), movRR .rax .rcx,
   i64 (.push (oR .rsi)), i64 .ret,
   .label abiCmpDeclineL, movRI .rax 0, movRI .rdx 1, i64 .ret]

/-- The compared run's entries, for the global `mode`. -/
def cmpStub (tab : Tab) (mode : GVar) : Program :=
  cmpEntries tab mode ++ cmpFront tab ++ cmpSeqTail tab ++ cmpThrTail tab ++ cmpExit tab

end L.Compiler
