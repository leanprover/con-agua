# Lane harness: review and polish of the trusted C harness

Goal: `harness/main.c` is trusted code a reviewer has to read and believe, so it should be as
simple, readable and direct as possible. Keep the interface (`ca_start(in, in_len, pins, pins_len,
base, base_len)`, the entry points, the exit codes and the output) identical. Lane parmode owns
the parallel-mode paths (`--jobs=N`, `--driver`, `run_jobs`, `worker`); the findings on those
parts are under "For parmode" below, not changed here.

## Review (2026-10-25, master 1134dff6)

### (a) What the harness does, step by step

`main.c`, 212 lines; `main FILE [PINS]` (plus parmode's `--jobs=N`, `--driver`):

1. Flags: `--jobs=N` (`atoi`, N ≥ 1), `--driver`; then `FILE` and an optional `PINS`. Usage
   errors exit 3.
2. `slurp(FILE)`, `slurp(PINS)` (if given; otherwise `pins = NULL`, `pins_len = 0`): `open`,
   `fstat`, `read(2)` until EOF into a `malloc` buffer that doubles, `fstat` again; a regular file
   whose size or mtime changed, or whose size is not the number of bytes read, is an error (exit
   3); so is any read error and a size ≥ 2^63.
3. `mmap` one anonymous private region of `ca_region_size` bytes (`MAP_NORESERVE`; ~10 TB of
   address space, only touched pages become real). Exit 3 on failure.
4. `madvise(MADV_HUGEPAGE)` on every word array's slot except its first and last 2 MB
   (performance only: lane compopt2, -10..14% wall on the big fixtures).
5. `--jobs=N > 1`: `run_jobs` (parmode). Otherwise one call, `ca_start(in, n, pins, np, base,
   ca_region_size)` (or `ca_start_drv` with the same arguments under `--driver`).
6. Print one line: `accept` iff `rdx = 0 ∧ rax = ACCEPT`; `ok R` (other `rax`, `rdx = 0`);
   `exhausted` (`rdx = 1`); `missing CODE` (`rdx = 2` and a `DIAG` word, only for `e2e-l asm`
   test programs: `ca_diag = -1` in `asm/checker.s`); `error`. Exit 0.

### (b) What the proof assumes of it, and where it is met

The final theorem (`checkerFile_accepts_remaining`, `ConAgua/Final/Remaining.lean`) starts at
`ca_start` (`Code checkerFile k0`) with `AbiCall b pb dm ra` (`ConAgua/Final/Abi.lean`), and
concludes that the machine returns to `ra` and `rdx = 0 → rax = ACCEPT → TwinAccepts [b]`.
It covers **only the default path** (step 5's `ca_start`), not `--driver` or `--jobs`.

| assumption | where it is met |
|---|---|
| `hin`, `hn`: `rdi` points at the bytes `b`, `rsi = b.size` | `slurp` returns exactly the bytes `read(2)` delivered and their count; the "buffer to stream" step (the file *is* `b`) is the trusted base's own item: the size/mtime check rejects a regular file that changed while it was read |
| `hpins`, `hnp`: the same for `pb` at `rdx`, `rcx` | `slurp(PINS)`, or `NULL`/0 (then `pb` is empty and every pin premise is vacuous) |
| `hb`, `hpb`: sizes < 2^63 | `slurp`'s last check |
| `hzero`, `hfits`: `[r8, r8 + r9)` mapped and zero, below 2^64 | a fresh anonymous `mmap` is zero; `madvise(MADV_HUGEPAGE)` does not change contents; user addresses are < 2^47. With `MAP_NORESERVE` a page the kernel cannot supply kills the process (SIGSEGV/SIGBUS/OOM), which prints nothing: never an accept |
| `hinEnd`, `hpinsEnd`, `hinDisj`, `hpinsDisj`, `hbufDisj`: buffers below 2^64, apart from the region and from each other | three distinct live allocations (two `malloc`, one `mmap`) |
| `hra`, `hcs`, `hcs24`, `hcs8`: return address at `rsp`, 32 bytes of stack around it mapped and apart from the buffers and the region | the C compiler's call, on the main thread's stack (its own mapping) |
| the code at `ca_start` is `asm/checker.s` (`Code checkerFile k0`) | `cc -O2 harness/main.c asm/checker.s`: the assembler and linker are trusted (`harness/check-asm.sh` checks the encoding, not branch targets) |
| the caller relies only on `rdx`, `rax` and the callee-saved registers | `ca_res` is a 16-byte struct of two integers: SysV returns it in `rax:rdx`, first member `rax`; `RegsRestored` (`checkerFile_accepts_regs`) gives `rsp`, `rbp`, `r14`, `r15`; `rbx`, `r12`, `r13` are not written on `ca_start`'s paths |
| accept is read as `rdx = 0 ∧ rax = ACCEPT` and nothing else | `main`'s first `if`; `ACCEPT` = `ConAgua.Final.ACCEPT` = `0x414343455054` |
| fuel, capacities, the layout | not assumed of the harness: the stub sets them (`abiFuel`, `abiNeed`); a short region makes the stub return `rdx = 1` |

**Route A** (parallel mode only, not yet in a theorem; parmode.md): after entry 1 the frozen
buffer `OUT` is `mprotect`ed `PROT_READ`, so a `ca_check_b` call that writes it faults and kills
the process, which prints nothing: never an accept. Met by `run_jobs`'s `mprotect` (checked)
over `[out, out + round_up(8·len, 4096))`. See (d) for what it does not cover.

### (c) More complex, indirect or clever than needed

In the parts this lane polishes:

1. **Test-only path in the trusted file**: `missing CODE` reads the `DIAG` array after the call
   (`ca_diag`, `ca_nw`, `ca_w0`, `ca_slot`); dead for the shipped checker (`ca_diag = -1`). It
   belongs to the e2e tooling, not to the trusted harness.
2. **Repeated error handling**: `{ perror(path); exit(3); }` seven times in `slurp`, plus the
   `fprintf(stderr, …); exit(3)` variants; a `die` helper makes the main path readable.
3. **Duplicated verdict printing**: `main` and `run_jobs` both map `(rax, rdx)` to a line.
4. **Duplicated THP loop**: `main` and `worker` each compute the 2 MB-aligned interior of a slot.
5. **`size` alias** of `ca_region_size` in `main`, while `run_jobs` uses `ca_region_size`.
6. **Missing contract comments**: how to build the binary; that only the default path is
   covered; why `ca_res` comes back in `rax:rdx`; the exit status (0 with a verdict line, 3 for
   a harness failure with no verdict).
7. `--jobs=` uses `atoi` (`--jobs=4x` is 4). Harmless.

`harness/e2e.c` (122 lines, the pre-abi driver calling `ca_enter` with its own layout and six
environment variables) is **not** trusted and not covered by any theorem, but it lives next to
`main.c`. Users: `scripts/asmprof.py` (instruction profile) and `bench.py --bin-old/--asm-old`
(A/B against pre-abi binaries, obsolete since lane abi). Proposal: port `asmprof.py` to `main.c`
and delete `e2e.c` and `--bin-old`, so `harness/` holds the trusted harness and the assembler
check only.

### (d) Wrong or fragile

1. **e2e was broken on master** (not soundness): `main.c` names parmode's symbols
   (`ca_start_a`, `ca_check_b`, `ca_start_drv`, `ca_out_off`, `ca_worker_size`), which `e2e-l asm`
   (`asmTextAbi`) did not define, so `cc` failed and all 675 fixtures read `l-crash`
   (`_tmp/e2e/census-run/e2e.md`, 6e34173b). Fixed in this lane's first landing (below).
2. **Route A covers the buffer, not what the header says** (parallel mode; soundness of the
   future threaded theorem): `ca_check_b` takes frozen array `i` at `buf + 8·buf[8+2i]` with length
   `buf[9+2i]` and checks neither against `buf_len`. The harness protects only
   `[out, out + 8·len)`. If a header pointed past it, a "frozen" array could lie in a hole later
   reused by a worker's `mmap` and be written and shared. The threaded theorem must therefore get
   "every frozen array lies inside `[0, len)`" from entry 1's postcondition (or the stub must
   check it); route A alone does not give it. Reported to parmode.
3. `g_stop` is a `volatile int` written by several threads: a data race in C11 terms (benign in
   practice). Relaxed `__atomic` loads/stores say what is meant.
4. Page size 4096 hard-coded in `run_jobs` (`bytes` rounding, the `munmap` start); right on x86-64.
   `munmap`'s results are unchecked (a failure only keeps memory mapped).
5. If entry 1 ever returned `rdx = 0, rax = ACCEPT` directly, `run_jobs` prints `ok …`, not
   `accept`: conservative, never a false accept.
6. Stale docs in Lean comments (not statements): `Final/Statement.lean` says the harness is
   "~100 lines" (212) and that `rbx` does not occur in `asm/checker.s` (`ca_start_drv` pushes and
   pops it; `ca_start`'s paths still do not write it). Its "the harness" bullet should say the
   default path of `main.c`.

### For parmode

* (d2) above: the header-in-bounds fact is part of route A's use.
* `g_stop`: `__atomic_load_n`/`__atomic_store_n(…, __ATOMIC_RELAXED)`.
* Thread start: the `ok[]` array, the `started` count and the "no thread: run on this one"
  fallback can go: start threads into `th[0..n)` with `res[0..n)` as they succeed; `n = 0` is a
  harness failure; join `th[0..n)`. Accept stays sound with any `n ≥ 1` (the started threads
  drain the counter).
* The 1 MB `pthread_attr_setstacksize` needs a reason or can go (the C stack is tiny, the L stack
  is in the region).
* Entry 1's non-pending result: use the shared verdict printer instead of a second copy.
* The worker's THP loop: use the shared helper.
* The 4096 page size and the `g_len > ca_slot / 8` check deserve one comment each.
* When `ca_start` becomes the driver: the `--driver` flag and its extern go, and the
  `Final/Statement.lean` remark about `rbx` needs updating.

## Landing 1: e2e runs the shipped code again

`scripts/e2e.py` and `bench.py` (default system) now build `check` with `asm/checker.s`'s own
generator (`ConAgua/Checker/AsmEmit.lean`, `e2e.checker_asm`), so e2e tests exactly what ships;
the report's "Compiled" line says whether the committed `asm/checker.s` is byte-identical to it
("up to date" / "STALE"). `check_np` (a test entry) is still compiled by `e2e-l asm`, which now
appends declining definitions of the parallel-mode symbols (`parDeclineText`: `rdx = 1`, never
accept) so that `main.c` links.

## Polish 1 (main.c, the parts outside parmode's)

Small commits, each building warning-free under `-Wall -Wextra`:
* the header states the contract: the build line, the default path as the one the theorem covers
  (with `AbiCall`), the verdict lines, exit status 0 with a verdict and 3 (no verdict) for a
  failure of the harness itself, and that `--jobs`/`--driver` are not covered yet;
* the test-only `missing CODE` path (and with it `ca_diag`) is gone: a test program that reaches
  an e2e stub now reads `error` (e2e has 0 stubs);
* `fail(what, why)`, `_Noreturn`, replaces the `perror`/`fprintf` + `exit(3)` copies in `slurp`
  and `main`; `slurp`'s comment is shorter (same checks);
* `print_verdict(ca_res)` and `advise_huge(start, nslots)` (the THP loop, with the two
  roundings commented); `main` names its values `in_len`, `pins_len`, `region` and passes
  `ca_region_size` directly; comments on `ca_res`'s return registers, `ACCEPT` and the asm
  constants.
`run_jobs` and `worker` are unchanged (parmode's). Note for parmode: `print_verdict` would print
`accept` for entry 1's `rax = ACCEPT`, where `run_jobs` now prints `ok …`; so switching
`run_jobs`'s first block to it is parmode's decision.
