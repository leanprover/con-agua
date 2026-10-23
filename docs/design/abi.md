# Lane abi: a five-argument entry, the region laid out by the compiled code

## Goal

Shrink the harness (and with it the trusted base): instead of laying out ~215 word arrays, the
descriptor table, the ROM and the L stack and calling `ca_enter(T, fuel)`, the harness maps one
zero region and calls an entry stub with the two input buffers and the region. The stub (emitted
by the compiler before the trampoline) sets up the rest; the proof (later, after compproofB) shows
that it establishes `Layout.Ok`/`MemRel`, so `compile_correct` applies.

## Prototype (2026-10-23, unproved)

**Interface.** `ca_start(in, in_len, pins, pins_len, base, base_len)` (System V: `rdi, rsi, rdx,
rcx, r8, r9`), returns `rax`/`rdx` as `ca_enter`. The user allowed the sixth parameter
`base_len`: the stub compares it with the size it needs (`ca_region_size`, exported) and returns
`rdx = 1` (resources exhausted, never accept) if it is smaller. So the theorem needs "the region
is mapped for `base_len` bytes", not a size premise. The old trampoline `ca_enter(T, fuel)` stays
(the stub tail-jumps into it), so `harness/e2e.c` still works on the same `.s` for experiments;
the rename (stub = `ca_enter`, trampoline = an internal label) waits for the proof phase.

**Stub** (`ConAgua/Compiler/Abi.lean`, `abiStub`): Kraken directives, straight-line apart from the
size check: `T = base`; descriptors by `mov rax, imm64; add rax, r8; mov [r8 + d], rax`; the ROM
by immediate stores, word by word (no `.rodata` read, so no loader premise about `ca_rom`; 4646
words, ~9300 instructions, run once); then `rdi := r8; rsi := 2^62 - 1; jmp ca_enter`. The
result area and the globals are the region's zeros. No loops, so the proof is an induction over
the list of stores.

**Partition.** Slots of `2^35` bytes (`2^32` words): slot 0 the table, slot 1 the L stack (`2^30`
bytes at the slot's bottom, as the old default `CA_STACK`), then byte arrays `2…nb-1`, then the
word arrays. Every array starts at its slot; length `2^32` words. Byte arrays 0 and 1 are the
caller's buffers (no copy). With `nb = 2`, `nw = 215`: `ca_region_size` = 217 × 2^35 ≈ 7.5 TB of
address space (x86-64 user space is 128 TB). `vm.overcommit_memory = 0` accepts it with
`MAP_NORESERVE`.

**Slot tables (until lane slotgrow lands).** Measured: the intern slot tables span their whole
array (`n := len64 a >>> 1`), so at `2^32` words every insert faults a fresh page. Until slotgrow's
growable tables land, `abiWords` gives the arrays whose length the program reads as
`len64 a >>> 1` (33 arrays, found in the program, not by number) `abiSlotTableWords = 2^25`
words; every other word array gets `2^32`. Lengths are not trusted (the theorem holds at any).
`CA_ABI_SLOT_WORDS` (read by `e2e-l asm`) overrides it for experiments.

**Harness** (`harness/main.c`, ~50 lines): `main FILE [PINS]`, reads both files, maps the region,
calls once, prints the verdict as `harness/e2e.c` did (`missing CODE` reads the DIAG array at
`ca_w0 + ca_diag * ca_slot`). No env knobs (`CA_WORDS`, `CA_FUEL`, `CA_STACK`, … are gone).

**Scripts.** `scripts/e2e.py` compiles with `harness/main.c`, passes the pin file as the second
argument, and drops the capacity retries (2^22 → 2^25 → 2^27). `scripts/bench.py`: `--bin/--asm`
use the new harness, `--bin-old/--asm-old` the old one with its `CA_WORDS` ladder (for A/B).
The emitters `e2e-l asm`, `compopt-asm` and `Checker/AsmEmit.lean` print the stub first.

**Results, master + abi (slot tables at 2^25).** `scripts/e2e.py` (675 fixtures): the same classes
as the compproofB baseline except `arena/good/perf/app-lam` (accept → error, both entries): it
needs slot tables of 2^27 words (old harness: `CA_WORDS` 2^27 on the retry). At 2^27 it accepts
(13.1 s, 3.96 GB; old harness at `CA_WORDS=2^27`: 13.5 s, 3.96 GB). A fixed 2^27 would cost every
small fixture the page faults of eight times larger tables (irrel_commit at 2^25: 91 MB vs 55 MB
at 2^22, 14 MB at 2^16), so the interim fix is not worth tuning: slotgrow removes the issue.

**Results, master + abi + slotgrow (test merge, worktree `abi-sg`, every word array 2^32 words,
`CA_ABI_SLOT_WORDS=2^32`).** e2e: 407 agree-accept (= baseline, app-lam included, no capacity
retries), the same rejects/timeouts. One change: `e2e/stack_fuel_offset` (con-leche expects an
abort, con-ron aborts with SIGABRT, `e2e-ref` memouts) was an L `error` at the old capacities and
is now an L memout under e2e.py's 6 GB guard: the input interns millions of application nodes
(arrays 4/5, `AREC`/`ASLOT`, full at 2^25 words), and with 2^32-word arrays L only stops at
`app_push`'s own limit of 2^27 records (~4 GB of records plus the slots). Neither accepts; but
with this layout the program's own record limits, not the harness, bound memory.

## Later: a parallel mode (user's design input, 2026-10-23; not built)

Entry 1 (the current arguments) runs the stages and the install fold (phase A) and returns the
number of declaration groups and a pointer to the installed, frozen tier-1 environment; entry 2
takes that pointer, a group index and its own region, and checks one group (phase B, as con-ron's
Pooled/Phased); a small trusted harness runs entry 2 in parallel. The partition does not preclude
it: every array has its own descriptor and its own slot at a fixed offset, so an entry-2 stub
writes, for each array phase B only reads (the tier-1 environment), `env_base + offset`, and for
every other array (scratch, memo tables, the work stacks) `own_base + offset`; its table (globals,
results) and its L stack live in its own region. The intended split: slots ordered as [table,
stack | tier-1 environment arrays | scratch arrays], so that the environment section is one
contiguous range (one `mprotect` read-only after phase A, one disjointness premise per worker).
Which arrays are tier 1 is the phase-B lane's classification; the stub then takes it as a
parameter (`ArrId → section`). Until then all arrays are in one section.

**Benchmark** (`abi-sg`, one `.s` linked with both harnesses; `bench.py --no-ref`, `new` =
`harness/main.c`, `old` = `harness/e2e.c` at its `CA_WORDS` ladder; load 9–17):

| set | instructions old/new | wall old/new | RSS |
|---|---:|---:|---|
| default (13 fixtures, 3 rounds) | 1.001 | 1.013 | identical per fixture (c04a 551/552 MB, beta-ladder 947/947 MB) |
| init (init-prelude, Init v4.35.0; 2 rounds) | 1.000 | 1.012 | Init 1222 / 1219 MB |

Init alone, `perf stat`, two runs each: new 37.2 / 41.3 s task-clock, old 36.6 / 39.6 s; page
faults 410 151 / 410 282 vs 409 274 / 409 163; dTLB load misses 256 M / 262 M vs 264 M / 265 M.
So the `2^35`-byte spacing costs nothing measurable, and the new harness needs no capacity
retries (the old one's c03d/let-ladder/beta-ladder/c04a/Init runs fail at 2^22 first). The stub
itself is ~10 000 instructions. `harness/check-asm.sh` passes with the stub in the checker's
file (278 363 instructions match).

**Landing order.** On master without slotgrow, the new e2e loses app-lam (no retry ladder, slot
tables at 2^25); with slotgrow it is clean. So: land after slotgrow, deleting `halfLen`,
`abiSlotTableWords` and `CA_ABI_SLOT_WORDS` in the same step (with growable tables every array
gets `2^32` words).

**Coordinator's decisions (2026-10-23).** Land right after slotgrow, deleting the hash-table
workaround in the same step. `stack_fuel_offset` running into the memory guard instead of an
early `error` is accepted (nobody accepts it); `scripts/e2e.py` classifies L memout against a
reference memout as `agree-memout` (passing, like `agree-timeout`). Proof after compproofD (its
trampoline loads ≤ 6 entry arguments into `rdi r8 r9 r10 r11 rsi`; the stub relies on no register
across the call).

**Landed with slotgrow (2026-10-23).** slotgrow is on master (7d42fede); the hash-table
workaround (`halfLen`, `abiSlotTableWords`, `CA_ABI_SLOT_WORDS`) is deleted: every word array gets
`abiWords = 2^32` words.
