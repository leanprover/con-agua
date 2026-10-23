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
