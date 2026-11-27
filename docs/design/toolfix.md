# toolfix: three broken measurement tools

Lane `toolfix` (2026-11-27) fixes the three tools that lane ronsync9 found broken on master
(`docs/design/ronsync9.md`, sections 4-6).

## 1. `scripts/asmprof.py`: the instrumented binary rejected `Init`

**Cause.** The instrumentation puts `incq ca_bb+8i(%rip)` at every block start, including the
instruction after a conditional jump. `incq` keeps CF but writes ZF, SF, OF and PF. The compiled
code never has flags live there, but the hand-written `ca_f_nat_cmp` (lane asm escape) has two
places with `jb …` followed by `ja …` on the same `cmp`. The counter between them overwrote ZF,
so `ja` was taken on equal limbs and `nat_cmp` returned "greater" for equal numbers. `Init`
was then rejected with "application type mismatch" after 18.9 G instructions. The `adc`/`sbb`
loops of the other hand-written functions read only CF, which `incq` keeps, so they were fine.

**Fix.** `build` checks each counter: if a flag other than CF is read after it (through labels
and instructions that write no flags) before any instruction writes the flags, the counter is
wrapped in `pushfq`/`popfq`. The compiled code stores nothing below `%rsp` (no red zone), so the
push is harmless. On master's `checker.s` this wraps exactly the two counters in `ca_f_nat_cmp`.
`asmprof.py run` now also prints the exit code and stderr and exits with the binary's code (a
rejection was easy to miss before: it printed only stdout).

**Check.** `Init` (`init435.ndjson`): accepted (plain `./checker`: accepted, 14.9 s;
instrumented: 18.2 s). The profile counts 202 632.7 M instructions, against 202 632.9 M from
`perf stat -e instructions:u` for the plain binary (ronsync9 section 5; the rest is `main.c` and
libc). `diff-e2e.py --bin` with the instrumented binary: 766/766 agree (447 accepted, 319 not),
the same as the plain binary.
