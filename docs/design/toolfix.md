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

## 2. `scripts/e2e.py`: the `check_np` link failed

**Cause.** `main.c` calls the compared run's entries `ca_start_c` and `ca_start_ac`
(`--compare`, lanes compare and compare2). Only the shipped checker defines them (`cmpStub` in
`ConAgua/Checker/AsmEmit.lean`). `e2e-l asm` compiles `check_np` without them, so `cc main.c
check_np.s` had two undefined references. A second problem showed up in a fresh worktree: the
`check` entry runs `ConAgua/Checker/AsmEmit.lean` with `lake env lean --run`, but e2e's build
list did not contain that module, so its imports (`ConAgua.Checker.ProgTab`, …) could be
missing.

**Fix.** `compile_entry` appends `ca_start_c`/`ca_start_ac` to every non-shipped entry's
assembler text, as one `ud2` (e2e runs no compared run, so they are never called). The build
list gets `ConAgua.Checker.AsmEmit`.

**Check.** `e2e.py --latest '' --assemble-only --no-diff`: both entries compile and link.
`e2e.py --latest '' --no-perf --no-diff` (827 fixtures): `check_np`
against `con-ron-lean-twin --no-prelude` has no disagreement: 463 agree-accept, 62
agree-decline, 288 agree-reject (7 of them as L aborts, 29 at another stage), 2 time out in both,
and 12 time out only in `check_np`. `check` matches ronsync9's run: 825 of 827 agree with
`con-ron` and `con-ron-lean-twin` (482 accept), and the other 2 time out in all three.

## 3. `scripts/census.py`: killed at its 6 GB memory limit

**What grew.** Measured per process (`/proc/PID/status`, every 0.2 s), master `c2c1c72ce`: the
link child that imports 573 modules peaks at 5.83 GB VmRSS, but only 0.24 GB of that is
anonymous (`RssAnon`); the other children (imports that fail on a module clash) at 3.5 GB with
0.38 GB anonymous. The tree (python, lake, driver, child) peaks at 6.06 GB VmRSS and 0.43 GB
anonymous. Almost all of it is file-backed: the oleans Lean maps from disk. The link pass walks
the proof terms of every linked theorem and of the end-to-end theorem's cone (`axiomsOf`,
`sorrySources`), so it touches nearly all of the imported data, and the project's oleans are now
0.62 GB `.olean` plus 4.23 GB `.olean.private` (the proofs), plus 0.32 GB of the toolchain.
When the guard was written (lane censusmem, 2026-10-22, `ac91b80e6`), the project had 238
`.lean` files under `ConAgua/`; now it has 1604. So the growth is legitimate: it is the
project's size, and it is page cache (on xfs, hard-linked into the shared Lake cache, shared
with every process that maps the same oleans, reclaimable), not heap. No bisect was needed:
the heap is small, so no single landing caused a leak.

**Fix.** The guard counts anonymous memory (`RssAnon` of the process tree) instead of `VmRSS`,
with the same limit of 6 GB. The heap is what took the machine down before (repeated imports
read into the heap, DESIGN.md, "Census memory"). `CENSUS_PEAK=1` prints both peaks. PLAN's figure
now says about 0.4 GB of heap and about 6 GB resident. `census.py --no-build`: 70.7 s, exit 0,
peak 0.43 GB anonymous, 6.06 GB resident.
