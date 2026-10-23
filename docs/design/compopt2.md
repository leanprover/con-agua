# Lane `compopt2`: compiler wins by wall time (journal)

Branch `compopt2`, worktree `_tmp/wt/compopt2`. Prototypes stay on the branch (one commit each);
only tooling lands. Measurements: `scripts/bench.py` (interleaved), `perf stat`, `scripts/asmprof.py`
(exact instruction counts), and the new tools below. Machine: AMD EPYC 9455 (Zen 5), 4 NUMA nodes.

## Tools (new)

* `scripts/compopt2/wallprof.py BIN FIXTURE…`: where the wall time goes. One run per PMU event group
  (no multiplexing), user mode: cycles, IPC, retire stalls on loads (`ex_no_retire.load_not_complete`),
  frontend/backend-bound dispatch slots, icache/op-cache misses, L1d demand fills by source (L2, DRAM),
  dTLB misses, store-to-load-forwarding failures; plus kernel cycles and page faults.
* `scripts/compopt2/ibsprof.py BIN FIXTURE`: AMD IBS op sampling (`perf record -e ibs_op/cnt_ctl=1/
  -d -W`, works without root here): precise (no skid) per-instruction data source and miss latency,
  summed per function. This is the "which loads miss" answer that `perf record` cannot give on this
  CPU. (IBS samples about one op in 4×period; use it for shares, not absolute counts.)
* `scripts/compopt2/l2c.py IN.prog OUT.c [--no-bounds] [--no-fuel]`: translates a program file into C
  with L's semantics (bounds checks that abort, fuel at every call and loop back-edge, multiple
  results, zero-initialised locals) and the harness ABI (`ca_enter`, runs on a 64 GB lazily mapped
  thread stack). `cc -O2` of it is the **perfect-compiler oracle**: how much wall time any compiler
  work on the same L code can buy.
* `scripts/compopt2/reorder.py IN.s OUT.s PROF.bin CNT…`: orders the functions of a `.s` by an
  asmprof profile (hot first).

## Profile: master 609cdd03 (A, E1, B, memo growth, derb, rfhash; before slotgrow)

`bench.py --set default --reps 3` (cpus 64-65, load ~10–25), geometric means vs master:

| | instructions | wall |
|---|---:|---:|
| master | 1.000 | 1.000 |
| cd (compproofD's C+D port, ce1afc82) | 0.850 | 0.949 |
| clang -O2 oracle (`l2c.py`) | 0.542 | 0.854 |
| con-ron | 0.701 | 0.577 |

The oracle's instruction counts are con-ron's (c03d 2.06 G vs 2.03 G, c04a 15.1 G vs 14.9 G): the L
code itself is not heavier than the Rust. **But a perfect compiler buys only ~15% wall** on this
memory configuration, and the oracle stays ~1.5× con-ron's wall: the gap is memory, not code.

`wallprof.py`, master (user mode unless said):

| fixture | user cycles | kernel | IPC | retire stalled on load | DRAM fills | icache miss / kinstr |
|---|---:|---:|---:|---:|---:|---:|
| irrel_commit | 0.05 G | 59% | 1.47 | 70% | 0.01 M | 82 |
| long_line_5mib | 0.27 G | 26% | 4.83 | 31% | 0.01 M | 9 |
| c03d | 2.31 G | 23% | 1.63 | 71% | 2.0 M | 22–37 (noisy) |
| let-ladder | 5.44 G | 11% | 1.58 | 76% | 5.8 M | 35 |
| beta-ladder | 11.54 G | 7% | 1.38 | 80% | 14.3 M | 27 |
| c04a | 14.53 G | 7% | 1.85 | 70% | 12.9 M | 15 |
| Init (v4.35.0) | 176–188 G | 2% | 2.2–2.4 | 57–60% | 132–138 M | 38–40 |

At ~500 cycles per DRAM fill (4 NUMA nodes, loaded machine) the DRAM misses alone are 40–60% of the
user cycles. IBS on c03d: 74% of the summed miss latency is in `app_find`/`forall_find`/`lam_find`
(the intern slot tables: lane slotgrow), then `ab_find` (L2 misses). Frontend: 10–20% of dispatch
slots, icache misses 15–40 per 1000 instructions (the code is ~1 MB, hot code spread over hundreds
of functions); function order by an Init+c04a profile changed nothing measurable on c03d.

Instruction profile (asmprof, master): c03d 3.76 G, 45.8 M calls (56% of instructions in leaves);
frame load+store 33%, zero locals 6%, prologue 5%, fuel 3.7%, bounds checks (cmp+jae+base) 9.3%.
Top: `der_b` 16.5% (8.7 M calls, 71 instructions each; called by `abs_*`, `il_go`, `ilg_go`,
`inst_go`, … which mostly use one of its three results), `ab_find` 12%, `ab_put` 7%. Init 418 G,
5.0 G calls: `der_b` 10.3% (613 M calls), memo finds (`ilm_find`, `app_find`, `apd_find`, …) ~95
instructions each. With C+D: c03d 3.20 G, Init 356.5 G.

## After slotgrow (program of branch slotgrow ab77aba8, "sg"; the baseline from now on)

`bench.py --set default --reps 3`, geomean vs sg (naive compiler on master):

| | instructions | wall |
|---|---:|---:|
| sg-cd (C+D) | 0.794 | 0.881 |
| clang -O2 oracle | 0.497 | 0.758 |
| con-ron | 0.604 | 0.831 |

Small fixtures now run at con-ron's speed (irrel_commit 18 ms both; page faults 45 K → 3.6 K,
kernel 59% → 23%). The big ones stay 2–2.7× con-ron even for the oracle (c03d clang 0.47 s,
con-ron 0.23 s): data structures and memory, not code.

Oracle split (vs sg-cd, wall; `l2c.py` variants, lengths/fuel typed apart from array words so
clang may keep them in registers): clang -fno-inline 0.851–0.878; non-leaf locals `volatile`
0.934; all locals `volatile` 0.976; -fno-inline plus only small leaves (≤ 400 nodes, 232
functions) inlined 0.825 (better than clang's own inlining, 0.851: code bloat). So: register
allocation in non-leaves ~9%, the rest of isel ~3%, leaf inlining (with optimisation after it)
~6%; bounds checks and fuel ≤ 3–5% each.

Init (2 rounds): sg 46.2 s, sg-cd 41.0–44.0 s, clang 30.0–32.4 s, clang -fno-inline 33.1 s,
con-ron 25.2 s. Init is less memory-bound than the default set: the compiler headroom there is
~27% of sg-cd's wall.

## Prototypes on C+D (branch compopt2; each one commit, cumulative unless reverted)

| | commit | what | result |
|---|---|---|---|
| I | 38675f94 (reverted) | inline small leaves at call sites: args into the callee's registers, sub-frame in the caller's frame (`Ctx.fb`), fuel burn kept | c03d instructions -5% (limit 400) / ~0% (40, 120), cycles +3..6%; code 200 K → 366 K lines. In a naive compiler call/ret are nearly free on Zen 5; clang's inlining gain is the optimisation after inlining (DCE of unused results, propagation). |
| R | 38ad9035 (reverted) | non-leaf locals in callee-saved rbx/r12/r13 (push/pop), 6 argument registers | wall 0.98–1.01, instructions +1.5–3% |
| T | e9181dae | tail calls: `x⃗ := f(a⃗); return x⃗` with all results from `f` (`xs.length = nr ≤ nrOf f`, ≤ 6 args): `add rsp; jmp f` (854 sites) | c03d: L1d misses served by L2 31.3 M → 17.8 M, branch mispredicts 7.0 M → 3.0 M (return-stack overflow in the deep recursion), user cycles -8% |
| P | 592faf97 | `if c abort` as one jcc to `ca_error` | small |
| E2 | d4eb67d0 | zero only maybe-unassigned locals (compopt 345dbb1a) | -6% instructions |
| E3 | 9a6603e1 | leaf temporaries in free registers, including result registers beyond the leaf's `nret` (compopt 550fab33 + that) | -2.6% instructions c03d; most hot leaves become frameless |

Why T works: IBS (`ibsmiss.py`) on c03d: ~45% of the L1d misses were frame and return-address
loads (frame load, result load from frame, `ret`): the recursion abs_go → ab_node → abs_lam →
abs_go keeps ~300 bytes of frames per term level, beyond L1d at depth ~1000. clang's small frames
had 7× fewer L1d misses. Tail calls drop two of the three frames per level.

`bench.py --set default --reps 5` (cpus 28-29, load ~30), geomean vs sg, cycles = user+kernel
(more robust than wall here):

| | instructions | cycles | wall |
|---|---:|---:|---:|
| sg-cd | 0.794 | 0.813 | 0.892 |
| + T | 0.787 | 0.790 | 0.881 |
| + P | 0.787 | 0.787 | 0.866 |
| + E2 | 0.743 | 0.778 | 0.853 |
| + E3 | 0.722 | 0.755 | 0.889 (noise) |
| clang oracle | 0.497 | 0.627 | 0.738 |
| con-ron | 0.604 | 0.860 | 0.857 |

Init: sg-cd 360.9 G / 44.0 s, T+P+E2+E3 326.0 G / 37.2 s (runs 32.9, 41.4), clang 233.1 G / 32.4 s.

* L1 (`derlbr.py`, L-source): `der_lbr` = `der_b`'s first result only, for the 64% of `der_b`
  calls (on Init) that bind only it (`ilg_go` 42%, `il_go`, `il_bvar` 11% each): Init
  instructions -0.8% only (the tag dispatch dominates). Dropped.
* Init `der_b` callers: `ilg_go` 42%, `mk_app` 24%, `il_bvar`/`il_go` 11% each, `lp_go` 5%.

## slotgrow's growth (diagnosis for the coordinator)

asmprof block counts, c03d, `app_push`: 1 085 136 calls, 19 growths (doubling from 8 slots),
zero loop 1 048 574 iterations (8 words each ≈ 2× the final table), re-registration 2 211 071
records (2.04 per push: 1 + 1/2 + 1/4 …), 2 563 692 probes. Nothing resets the slot count; it is
amortised doubling at ~270 naive-compiled instructions per push (hash, bounds checks, probe).

Verdict agreement: `bench.py --set all --reps 0`, sg vs T+P+E2+E3: 675 fixtures, 0 disagreements.

## (e) Memory side after slotgrow (coordinator: "why is even clang-compiled L 2x con-ron?")

Tools: `ibsarr.py` (IBS load misses mapped to L arrays through an `l2c.py` build that writes its
array map, `CA_ARRMAP`), harness experiments `CA_THP` and `CA_PRESET` (harness/e2e.c).

**TLB.** c03d: con-ron 409 page faults and 54 K dTLB misses; L 98 K faults, 13.5 M dTLB misses
(c04a 70 M). Huge pages on every array except its first and last 2 MB (`CA_THP=3`; the first so a
small run does not zero 2 MB per array, the last because the slot tables keep their size in the
array's last word; THP everywhere costs the small fixtures +40–90%): c03d cycles 0.885 / wall
0.876, let 0.912/0.878, beta 0.898/0.895, c04a 0.873/0.859, small fixtures +2–6% cycles (noise
level); Init cycles 0.943–0.952, wall 0.944–0.95. Patch for abi's harness/main.c:
`_tmp/compopt2/abi/thp.patch` (madvise each word array's slot [2 MB, end − 2 MB); c04a 3.54 →
3.32 s with abi's binary, irrel_commit unchanged).

**beta-ladder slower with slotgrow** (5.2 → 6.2 s at the coordinator's load). Not repeated
growth: app 8.03 M pushes, 21 doublings, 8.58 M re-registrations; lam 4.0 M / 20 / 4.24 M. Each
re-registration is a random write into the new table (2^24 slots × 16 B = 256 MB): DRAM demand
fills 14.2 M → 26.5 M. Pre-sizing the three tables (`CA_PRESET`, no growth): fills 25.1 M →
14.1 M, cycles −12%, wall 3.29 → 2.95 s.

**Slot-table layout prototypes** (`slotk2.py`, `slotsep.py`, `recsep.py`; program-file edits of
`app/lam/forall_find/_push`; base master 7d42fede program, T+P+E2+E3 compiler, slot arrays at 2^28
words; verdicts checked):

| variant | what | result |
|---|---|---|
| K | key `f \| a << 32` in the slot next to the value; find never reads the record; growth re-inserts from the old slots in order (multiplicative home is monotone: streams) | DRAM fills halve; cycles flat (first version's 3-pass growth +40% instructions) |
| S alone | tiers in separate halves, records still compared | no gain (c03d), loss (beta) |
| K+S, one size | both | Init +5% cycles (tier-0 heavy: tier 1's half dead) |
| R | records by tier too | no gain |
| **KST** | K + S + each tier its own size/base (words at the end of its half), only the pushing tier grows, growth into a fresh region above (no zeroing, no record reads) | default 7 rounds cycles/wall: c03d 0.874/0.912, beta 0.863/0.889, c04a 0.857/0.857, let 0.970/0.977, small fixtures noise; Init (with THP, 3 rounds) 0.895/0.894; DRAM fills c03d 4.2 → 1.4 M, beta 25 → 11.4 M; RSS ×1.25–1.5 on the big fixtures |

The spec of KST's layout and code is `slotk2.py` (docstring and generator); it is meant for the
planned generic cons-table library. RSS: two words a slot per tier instead of one, and the
moving-up regions keep old tables resident (an in-place doubling or a two-region scheme would
fix the latter).

Bench pitfall found: `bench.py`'s per-fixture rows show a ratio even when a system's verdict is
not `accept` (the geometric mean excludes it); my first K+S beta-ladder figure (0.48) was an abort
on a too-small capacity.

## Final growth scheme for the cons tables (handed to lane conslib)

`slotk2.py --sep --pertier --pingpong` (KSTP): each tier has its own half of the slot array, its own
size and region base (last two words of the half), and two fixed regions it alternates between;
growth zeroes the target region, walks the old slots in order and re-inserts the live ones
(near-sequential: the multiplicative home is monotone). Slot words touched ×1.5 of master's, peak
RSS ×1.20–1.27 on the big fixtures (moving-up regions: ×1.42–1.53), cycles as KST. In-place
doubling was not pursued: with linear probing an entry displaced further than its home index
lands below unprocessed ones.

## Closing (2026-10-23)

Landed (tooling only): `scripts/compopt2/` (wallprof, ibsprof, ibslat, ibsmiss, ibsarr, l2c,
reorder, derlbr, slotkey, slotk2, slotsep, recsep), `bench.py` cycles reporting, this journal.
`l2c.py` emits the old harness ABI (`ca_enter`, `harness/e2e.c`); the harness switches used
here (`CA_THP`, `CA_PRESET`, `CA_HWM` per array length, in `harness/e2e.c`) stay on branch
`compopt2`, superseded by `harness/main.c` (which has the THP madvise). The compiler prototypes
stay on branch `compopt2` for the proof lane: T `e9181dae`, P `592faf97`, E2 `d4eb67d0`,
E3 `9a6603e1`, on top of compproofD's C+D port (`1389ba18`). The memo tables (ABMEMO, ILMEMO:
the next miss sources on c03d/c04a) are left for a new lane.
