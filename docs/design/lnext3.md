# Lane lnext3: the next steps for L, re-measured and re-ranked (analysis journal)

Question: lnext2.md §2's ranked steps are all done or decided (the inliner, bce, the whole-program
split, growtop, parprof and its follow-ups memosplit/derbv/derbr/memoglob/mkmax/walkmax, the
refgen and forloop no-gos, natsurvey/offkit; `der` parked by the user, gframe's `KGH` parked).
Re-measure on master and rank the next 5–8 steps across the three goals: faster code, smaller L
code, smaller simulation proofs (work moved into the compiler and the libraries).

Base: master 9f23b3b8. **Only this journal lands.** Scratch: `_tmp/lnext3/` (`bin/`: the binaries;
`p1/`, `p16/`: phase benches; `wb1.json`, `wb16.json`, `wbR.json`, `span.jsonl`, `pstat.json`:
paired benches; `prof/`: exact profiles; `survey/`: lnext2's survey scripts pointed at this
master; `build/`: the cold build, its import graph and `cp.py` output; `rf/rfc.s`: the D40
prototype).

**Measurement conditions.** Load 20–52 throughout (96 CPUs). The user slice was at 39–52 GB of
its 50 GiB cap (another session held 27–44 GB), so page faults went through direct reclaim
(`pgscan_direct` in the slice's `memory.stat`) and transparent huge pages often fell back to 4 KB
(`thp_fault_fallback`). Fault-heavy runs pay for this in kernel time, con-ron more than L on most
inputs (it frees and re-faults), L far more on c05b (§1.4). The wall ratios below are today's, not
a quiet machine's (OVERVIEW §3 has those); user-mode cycles and instructions are the stable
numbers.

**Answer in short.**

* **`Init` at 16 threads is within 4–6 % of con-ron** (whole run 1.044, p 0.034 with perf; 1.011,
  p 0.29 without; parallel phase 1.06, p 0.008). The parse is at parity (1.85 vs 1.80 s, p 0.83).
  Phase B executes 1.13× con-ron's instructions (192.0 vs 170.6 G; parprof had 1.24×).
* **One thread on `Init` is 1.10× con-ron** (p < 0.001, n 30) at this load: 1.16× the instructions,
  1.23× the user cycles. L's IPC advantage (parprof §1.4) needs an idle SMT sibling.
* **The large outlier is c05b, 2.1× con-ron, and its cause is a twin deviation**: the `replace_fvars`
  memo (D40) is never cleared, holds 510 of the run's 640 MB, and every page of it is faulted in.
  A one-clear prototype: **c05b −48.5 % wall** (p < 0.001, n 40), RSS 644 → 131 MB (con-ron 195),
  `Init` and app-lam unchanged, 634/634 verdicts (§1.4). Rank 1.
* **Build: the largest lever left is the module system's early cutoff for the proofs.** A
  proof-only landing like offkit rebuilds 435 modules (1,386 module-s, 209 s critical path); with
  `module` files above the twin it would be about 56 (181 module-s, 32 s). It needs con-ron's
  arena and bridge as `module` files (restructure.md had found the blocker; §1.6 measures what it
  costs per landing). Rank 2.
* **Proofs: no large generic lever is left.** The refinement layer is 109 k of 303 k proof lines,
  hand-written. The RefWalk kit (refgen) is the one measured reduction (−17 % per file, 12 % less
  elaboration); as a uniform migration it is worth −4 to −5 k lines and one per-call shape for twin
  syncs. L-level sugar, fuel, `Nat`-valued models and word ↔ `Nat` kits are measured out (§3).
* **Codegen leftovers and gframe `KGH`** each save 0.4–2 % of the instructions; at the measured
  instructions → wall elasticity of ~0.5 that is ≤ 1 % wall each. Not worth a lane on their own
  (§3); as a bundle they are the last ranks.

## 1. Measurements

### 1.1 `Init` against con-ron, by phase

`_tmp/lnext2/phase.py` (perf record, parse = the last 50 ms window of the main thread with ≥ 10 %
scanner samples, parallel start = the first window with ≥ 4 threads), interleaved rounds; ratios
are medians of the per-round ratios, Wilcoxon signed-rank p (`_tmp/lnext3/phstats.py`). One thread
pinned to CPUs 44,92 (one core, both SMT threads), 16 threads to 24–39. con-ron: the default binary
`_tmp/ref/con-ron-integrate/target/release/con-ron`.

| cell | ours | con-ron | ratio | p | lnext2 |
|---|---:|---:|---:|---:|---:|
| 1 thread, whole run (12 rounds, load 21–35) | 20.86 s | 20.32 s | 1.036 | 0.043 | 0.99 |
| 1 thread, parse | 1.95 s | 1.85 s | 1.04 | 0.70 | 1.12 |
| 16 threads, whole run (24 rounds, load 20–31) | 3.99 s | 3.81 s | **1.044** | 0.034 | 1.09 |
| 16 threads, parse | 1.85 s | 1.80 s | 1.01 | 0.83 | 1.12 |
| 16 threads, serial part after the parse | 0.50 s | 0.50 s | 1.00 | 0.18 | 1.0 |
| 16 threads, parallel phase | 1.56 s | 1.42 s | **1.064** | 0.002 | 1.12 |

Without perf (`_tmp/bce/wb2.py`, the two binaries back to back in random order):

| cell | n | con-ron | ours vs con-ron | load |
|---|---:|---:|---|---|
| `Init`, `--jobs=16` (24–39) | 100 | 4.79 s | +1.1 % (p 0.29; [−1.5, +3.0]) | 23–44 |
| `Init`, one thread (44,92) | 30 | 22.92 s | **+10.2 %** (p < 0.001; [+6.6, +15.5]) | 26–52 |

The parallel phase per worker (`_tmp/parprof/ws.py`, 30 interleaved rounds, load 26–36):

| | ours | con-ron | ratio | p |
|---|---:|---:|---:|---:|
| span | 1.709 s | 1.621 s | **1.059** | 0.008 |
| worker instructions (user + kernel) | 192.0 G | 170.6 G | **1.127** | < 0.001 |
| worker cycles | 107.6 G | 102.2 G | 1.075 | 0.015 |
| worker kernel time | 0.68 s | 2.20 s | 0.45 | 0.038 |

So the 16-thread gap is the parallel phase, and in it the instruction count: parprof's 1.24× is
now 1.13×. The span moves by about half the instruction ratio (ln 1.059 / ln 1.127 = 0.48),
as wallcum.md found (§4: −7.1 % instructions, −3.5 % wall at one thread, −3.9 % span).

### 1.2 Other inputs

One thread, both systems pinned to the same SMT pair. Wall: `wb2.py`, 30 rounds on CPUs 44,92 (load
26–52). User cycles, kernel cycles and instructions: `perf stat`, 6 interleaved rounds on CPUs 6,54
(`_tmp/lnext3/pstat.py`, load 26–44). Medians; ratio = ours ÷ con-ron.

| input | wall ours / con-ron | wall ratio (p) | user cycles ratio | instructions ours / con-ron | kernel cycles ratio | OVERVIEW §3 (quiet) |
|---|---:|---:|---:|---:|---:|---:|
| `Init` | 26.06 / 22.92 s | **1.10** (< 0.001) | 1.23 | 214.0 / 184.5 G (1.16) | 0.38 | — |
| app-lam | 13.03 / 13.46 s | 0.92 (0.035) | 1.45 | 41.6 / 27.3 G (1.53) | 0.60 | 1.44 |
| beta-ladder | 2.90 / 3.28 s | 0.91 (0.038) | 1.36 | 11.2 / 8.4 G (1.33) | 0.73 | 1.27 |
| let-ladder | 1.27 / 1.74 s | 0.75 (< 0.001) | 1.21 | 5.9 / 4.6 G (1.27) | 0.88 | 1.10 |
| eager_open | 3.40 / 4.03 s | 0.82 (< 0.001) | 1.06 | 16.0 / 13.2 G (1.21) | 0.25 | 1.07 |
| c04a | 2.97 / 3.54 s | 0.95 (0.20) | 1.13 | 16.2 / 15.0 G (1.08) | 0.41 | 1.13 |
| c05b | 2.40 / 0.98 s | **2.10** (< 0.001) | 1.70 | 12.9 / 9.6 G (1.35) | **6.1** | 1.75 |

Today's walls on the table-heavy inputs favour L only because con-ron's frees and re-faults cost
it more under reclaim; the user-cycle column agrees with the quiet OVERVIEW ratios (app-lam 1.45 vs
1.44, beta-ladder 1.36 vs 1.27). c05b is the exception in the other direction (§1.4).

### 1.3 Exact instruction profiles (`scripts/asmprof.py`, `checker.s` of master)

**`Init`**: 214.0 G instructions (lnext2: 237.3 G, −9.8 %), 4.09 G calls, 47.3 % in leaves.
Phase B alone (parprof's `asmprof_pb.py` harness on today's `main.c`, `--jobs=2` on one CPU):
189.7 G (parprof: 203.3 G), phase A 25.2 G.

| function | share | calls | per call |
|---|---:|---:|---:|
| `der_bv` | 5.15 % | 393 M | 28 |
| `ilm_find` | 4.75 % | 238 M | 43 |
| `app_find` | 4.67 % | 173 M | 58 |
| `mk_app` | 4.66 % | 164 M | 61 |
| `intern_app` | 4.50 % | 164 M | 59 |
| `ilg_go` | 4.43 % | 257 M | 37 |
| `ilg_app` | 4.42 % | 104 M | 91 |
| `get_app_spine` | 3.79 % | 25 M | 329 |
| `der_b` | 3.52 % | 219 M | 34 |
| `ilm_put` | 3.21 % | 116 M | 59 |

By category (asmprof's patterns; the finer split from `_tmp/cgproto/py/ana.py`):

| category | `Init` | lnext2 |
|---|---:|---:|
| frame stores + loads | 16.1 % (10.5 + 5.6) | 15.3 % |
| of which call arguments loaded from the frame | 5.0 % | (counted as "result registers") |
| fuel check (`subq $1, %r14; jb`) | 4.6 % | |
| stack check (4 instructions per check, 2.10 G checks) | ≈ 3.9 % | 5.6 % with fuel |
| prologue / epilogue | 4.9 % | 5.5 % |
| result loads and zeroing before `return` | 0.6 % | |
| compiler bounds checks (`cmp` + `jae`/`jbe ca_error`) | 5.0 % (10.7 G) | 6.5 % (cgproto) |
| `call` + `ret` | 3.3 % | 3.4 % |

**Phase B by family against con-ron** (parprof's `fam.py`; con-ron's column is parprof's sampled
`instructions:u`, the same binary; Rust inlining moves cost between families, so read the sums):

| family | ours | con-ron | difference |
|---|---:|---:|---:|
| `der_b`, `der_bv` (inlined at con-ron's call sites) | 18.0 G | — | +18.0 |
| bvar instantiate and its memo | 46.2 G | 32.3 G | +14.0 |
| interning (`mk_*`, node tables) | 45.2 G | 30.9 G | +14.4 |
| whnf, defeq, infer, reduction and their caches | 54.2 G | 37.3 G | +16.9 |
| level-parameter instantiate | 7.6 G | 6.2 G | +1.4 |
| environment lookups | 5.3 G | 3.3 G | +2.0 |
| app spine and arguments | 12.4 G | 19.0 G | −6.6 |
| allocation, copies, drops | 0.7 G | 22.9 G | −22.2 |

The excess is spread over the hot small functions as in parprof; no single family holds more than
a third of it.

**app-lam** (41.6 G): `app_push` 19.2 % (249 per call), `ilm_find` 11.0 %, `ilm_put` 10.5 % (110
per call against 59 on `Init`). 2.07 G of `ilm_put`'s 4.39 G are in blocks that run less than 0.7
times per call, i.e. the inline growth of the instantiate memo, which starts from its default region
in every `inst_list` call (D37; con-ron's `HashMap2<EIdxNat, _>` spends 0.18 % in `move_slots`).
**beta-ladder** (11.2 G): `app_push` 17.7 %, `lam_push` 8.8 % (247 per call: the amortised doubling).
**c05b** (12.9 G): `e_view` 10.4 %, `forall_find` 9.5 % (3.8 probes per call, against 1.2 on
`Init`), `rf_put` 7.3 % (234 per call), `rf_find` 4.3 %.

### 1.4 c05b: the `replace_fvars` memo (D40)

`perf stat` on c05b, one run each (CPU 5, same conditions): con-ron 3.55 G user cycles, 0.82 G kernel
cycles, 3.8 k page faults, 26 k 4 KB TLB reloads; ours 6.28 G user, 3.39 G kernel, 33.5 k faults,
7.2 M TLB reloads, 3.3× the DRAM fills. The resident set by array (`/proc/PID/smaps` at exit,
under gdb, slots mapped to arrays through `ConAgua/Layout.lean` and `Tab.slotOf`): **`RFM`
(`Ind.RFM`, the `replace_fvars` memo) holds 510.5 of 639.8 MB** (456 MB of it in huge pages); the
next arrays are `ASLOT` tier 1 30 MB, `IW` 14.5 MB.

The memo is banked (`rf_bank_enter`/`rf_bank_leave`, MemoBank.lean): each `replace_fvars` call gets
a fresh generation, so its lookups are those of the twin's fresh map. But the dead generations stay
in the table until a clear, and `rf_clear` is never called (D40: "keeps its entries for the whole
run"), so the table grows over all 4.0 M puts of the run.

**Prototype** (`_tmp/lnext3/rf/rfc.s`, an edit of `checker.s`): after the inlined bank leave in
`ca_f_replace_fvars`, if the restored generation is 0 (the outermost call: 5,991 of 6,081 calls),
clear the memo (its epoch word `CTL[208]` + 1, count `CTL[209]` := 0, as `memoClearG`):

| | ours | prototype | con-ron |
|---|---:|---:|---:|
| c05b wall (`wb2.py`, 40 rounds, CPUs 8,56, load 33–42) | 2.34 s | 1.19 s (**−48.5 %**, p < 0.001; [−51.2, −42.8]) | 0.93 s |
| user cycles (median of 6, CPUs 6,54) | 6.05 G | 4.52 G | 3.53 G |
| kernel cycles | 3.19 G | 0.08 G | 0.06 G |
| instructions | 12.94 G | 12.04 G (−7.0 %) | 9.58 G |
| peak RSS | 644 MB | 131 MB | 195 MB |

`Init` 214.004 → 214.000 G instructions, app-lam 41.647 → 41.647 G. `diff-e2e --bin` on the
prototype: 634 of 634 agree (406 accepted), 0 UNSOUND / INCOMPLETE / CRASH / TIMEOUT. On a quiet
machine the kernel part is smaller (OVERVIEW: c05b 1.28 s against con-ron's 0.73 s); the user-cycle
part (−25 %) and the memory are not load effects.

### 1.5 Proof lines (lnext2's survey, rerun)

303,133 proof lines without comments and blanks (lnext2: 298,543; +3.3 k in `Compiler/` from the
inliner and bce, +0.5 k in `Checker/`). L code: 18,224 lines.

| layer | lines | share | lnext2 |
|---|---:|---:|---:|
| refinement (model ⊑ twin) | 109,123 | 36.0 % | 108,287 |
| other lemmas | 51,148 | 16.9 % | 49,678 |
| commands, structures, other | 35,004 | 11.5 % | 34,610 |
| model equations | 28,908 | 9.5 % | 28,721 |
| spec (L ⊑ model) | 26,900 | 8.9 % | 26,592 |
| frames | 9,562 | 3.2 % | 9,523 |
| hand word models | 8,877 | 2.9 % | 8,877 |
| error claims | 5,701 | 1.9 % | 5,451 |

By family (`survey/fam3.py`, by file path):

| family | proof lines | share | refinement | spec | model eq. | other lemma |
|---|---:|---:|---:|---:|---:|---:|
| inductive types (`Ind*`, `Rec*`, `GenRec`, `Install`, …) | 79,576 | 26.3 % | 31,031 | 8,672 | 8,795 | 8,796 |
| whnf, defeq, infer, reduction, declarations | 69,809 | 23.0 % | 36,160 | 6,384 | 4,965 | 7,297 |
| expression store, interning, memos, levels, walks | 52,187 | 17.2 % | 16,379 | 5,114 | 7,552 | 9,086 |
| other `Arena/` | 8,362 | 2.8 % | 2,029 | 1,021 | 847 | 1,897 |
| front end (`Front/`) | 19,565 | 6.5 % | 4,160 | 1,870 | 1,947 | 5,786 |
| compiler (`Compiler/`) | 19,522 | 6.4 % | 2,436 | 0 | 1,576 | 8,496 |
| whole program, threads, final (`Checker/`, `Final/`) | 17,480 | 5.8 % | 5,934 | 669 | 1,171 | 3,901 |
| verdict closure (`Verdict/`) | 14,340 | 4.7 % | 7,465 | 772 | 341 | 1,291 |
| scanner (`Scan/`) | 7,484 | 2.5 % | 732 | 1,519 | 880 | 2,034 |
| L core (`L/`) | 6,601 | 2.2 % | 161 | 499 | 38 | 1,566 |
| ROM, pins (`Rom/`) | 6,317 | 2.1 % | 2,627 | 380 | 796 | 992 |

Patterns (`patterns.py`, a line counted once per group): word ↔ `Nat` 32.2 k, glue 18.0 k, fuel
15.7 k, abort plumbing 10.0 k, frames 7.8 k, twin bridge 8.1 k, tags 3.6 k; all within ±1 % of
lnext2. The `RefE` theorems (`_tmp/refgen/reflen.py`): 321, 26,710 lines, unchanged since refgen.
Program lookups: 5,023 lines mention `p.lookup "…"`, 1,315 of them are nothing but lookup
hypotheses. Preservation lemmas named `_frame`, `_afr`, `_mfr`, `_grow`, `_top*`, `_keep`: 605
declarations, 6.2 k lines (median 8).

Nothing moved since lnext2 at the scale of the layers: the landings of the last two days were
speed work and two small kits.

### 1.6 Build

**Cold build** of this master (`LAKE_COLD=1 scripts/lake build`, a fresh worktree). The memory cap
did not allow 16 jobs: a guard stopped the build twice when the slice passed 51 GB, and it ran to
the end in three parts with 6, 4 and 2 jobs (`LEAN_NUM_THREADS`, which also caps each `lean`'s
threads), at load 30–50. Wall time is therefore not comparable to lnext2's 452 s, and per-module
times are inflated against a quiet 16-job build (the asm parts: 45–63 s here against 14–33 s alone,
inline.md §4).

* **6,457 module-seconds** over 2,088 modules (lnext2: 5,742 over 2,047), **critical path
  374 s** (75 modules; lnext2 327 s). It now runs `L → Scan → Front → Rom → Prelude → DataLit →
  … → DefEq* → … → Checker.LoopProgInd (41 s) → LoopProg (20 s) → … → VerdictEntry1 (17 s) → Final`:
  the whole-program checks are off the cold path (wholeprog's split did that).
* By module kind (module-seconds, modules): whole-program (`Checker/`, `Final/`) 1,741 (148);
  other 1,332 (512); refinement modules without an `l_model` 1,304 (464); modules with an
  `l_model` 994 (190); vendored con-leche / con-ron 984 (737); compiler 103 (37). The generated
  `Checker/Prog*`/`Asm*` pipeline is 938 module-s in 43 modules.

**What an edit rebuilds** (`cp.py --touch`: the edited module's importers, transitively, with no
early cutoff; the critical path among them, unlimited cores):

| edited module | rebuilt modules | module-s | critical path |
|---|---:|---:|---:|
| `Checker/Prog` (the program literal; every L change) | 109 | 1,560 | 154 s |
| `Arena/IndPos` (an L definition module) | 701 | 3,327 | 229 s |
| `Arena/WhnfCore` | 736 | 3,490 | 246 s |
| `Arena/InstList` | 712 | 3,377 | 254 s |
| `Front/ApplyExpr` | 810 | 3,768 | 310 s |
| `Arena/MemoLib` | 1,086 | 4,635 | 334 s |
| `Arena/ExprMk` | 1,067 | 4,586 | 321 s |
| `Compiler/Compile` | 849 | 4,040 | 272 s |
| `L/ModelGen` | 975 | 4,404 | 310 s |
| `Arena/IndT/Sum4` (a refinement) | 24 | 100 | 71 s |

The program literal's path is `Prog → ProgIdx → ProgIPart4 (40 s) → ProgI → ProgSktPart2 (21 s) →
ProgSkt → AsmPart3 (63 s) → Asm → AsmFileEq → Final/*`.

**Early cutoff, checked.** In the built worktree, one `skip` added to a proof in
`Compiler/SimStore.lean` (a `module` file; its closure is 20 modules) and a build with the cache
off: Lake rebuilt SimStore and the 14 non-`module` files below it (`Final/*`, `Checker.ProgIRef`,
`Verdict.TopE`, …), and none of the `module` importers (`SimBlock`, `Correct`, `Main`, `MainRef`).
So the cutoff works where both sides are `module` files, as restructure.md §"What the module system
can and cannot do here" says; it cannot apply above the twin, because con-ron's arena and bridge
(`vendor/con-ron`) are not `module` files, and 1,174 of ConAgua's 1,363 files are not `module` files
either (anything that imports the twin, directly or not, cannot be one).

What that costs per landing (the landings of the last two days, changed `.lean` files from git;
"today" = their closures; "with cutoff" = the changed modules, their direct importers and, for an L
change, the program literal's 109 modules; module-s / critical path):

| landing | changed | today | with cutoff |
|---|---:|---|---|
| offkit (proofs only) | 17 | 435 modules, 1,386 module-s, 209 s | 56, 181 module-s, 32 s |
| derbv (L + specs) | 31 | 1,088, 4,700, 321 s | 292, 2,594, 233 s |
| memosplit (MemoLib) | 1 | 1,086, 4,635, 334 s | 117, 1,601, 172 s |
| mkmax (ExprMk) | 1 | 1,067, 4,586, 321 s | 116, 1,596, 176 s |
| memoglob | 2 | 1,086, 4,635, 334 s | 121, 1,624, 172 s |
| derbr | 2 | 1,098, 4,651, 334 s | 119, 1,607, 181 s |

The "with cutoff" column assumes the statements did not change; a changed statement rebuilds its
direct importers and stops there.

## 2. Ranked next steps

Costs are in lane hours as the velocity log measures them. For calibration: the inliner was
estimated at 12–18 h and landed in 200 work minutes, bce (25–40 h) in about 2 h, growtop (15–25 h)
in 90 minutes, memosplit (6–12 h) in 36 minutes (`_tmp/velocity.csv`).

| rank | step | axis | evidence | estimated gain | cost | risk | fit |
|---:|---|---|---|---|---|---|---|
| 1 | D40: clear the `replace_fvars` memo when the outermost call returns | speed (c05b), memory | prototype: c05b −48.5 % wall (p < 0.001), RSS 644 → 131 MB, −7 % instructions; `Init`/app-lam unchanged; 634/634 | c05b from 2.1× to ~1.25× con-ron (today), from 1.75× towards ~1.3× quiet | 1–2 h | low | closes a Temporary deviation; mirrors the twin's per-call map |
| 2 | Early cutoff above the twin: con-ron's arena and bridge as `module` files, then ConAgua's twin-facing files | build | a proof-only landing: 435 → ~56 modules, 209 → ~32 s path; an L landing: ~1,090 → ~120 modules, 4.6 k → 1.6 k module-s, 334 → ~175 s | every landing's worktree build and the merge queue's incremental gate | 6–12 h (≈ 300 vendored + 1,174 own files, mostly scripted) | medium: `meta`/`@[expose]` fallout, a vendor patch to carry at twin bumps unless con-ron adopts it upstream | neutral; no proof change |
| 3 | The RefWalk kit (refgen.md §5) as a uniform migration, family by family | proofs | pilot: −17 % per file with its steps, −12 % elaboration work; patch applies to this master unchanged (checked) | −4 to −5 k of the 26.7 k `RefE` lines; one per-call shape | 10–20 h over the families (helpers in parallel) | low per family; two styles until done | uniform structure for twin syncs; guards by `grind` |
| 4 | D37 for memos: re-make a cleared memo at the twin's `clear_fit` size (prototype first) | speed (app-lam) | app-lam: the instantiate memo's growth is 2.07 G (5.0 % of instructions); con-ron's matching table spends 0.18 % in `move_slots` | app-lam −3 to −5 % instructions; ~0 elsewhere | prototype 1 h; proof 2–4 h (`MemoLib` header, `memoRV_clear`) | low | closes a Temporary deviation |
| 5 | Finer whole-program parts (`ASM_PARTS`, `INL_PARTS`, `SKT_PARTS` in `scripts/checker_prog.py`) | build | an L change's path is 154 s, of it `AsmPart3` 63 s, `ProgIPart4` 40 s, `ProgSktPart2` 21 s | −40 to −60 s per L landing's path | 1–2 h | low; each part loads ~3 GB, so more parts in parallel need memory | neutral |
| 6 | Memo library, second round: `KGH` (gframe.md §3) and a fused probe-and-put for the walks' second lookup | speed (`Init`, 16 threads) | `KGH` −1.94 % instructions (gframe, measured); the re-probe before `ilm_put` is 116 M of `ilm_find`'s 238 M calls (≈ −1.5 %, estimated) | ≈ −3.5 % instructions, −1 to −2 % wall | 4–8 h (the frame change touches 39 files) | medium: `MemFrame` "kept or zeroed", the five phase-B swaps | proved once in the library; no deviation |
| 7 | Codegen instruction diet: `fleaf` + `stk` + `dres` (cgproto.md §3) | speed (one thread) | −1.70 / −1.66 / −0.41 % instructions; −1.5 / −1.4 / −1.0 % wall at one thread, none resolved at 16 | ≈ −3.8 % instructions, −1.5 to −2 % wall at one thread | 4–8 h | low; layout noise ±1–2 % in the parse | proved once in the compiler |

Ranks 6 and 7 are below the 2 % wall bar on their own. They are listed because they are the only
generic instruction cuts left and the 16-thread gap is now the instruction ratio (§1.1): together
they would take phase B from 1.13× towards ~1.06× con-ron's instructions. Do them only if 16-thread
parity on `Init` becomes the target.

### 1. D40: clear the `replace_fvars` memo where the twin's map ends

**What.** In `replaceFVars` (`Arena/IndPos.lean`), after `u := call rf_bank_leave(s)`, clear the memo
when `s` is the base generation (`if s == 0 { u := call rf_clear() }`), or let the outermost caller
call `rf_clear`. The twin makes a fresh map per call and drops it at return; the bank emulates the
nesting, the clear frees what the bank leaves behind.

**Why.** §1.4: the memo is 80 % of c05b's resident set, and faulting it in is most of the run's
kernel time and DRAM traffic. The prototype halves c05b's wall time today; c05b is the largest
remaining ratio in OVERVIEW §3.

**Proof.** `memoClearG_spec` exists. `replaceFVars_refines` (`IndPosSpec/ReplaceFVarsGo.lean`)
threads the banked memo's map `M` in `RfInv`/`RxPost`; after the clear it is `∅`, which
`memoRV_clear` gives. Callers that carry `RfInv` to a later call get it from the empty map. The
deviation row D40 moves to Fixed. `checker.s` regenerated.

### 2. Early cutoff above the twin

**What.** Make `vendor/con-ron`'s arena and bridge (303 of 328 files) `module` files (`module`,
`public import`, `@[expose] public section` for definitions the refinements unfold), then convert
ConAgua's non-`module` files the same way (they can then import the twin). Ideally upstream in
con-ron, so no patch is carried across bumps (PLAN.md "Bumping the twin").

**Why.** §1.6: every landing today rebuilds the whole import closure of what it touched, because
non-`module` files depend on every artifact below them. With `module` files throughout, a proof-only
edit stops at the edited module (checked on `SimStore`), and an L change rebuilds the edited module,
its direct importers and the program literal's chain. For the last two days' landings that is 3–9×
fewer module-seconds and half to a sixth of the critical path. It also cuts the CI rebuild, which
lnext2 §1.4 measured at 65 minutes of a 100-minute run.

**Uncertain.** How much of each refinement module's statement mentions exposed twin definitions (a
changed twin definition still rebuilds everything that unfolds it, which is the point); the `meta`
code (`l_model`, `vcgen` recipes) under the module system's phase rules; whether whole-program
modules need `import all`. Pilot first on one family (`Arena/IndT`), measuring the rebuild set of
an edit to `Sum4`.

### 3. The RefWalk kit as a migration

**What.** Land `Arena/RefWalk.lean` (82 lines) from `_tmp/refgen/pilot.patch` and convert the `RefE`
theorems family by family: the walk rules `bindSim`, `bindE`, `guard`, `guardOpt`, `abort0`, one
package per family (`SumAt`), step lemmas only for callees with two or more sites.

**Why.** It is the only measured reduction of the refinement layer (refgen §3: −17 % per file
counted with its steps, Sum4's elaboration work 4.20 → 3.38 s). The user's preference for uniform
per-function proof shapes (one walk, one way to split a callee's outcome) is the stronger reason:
twin syncs touch these theorems, and a walk of `refine` steps against fixed rules is easier to redo
than hand plumbing with long `K.abortN` argument lists.

**Gain and cost.** refgen §5 estimated −15 to −20 % per converted file: −4 to −5 k lines over the
26.7 k `RefE` lines. Converting by family keeps each landing small; the families with the most
`RefE` lines first (`IndT`, `Verdict/IndB*`, the declaration arms).

### 4. D37 for memos (prototype first)

**What.** At a memo's clear, remember a decaying high-water mark of its entries and size the next
epoch's region from it, as con-ron's `ron/hashmap2.rs` `clear_fit` does, instead of restarting at the
default `MN0` slots and growing in place.

**Why.** On app-lam the instantiate memo is fresh in every `inst_list` call and grows inside many of
them: 2.07 G of `ilm_put`'s 4.39 G instructions (§1.3). On `Init` and beta-ladder the growth is
negligible, so the gain is app-lam's (1.45× con-ron in user cycles).

**Prototype.** An edit of `checker.s` (the clear and the fresh-header `n`), the paired bench on
app-lam, beta-ladder and `Init`. Go if app-lam gains ≥ 2 % wall without RSS growth.

### 5. Finer whole-program parts

Raise the part counts in `scripts/checker_prog.py` so that no generated module on the L-change path
takes more than ~25 s (today `AsmPart3` 63 s, `ProgIPart4` 40 s, `ProgSktPart2` 21 s in this build).
The comment there notes ~3 GB per asm part; the memory cap (50 GiB for every agent and build) is the
limit, not the cores. Measure each module alone, as inline.md §4 did, before and after.

### 6 and 7. The remaining instruction cuts (conditional)

See the table. `KGH` is costed in gframe.md §3; the fused probe-and-put replaces `ilm_find` +
`ilm_put(fd, j)` after the recursion by one leaf that probes and writes, in `MemoLib` once for all
memos. cgproto's variants are costed in its §5.

## 3. Re-evaluated, and not worth it now

* **gframe `KGH`** (memo globals keyed by the stamp word): −1.94 % instructions on `Init`. At the
  elasticity of §1.1 (0.48) that is about −0.9 % wall at 16 threads, −1 % at one thread, for a frame
  change in 39 files plus a MemoLib round. Below the bar alone; rank 6 bundles it.
* **Frame traffic** (16.1 % of `Init`'s instructions, plus 5.0 % call arguments from the frame):
  nlregs measured every register scheme for non-leaf functions at ≤ −1.0 % wall (loop promotion),
  some slower. Unchanged by the landings since.
* **Fuel** (`fleaf`: −1.7 % instructions, −1.5 % wall at one thread, nothing at 16 threads),
  **prologue / stack check** (`stk`: −1.66 %, −1.4 %), **result registers** (`dres` −0.41 %, `peep`
  −0.19 %; most of lnext2's 5.8 % were call arguments, cgproto §3.3): each below the bar; rank 7
  bundles the three.
* **The remaining bounds checks** (5.0 %, 10.7 G): most need `count ≤ len` of a table's columns, a
  program invariant, not a local fact (cgproto §3.1). Even removing all of them was −3.5 % wall at
  one thread before bce took a third.
* **Fuel-free models** for functions off any call cycle: lnext §3.3, 326 functions, the strictly
  fuel lines sit in recursive and loop functions. Fuel lines are 15.7 k, unchanged.
* **L-level sugar** (node views, tag `match`, guard and sentinel sugar, memo sugar, block
  primitives): lconstructs.md measured each at ≤ −0.3 k L lines and ≤ −1 k proof lines; the L code is
  18.2 k lines against 303 k proof lines, so L-line savings do not move the totals. `for` with
  `Nat`-indexed models: forloop.md, no-go.
* **Word ↔ `Nat`**: natsurvey.md; `lia` as a default costs ×2–4 elaboration; bounded arrays and `Nat`
  addressing no-go; the offset kit is rolled out.
* **Function names as numbers** (lrecords rank 7): of 5,023 lines that mention a lookup, 1,315 are
  lookup hypotheses only; the rest are uses a numeric name would keep. ≤ 1.3–2 k lines for a change
  to `Prog`'s type.
* **A refinement generator**: refgen.md, no-go (−4 to −6 k for 70–110 h); rank 3 takes its kit.
* **The parse** (`der` in the parser): parked by the user; the 16-thread parse is at parity today
  (§1.1).
* **TLB / packed layout of the small arrays** (parprof §1.3, ≤ 1–3 % of cycles): needs the
  compiler-owned layout; high cost. The huge-page variant over the worker region was measured worse.
* **Claim scheduling, sharing memos across workers**: parprof §1.1 (no imbalance, +0.5 %
  duplication).

## 4. Honest summary

* **Speed.** `Init` is within 4–6 % of con-ron at 16 threads and that gap is the parallel phase's
  instruction ratio (1.13×). No single generic change left saves 2 % of wall time there; the bundles
  of ranks 6–7 would roughly halve the ratio for 8–16 h. The one large ratio, c05b, comes from a
  known deviation, and its fix is the cheapest item here.
* **Proofs.** 303 k lines, 36 % hand-written refinement. Nothing measured would move more than
  1.5 % of them. The RefWalk migration is worth doing for uniformity more than for its −4 to −5 k
  lines.
* **Build.** The cold critical path is no longer the whole-program checks. What costs is the
  incremental rebuild: every landing re-elaborates the whole import closure of what it touched (435
  to 1,100 modules), because nothing above the twin can use the module system's early cutoff.
  Making con-ron's arena and bridge `module` files is the largest build lever left.
