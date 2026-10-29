# Lane parsespeed: where the parse phase's wall time goes, and inlining with non-leaf registers

Question: can the parse phase (`front_run`: `front_line` = `skip_ws`, `line_rec`, the `apply_*`
steps, and the interning they do) become faster than con-ron's, by generic compiler work rather than
by hand-tuned L? Step 1 measures where wall time goes, for us and for con-ron. Step 2 tries the
combination that the journals left untested: L→L inlining (lnext §3.1) together with registers in
non-leaf functions (nlregs: loop promotion `promoc`, IPRA).

Base: master 72557e98. Nothing landed but this journal. Unproved prototype, assembly, binaries,
profiles and bench data: `_tmp/parsespeed/` (`proto/Combo.lean`, `s/`, `bin/`, `prof/`, `wb*.json`,
`phase1.json`, `phasebench.py`, `wb.py`, `wstats.py`).

**Answer in short.**
* **Step 1.** On `Init` the parse phase is 9–11 % of a one-thread run but **half of a 16-thread run**
  (it is sequential), for us and for con-ron alike. Ours takes **1.23× con-ron's wall in the parse
  phase** (2.25 s against 1.80 s, one thread; 2.23 s against 1.70 s at 16 threads, both p < 0.03).
  The gap is not mainly the scanner: by cycle samples the scanner is ≈ 1.1× con-ron's, the
  **interning (hash-consing `app` nodes, `der_b`) ≈ 1.9×**. The interning code runs at IPC 0.3–1.0
  and is memory-bound (one load in `app_find` takes 78 % of its samples). The whole run is
  memory-bound in the same places (`app_find` 18 %, `der_b` 11 % of all cycles), not front-end
  bound; con-ron is the more front-end bound of the two.
* **Step 2.** Inlining (S = 80, 2 rounds) is the only part that reliably helps: **−4.6 % wall on the
  parse phase** (median of 55 paired rounds, Wilcoxon p = 0.001), −1.7 % instructions on the whole
  run. Adding loop promotion and IPRA does not add anything measurable (−4.2 %, p = 0.019, on the
  parse phase; on the whole run −1.4 to −2.5 %, none significant in 35 paired rounds). On the whole of `Init`, at 16
  threads and on the long fixtures, no variant reaches 2 % significantly.
* **Recommendation.** No implementation lane for promotion or IPRA. Inlining clears the 2 % bar only
  on the parse phase, which is ≈ 0.1 s of a 2.2 s phase; the gap to con-ron there (≈ 0.45 s) is
  mostly interning, i.e. data layout and the hash-cons path, which are candidates for an analysis
  lane (§5), not compiler work. A proof plan for the inliner is sketched in §6 for when it is wanted
  together with a later register change.

## 1. Method

**Wall time** is the measure; instructions (`perf stat -e instructions:u`, exact and deterministic)
only explain. The machine was loaded throughout (other lanes' Lean builds, 1-minute load 10–130,
median 20–40), so every bench:
* runs each round's (fixture, binary) cells in a fresh random order (`wb.py`), pinned with `taskset`
  to both SMT threads of one physical core (45/93, 47/95, 43/91) or to 16 cores (24–39) for
  `--jobs=16`; no run is discarded for load;
* compares paired by round: per round the ratio variant/base, then the **median paired ratio** with
  an exact two-sided **Wilcoxon signed-rank test**, and the 95 % t-interval of the mean log ratio
  (`wstats.py`, from `_tmp/nlregs/wallstats.py`). The medians are robust against the +50 % outliers
  that load spikes cause; the t-intervals are not, and are wide.

**The parse phase.** Both checkers parse the whole input before checking (`check_a`: `front_run`,
then `prepare_prelude` …; con-ron's `runPipelineHead`). Two measurements:
* for both, `perf record -T -F 997 -e cycles:u` and the end of the last 50 ms window in which at
  least 10 % of the samples are in scanner symbols (ours: `next_member`, `sub_rec`, `line_rec`,
  `skip_ws`, `key_*`, `value_at`, `read_nat`, `skip_digits`, `apply_*`; con-ron:
  `frontend::*`, `scan_fast::*`) (`phasebench.py`); the boundary is sharp in both timelines;
* for ours also a **parse-only binary** (`CA_PARSEONLY=1`: `Combo.lean` replaces `check_a`'s call of
  `prepare_prelude` by `return 1`; exit 3, `ok 1`), timed like any binary, and profiled exactly
  with `scripts/asmprof.py`.

## 2. Step 1: where wall time goes

### 2.1 Us against con-ron, whole run and parse phase

`Init` (`init435.ndjson`), 18 interleaved rounds of the four runs (ours/con-ron × 1/16 threads),
`phase1.json`:

| | ours | con-ron | ratio (median paired) | Wilcoxon p |
|---|---:|---:|---:|---:|
| 1 thread, whole run | 24.85 s | 19.67 s | 1.26 | < 0.001 |
| 1 thread, parse phase | 2.25 s | 1.80 s | 1.23 | 0.021 |
| 1 thread, after the parse | 22.60 s | 17.79 s | 1.26 | < 0.001 |
| 16 threads, whole run | 4.27 s | 3.46 s | 1.19 | < 0.001 |
| 16 threads, parse phase | 2.23 s | 1.70 s | 1.24 | < 0.001 |
| 16 threads, after the parse | 2.06 s | 1.78 s | 1.11 | < 0.001 |
| parse share, 1 thread | 9.1 % | 9.2 % | | |
| parse share, 16 threads | 52 % | 49 % | | |

The one-thread ratio, 1.26, is well above OVERVIEW §3's 1.06 (a quiet machine): under this load
our run suffers more than con-ron's (see the memory-bound profile below). The ratios are the same
for the parse phase and for the rest, so **neither phase is special in wall time on one thread**.
At 16 threads **the parse phase is half the run, for both**, and it is where most of our 16-thread
gap is (0.53 of 0.81 s).

Exact instructions: ours 242.98 G for the whole run, 23.32 G in the parse-only binary; con-ron
184.5 G, ≈ 15.5 G up to its parse boundary (`perf record -e instructions:u -c 10M`, ±0.5 G). So the
parse phase is 1.50× con-ron's instructions but only 1.23× its wall.

### 2.2 Top-down (`perf stat -M PipelineL1/PipelineL2`, AMD Zen 5, one thread, whole `Init`)

| | ours | con-ron |
|---|---:|---:|
| instructions | 243 G | 185 G |
| cycles (this run; varies 115–142 G for ours under load) | 115–142 G | 87–115 G |
| retiring | 19 % | 19 % |
| front-end bound | 35–37 % | 48 % |
| back-end bound | 35 % | 17–22 % |
| of which waiting for a load (`ex_no_retire.load_not_complete` / `not_complete`) | 98 % | 96 % |
| bad speculation | 4 % | 10 % |
| L1D loads / misses | 118 G / 3.0 G | 97 G / 1.8 G |
| fills from DRAM | 161 M | 144 M |
| fills from the local L3 | 208 M | 393 M |
| branch misses | 0.33 G | 0.65 G |

Ours is **back-end bound on loads**; con-ron is front-end bound and mispredicts twice as often. Both
pull about the same number of lines from DRAM. Per 250 ms interval (`perf stat -I 250`), the parse
phase looks the same: ours IPC ≈ 2.1, back-end 0.35–0.45, front-end 0.3–0.4; con-ron IPC ≈ 1.9,
back-end 0.15, front-end 0.6.

**Where the stalls are** (cycle samples, whole run): `app_find` 17.7 % of all cycles, with **78 % of
its samples on the instruction after the slot load** (`mov (%rbx,%r11,8),%rbx` — a DRAM miss on the
hash table), `der_b` 11.1 % (a load of a child's `APP_DER` word), `ilm_find` 5.1 %, `app_count`
3.2 %. con-ron's top functions are the same kind: `EStore::intern_app` 15–19 %, `instantiate_list_go`
10–12 %, `HashMap2<AppNode>` 7–10 %. **The run is memory-bound in the hash-cons tables, not
bound by the scanner, by instruction count or by the front end.**

### 2.3 Inside the parse phase

Cycles and instructions per function in the parse-only binary (`perf record -c 2M` of each event,
`asmprof.py` for exact counts):

| group | cycles | instructions | IPC |
|---|---:|---:|---:|
| scanner (`next_member`, `line_rec`, `sub_rec`, `read_nat`, `key_end`, `key_at*`, `skip_digits`, `skip_ws`, `value_at`, `num_end`, `slot_nat`, `sub_val`, `front_line`) | 50 % | 15.5 G | 2.1 |
| interning (`app_push`, `app_find`, `der_b`, `mk_app`, `expr_put`, `intern_app`, `lam_*`, `esp_find`, `apply_expr`) | 39 % | 5.9 G | 1.0 |
| ↳ `der_b` | 7.9 % | 0.34 G | 0.28 |
| ↳ `mk_app` | 4.0 % | 0.22 G | 0.37 |
| ↳ `app_push` | 10.9 % | 1.22 G | 0.75 |

con-ron's parse phase (cycle samples): scanner (`scan_line_loop`, `next_member`, `key_at`,
`scan_line_fwd`, `apply_line`, …) ≈ 60 %, interning (`intern_app`, `HashMap2<AppNode>`,
`intern_lam`, `intern_forall_e`, …) ≈ 28 %.

In seconds, at the medians of §2.1: **scanner 1.1 s against 1.1 s (≈ 1.1×); interning 0.9 s
against 0.5 s (≈ 1.9×)**. The parse-phase gap is mostly in the interning, which our code runs at
IPC ≈ 1: the same misses as con-ron's plus a longer path around them (`app_push` 302 instructions
per call including the table's growth, `mk_app` 120, `der_b` 36 per child, `intern_app` 58).

Two scanner details from the exact profile (parse-only, `Init`):
* `read_nat` costs **130 instructions per number** (20.1 M calls, 2.6 G), and the digits are
  still read twice (`skip_digits` 64 per call in the walk, then `read_nat`).
* `next_member` (41 M calls, 64 instructions) stays a non-leaf function under every inlining
  threshold: its callee `key_at` dispatches to the six `key_at_g*` decision trees, whose static size
  (≈ 900 nodes inlined into `key_at`) is beyond any sensible threshold. So the scanner's hottest
  loop never gets leaf registers (§4.2).

## 3. Step 2: the variants

`proto/Combo.lean` = lnext's `Inline.lean` (L→L inlining of leaves of at most S nodes, R rounds)
followed by nlregs' `NL.lean` code generator (loop promotion, IPRA), on the inlined program:
`lake env lean --run Combo.lean OUT.s S R K MINUSE LEAFMODE STUBS MODE CYCMIN PROMO CALLS`.
`0 1 0 2 old none none 0 0` gives a `checker.s` byte-identical to master's.

One fix was needed to combine promotion with IPRA: `NL.lean` did not spill promoted registers around
calls in IPRA mode, and its IPRA table did not count the registers a promoted loop writes. In
`Combo.lean`, under IPRA a loop promotes only into registers that its function's callees clobber
anyway (`pfree`, so the function's own clobber set does not grow), and a call in a promoted loop
spills exactly the promoted registers in the callee's transitive clobber set (`clob`).

| variant | arguments | what |
|---|---|---|
| `c0` (base) | `0 1 0 2 old none none 0 0` | master |
| `inl20` | `20 1 …` | inline leaves ≤ 20 nodes, 1 round (50 leaves) |
| `inl80` | `80 2 …` | ≤ 80, 2 rounds (232 + 261 leaves) |
| `inl160` | `160 2 …` | ≤ 160, 2 rounds (298 + 355) |
| `promoc` | `0 1 0 2 old none none 0 3 calls` | nlregs' loop promotion with spills |
| `inl80promoc`, `inl160promoc` | `80 2 0 2 old none none 0 3 calls` | inlining, then promotion |
| `inl80promocipra` | `80 2 3 2 mix stubs ipra 0 3 calls` | inlining, promotion, IPRA (73 non-leaf functions get registers, against 147 without inlining) |

**Verdicts** (`diff-e2e.py --refs --parallel 8`, 634 fixtures): every variant (`inl20`, `inl40`,
`inl80`, `inl160`, `promoc`, `inl80promoc`, `inl160promoc`, `inl80ipra`, `inl80promocipra`) 634
agree, 0 UNSOUND/INCOMPLETE/CRASH/TIMEOUT/REFDIFF; `inl80promoc` and `inl80promocipra` also with
`--jobs 4`: 634 agree.

### 3.1 Instructions (exact, `Init`)

| variant | whole run | Δ | parse-only binary | Δ |
|---|---:|---:|---:|---:|
| `c0` | 242.98 G | | 23.32 G | |
| `inl20` | 239.81 G | −1.3 % | 22.45 G | −3.7 % |
| `inl40` | 239.74 G | −1.3 % | | |
| `inl80` | 238.90 G | −1.7 % | 22.41 G | −3.9 % |
| `inl160` | 237.78 G | −2.1 % | 22.41 G | −3.9 % |
| `promoc` | 245.01 G | +0.8 % | 24.36 G | +4.5 % |
| `inl80promoc` | 240.52 G | −1.0 % | 23.02 G | −1.3 % |
| `inl160promoc` | 239.41 G | −1.5 % | | |
| `ipra` (no inlining) | 242.21 G | −0.3 % | | |
| `inl80ipra` | 238.60 G | −1.8 % | | |
| `inl80promocipra` | 240.01 G | −1.2 % | 22.75 G | −2.4 % |
| con-ron | 184.54 G | | ≈ 15.5 G | |

In the parse phase inlining folds `skip_ws`, `key_end`, `value_at`, `skip_digits`, `num_end` into
`next_member` (64 → 141 instructions per call, 2.6 → 5.8 G, but 0.9 G fewer in total); `read_nat`
(130 per call) and `key_at` stay calls. Promotion adds its spills in `line_rec`/`sub_rec`
(+0.4 G) and wins nothing back in `next_member` (5.78 → 5.74 G): its loop runs 1–3 iterations per
call and calls `key_at` in each.

### 3.2 Wall time

**Parse phase** (parse-only binaries, `Init`, cores 47/95; 15 rounds in bench B plus 40 in bench D,
pooled, `wbBD.json`; load 12–131, median 27–39):

| variant | median paired Δ | Wilcoxon p | 95 % CI of mean |
|---|---:|---:|---:|
| `c0` | 2.22 s | | |
| `inl20` | −2.3 % | 0.117 | [−6.9, +5.7] |
| `inl80` | **−4.6 %** | **0.001** | [−7.9, +3.6] |
| `inl160` | −3.8 % | 0.133 | [−7.2, +5.2] |
| `promoc` | −0.1 % | 0.858 | [−5.2, +5.6] |
| `inl80promoc` | −5.3 % | 0.061 | [−5.8, +9.2] |
| `inl80promocipra` | **−4.2 %** | **0.019** | [−5.6, +4.4] |

(Bench D alone, 40 rounds: `inl80` −4.5 %, p = 0.005; `inl80promocipra` −4.3 %, p = 0.034.)

**Whole `Init`, one thread** (cores 45/93; bench A, 15 rounds of all eight binaries, and bench A2,
20 rounds of four, pooled where both have the binary, `wbAA.json`):

| variant | pooled (35 rounds): median paired Δ | Wilcoxon p | 95 % CI of mean | A only (15 rounds) |
|---|---:|---:|---:|---:|
| `c0` | 23.10 s | | | 24.69 s |
| `inl20` | | | | −1.6 % (p 0.303) |
| `inl80` | −1.4 % | 0.461 | [−11.5, +4.4] | −2.3 % (p 0.277) |
| `inl160` | | | | −2.1 % (p 0.679) |
| `promoc` | −1.7 % | 0.565 | [−7.7, +5.7] | +1.0 % (p 0.847) |
| `inl80promoc` | | | | −1.2 % (p 0.804) |
| `inl160promoc` | | | | +1.1 % (p 0.720) |
| `inl80promocipra` | −2.5 % | 0.131 | [−10.3, +4.1] | −2.5 % (p 0.303) |

Load 5–116 (median 21). Bench A2 alone (20 rounds, load median 18): `inl80` −1.0 % (p 0.956),
`promoc` −2.0 % (p 0.123), `inl80promocipra` −2.2 % (p 0.312). Every variant is within −2.5 % to
+1.1 %, none significant; the expected effect from the instruction counts (≤ 2 %) is below what
35 rounds resolve at this load.

**`Init` at 16 threads** (cores 24–39; bench C, 20 rounds, and C2, 30 rounds, pooled for the three
binaries both have, `wbCC.json`; load 14–100):

| variant | median paired Δ | Wilcoxon p | 95 % CI of mean |
|---|---:|---:|---:|
| `c0` | 4.08 s | | |
| `inl80` | −2.3 % | 0.261 | [−5.8, +6.7] |
| `inl80promocipra` | +1.2 % | 0.553 | [−7.2, +2.9] |
| `inl160` (C only, 20 rounds) | −2.8 % | 0.015 | [−7.5, +3.6] |
| `promoc` (C only) | −1.3 % | 0.133 | [−8.9, +3.2] |
| `inl80promoc` (C only) | −0.3 % | 1.000 | [−6.9, +8.2] |

`inl80promocipra` was −2.2 % (p 0.076) in C and +3.2 % (p 0.033) in C2: at 16 threads on a loaded
machine, single benches of 20–30 rounds disagree in sign; only the pooled numbers are reported.

**Long fixtures** (bench B, cores 47/95, 15 rounds; median paired Δ against `c0`, **bold** = p <
0.05):

| fixture | `c0` | `inl80` | `inl160` | `promoc` | `inl80promoc` | `inl80promocipra` |
|---|---:|---:|---:|---:|---:|---:|
| `app-lam` | 10.16 s | +0.2 % | +2.3 % | +1.6 % | +0.6 % | +0.1 % |
| `beta-ladder` | 2.73 s | −0.4 % | −1.2 % | −1.1 % | +0.2 % | +2.3 % |
| `let-ladder` | 1.12 s | +0.2 % | −0.7 % | +0.1 % | −4.1 % | −1.0 % |
| `complete_c04a_restart_70` | 2.47 s | +4.4 % | +5.1 % | **+7.9 %** | +2.5 % | +2.1 % |
| `complete_c05b_nest30_pi1000` | 1.49 s | −3.2 % | −0.9 % | −3.4 % | −1.8 % | +1.0 % |
| `long_line_5mib` | 0.03 s | +1.6 % | +3.3 % | **+2.9 %** | −0.1 % | +2.1 % |

Nothing on the long fixtures is a gain; the two significant cells are losses of `promoc`
(c04a: +7.9 %, p = 0.048, one of 30 tests at 5 %).

## 4. Verdict

### 4.1 The combination

* **Inlining is the useful half.** On the parse phase it is −4.6 % wall (p = 0.001), consistent
  with its −3.9 % instructions there; on the whole run it is −1.7 % instructions and about −2 % wall,
  which this load cannot separate from zero.
* **Promotion and IPRA add nothing on top.** `inl80promocipra` is −4.2 % on the parse phase, no
  better than `inl80` alone; `promoc` alone is +0.8 % instructions and ±0 wall here (nlregs §7
  measured −1.0 % on `Init`, p = 0.008, in a quieter bench: an effect of that size is below this
  bench's resolution). The hypothesis of nlregs §5 — inlined code in non-leaf callers makes
  registers there worth more — does not hold for the parser: the inlined bodies land in
  `next_member`, `line_rec`, `sub_rec`, whose loops run 1–3 times per call and contain a call
  (`key_at`, `read_nat`, `next_member`), so promotion only adds spills; and inlining halves the
  functions IPRA can give a register (147 → 73), because the inlined bodies' register uses now count
  against their callers.
* **No variant clears 2 % wall significantly on whole `Init` (1 or 16 threads) or on a long fixture.**
  The 2 % bar is met only on the parse phase, by inlining.

### 4.2 What would move the parse phase

Against con-ron's parse phase (§2.3), the remaining gap is ≈ 0.45 s, of which ≈ 0.4 s is
interning. In order of expected effect:
1. **The hash-cons path (data layout / L code, not compiler).** `der_b` runs at IPC 0.28 and
   `mk_app` at 0.37: for each new `app` node, `mk_app` re-reads the node count, calls `der_b` for each
   child (which re-derives the child's tier, index and bounds and loads its `APP_DER` word), and
   `app_push` costs 302 instructions per call including growth. Candidates, to be measured before any
   prototype: keep a node's derived word next to its record (one line per child instead of two, as
   con-ron's `rows: Vec<(A, D)>`), or pass the children's derived words from the parser, which has
   just built (and so has in cache) most children; size the persistent `app` table from the input
   length to avoid rehashing during the parse. Rehash growth is an OS-free change; no `madvise`.
2. **Leafify the scanner's hot loop.** `next_member` would become a leaf if `key_at` were a leaf it
   could absorb. Generic options: an inliner rule "inline a leaf into a caller if that makes the
   caller a leaf and the caller is in a loop nest" with a larger size budget for that case only; or
   **partial inlining**: inline `key_at`'s dispatch and leave the `key_at_g*` trees as calls — which
   keeps `next_member` non-leaf, so it only helps together with loop promotion of `next_member`'s
   own loop, which this prototype shows is not enough alone. The scanfast leaf/non-leaf gap (15 %)
   is the size of the prize on the scanner part (≈ 0.15 s).
3. **`read_nat`** (130 instructions per 6-digit number, after `skip_digits` has walked the digits):
   a single pass that validates and accumulates, as con-ron's `read_nat_at`. That is L code in the
   scanner (lane scanfast-p3's single pass did this for the structure but not for the digits).

None of these is a compiler change; the compiler changes measured here are worth ≈ 0.1 s of the
parse phase.

## 5. Recommendation

* **No implementation lane** for loop promotion or IPRA, alone or combined with inlining (§4.1).
* **Inlining** is the one compiler change with a significant parse-phase gain (−4.6 % of 2.2 s) and
  −1.7 % instructions overall; on its own it does not reach 2 % on a whole run. It is worth landing
  only together with something that makes the inlined code cheaper (leaf registers for
  `next_member`, §4.2 item 2), or as the first step of a general optimisation pipeline. Its proof
  plan is in §6.
* **Next analysis lane, if the parse phase stays the target:** the interning path of §4.2 item 1
  (`mk_app`/`der_b`/`app_push` against con-ron's `intern_app`/`der_of_app`/`Tbl::push`), with a
  wall-time prototype in L first. It is where 0.4 s of the 0.45 s gap is, and at 16 threads the parse
  phase is half of the run.

## 6. Proof plan for the inliner (for when it is wanted)

The inliner is an L→L transformation, so it needs no change to the code generator or its
simulation proofs. Correctness is a theorem `inline_sound`: for the inlined program `p'`, every run
of `invoke p' f args` with fuel n is a run of `invoke p f args` with the same result and memory
(`p'` needs no more fuel, as lnext §3.1 argues: the wrapper loop charges one unit where the call did).
* `Inline.lean` into `ConAgua/Compiler/` (~250 lines: `shE/shS/conv/inlineCall/inlS` as total
  functions over the statement syntax).
* **Shift lemmas** (~300): executing `shS o xs exit s` on a state whose locals `o..o+nl` hold the
  callee's frame simulates `s` on that frame; `conv` (tail form) and the `while true {…; brk}` wrapper
  each against the call rule of `exec` (`Stmt.call`: fresh frame, `needZero` locals zeroed,
  results assigned, `0` for missing ones).
* **Program-level theorem** (~200): by induction on fuel over `exec`, every call to an inlined leaf
  is replaced by its simulation; non-inlined calls unchanged. `needZero` and `nlocals` bookkeeping.
* **Wiring** (~100): `checkerFile_eq`/`asm_lit` compile `inline checkerProg` instead of
  `checkerProg`; the end-to-end theorem composes `inline_sound` with the compiler's correctness;
  the kernel evaluates the inliner once (a 3-second interpreted run here; to be watched in
  `decide`/`asm_lit`).

Total about 850 lines, 12–18 agent-hours, in `ConAgua/Compiler/` only; the per-function models and
refinements are unchanged (they are about `checkerProg`). Risk: the kernel evaluation of the inliner
in `asm_lit`, and the shift lemmas' interaction with `scan8`/`copy*` (the statements with implicit
locals).
