# wallcum: the cumulative wall-time effect of the perf landings of 2026-10-30

Measurement only; no code changed. Question: what do bce, parprof's follow-ups, memosplit, derbv,
derbr and memoglob add up to in wall time? Three binaries, built by `make` from the committed
`checker.s` of three commits (a worktree each):

| tag | commit | state |
|---|---|---|
| `b` | b4747f1d | before bce |
| `f` | ff57e2c3 | after bce, before parprof's follow-ups |
| `m` | 4f70d767 | master: after memosplit, derbv, derbr, memoglob |

The parse-phase binaries `Pb`, `Pf`, `Pm` come from a small script (`_tmp/wallcum/ParseEmit.lean`,
the committed `AsmEmit` with `check_a` cut after the parse, as in cgproto/internspeed's
`CA_PARSEONLY`); with the cut off it reproduces each commit's `checker.s` byte for byte (checked).

## 1. Method

Interleaved paired rounds (`_tmp/bce/wb2.py`: per fixture, the variants back to back in random
order, fixtures in random order; `wstats.py`: median paired change, Wilcoxon p, mean with 95 % CI).
One thread: pinned to CPUs 44,92 (the SMT pair, as bce.md §6), 40 rounds. `--jobs=16`: CPUs 24-39,
100 rounds. The two ran concurrently, with other lanes' work on the machine (no quiet wait, no
`nice`). The parallel-phase span is `_tmp/parprof/ws.py` (perf record, workers = threads first
sampled > 0.5 s in), 30 interleaved rounds of the three binaries, `--jobs=16`, CPUs 24-39.
Instructions: `perf stat -e instructions:u`, one run each (deterministic to the digit for
single-threaded runs).

Load (1-minute average at the start of each run): one thread 4.1-14.9, median 6.1; 16 threads
median 11.6 (range 4.1-14.9 over the same window); span rounds 5.5-12.8, median 9.4.

## 2. Wall time

Change relative to `b` (median of the paired changes; Wilcoxon p; mean with 95 % CI in
brackets). Bold: p < 0.05.

| cell | `b` | `f` vs `b` | `m` vs `b` | `m` vs `f` |
|---|---:|---|---|---|
| `Init`, one thread (n 40) | 18.06 s | **-1.7 %** (p < 0.001; [-2.4, -0.8]) | **-3.5 %** (p < 0.001; [-4.0, -2.6]) | **-2.0 %** (p < 0.001; [-2.3, -1.1]) |
| `Init`, `--jobs=16` (n 100) | 3.62 s | **-1.3 %** (p 0.024; [-2.8, +3.2]) | **-2.1 %** (p < 0.001; [-4.1, +1.9]) | **-0.6 %** (p 0.041; [-4.5, +2.0]) |
| `Init`, `--jobs=16`, parallel-phase span (n 30) | 1.325 s | -2.9 % (p 0.11; [mean -1.1]) | **-3.9 %** (p 0.005; [mean -3.4]) | -0.3 % (p 0.31; [mean -2.3]) |
| parse phase, one thread (n 40) | 2.20 s | -0.8 % (p 0.22; [-1.5, +1.8]) | +0.0 % (p 0.71; [-1.6, +0.9]) | +1.0 % (p 0.11; [-2.3, +1.4]) |
| app-lam, one thread (n 40) | 11.29 s | -0.8 % (p 0.089; [-3.7, +1.7]) | **-2.8 %** (p 0.007; [-5.5, +1.1]) | -1.2 % (p 0.17; [-3.8, +1.4]) |
| c05b, one thread (n 40) | 2.27 s | +0.3 % (p 0.28; [-3.8, +7.4]) | **-3.7 %** (p 0.048; [-9.1, +2.6]) | **-5.1 %** (p 0.002; [-11.0, +1.5]) |

(The `f` vs `b` column is bce plus whatever else landed up to ff57e2c3; `Init` one thread
reproduces bce.md §6's -1.5 %.) Absolute times are higher than bce.md §6's (17.6 s, 3.56 s) because
of the load. Per-round spreads are wide at this load (`Init` at 16 threads +-40 %, c05b +-29 %,
parse +-14 %), so only `Init` one thread resolves 2 %; the 16-thread cell needed all 100 rounds
to reach p < 0.05 for `m` vs `f`, and its intervals still include zero in the mean (the
median, which Wilcoxon tests, is robust to the few loaded rounds).

## 3. Instructions (`perf stat -e instructions:u`)

| cell | `b` | `f` | `m` | `f` vs `b` | `m` vs `b` | `m` vs `f` |
|---|---:|---:|---:|---:|---:|---:|
| `Init`, one thread | 232.502 G | 228.175 G | 215.953 G | -1.86 % | **-7.12 %** | -5.36 % |
| `Init`, `--jobs=16` (all threads) | 234.312 G | 230.021 G | 217.736 G | -1.83 % | -7.08 % | -5.34 % |
| parse-only binary | 18.937 G | 18.688 G | 18.577 G | -1.32 % | -1.90 % | -0.59 % |
| app-lam | 45.702 G | 44.977 G | 42.463 G | -1.59 % | -7.09 % | -5.59 % |
| c05b | 14.147 G | 14.020 G | 12.996 G | -0.90 % | -8.14 % | -7.30 % |

## 4. Reading

* The instruction count fell 7.1 % on `Init` across the day (1.9 % from bce, 5.4 % from the later
  landings, which touch the memo hash, `der_b` and the memo put, i.e. the check phase, not the
  parse: the parse-only count moves 1.9 %).
* Wall time follows at about half: -3.5 % at one thread, -2.1 % at 16 threads, -3.9 % in the
  16-thread parallel span (the span is the better 16-thread number: the main thread's serial prefix
  is the same code in all three). The later landings alone give -2.0 % (one thread, p < 0.001)
  and -0.6 % (16 threads, marginal). As in bce.md §6 and cgproto, wall time moves by less than the
  instruction count: the checker is partly memory-bound, and the removed instructions are cheap
  ones.
* Parse phase: no change in wall time (the code did not change there beyond bce's checks, -1.9 %
  instructions): the parse is bound by memory, not instructions.
* app-lam and c05b improve by about 3-4 % with wide intervals (c05b is the shortest cell and the
  noisiest).
