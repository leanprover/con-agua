# Lane parprof: the parallel phase at 16 threads

The task (lnext2 §2 item 4, part 2): at `--jobs=16` on `Init` the parallel phase took 1.31 s
against con-ron's 1.17 s (lnext2 §1.1). Is that load imbalance across the workers, or per-thread
speed, and in which functions? Then rank remedies.

**Setup.** Master ff57e2c3 (the inliner and bce included), `make`. con-ron: the default binary
`_tmp/ref/con-ron-integrate/target/release/con-ron` (12752ca7). Input `Init`
(`_tmp/fixtures/init/init435.ndjson`, 57,292 pending groups). 16 threads pinned to CPUs 24–39
(16 physical cores, SMT siblings 72–87). Machine load was 40–170 throughout (96 CPUs).

**Method** (scripts in `_tmp/parprof/`):
* `ws.py`: `perf record -T` with a group led by `task-clock` (`{task-clock,cycles,instructions,…}:S`,
  one sample per ms of on-CPU time), summed per thread. The workers are the threads first sampled
  more than 0.5 s after the start.
* The counts are user plus kernel, split by the sample's ip.
* `asmprof_pb.py` + `main_prof.c`: `scripts/asmprof.py` with a harness that dumps the block
  counters after entry 1, so phase B's exact profile is the total minus that dump (`--jobs=2` on one
  CPU, so the non-atomic counters are exact).
* `symprof.py`: con-ron's sampled profile of the workers (`instructions:u`, `cycles`).
* Wall: `_tmp/bce/wb2.py` and `wstats.py`.

## 1. Findings

### 1.1 No load imbalance

The claiming is con-ron's: one `fetch_add` counter, groups in index order, each worker keeps its
state across its claims (`main.c` `worker`; con-ron `crates/con-ron/src/pool.rs`).

* **Per-thread work evens out.** In a run at moderate load, every con-agua worker spans 1.34–1.36 s
  and is on-CPU 1.28–1.36 s; every con-ron worker spans 1.16 s.
* **The workers end together.** Over 21 paired runs, from the first worker's last sample to the
  last's:
  * con-agua: median 14 ms (8–26 ms);
  * con-ron: median 15 ms (9–91 ms).

  That is about 1 % of the phase for both. Start spread: 22 ms against 18 ms.
* **No cost from per-worker memos.** Each worker starts with empty memos, but the worker
  instructions hardly grow with the thread count:

  | | 2 threads | 4 threads | 16 threads |
  |---|---:|---:|---:|
  | con-agua | 203.5 G | 203.8 G | 204.5 G |
  | con-ron | 164.4 G | 164.8 G | 165.3 G |

  That is +0.5 % from 2 to 16 threads in both.

A scheduling change (other claim orders, larger groups first) has nothing to gain.

### 1.2 Kernel time and page faults: not a con-agua disadvantage

Kernel time and page faults of the workers, medians of 21 paired runs at 16 threads (load 45–155):

| | con-agua | con-ron |
|---|---:|---:|
| kernel time, all workers | 0.95 s | 2.89 s |
| page faults | 148 k | 102 k |

In a quieter run, con-agua's workers had 0.20 s of kernel time against con-ron's 0.03 s, about
12 ms per worker or 1 % of the phase.

Where con-agua's faults come from:
* each worker maps its own zero region;
* the first 2 MB of each array slot is on 4 KB pages, as `advise_huge` leaves it (about 87 slots
  per worker, together ~18 MB resident per worker in 4 KB pages, from `/proc/PID/smaps`);
* the slot middles and the frozen buffer (279 MB, 260 MB of it huge) are on huge pages.

**Prototype: huge pages for the whole worker region** (`main_hugew.c`, one `madvise` over the
region). It is worse:
* worker kernel time 4.7–5.5 s against 0.2–0.6 s (2 MB zeroing per touched slot);
* span 2.15–2.22 s against 1.76–1.95 s.

Rejected.

### 1.3 TLB

con-agua's workers make 1.6–1.8× con-ron's page walks for 4 KB pages
(`ls_l1_d_tlb_miss.tlb_reload_4k_l2_miss`):

| run | con-agua | con-ron |
|---|---:|---:|
| 1 | 304 M | 188 M |
| 2 | 131 M | 73 M |

The likely cause is the ~4,600 hot 4 KB pages per worker, the slot starts of §1.2. That is more
than the L2 DTLB holds.

At 20–40 cycles per walk, the difference is roughly 1–3 % of the workers' cycles. The fix would be
a packed layout of the small arrays: compiler-owned layout, the parked array abstraction. That is
not a cheap step.

### 1.4 The gap is per-thread speed: 1.24× instructions, hidden or not by IPC

Worker sums in one run at moderate load, 16 threads:

| | con-agua | con-ron |
|---|---:|---:|
| instructions | 204.4 G | 165.6 G |
| cycles | 85.8 G | 91.2 G (that run) |
| IPC | 2.37 | 2.03 |

con-agua executes **1.24× con-ron's instructions** in phase B (whole run: 1.31×). It makes up for
most of that with a higher IPC, but the IPC advantage depends on the SMT sibling.

**SMT experiment** (`ws.py`, 10 interleaved rounds, ratios con-agua ÷ con-ron, medians):

| 16 threads on | span | worker cycles | IPC con-agua | IPC con-ron |
|---|---:|---:|---:|---:|
| 16 cores, CPUs 24–39 (siblings: other load) | **1.06** | 1.01 | 1.94 | 1.67 |
| 8 cores × 2 SMT threads, CPUs 24–31, 72–79 | **1.18** | 1.13 | 1.41 | 1.32 |

When a core's issue slots are shared, con-agua's extra instructions cost cycles. Its IPC drops
27 % against con-ron's 21 %, and the ratio moves toward the instruction ratio. The machine load
does the same through the siblings 72–87 of CPUs 24–39. Paired span ratios on CPUs 24–39 ranged
from 1.0 to 1.28 between rounds, median 1.10 (21 rounds, load 45–155). The per-worker IPC in one
run ranged from 1.59 to 2.49 for con-agua and from 1.97 to 2.12 for con-ron, at equal spans.
lnext2's 1.12 (load 4–31) lies in this range.

So the parallel phase is slower because of per-thread speed, and only through the instruction
count. The cure is fewer instructions in phase B.

### 1.5 Where phase B's instructions go

Exact profile, phase B only (`asmprof_pb.py`, 203.3 G, 3.59 G calls):

| function | share | calls | instructions per call |
|---|---:|---:|---:|
| `der_b` | 11.1 % | 597 M | 38 |
| `ilm_find` | 6.4 % | 237 M | 55 |
| `mk_app` | 5.3 % | 150 M | 72 |
| `ilg_go` | 4.6 % | 256 M | 37 |
| `ilg_app` | 4.6 % | 103 M | 91 |
| `app_find` | 4.5 % | 159 M | 57 |
| `intern_app` | 4.4 % | 150 M | 59 |
| `ilm_put` | 4.1 % | 116 M | 71 |
| `get_app_spine` | 4.0 % | 25 M | 329 |

By the code generator's categories:
* frame stores 10.5 %, frame loads 6.1 %;
* prologue and epilogue 5.2 %;
* the fuel and stack check 5.2 %;
* result registers 5.1 %;
* bounds checks 3.2 %.

All memo finds and puts together are 36.6 G (18.0 %); `ilm_*` alone is 21.2 G.

**By family, against con-ron** (`fam.py`; con-ron's numbers are sampled `instructions:u`, and Rust
inlining moves cost between families, so read the sums, not single rows):

| family | con-agua | con-ron | difference |
|---|---:|---:|---:|
| `der_b` (inlined at con-ron's call sites) | 22.6 G | — | +22.6 |
| bvar instantiate and its memo | 50.5 G | 32.3 G | +18.2 |
| level-parameter instantiate | 8.3 G | 6.2 G | +2.1 |
| interning (`mk_*`, node tables) | 47.1 G | 30.9 G | +16.2 |
| app spine and arguments | 12.4 G | 19.0 G | −6.6 |
| allocation, copies, drops | 0.7 G | 22.9 G | −22.2 |
| environment lookups | 5.4 G | 3.3 G | +2.1 |
| whnf, defeq, infer, reduction and their caches | 56.3 G | 37.3 G | +19.0 |

The excess is in the hot small functions:
* the derived-word reads;
* the instantiate memo;
* the interning.

Against it, con-ron spends 23 G on malloc, `Vec` copies and drops, which L does not have.

**Three specifics.**

* **`der_b`'s calls by caller:**
  * `ilg_go` 256 M;
  * `mk_app` 136 M;
  * `il_bvar` and `il_go` 67 M each;
  * `lp_go` 31 M;
  * `ab_fvb` 15 M.

  By tag: app 270 M, bvar 162 M, const 67 M, lam 57 M, fvar 13 M, forall 11 M, sort 8 M, proj 5 M.
  The six walk call sites (`ilg_go`, `il_go`, `il_bvar`, `inst_go`, `lift_go`, `bvar_b`) read only
  the first of its three results. The inliner leaves `der_b` a call: lnext2 §1.5 found it too large
  for S = 80. Also, its `return`s carry values that can fail (array reads) and that these callers do
  not read, which the tail conversion refuses (inline.md §1).
* **The instantiate memo hits rarely in phase B.** Of `ilm_find`'s 237 M calls (from `ilg_app` 201 M,
  `ilg_lam` 27 M), 116 M are the second lookup on a miss before the put. The table header never
  matches the epoch (the table is fresh in every call of `inst_list`), so every call recomputes
  `n` from the array length (about 10 instructions). 232 M of 239 M probes end on an empty
  slot; there are 6 M hits. This is the twin's memo (`instantiate_list_go`'s `inst_l_get` /
  `inst_l_set`, the same calls). con-ron's `HashMap2` operations cost about 18 instructions each,
  L's 55 (find) and 71 (put).
* **`ilm_put` runs out of registers.** Its growth block (the rehash) is inline, so the function
  has more locals than the leaf register allocation takes. All five parameters go to the frame
  first, and every one of its eight array accesses carries a bounds check. The common path
  (no growth) is 71 instructions.

## 2. Prototypes (unproved, `_tmp/parprof/proto/`)

Both edit `checker.s` directly.

* **`derfast.py`.** Before each of the 23 `call ca_f_der_b`, an inline fast path for the app and
  bvar arms (all three results, the same tier guard and count check). Any other case takes the
  call.
* **`putfast.py`.** A register-only fast path at `ca_f_ilm_put`: a found slot, or a fresh header
  with no growth. Anything else takes the original body.

`Init`, accept. Instructions with `perf stat -e instructions:u` at `--jobs=4`; phase B from the
worker sums:

| variant | whole run | Δ | phase B (workers) | Δ |
|---|---:|---:|---:|---:|
| master | 229.31 G | | 203.29 G | |
| der fast path | 226.16 G | −1.37 % | 200.23 G | −1.51 % |
| `ilm_put` fast path | 224.78 G | −1.98 % | 198.78 G | −2.22 % |
| both | 221.63 G | −3.35 % | 195.73 G | −3.72 % |

**Both at 16 threads, CPUs 24–39** (12 interleaved rounds, `ws.py`, load 41–131):
* worker cycles: median **−5.4 %**, lower in 10 of 12 rounds;
* span of the parallel phase: median **−5.5 %**.

Whole-run wall time (`wb2.py`, 40 rounds, load 43–166, base 4.97 s instead of the 3.6 s of a quiet
machine): −0.8 %, p 0.92 [−4.7, +5.4]. This is not resolved at that load.

## 3. Ranked remedies

The estimates are for phase B at 16 threads. A twin deviation is needed in none of them: `der_b`
and the memo library are L's own ("con-ron: none").

| rank | remedy | estimated gain | proof cost |
|---:|---|---|---|
| 1 | Memo put split in `MemoLib` | −2.2 % phase-B instructions measured on `ilm_put` alone; −3 to −3.5 % for all memos | 6–12 h |
| 2 | One-result `der_bv` for the six walk sites, small enough for the inliner | −1.5 to −2 % instructions | 4–8 h |
| 3 | Cheaper memo find | −1.7 % (`ilm`) to −2.5 % (all memos); not prototyped | 6–10 h |
| 4 | The codegen leftovers (lnext2 rank 6) | 1–2 % each | 10–25 h each |
| 5 | Packed layout of the small arrays | ≤ 1–3 % of cycles | high; parked |

### 1. Memo put split in `MemoLib`

**What.** The growth and rehash block of `memoPutG` goes into its own function per schema
(`memo_grow`). The put becomes a small leaf that fits the leaf register allocation.

**Gain.** Measured on `ilm_put` alone: −2.2 % of phase-B instructions, −2.0 % of the whole run.
All memo puts in phase B come to about 13 G, so all memos together should give −3 to −3.5 %.
Together with rank 2 the measured effect was −5.4 % worker cycles, −5.5 % span.

**Proof cost.** One generic change: `memoPutG`'s spec is split, and the grow block's proof moves
into the new function's. The new function also has to go into every function list that has a memo
put (`LoopFns`, `LeafFns`, `IndMemoFns`, `CoreErec`, `NoVerdictFns`, `WriteSets`, …). That part is
mechanical but touches many files.

### 2. One-result `der_bv` for the six walk sites

**What.** A leaf `der_bv` that returns only the bvar range, for the six walk sites (`ilg_go`,
`il_go`, `il_bvar`, `inst_go`, `lift_go`, `bvar_b`). Its const, sort and fvar arms read nothing,
so no extra value can fail, and it is small enough for the inliner. If it comes out above
S = 80, raise S and measure (in inline.md §1, S = 160 inlined nothing more than S = 80).

**Gain.** The prototype, which covers the app and bvar arms at all 23 sites, saves 1.5 %.

**Proof cost.** `der_bv` and its spec (`derB_spec`'s pattern); in the six callers' specs the
lemma changes; the `l_model`s regenerate.

**Not this.** The parser's `der` (lnext2 item 4, part 1) is parked and not part of this remedy.

### 3. Cheaper memo find

**What.** In `MemoLib`, the effective `n` and base kept in named globals (lfeat), set at the epoch
bump or growth, instead of being recomputed from the length on every call. The probe step's
bounds checks covered by bce facts.

**Gain.** About −15 instructions per call. That is −1.7 % (`ilm` alone) to −2.5 % (all memos).
Not prototyped.

**Proof cost.** A generic `MemoLib` change.

### 4. The codegen leftovers (lnext2 rank 6)

In phase B:
* frame traffic 16.6 %;
* the fuel check 5.2 %;
* prologue 5.2 %;
* result registers 5.1 %.

They are unchanged by this lane; each item is worth 1–2 %.

### 5. Packed layout of the small arrays (TLB, §1.3)

Estimated at ≤ 1–3 % of cycles. Compiler-owned layout: a high cost, parked.

**Not worth doing:**
* claim scheduling (no imbalance, §1.1);
* huge pages over the worker region (measured worse, §1.2);
* page-fault work (con-ron pays more, §1.2);
* sharing memos across workers (+0.5 % duplication).

**What reaching parity takes.** On a quiet machine with idle siblings, phase B is already at
1.0–1.06× con-ron's cycles. Under SMT contention it is 1.13–1.18×, and only fewer instructions
help there. Ranks 1–3 together are about −7 to −8 % of phase-B instructions, against the 24 %
excess. The rest is spread over the code generator's overheads (rank 4) and the interning
functions.
