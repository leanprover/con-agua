# Lane `parmode`: parallel checking with threads over a frozen buffer (journal)

Branch `parmode`, worktree `_tmp/wt/parmode`. Goal: `harness/main.c --jobs=N FILE PINS` checks
the pending groups (phase B) on N threads that share one read-only copy of the persistent tier,
per the user's design; keep `ca_start` (sequential) and its theorems unchanged. Background: lane
`parallel` (branch `parallel`, 5b065c31; fork design, rejected), lanes tierarr/tiercost/tierswitch
(tiered arrays, landed), tierpool (the pool tiered by the scratch flag, not landed), memlay
(hash-table internals, not landed).

## Phase 1: design and unproved prototype (2026-10-25)

### The twin

con-ron's `--jobs` (`crates/con-ron/src/pool.rs`, `arena/checker.rs`): after phase A,
`freeze_tier` MOVES the four persistent tables into one `PersTier` that every worker borrows
read-only; each of the `n` scoped threads builds ONE `worker_state(pins)` (an empty store, frozen
so every append is a scratch append, fresh memos and caches, a copy of the pins) and threads it
through the pending records it claims (`fetch_add` on one counter), `check_pending` each. The
twin side is `PooledAccepts` (`ConRon/Arena/Pooled.lean`): a family of record lists covering every
pending record, each accepted by `checkPendingList` from the phase-A state's worker. The L design
below is that shape: one region per thread, initialised on its first call and threaded through
the groups the thread claims.

### What phase B touches (static, the call closure of `check_pending`)

`_tmp/parmode/ws.lean` (580 functions in phase B's closure). Phase B reads/writes:

* **only reads**: `PINS` (128), `EIXA/EIXS/EIXN` (132–134), `EREC` (136), `PEND` (137); no byte
  array (the input is not read after phase A); no global (master has none yet);
* **tier 0 of every store** (records, KSTP slot tables, the DER and hash/level columns): read; the
  stores' `st64t`s name both tiers statically, but with the scratch flag set every push goes to
  tier 1 (a write to tier 0 in phase B would be a bug: route A turns it into a crash, never an
  accept);
* **read and written**: `CTL`, `POOL` (until tierpool), the tier-1 arrays, the memos and caches
  (`BMEMO`, 47–54, 96–106), the walk stacks and scratch heaps (144, 145, 151–155, 192, 200).

Everything else (the front's arrays, `DECL`, `ECON`, the ROM scratch, …) is untouched by phase B.

### The design

**Entry 1 (`ca_start_a`, `check_a`)**: `MODE := 1` (stub), then exactly the sequential stages and
phase A (`install_fold_go`), then `par_compact(vis)`, which writes the **frozen buffer** into the
word array `OUT` (240) and returns; `check_a` returns `2^63 + k` (`k` = `CTL[130]`, the pending
groups). Buffer layout (words): header (`HDRF`): `0` magic, `1` total length, `2` `k`, `3` the
final view, `4` the number of frozen arrays, `(off, len)` of entry `i` at `8 + 2i`; then each
frozen array's image, back to back:

| frozen array | image |
|---|---|
| `CTLF` (242) | `CTL[0‥256)` (seed: copied into the worker's `CTL`) |
| `POOLF` (243) | `POOL[0‥CTL[0])` (seed, until tierpool lands; then `POOL⟨0⟩` is frozen in place) |
| store records `R` | `R[0‥count₀ · w)` |
| store slot tables `S` | the live tier-0 table moved to offset 0: `[n − SN0, 0, table…]`, `2 + 2n` words |
| columns (DER, HP/LP) | `C[0‥count₀)` |
| `PINS` | 71 words |
| `EIXA/S/N` | `2 · count₀` of the anonymous/str/num name stores (with the tiered index, below) |
| `EREC` | `[0‥CTL[129])` |
| `PEND` | `[0‥3 · CTL[130])` |

The extents are the stores' own (`count₀ · w`, KSTP's `2 + 2n`), so in the real version each
image comes from a **store-library function** (`ConsLib`: a generated `X_freeze(o)` per schema
that writes tier 0's records, its slot table in canonical form and its column at `OUT[o‥]` and
returns the length), not from layout hard-coded in the compactor: memlay's packed records,
one-word slots and grow-in-place change only the library's generator (with grow-in-place the
table is already at offset 0 and the move is a prefix copy). Every copy is one `copy!`.

**The harness** (trusted; `harness/main.c`, `run_jobs`): after entry 1 it keeps the buffer
where entry 1 wrote it and unmaps the rest of the region around it (no second copy at the peak;
`OUT` starts at a slot boundary), frees the two input buffers (phase B reads no byte array),
`mprotect`s the buffer read-only, starts `N` threads; each maps its own zero region
(`ca_worker_size`) and loops: `j := fetch_add(next)`; `ca_check_b(buf, len, j, region, size)`;
stop at the first non-accept. Accept iff every call accepted. A write to the buffer faults and
kills the process: never an accept (**route A**, the trusted assumption: "a call of `ca_check_b`
that returns did not write the buffer").

**Entry 2 (`ca_check_b(buf, len, j, region, region_len)`)**, a stub then `check_b`:
* the table in slot 0 of the region, the L stack in slot 1, and one slot per **owned** array
  (the arrays phase B touches that are not frozen: 81 ids, `ca_worker_size` = 83 slots = 2.85 TB
  of `MAP_NORESERVE` address space; 16 workers fit in 128 TB with room to spare; giving every id
  a slot, as `ca_start` does, would need 13.7 TB per worker);
* each frozen id's descriptor is `(buf + 8 · off_i, len_i)`, loaded from the header (no copy);
* every other id (and both byte arrays) gets `(0, 0)`: any access is out of bounds, an error;
* the ROM words as in `ca_start`, `PJ := j`, `MODE := 2`, `ca_enter`.

`check_b`: on the region's first call (global `INIT = 0`) copy `CTLF` → `CTL` and `POOLF` →
`POOL` and set `INIT`; then `check_pending(PJ, view)`. Later calls on the same region continue on
the state the previous call left (the worker's state, threaded as in con-ron). The tier-1 arrays,
memos and caches start as the region's zeros, which the library already reads as empty (KSTP:
an all-zero slot array is a table of `SN0` free slots; memos: stamp `0` is never live).

**The env index, tiered (a prerequisite, small).** `EIXA/S/N` hold the row of name node `i` of
tier `t` at word `4i + 2t` (interleaved, like D35 before tierswitch). Phase B looks up scratch
names too (`env_row_get` on a tier-1 handle reads row `4i + 2`, always empty), so a truncated
tier-0 image would make those reads out of bounds. With the index tiered like the stores
(`EIXA⟨t⟩[2i]`, `env_row_get`/`env_row_set` only, 13 files on the proof side, all through
`rowIx`/`rowSet` in `Arena/Env.lean`), tier 1 of the index is the worker's own zero array.

**The pool.** Until tierpool lands the pool is a seed (each worker copies the whole tier-0 pool,
13.6 MB on Init, once). With tierpool (tier = scratch flag, tag bit 40): `POOL⟨0⟩[0‥top₀)` is frozen
in place, the worker allocates in `POOL⟨1⟩` (its own), and `PTOP0` joins the seed (copied into the
worker's global). The compaction gets the pool image from the pool library (`Arena/Pool.lean`).

### Prototype

`ConAgua/Proto/ParMode.lean` (not in the lake globs; `scripts/lake env lean --run
ConAgua/Proto/ParMode.lean OUT.s`, ~10 s): `checkerProg` with `check` (MODE dispatch), `check_a`,
`check_b`, `par_compact` and the tiered `env_row_get`/`env_row_set` spliced in, compiled, and the
two stubs printed as assembler text in front of `ca_start`; the owned-array list is computed from
the program (the closure of `check_b`). The proved program is untouched. Binaries
`_tmp/parmode/par2.{s,bin}` (`cc -O2 -pthread harness/main.c par2.s`).

Size of the buffer on Init (57 292 pending groups): 65.4 M words = 523 MB. The first version
copied each slot array's whole prefix `2 + o + 2n` (KSTP's ping-pong leaves the old tables below
the live one): 137.8 M words, of which `ASLOT` alone 100.7 M; moving the live table to offset 0
halved the buffer. Largest images now: `ASLOT` 33.6 M words (2^24 slots for 5.2 M app nodes;
memlay's load 3/4 and one-word slots would cut it to 8.4 M), `AREC` 10.4 M, `LASLOT` 6.3 M, `EREC`
5.2 M, `FASLOT` 4.2 M, `POOL` 1.7 M.

Phase A + compaction alone (`CA_PAR_ONLYA=1`): 4.0 s wall on Init.

### Measurements (2026-10-25, `_tmp/parmode/bench1.{json,log}`, `bench_par.py`; load 25–45 on 96 cores; 2 interleaved rounds, medians; RSS = peak `ru_maxrss`, PSS = peak sampled `smaps_rollup`; one process for every system)

Init (`init435`, 57 292 pending groups):

| system | wall | CPU | peak RSS | peak PSS |
|---|---:|---:|---:|---:|
| L sequential (`ca_start`) | 36.98 s | 36.77 s | 1446 MB | 1445 MB |
| L `--jobs=1` | 30.29 | 30.15 | 1762 | 1630 |
| L `--jobs=2` | 17.39 | 30.54 | 1762 | 1757 |
| L `--jobs=4` | 11.73 | 33.23 | 1762 | 1591 |
| L `--jobs=8` | 6.64 | 27.24 | 1762 | 1593 |
| L `--jobs=16` | 5.20 | 30.67 | 1762 | 1623 |
| con-ron `--jobs=1` | 20.24 | 20.15 | 508 | 507 |
| con-ron `--jobs=2` | 12.06 | 21.56 | 582 | 582 |
| con-ron `--jobs=4` | 6.60 | 19.51 | 640 | 643 |
| con-ron `--jobs=8` | 4.47 | 20.37 | 787 | 789 |
| con-ron `--jobs=16` | 3.58 | 22.58 | 931 | 934 |

* L's speedup over sequential: 5.6× at 8 jobs, 7.1× at 16 (con-ron over its `--jobs=1`: 4.5×,
  5.7×). L/con-ron wall: 1.5× at 8 and 16 (1.8× sequential). The fork design measured 9.1 s / 7.5 s
  at 8 / 16 jobs and CPU 40–44 s (copy-on-write); threads: 6.6 / 5.2 s, CPU 27–31 s.
* Phase A + compaction: 4.0 s (`CA_PAR_ONLYA`). Phase B's total CPU in the workers (~26 s) is
  below sequential mode's phase B (~33 s): fresh, small tier-1 tables per worker instead of the
  tables phase A grew, and dense frozen images.
* **Memory does not grow with the jobs**: the peak is at the end of entry 1 (the region as phase A
  left it, the input buffer, and `OUT`, 523 MB); afterwards the region and the inputs are freed,
  and the workers (the frozen buffer shared, each its own tier 1, memos, pool seed) stay below it
  at 16 jobs. The peak is 1.2× sequential mode's; con-ron's peak grows ~30 MB per worker from
  0.5 GB. Ways down, not in the prototype: memlay (smaller slot images: `ASLOT` 268 MB → ~67 MB),
  and tierpool (no pool seed per worker).
* The other big fixtures (app-lam, beta/let-ladder, c03d/c04a/c05b, eager_open, init-prelude: at
  most a few dozen groups, one dominant) gain nothing from jobs, for L or con-ron; L `--jobs=N`
  is as fast as sequential there (app-lam is faster: 8.5–9 s against 11.1 s), so the mode costs
  nothing when there is no parallelism. Peak RSS +0…+10 MB (`OUT` is small there), except
  init-prelude at 16 jobs (141 MB against 39 MB: 16 worker regions' first pages).

### Phase 2 plan (proofs and landing), for the coordinator's OK

**L changes** (all small; `asm/checker.s` regenerated):
1. The env index tiered (`env_row_get`/`env_row_set`, `rowIx`/`rowSet` in `Arena/Env.lean` and
   the 13 files that name `EIXA/S/N`; write-set lists gain `EIX + 256`). Lands first, alone
   (sequential behaviour unchanged).
2. Store-library freeze functions: `ConsLib` generates `X_freeze(o)` per schema (records,
   canonical slot table, column) with a spec "`OUT[o‥o+e)` is the frozen image of tier 0"; one
   generic copy lemma (`copy!` → `Mem.copy64`). After memlay lands, its generator is the one that
   changes. Plus images of `PINS`, `EREC`, `PEND`, the env index, `CTL`, the pool (the pool
   library's, tierpool's `POOL⟨0⟩` once it lands).
3. Globals `MODE`, `PJ`, `INIT` (`Arena/Globals.lean`, lane parallel's file); `check` dispatches
   on `MODE` (`check_of_stages` takes `MODE = 0` of the zero region, as in lane parallel);
   `check_a` = the stages + `phase_a` (lane parallel's factoring of `install_then_check`) +
   `par_compact`; `check_b`.
4. Stubs `ca_start_a` (lane parallel's `parStub` head) and `ca_check_b` (new: descriptors from
   the header, owned slots, `(0, 0)` for the rest) in `Compiler/Abi.lean`; `asmTextAbiPar`.

**Theorems** (sequential semantics; `ca_start`'s theorems unchanged in statement):
* (a) `checkA_run`: a run of `check` with `MODE = 1` returning `2^63 + k` gives phase A's
  acceptance (`installFold … = .ok (k, fe, pend), a'`) and `OUT` = `Frozen m` where `m` is the
  memory of lane parallel's `PhaseBStart … m a'` (reused: `phaseA_refines`, `PhaseBStart`).
* (b) **The transfer** (the new work): `PhaseBStart … m a'` and `w` = the worker memory built from
  `Frozen m` (frozen arrays at their image lengths, owned arrays zero, the rest empty) with the
  seeds copied give `WorkerStart … w a'.worker`: `LoopR`/`LoopMem`/`CoreMemos`/`CrOK` at the
  worker state. Per component: tier-0 store relations read only below the counts (records,
  columns) and through the slot predicates (the canonical table: a library lemma `freeze_tierR`);
  tier 1 empty = `consR_init` on zero arrays; memos empty on zero arrays (MemoLib: stamp `0` is
  never live) = `Memos.empty`/`Caches.empty`; env rows below the name counts (tier 1 of the index
  zero = no row); pins, `EREC`, `PEND` below their extents. Lengths of frozen arrays shrink, so
  every relation that states a capacity of a tier-0 array must only need it for tier 1 (pushes in
  phase B go to tier 1): to be checked per relation, fixed where one asks more.
* (c) `checkB_run`: from `WorkerStart … w s js` (the worker after the groups `js`), a run of
  `check` with `MODE = 2`, `PJ = j` returning `ACCEPT` gives `checkPending` on group `j` from
  that state and `WorkerStart … (js ++ [j])` (lane parallel's `PhaseBStart.step` with
  `TwinPend.dup`; the first call's `INIT` branch establishes it from (b)).
* (d) Composition: every `j < k` accepted by some worker's chain ⇒ `PooledAccepts` (each
  worker's list from `a'.worker`, exactly con-ron's shape, no `checkPendingList_worker` detour)
  ⇒ `TwinAccepts`' `_pure`/`_model`/`_no_False` (lane parallel's `pooledAccepts_bridge` use).
* (e) Machine level: entry 1 as `ca_start` plus the mode store (lane parallel's `abiA_outcome`);
  entry 2: the stub establishes `Layout.Ok`/`MemRel` for the two-place layout (frozen arrays in
  the buffer, owned arrays in the region, zero-length arrays), then `compile_correct`; the
  buffer's words are `Frozen m` by (a). **Route A**: the harness's assumption that a returning
  `ca_check_b` call did not write the buffer (it is read-only) — so the next call sees the same
  frozen words — goes into `ParFinal`'s module doc with the other harness assumptions (each
  thread's region as its previous call left it, each `j` claimed once, accept only if all
  accepted, a crash is a failure).

**Reuse from branch `parallel`**: `phase_a`/`phaseA_refines`/`PhaseBStart`, `PhaseBStart.step`,
`TwinPend.dup`, `GSetSplit` (phase B writes no global but `INIT`: re-check), `ParEntry`'s shape,
`ParAbi`'s `abi_start_outcome`/`abiA_outcome` (entry 1 unchanged in kind), `ParFinal`'s shape,
`Twin.lean`'s pooled corollaries. Dropped: everything fork-specific (copy-on-write memory equal
to the parent's, `abiB_outcome` on the same region).

**Order and estimate**: env-index tiering (1–2 days, lands alone); `phase_a` + globals + MODE
dispatch + stubs + harness with the reused proofs (3–4 days); freeze functions and (a) (2–3
days); the transfer (b) (5–7 days, the bulk; parallelisable per relation family over 2–3
helpers); (c)–(e) (3–4 days). In all ~15–20 lane-days. Tierpool integration after it lands:
the pool image and `PTOP0` seed (1–2 days); memlay: only the freeze generator and its lemma.

### Verdicts

`bench.py --set all --reps 0 --no-conron --no-ref` (`_tmp/parmode/verdicts2.{out,log}`): master's
`asm/checker.s` (sequential), the prototype's `ca_start`, and the prototype at `--jobs=1`, `4`,
`16`: **675 fixtures, 0 disagreements** (407 accept, 262 error, 3 reject-front, 2 timeout,
1 exhausted: `stack_fuel_offset`, as on master).
