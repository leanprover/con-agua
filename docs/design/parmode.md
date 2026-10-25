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

`ConAgua/Proto/ParMode.lean` (removed when the real code landed; in the branch history at b01beaf4; not in the lake globs; `scripts/lake env lean --run
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
`16`: **675 fixtures, 0 disagreements** (408 accept, 261 error, 3 reject-front, 2 timeout,
1 exhausted: `stack_fuel_offset`, as on master).

## Phase 2 (2026-10-25): re-plan after the user's decision

User (via the coordinator): "in sequential mode we still want to use the same entry points and
memory patterns, for consistency, but from a simple sequential driver written in L or asm and
covered by the main theorem (and no mprotect, that's optional anyways)." So:

* **One code path.** `ca_start(in, in_len, pins, pins_len, base, base_len)` stays the entry, but
  behind it is a **sequential driver** (asm: it calls the two entries, which L cannot do, because
  an L program has one descriptor table): entry 1 on the first part of the region, then entry 2
  for `j = 0‥k-1` on the buffer `OUT` (inside the first part, where entry 1 wrote it) and a worker
  region carved from the rest of `base`; the first result that is not `ACCEPT` is the result. The
  monolithic `MODE = 0` path (`install_then_check` straight through) goes away once the driver is
  proved. `--jobs=1` and no `--jobs` both call `ca_start`; `--jobs=N > 1` uses the threads.
* **No mprotect in the driver, and no route A needed there**: with one worker the buffer is simply
  part of that worker's L memory, threaded from call to call (each call's `MemRel` covers it), so
  whatever an L run did to it, the next call's L memory is what the theorem talks about. Route A
  (read-only buffer) stays the threaded harness's assumption only, because there the buffer is
  shared.
* **The driver's registers**: the compiled code never touches `rbx`, `r12`, `r13` (checked in
  `asm/checker.s`), so the driver keeps `base`, the group counter and `k` there across the calls.
* **Memory.** The driver cannot free memory (no syscalls in the machine model, no new harness
  hooks), so sequential mode's peak becomes: phase A's region + `OUT` + the worker's scratch.
  Measured below; options if it matters: let entry 2 reuse phase A's own arrays as the worker's
  (a `worker_reset` that empties tier 1 and the memos in place) — not planned unless asked.

**Revised steps**:
1. Env index one array per tier (below; lands first).
2. Prototype the driver (asm in `ConAgua/Proto/ParMode.lean`), benchmark it against today's
   sequential mode (instructions, wall, interleaved; peak RSS) and re-check all verdicts.
3. L side for real: globals, `check_a` (stages + `phase_a` + `par_compact` from store-library
   freeze functions), `check_b`; the stubs `ca_start_a`, `ca_check_b` and the driver
   (`Compiler/Abi.lean`); harness `--jobs=N` threads. Until step 6 the driver has its own label
   (`ca_start_drv`, unproved) and `ca_start` stays the proved monolithic path, so the final
   theorem and the harness's default keep holding while the proofs come in.
4. Theorems shared by both modes: (a) entry 1's run (`phaseA_refines` + compaction spec);
   (b) the transfer `PhaseBStart m a'` → worker start state over `Frozen m` and a zero region;
   (c) entry 2's run (one group, threading the worker state).
5. The driver theorem: machine-level loop over the `k` calls (invariant: the machine memory is
   `MemRel` to the worker's L memory after groups `0‥j-1`), composed with (a)–(c) into
   `PooledAccepts` with ONE worker list `[0‥k-1]` → `TwinAccepts` for the committed file. The
   threaded harness's theorem is the same (b)–(c) with route A and one list per thread.
6. Switch the final theorem (`checkerFile_accepts…`) to the driver; delete the monolithic path
   (`MODE = 0` branch, `install_then_check`'s direct use, its asm label).

**Estimate**: step 1: 1 day (done in this landing); steps 2: 1 day; 3: 3–4 days; 4: 7–9 days
(the transfer is the bulk; helpers per relation family); 5: 3–4 days (the machine loop is new,
lane parallel's per-call `ParAbi` outcomes cover a single call); 6: 1–2 days. In all **16–21
lane-days** (was 15–20: the driver's machine loop and the switch-over replace the per-thread
composition, which becomes a corollary). Tierpool / memlay integration unchanged.

**Twin.** con-ron's sequential `--jobs=1` runs the same pool code with one worker (`parallel_all`
on one thread: `worker_state` once, then every pending record in order), so the driver is that
shape exactly; con-ron has no frozen-buffer copy (it moves its tables, `freeze_tier`) — a layout
matter, not a behavioural deviation. No `docs/deviations.md` row so far; one will be added if the
driver turns out to differ (e.g. if memory forces a `worker_reset` in place).

### Step 1: the env index, one array per tier

`EIXA/EIXS/EIXN` (132–134) hold tier 0's rows at `2 i`, new `EIXA1/EIXS1/EIXN1` (140–142) tier 1's
(not `a + 256`: ids at and above 320 would break every write-set list that assumes the arrays
end at 320). `env_ix(w)` returns the selector `w >> 27` (`2 tag + tier`) and `2 (w mod 2^27)`;
`env_row_get`/`env_row_set` dispatch over six arrays. Models: `rowTier`, `rowArr w = 132 + tag +
8 tier`, `rowIx w = 2 (w mod 2^27)`, `rowSelW`, `selArr` (`Tiers.lean`, `Env.lean`); the word
models `rowCW`/`rowPW` read `selArr (rowSelW w)`, and their `_eq` lemmas collapse to
`selArr_rowSelW`. Frames: `EnvR.congr`/`grow`/`promoted` and `frameN` name the six arrays,
`CheckR.frame_hi`/`StageR.frame_hi` exclude 140–142 from the "high" writers, the frame lists that
name `EIXA, EIXS, EIXN` name the tier-1 arrays too, `loopZeroArr` includes them.

### Step 2: the driver prototype, measured (2026-10-25)

`ConAgua/Proto/ParMode.lean` now emits `ca_start` as the asm driver (entry 1 on
`[base, base + needA)`, then `ca_check_b` for `j = 0‥k-1` on `OUT` and the worker region at
`base + needA`; `rbx`/`r12`/`r13` hold base, `j`, `k`), the old path as `ca_start_mono`
(harness: `CA_MONO=1`); `ca_region_size` = `needA + ca_worker_size`. `bench.py --set full --reps 3`
(`_tmp/parmode/bench_drv.{out,json}`, load ~19; MASTER = master's `asm/checker.s` before the env
split, MONO = the prototype's monolithic path through a `sh` wrapper, which adds ~9 M
instructions per run, DRV = the driver):

| system | instructions | cycles | wall |
|---|---:|---:|---:|
| MASTER | 1.000 | 1.000 | 1.000 |
| MONO | 1.033 | 1.083 | 1.054 |
| DRV | 1.024 | 1.072 | 1.051 |

| fixture | MASTER instr / wall / RSS | DRV instr / wall / RSS |
|---|---|---|
| Init (`init435`) | 360.1 G / 22.9 s / 885 MB | 359.3 G / 21.7 s / 1201 MB |
| app-lam | 72.85 G / 11.1 s / 1921 MB | 72.86 G / 10.8 s / 1930 MB |
| c04a | 27.53 G / 2.64 s / 398 MB | 27.53 G / 2.62 s / 410 MB |
| eager_open_nat | 26.60 G / 3.12 s / 569 MB | 26.50 G / 3.17 s / 574 MB |
| pinstall_ok | 184 M / 25 ms / 26 MB | 218 M / 29 ms / 26 MB |
| long_line_5mib | 560 M / 42 ms / 52 MB | 593 M / 46 ms / 95 MB |
| init-prelude | 2.03 G / 140 ms / 32 MB | 2.06 G / 146 ms / 49 MB |

* **Instructions**: the compaction and the per-group stub (~2 K instructions: the table's ~640
  descriptor stores) are invisible on the big fixtures (Init −0.2 %: phase B's fresh small tier-1
  tables save more than the compaction and 57 K stub runs cost); the small fixtures pay +1–3 %
  (pinstall_ok +18 %: many groups, each a stub run, on a 0.2 G run). The cycle/wall geomeans
  (+5–7 %) are dominated by the 20–40 ms fixtures, where the spreads are 5–20 %.
* **Memory**: the driver keeps phase A's region, `OUT` and the worker's scratch: Init 885 →
  1201 MB (+36 %; `OUT` is ~250 MB after memlay), the small fixtures +0…+43 MB (the worker
  region's first pages and `OUT`). The kernel-heavy fixtures with few groups +5–12 MB. If this
  matters, an in-place `worker_reset` (the worker reuses phase A's own tier-1 and memo arrays)
  would save the worker's separate scratch, not `OUT`.

Verdicts of the driver prototype (`bench.py --set all --reps 0`, the two timeout fixtures left
out; `_tmp/parmode/verd_drv.out`): master, the driver and `--jobs=8`: 673 fixtures, 0
disagreements.

### Step 3: the parallel mode in the real program (unproved parts listed)

* `Arena/Globals.lean`: `MODE` (8), `PJ` (9), `INIT` (10) (ids 0‥7 left to tierpool's pool
  globals).
* `Arena/Freeze.lean`: the frozen list (`frozen`, header order; `fzStores` from the cons schemas,
  `fzCols`), the image generators `fzPreG` (a prefix of length `e`) and `fzSlotG` (a slot table in
  canonical form), `fzF i` (`fz_i`), `par_compact(vis)` (all images, then the header),
  `parOwned` (the worker's arrays) and the literal copies `frozenIdsL`, `parOwnedL` the stub is
  built from (`#guard`ed equal: with the computed lists `AsmStubEq`'s `list_eq` re-evaluated them
  in every piece and memwatch killed it at 16 GB; with the literals it peaks at 5.4 GB).
* `Checker/Entry.lean`: `check` dispatches on `MODE` (`1` `check_a`, `2` `check_b`, else the
  pipeline as before); `check_a` (the stages, `install_fold_go`, `par_compact`; returns
  `2^63 + k`), `check_b` (the seeds on the first call, then `check_pending(PJ, view)`), the
  `fz_i` bindings. `Checker/ParOwned.lean` checks that every array `check_b`'s closure names is
  frozen or owned.
* `Compiler/Abi.lean`: `parStub` = `ca_start_a` (entry 1), `ca_check_b` (entry 2: descriptors from
  the header, owned slots, `(0, 0)` for the rest), `ca_start_drv` (the sequential driver);
  `asmTextAbiPar`, `parSymbols` (`ca_out_off`, `ca_worker_size`, `ca_region_a_size`,
  `ca_region_drv_size`). `AsmStubEq`: the file's stub is `parStub … ++ abiStub`; `AsmFinal`'s
  `code_of_checkerFile_abi` shifts by `parStub`'s length (the final theorems' statements are
  unchanged: they are about `ca_start`).
* `Checker/Pipeline.lean`: `check_of_stages` takes `Q0 m → m.glob MODE = 0` (the zero region).
* `harness/main.c`: `--jobs=N` (N > 1) threads; `--driver` runs `ca_start_drv`; the default is
  still `ca_start` until step 6.
* Unproved (no theorem mentions them yet; no `sorry`): `check_a`, `check_b`, `par_compact`,
  `fz_i`, the three stubs.

### Step 4: how the shared theorems go (design)

The existing phase-B proof (`checkPending_refinesT`, `PhaseBT.lean`) runs from `LoopR` over the
whole memory, which names arrays a worker region does not have (`DECL`/`DLP`, the promotion
memo, …). Rather than weakening that proof, two generic pieces:

* **(b1) Images.** From `PhaseBStart m a'` (end of phase A), the memory `m'` = `m` with every
  frozen array replaced by its image and the worker's arrays reset (tier 1 empty, memos empty,
  `CTL`/`POOL` as in `m`) satisfies `PhaseBStart m' a'.worker`. Per relation: a store's tier 0 reads
  records below the count and the slots through `SlotsOKG` (a library lemma for the canonical
  table); columns below the count; the env index's tier 0 below the name counts and its tier 1
  empty; `PEND`, `EREC`, `PINS` below their extents; memos/caches zero = empty
  (`Memos.empty`/`Caches.empty`); `LoopR`'s parts about arrays phase B never touches are kept
  (they are the same arrays in `m'`).
* **(b2) Non-interference.** A generic L lemma: two memories that agree on a set `S` of arrays
  (contents) give runs of a function whose call closure only names arrays in `S` that agree on
  `S` and on the results (with a static check over the closure, like `closedA`). The worker's
  actual memory `w` (frozen arrays = images, owned arrays as the region holds them, every other
  array empty) agrees with `m'` on `S` = frozen ∪ owned, so `check_pending` on `w` is
  `check_pending` on `m'`, which `checkPending_refinesT` covers.

So (c) for a call: the worker state `WorkerStart w js` = "there is an `m'` with `PhaseBStart m'
(a after js)` that agrees with `w` on `S`"; one more group keeps it (`PhaseBStart.step` on `m'`,
the run agreeing on `S`). Helpers: (b2) is self-contained (L semantics); (b1) splits by relation
family (stores/columns/slot images; env/pend/erec/pins; memos and the twin's worker state).

Landing of steps 3 (and lane helper parmode-ni's `L/Agree.lean`, the generic non-interference
lemma (b2): `readsIn`, `Agree`, `invoke_agree`, `run_agree`), after merging tierpool: the pool's
tier 0 (`POOL`, array 0) is a frozen image `[0‥CTL[0])`, the worker owns `POOL⟨1⟩` (256) and
`PT0` (62); the only seed left is `CTL`. Verdicts (`_tmp/parmode/verd_real2.out`, the two
timeouts left out): master, this `ca_start`, `--driver`, `--jobs=8`: 673 fixtures, 0
disagreements. Init after the merge (single runs, load ~20): `ca_start` 22.3 s / 791 MB,
`--driver` 21.6 s / 1108 MB, `--jobs=8` 6.1 s / 1056 MB.

## Redesign (2026-10-25, coordinator): the driver in place, entry 2 over a range

Coordinator: the driver's peak RSS (+36 % on Init) is not acceptable — target: at or below
`ca_start`'s — and the per-group stub (pinstall_ok +18 %) should go: one entry per worker that
loops over its groups, as con-ron's worker loop.

* **Every image is a prefix of its array.** The slot tables' offset word is never written (the
  table sits at word 2; memlay's growth in place keeps it there), so the canonical slot image is
  the prefix `[0‥2 + 2n)`; `fzSlotG` is gone, every frozen array is `fzPreG src e`.
* **The driver copies nothing.** Entry 1 in mode `3` (`ca_start_a0`) writes only the buffer's
  header (the extents); entry 2 in place (`ca_check_seq(base, lo, hi)`) rewrites the table at
  `base` as `ca_start` lays it out, except that every frozen array is its own array cut to the
  extent (the header at `OUT`'s slot, the `CTL` seed is `CTL` itself), the byte arrays get no
  memory; the owned arrays are phase A's own, as it left them. So the driver's memory is
  `ca_start`'s: phase A's pages, then phase B on the same arrays. `ca_start_drv` is entry 1 then
  one `ca_check_seq(base, 0, k)`; it needs exactly `ca_start`'s region (`abiNeed`), so it can
  become `ca_start` without a harness change.
* **Entry 2 checks a range** `PLO‥PHI-1` with phase B's own loop (`check_pending_go`), so the
  driver enters it once; the threaded harness claims **chunks** (`k / 16N` groups, 1‥64) from the
  atomic counter and calls `ca_check_b(buf, len, lo, hi, region, size)` per chunk. L has no atomic
  word, so the claiming stays in the harness; at Init's 57 K groups and 8 threads a chunk is 64
  groups, ~900 stub runs in all instead of 57 K.
* **Effect on the proofs.** The driver's twin side is the sequential one: its worker *is* phase
  A's state `a'` (owned arrays not reset), so it composes into `TwinAccepts` the way
  `installThenCheck` does (phase A, then `checkPendingList` from `a'`), and needs no
  `AState.worker` transfer. What the two modes share: (a) entry 1 (images = prefixes, one
  generic copy lemma; mode 3 writes the header only); (b1) the **truncation** lemma
  (`PhaseBStart m a` → `PhaseBStart (m with every frozen array cut to its extent) a`); (b2)
  non-interference (done, `L/Agree.lean`); (c) entry 2's run = `check_pending_go` over a range
  (lane parallel's `PhaseBStart.step`, iterated). The threads add the fresh-worker transfer
  (owned arrays zero, `a'.worker`) and route A. The driver's machine proof is two calls in
  sequence, no machine loop: step 5 shrinks (1–2 days instead of 3–4).

**Revised after the user's answer** (via the coordinator): entry 2 for the threads stays **one call
per group** (`ca_check_b(buf, len, j, region, size)`, i.e. the range `[j, j+1)`); the claim
counter is the harness's. The in-place entry `ca_check_seq(base, lo, hi)` keeps the range: the
driver enters it once for `[0, k)`. No atomics or concurrency anywhere in L, the stubs or the
proofs: every call is a sequential L run.

**No overlapping arrays in place.** In `ca_check_seq` the header `HDRF` is `OUT`'s prefix, so `OUT`
itself gets `(0, 0)`; the `CTL` seed `CTLF` gets `(0, 0)` (the worker's `CTL` is `CTL`; the seed
copy copies nothing). The compiler's `Layout.Ok` needs the arrays disjoint.

**Measured** (`bench.py --set full --reps 3`, `_tmp/parmode/bench_drv2.{out,json}`, load ~35, all
three systems through the same `sh` wrapper): master's `ca_start`, this branch's `ca_start`, and
the driver: instructions 1.000 / 1.000 / 1.000 (the driver adds ~15 K instructions per run: the
header and one stub run; pinstall_ok 185.68 M → 185.69 M), cycles 1.000 / 0.991 / 0.989, wall
1.000 / 0.994 / 0.987; **peak RSS equal** on every fixture (Init 754 / 749 / 752 MB, app-lam
1912 / 1913 / 1920 MB). The driver costs nothing over `ca_start`.

**The harness's concurrency** (`run_jobs`): the threads share only the read-only frozen buffer and
the claim counter (one `fetch_add`: each group index is handed out once); each thread has its own
region and its own result slot, which `main` combines after joining all threads (a plain stop flag
only shortens a failing run). Each `ca_check_b` call is an ordinary sequential run of the checker on
the thread's region and the buffer; the buffer is read-only (route A), so no call can change what
another reads.

**The driver's frozen arrays are whole** (later the same day): `ca_check_seq` writes static table
words (`seqVals`, through `storesCode` as `abiStub`), giving every array its `ca_start` slot and
length except `OUT` and the `CTL` seed (no memory) and the header `HDRF` (`OUT`'s first `hdrW`
words). So the driver's entry 2 runs on phase A's memory as it is: its proof needs neither the
truncation lemma nor a header load in the stub, only non-interference (the worker memory differs
from phase A's in `OUT`, `HDRF`, `CTLF`, the byte arrays and the globals, none of which phase B's
loop names). The truncation is the threads' (their images live in the compact buffer).

### Step 4 progress

* **Phase B's read set** (helper parmode-ni): `L/Agree.lean` over predicates; `Compiler/ReadSetSplit.lean`
  (`rdChk`, `readsIn_of_all`, the `prog_all` pattern of the write sets);
  `Checker/PhaseBReads.lean`: `checkerProg_phaseBReads : readsIn checkerProg (· ∉ {240, 241,
  242}) (none) phaseBFns` (the 582-function closure of `check_pending_go`, regenerated by
  `scripts/phaseb_fns.py`).
* **Truncation** (helpers parmode-tr, parmode-inv): `PhaseBStart.trunc'`
  (`Arena/FreezeTrunc*.lean`), from `PhaseBStart` alone. Three invariants were added for it:
  `TierLay` says tier 0's slot offset word is 0 (it is never written); `PoolOK`'s bound on the
  saved tier-0 top `PT0[0]` now holds only while the top is in tier 1 (in tier 0 the word is
  written before it is read), so the pool's tier 0 can be cut at the top; `PendR` bounds the
  pending count by `2^62` (`pend_push`'s guard), so `PEND`'s extent `3·count` does not wrap. No
  size bound fails after the cut.
* **Entry 2 in place, in L** (`Checker/ParDriverL.lean`): `PhaseBStart.frame0` (a change that
  keeps every word array: globals, bytes), `checkPendingGo_agree` (phase B's loop on a memory that
  agrees with phase A's on every word array but `OUT`/`HDRF`/`CTLF` refines phase B on the worker:
  `run_agree_ok` + `checkerProg_phaseBReads` + `checkPendingGo_workerT`), `checkB_agree`,
  `checkMode2_agree`, `runMode2_agree` (`L.run checkerProg n "check" [] w` returning `ACCEPT`, with
  `MODE = 2`, `PLO = 0`, `PHI = k`, an empty seed and the view in the header, gives
  `checkPendingList … a.worker = .ok`). With entry 1's theorem this is `SeqAccepts`, i.e.
  `TwinAccepts` (`Final/Twin.lean`).
* **The driver on the machine** (helper parmode-abi, in progress): no `rbx`; the driver saves the
  return address and the caller's `r15` in the top 16 bytes of the stack slot (above the L stack,
  outside every layout part), keeps `base` in `r15` (which `ca_finish` restores), and calls both
  entries from the caller's own return-address slot, so the callee's stack window is exactly
  `AbiCall`'s; `compile_correct_frame` (cells outside the layout and the stack window unchanged)
  keeps the saved words across the two runs. The final theorems' assumptions stay `AbiCall`'s.
* **Entry 1** (helper parmode-e1): `Arena/FreezeSpec.lean` (`par_compact`'s exact run:
  `parCompact_run`, `parCompactMem`, header words, images, write set `OUT` only),
  `Arena/PhaseAEntry.lean` (`installFoldGo_phaseA`: phase A's fold ends in `PhaseBStart`),
  `Checker/ParEntryA.lean` (`check_dispatchA`, `checkA_of_stages`), `Pipeline.lean`'s
  `stageSpecs_of_rels` (lane parallel's refactor), `Checker/CheckARun.lean` (`checkA_run`: from
  the loaded memory with the mode word 1 or 3, a run returning `2^63 + k` gives the twin's stages
  and phase A accepted, `PhaseBStart` at phase A's memory `m`, and the final memory
  `parCompactMem m v c`).
* **The driver in L** (`Checker/ParDriverTwin.lean`): `drv_twinAccepts`: entry 1's run
  (`checkA_run`, mode 3) and entry 2's run (`runMode2_agree`, now over the substituted program
  `Prog.subPB pb checkerProg` like the sequential proof, with phase A's memory still holding the
  pin data) give `TwinAccepts [b]`. What is left for the driver's final theorem: the machine
  level (helper parmode-abi), then the switch of `ca_start`.
