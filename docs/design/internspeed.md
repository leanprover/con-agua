# Lane internspeed: the interning path against con-ron's, and seven prototypes

Question: the parse phase is 1.23× con-ron's wall and the gap is mostly interning (parsespeed §2.3).
What does our interning do differently from con-ron's per node, and which changes, generic and
provable, close the gap? Step 1 compares the two paths (layout, loads, probes, growth) with exact
counts and `perf`; step 2 prototypes the candidates in L (unproved), checks verdicts and measures
wall time; step 3 gives a proof plan for the winners.

Base: master a417ec3d (`checker.s` byte-identical to the prototype script's `base`). Nothing landed
but this journal. Prototype, assembly, binaries, profiles, bench data: `_tmp/internspeed/`
(`proto/Proto.lean`, `mk.sh`, `s/`, `bin/`, `prof/`, `perf/`, `wb*.json`, `memprof.py`, `blocks.py`,
`e2e*.log`).

**Answer in short.**
* **The two paths touch the same cache lines.** Per new `app` node both pay one random line in the
  cons table (the slot load, the one real miss: 88 % of `app_find`'s cycles), append one record,
  and read the two children's derived words (mostly cache hits). Interleaving the derived word with
  the record, as con-ron's `rows: Vec<(A, D)>`, saves no line in the parse (`der_b` reads the derived
  word alone) and costs index arithmetic everywhere: no gain.
* **What differs is work, not lines.** In the parse all 5.19 M `app` interns are misses (64 hits).
  Ours spends **669 instructions per new `app` node** in `mk_app`/`intern_app`/`app_find`/`app_push`/
  `der_b`, of which **225 are the table's growth**: the in-place doubling (D38) runs 20 times up to
  8 M slots and re-inserts 6.3 M entries, 1.17 G instructions, **12 % of the parse phase's cycles**
  (`app_push`). The probe itself is 3.25 slot loads per miss at our load factor.
* **Prototypes** (parse phase, `Init`, 40 paired rounds; whole runs: §3):
  * `sz`, presize the persistent `app` table from the input length: **−9.0 %** parse wall
    (p < 0.001), −6.0 % instructions; `szall` (also `lam`, `forallE`): −9.3 %.
  * `der`, the parser keeps each id's derived word with its handle and passes the children's to
    `mk_*` (no `der_b` call): **−5.5 %** (p < 0.001).
  * `rnat`, `read_nat` converts eight digits per word (SWAR): **−4.5 %** (p < 0.001), −7.2 %
    instructions (scanner, not interning; the parsespeed item 3).
  * `fresh` (mirror `IdTable.bound`'s empty-sparse shortcut, removes D8): −1.7 % instructions,
    wall ±0; `hsh` (con-ron's `pack2` key as the hash): ±0; `ilv` (interleaved derived word): +0.4 %.
  * Combined `szall+fresh+der` (`C1`): **−12.2 %**; with `rnat` (`C5`): **−13.4 %**, i.e. the
    parse phase goes from 2.2 s to ≈ 1.9 s, ≈ 1.07× con-ron's 1.80 s (parsespeed §2.1).
  * Whole `Init`: **−5.9 % (`C1`) and −6.1 % (`C5`) at 16 threads** (p < 0.001), where the parse
    is half the run; at one thread the expected −1.2 % is not resolved (−0.5 %, p 0.17, 25 rounds).
* **Recommendation:** implementation lanes for `sz` (small, ~250 lines), `der` (~600 lines) and
  `rnat` (~350 lines), in that order; `fresh` only as the cleanup of D8 (it buys no wall time);
  not `ilv`, not `hsh`.

## 1. Method

* **Prototypes** are L→L substitutions on `checkerProg` in `proto/Proto.lean`, compiled with the
  unchanged compiler (`compileProg`, `asmTextAbiPar`): `lake env lean --run Proto.lean OUT.s V1,V2,…`
  (`base` reproduces `checker.s` byte for byte). `CA_PARSEONLY=1` cuts `check_a` after the parse
  (parsespeed's parse-only binary). `mk.sh NAME VARIANTS` builds both binaries.
* **Verdicts:** `diff-e2e.py --refs --parallel 8` (634 fixtures) on every full binary, and
  `--jobs 4` for `ilv`, `der`, `C1`, `C4`, `C5`.
* **Exact counts:** `perf stat -e instructions:u`; per function and per block `scripts/asmprof.py`
  (`blocks.py` prints one function's blocks with their counts).
* **Memory events** (`memprof.py`): `perf record` of `cycles:u` and the demand fills from DRAM and
  from the local L3 (`ls_dmnd_fills_from_sys.{dram_io_all,local_ccx}`) and page walks
  (`ls_l1_d_tlb_miss.all_l2_miss`), four events (no multiplexing), cut at the parse boundary as
  parsespeed's `phasebench.py`. The fill events skid (their samples land a few instructions to a
  few functions later), so they are read per group of functions, not per instruction. IBS op
  sampling works (`perf record -e ibs_op//`, not with `:u`) but is capped at 6 000 samples/s:
  too few loads per function to count misses; it confirms the per-function cycle split.
* **Wall** as parsespeed (`wb.py`, `wstats.py`): every round runs every cell once in a fresh random
  order, pinned with `taskset` (parse phase and one thread: both SMT threads of one core, 46/94 resp.
  44/92; 16 threads: 24–39), the machine loaded by other lanes (1-minute load 4–54); per round the
  ratio variant/base, the median paired ratio, an exact Wilcoxon signed-rank test, and the 95 %
  t-interval of the mean log ratio. Bold: p < 0.05.

## 2. Step 1: the two interning paths

### 2.1 Per node

| | ours (`mk_app` → `intern_app` → `app_find`, `app_push`; `der_b` ×2) | con-ron (`EStore::intern_app` → `Tbl::find`, `der_of_app`, `Tbl::push`) |
|---|---|---|
| record | `AREC⟨t⟩[i]`: `f \| a << 32`, 8 B | `rows[i].0`: `AppNode {f, a}`, 8 B |
| derived word | `ADER⟨t⟩[i]`, own array, 8 B: bvar range, fvar range, lp bit (31 bits) | `rows[i].1`, next to the record (16 B rows): the same plus a 32-bit structural hash |
| slot | 16 B: value word (`B t + i + 1`), key word (`f \| a << 32`, an exact table, D34): 4 per line | `Slot::Live(stamp, AppNode, EIdx)`: 20 B, 3.2 per line |
| hash | FNV-1a over `f`, `a` (2 multiplies), then `x = h·φ; x ^ x >> 32` | `pack2(f, a) = f \| a << 32`, then the same finalizer |
| home | `mulhi(x, n)` (D36) | `x & (n − 1)` |
| probe | linear; a slot whose key word equals the key is the hit (no record read) | linear; compares the stamp, then the key in the slot |
| a miss | **one probe**: `app_find` returns the free slot, `app_push` writes there | **two probes**: `find`, then `push` → `insert` re-probes (the lines are hot) |
| load factor, growth | 3/4; doubles **in place** (zero the upper half, mark, re-insert; D38) | 3/4; a new table of twice the size, entries moved, old one freed |
| start size | 8 slots | 0 (32 at the first insert) |
| derived word of a new node | `der_b(f)`, `der_b(a)`: dispatch on the tag, bounds, load (per child) | `derived(f)`, `derived(a)`: `rows[i].1` (per child) |

**Cache lines per new `app` node**, both: one random slot line (plus the next line when the run
crosses a boundary), the record append (sequential), the two children's derived words (random into
the recent past; mostly hits), and the id table's two reads and one append in the parser. Ours
writes a second sequential stream (`ADER`). No difference in random lines: interleaving (`ilv`)
can only help walks that read record and derived word together, i.e. after the parse.

### 2.2 Exact counts (parse-only binary, `Init`)

* `app_find` 5 189 440 calls, `app_push` 5 189 376: **all but 64 interns in the parse are misses**
  (the export format shares subterms by id; the hash-cons finds nothing new to share).
* Probes: **16.87 M slot loads, 3.25 per lookup** (2.25 occupied slots and the free one); a hit
  never happens here, so every lookup is a full unsuccessful probe at the table's current load
  (3/8‥3/4).
* Instructions per new `app` node: `mk_app` 120, `intern_app` 58, `app_find` 116, `app_push` 302,
  `der_b` 2 × 36 = **669**; around it the parser's `node_bin` 31, `expr_get` 2 × 27, `expr_fresh`
  25 + `esp_find` 56, `expr_put` 56, `apply_expr` 36.
* **The growth:** 20 doublings to 8 388 608 slots (128 MB), 6.29 M entries re-inserted
  (`kpickB`/`kprobeL`/`kplaceB` 6.29 M times, the zero loop 2.1 M times 8 words, the mark loop 8.4 M
  slots): **1.17 G instructions of `app_push`'s 1.57 G** (5.0 % of the parse phase's 23.32 G);
  `lam_push` (350 per call), `forall_push` (321), `nstr_push` (387), `const_push` (437) are the same
  pattern on smaller tables.
* `read_nat` 20.1 M calls, 130 instructions each (2.62 G, 11.2 %).

### 2.3 Where the cycles go (one run each, under load; per cent of the parse phase's cycles)

| | ours | con-ron |
|---|---:|---:|
| parse-phase cycles | 8.9 G | 7.1 G |
| interning (ours: `app_*`, `mk_*`, `der_b`, `intern_*`, `lam_*`, `forall_*`, `esp_find`, `expr_*`; con-ron: `EStore::intern*`, `HashMap2<…>`, `Tbl`) | ≈ 30 % (2.7 G) | ≈ 25 % (1.8 G) |
| ↳ `app_push` (the growth) | 11.8 % | (`HashMap2` resize/move ≈ 3 %) |
| ↳ `app_find` | 10.4 % (88 % of it on the instruction after the slot load) | `intern_app` 13.3 % |
| ↳ `der_b` | 3.2 % | (inlined) |
| demand fills from DRAM / local L3 | 7.3 M / 5.7 M | 15.0 M / 7.4 M |
| page walks | 1.8 M | 0.1 M |

The slot load is the miss on both sides: ≈ 165 cycles per lookup on average in `app_find`. It is
not a DRAM miss every time: the demand fills attributed to the interning functions are well below
one per lookup, and a small IBS sample (≈ 40 slot loads) puts about half of them in L1 and one in
eight in DRAM. The table has locality: consecutive nodes have nearby handles, and a
multiplicative hash maps keys that differ by a constant to an arithmetic progression of slots. Con-ron pulls twice as many lines from DRAM, mostly in its scanner (its chunked
`read` of the input); ours has 18× the page walks, spread over the scanner and the tables (the input
is a file mapping in 4 KB pages, and `main.c`'s `advise_huge` leaves each array's first 2 MB on
4 KB pages). Neither is in reach of the L code; the walks are a note for `main.c` (§6).

**So the gap in the interning is instructions, not misses**: 225 instructions of growth per node,
two `der_b` dispatches, and the probe at a load that grows to 3/4 between doublings.

## 3. Step 2: the prototypes

| variant | what | deviation |
|---|---|---|
| `sz` | `app_presize()` at the start of `check_a`: if `ASLOT⟨0⟩` is still the fresh table (word 0 is `0`), make it `n` zero slots, `n` the power of two `≥ len(IN) / 64` (8 M on `Init`), so the parse never grows it | new (con-ron starts empty; `HashMap2::with_capacity` exists) |
| `szall` | `sz` and also `LASLOT⟨0⟩` (`len / 512`), `FASLOT⟨0⟩` (`len / 1024`) | new |
| `hsh` | the `app` schema's `ihash` is `f \| a << 32` (con-ron's `pack2`), so `kfHead`'s finalizer is the only mixing | removes a (silent) one |
| `fresh` | `tbl_fresh` (names, levels, expressions) returns "fresh" without the sparse probe when the sparse memo's count `CTL[2b − 63]` is `0` | removes D8 |
| `ilv` | the `app` derived word next to the record: `AREC⟨t⟩[2i]`, `AREC⟨t⟩[2i + 1]` (a rewrite of every `AREC`/`ADER` access, and of the two frozen images) | removes a layout difference (con-ron's rows) |
| `der` | `EID` one word per id, `h \| der << 32`; `expr_get` masks; `apply_expr` of an `app`/`lam`/`forallE` line calls `node_bin_d` → `mk_app_d(f, a, df, da)` (and `mk_lam_d`, `mk_forall_d`), which compute the new node's derived word from the children's without `der_b`; other lines call `der_b` once on their own node | new (con-ron reads `derived` of the children) |
| `rnat` | `read_nat(v, e)`: for 1‥8 digits one `ld8x8` word shifted left by `8 (8 − L)` and three multiply-mask steps (`·2561 >> 8`, `·6553601 >> 16`, `·42949672960001 >> 32`); 9‥16 digits two words; otherwise (17, 18 digits, or the word would pass the input's end) the byte loop | new (con-leche's `readNatAt` is the byte loop) |
| `C1` | `szall, fresh, der` | |
| `C2` | `C1, hsh` | |
| `C3` | `C1, ilv` | |
| `C4` | `C1, hsh, ilv` | |
| `C5` | `C1, rnat` | |

**Verdicts:** every variant 634 agree, 0 UNSOUND/INCOMPLETE/CRASH/TIMEOUT/REFDIFF, sequential, and
with `--jobs 4` for `ilv`, `der`, `C1`, `C4`, `C5`. (A first `rnat` took 17‥18 digits into the
two-word path with a negative shift and declined `rounds_huge_gaps`; fixed by the `L ≤ 16` bound.)

### 3.1 Instructions (exact, `Init`)

| variant | parse-only | Δ | whole run | Δ |
|---|---:|---:|---:|---:|
| `c0` | 23.316 G | | 242.98 G | |
| `sz` | 21.914 G | −6.0 % | 241.48 G | −0.6 % |
| `szall` | 21.650 G | −7.1 % | 241.21 G | −0.7 % |
| `hsh` | 23.271 G | −0.2 % | 242.36 G | −0.3 % |
| `fresh` | 22.913 G | −1.7 % | 242.58 G | −0.2 % |
| `ilv` | 23.379 G | +0.3 % | 246.02 G | +1.3 % |
| `der` | 22.433 G | −3.8 % | 242.10 G | −0.4 % |
| `rnat` | 21.645 G | −7.2 % | 241.31 G | −0.7 % |
| `C1` | 20.364 G | −12.7 % | 239.93 G | −1.3 % |
| `C2` | 20.344 G | −12.7 % | 239.20 G | −1.6 % |
| `C3` | 20.390 G | −12.6 % | 242.93 G | ±0 |
| `C4` | 20.370 G | −12.6 % | 242.20 G | −0.3 % |
| `C5` | 18.693 G | −19.8 % | 238.25 G | −1.9 % |

With `szall`+`der` the `app` path is 301 instructions per new node (`mk_app_d` 95, `intern_app` 58,
`app_find` 71, `app_push` 77), against 669; the presized table also shortens the probe to 1.80 slot
loads per lookup (the load stays below 5/8). `ilv` adds a shift per `AREC`/`ADER` access, 3 G over
the whole run.

### 3.2 Wall time

**Parse phase** (parse-only binaries, cores 46/94; bench A 40 rounds of 11 binaries, bench A2 40
rounds of 5; load 4–54, median 12):

| variant | median paired Δ | Wilcoxon p | 95 % CI of mean |
|---|---:|---:|---:|
| `c0` (A; A2) | 2.14 s; 2.22 s | | |
| `sz` (A) | **−9.0 %** | < 0.001 | [−9.3, −7.9] |
| `sz` (A2) | **−8.9 %** | < 0.001 | [−12.8, −6.8] |
| `szall` | **−9.3 %** | < 0.001 | [−10.0, −6.6] |
| `hsh` | −0.5 % | 0.183 | [−0.8, +1.9] |
| `fresh` | −0.2 % | 0.590 | [−0.9, +3.7] |
| `ilv` | **+0.4 %** | 0.045 | [−0.5, +2.9] |
| `der` | **−5.5 %** | < 0.001 | [−5.8, −1.0] |
| `rnat` (A2) | **−4.5 %** | < 0.001 | [−7.8, −1.5] |
| `C1` (A) | **−12.2 %** | < 0.001 | [−12.5, −8.9] |
| `C1` (A2) | **−11.9 %** | < 0.001 | [−14.3, −9.8] |
| `C2` | **−11.4 %** | < 0.001 | [−11.8, −9.1] |
| `C3` | **−12.2 %** | < 0.001 | [−12.7, −9.3] |
| `C4` | **−11.5 %** | < 0.001 | [−12.2, −9.5] |
| `C5` (A2) | **−13.4 %** | < 0.001 | [−15.2, −8.8] |

(`C5` against `C1` in A2: −1.9 %, p = 0.57: `rnat` on top of `C1` is not resolved in 40 rounds.)

**`Init`, one thread** (cores 44/92). Bench B, 20 rounds of ten binaries (load 4–135, median 40):

| variant | median paired Δ | Wilcoxon p | 95 % CI of mean |
|---|---:|---:|---:|
| `c0` | 21.84 s | | |
| `szall` | −1.4 % | 0.701 | [−6.6, +8.2] |
| `hsh` | +0.7 % | 0.452 | [−3.1, +10.3] |
| `fresh` | −0.3 % | 0.546 | [−10.3, +5.9] |
| `ilv` | −2.0 % | 0.812 | [−6.1, +6.5] |
| `der` | −0.6 % | 0.430 | [−9.8, +4.8] |
| `rnat` | −0.9 % | 0.622 | [−10.4, +7.5] |
| `C1` | −1.2 % | 0.154 | [−8.8, +4.2] |
| `C4` | −4.3 % | 0.105 | [−10.3, +1.4] |
| `C5` | −0.5 % | 0.927 | [−9.2, +10.1] |

Bench B2, 25 rounds of `c0`, `C1`, `C5` on a quieter machine (load 3–86, median 7): `c0`
18.40 s, `C1` −0.5 % (p 0.173, [−2.9, +9.6]), `C5` −0.2 % (p 0.958, [−2.5, +9.0]).

The expected effect is the parse phase's gain on a tenth of the run: −1.2 % (`C1`), −1.3 % (`C5`).

**`Init` at 16 threads** (cores 24–39). Bench C, 30 rounds of ten binaries, ran at load 34–139
(median 65) and resolved nothing (`C1` −6.4 %, p 0.47; `szall` −4.6 %, p 0.14; `ilv` +2.7 %,
p 0.045; every other cell p > 0.19). Bench C2, 40 rounds of four, load 10–49 (median 15):

| variant | median paired Δ | Wilcoxon p | 95 % CI of mean |
|---|---:|---:|---:|
| `c0` | 3.94 s | | |
| `szall` | **−4.2 %** | < 0.001 | [−12.6, −3.2] |
| `C1` | **−5.9 %** | < 0.001 | [−12.6, −0.1] |
| `C5` | **−6.1 %** | < 0.001 | [−13.8, −1.4] |

At 16 threads the parse phase is half the run (parsespeed §2.1), so its −12 % shows as −6 %.

## 4. Verdict

* **The interning gap was the growth.** Presizing the persistent `app` table removes 1.4 G
  instructions and 9 % of the parse phase's wall, the largest single item; the doubling in place
  (D38) costs ≈ 225 instructions per node in the parse, where con-ron's move-into-a-new-table is
  cheaper but not free. Presizing also lowers the average load, which shortens the probe (1.80
  against 3.25 slot loads).
* **`der_b` was the second.** Each new compound node dispatched twice on its children's tags and
  re-loaded their derived words; the parser had both words one load away (the id table line it
  reads anyway). `der` is −5.5 % on the parse phase.
* **Layout and hash do not matter here.** `ilv` and `hsh` change no cache line per intern in the
  parse (§2.1); their wall effects are ±0.5 %, `ilv` +1.3 % instructions over the whole run.
  `fresh` saves 0.4 G instructions (one empty probe per line), which do not show in the wall.
* **Winners** (≥ 2 % on the parse phase, significant): `sz`/`szall`, `der`, `rnat`, and their
  combination: **`C5` −13.4 % on the parse phase, −6.1 % on `Init` at 16 threads**; on one thread
  the expected −1.3 % is below what 20–25 rounds resolve at this load. With `C5` the parse phase is
  ≈ 1.92 s against con-ron's ≈ 1.80 s (parsespeed's medians; not re-measured side by side here).

## 5. Proof plans

Order by gain per line of proof: `sz`, then `der`, then `rnat`; `fresh` with D8's cleanup.

**`sz` (≈ 250 lines, 4–6 agent-hours).**
* L: a cons-library template `consPresizeG C k` (`if sa⟨0⟩[0] == 0 && 2 n + 2 ≤ len(sa⟨0⟩) {
  sa⟨0⟩[0] := n − SN0 }`, `n` the power of two `≥ len(IN) >> k`), instances for `app`
  (and `lam`, `forallE` if `szall`); one call each at the start of `check_a`, before
  `intern_reserved_pins` (the stage that first interns).
* Proof: at that point the memory is `initMem` (all word arrays zero; `RomProgInit`), and
  `arenaR_init` holds. The new lemma: `ArenaR` holds on `initMem` with word 0 of `sa⟨0⟩` set to
  `n − SN0` for `n` a multiple of 8 with `2 n + 2 ≤ |sa⟨0⟩|`: the KSTP slot invariant for `n` zero
  slots (no live slot, the empty `cons` map), the same argument as the existing `SN0`-slot case
  with `n` for `SN0` (~120 lines in `ConsLibSpec`/`ArenaRel`). `check_a`'s spec threads it
  (~80), the template's spec (~50). If the start state were not known to be zero, the template
  would zero the `2 n` words itself (the growth's `kzeroLs`), costing the page faults up front.
* Deviation: **new Deliberate row** (con-ron's `HashMap2` starts empty; effect none, performance
  only). Alternatively con-ron could size its persistent table the same way
  (`HashMap2::with_capacity` exists), which would keep the twins equal.
* The frozen image of `ASLOT` is the whole table (`fzSlotExt`): unchanged on `Init` (8 M slots
  either way), larger than today for inputs whose table would have stayed below `len / 64`.

**`der` (≈ 600 lines, 10–15 agent-hours).**
* L: `EID` one word per id (`h | der << 32`, `der < 2^31`: two 15-bit ranges and the lp bit); the
  id-table templates (`tblGetG`, `tblPutG`) get an entry width (EID 1 word, NID/LID 2 per word as
  today); `expr_get` masks; `expr_get_der`; `mk_app_d`, `mk_lam_d`, `mk_forall_d` (as `mk_*` with
  the children's packed words as arguments); `node_bin_d`; `apply_expr` stores `h | der << 32`,
  calling `der_b` once for the other node kinds.
* Proof: `TblR` for `EID` gains "the high half of id `i`'s word is `packBFL (derBW h) (derFW h)
  (exprLPW h)` of its handle `h`" (`StateDR`); it is preserved because the parse interns only into
  the persistent tier (scratch closed) and a persistent node's derived word never changes (the
  `ADER` frame lemmas give it, ~150 lines). `mk_*_d`'s specs are `mkAppW`/`mkLamW`/`mkForallW` under
  the hypothesis on the arguments (~150, mostly copied from `mkApp_spec`). `ApplyExprRefine`,
  `node_bin` and the `IdTable` specs at width 1 (~250). D9's capacity halves for `EID` (ids past
  the dense array go to the sparse memo, as today).
* Deviation: **new** (con-ron's `der_of_app` reads the children's rows): performance only.

**`rnat` (≈ 350 lines, 6–10 agent-hours; risk in `bv_decide`).**
* L: `read_nat` as prototyped (one word for 1‥8 digits, two for 9‥16, the byte loop otherwise).
* Proof: (1) for each `L ≤ 8` and digit bytes `b₀‥b_{L−1}`, the three multiply-mask steps of
  `ld8x8 << 8 (8 − L)` equal `rdLoopN` on them: eight `bv_decide` goals over 64-bit words with
  constant multiplications (or one goal with `L` symbolic); (2) `rdLoopN` over `[v, e)` splits at
  `e − 8` (`· 10^8 +`); (3) `read_nat`'s spec takes the precondition "every byte of `[v, e)` is a
  digit", which its five callers have from `skip_digits`/`num_end` (`skipDigitsN`); without it the
  two functions differ on non-digit bytes. The model `rdNatN` is unchanged.
* Deviation: none (same value on every call the program makes).

**`fresh` (≈ 150 lines).** D8's proposed fix: relate the memo's live count to the sparse map's
emptiness (`MemoRV`), then test it first. Removes D8; no wall gain measured.

**Not recommended:** `ilv` (no line saved in the parse, +3 G instructions over the run, and every
frame lemma that separates `AREC` from `ADER` would need rework); `hsh` (no effect).

## 6. Notes

* **Page walks.** Ours takes 1.8 M page walks in the parse phase against con-ron's 0.1 M. Two
  sources outside L: the input is a `MAP_PRIVATE` file mapping (4 KB page-cache pages), and
  `advise_huge` leaves the first and last 2 MB of every array slot on 4 KB pages (where the small
  arrays and the start of every array live). Both are `main.c` (trusted C) decisions; reading the
  input into an anonymous, huge-page region would be the experiment. Not measured here.
* **The hash.** `hsh` changes neither the probe counts (16.90 M against 16.87 M slot loads) nor the
  wall: the FNV multiplies are not on the miss's critical path enough to matter. The `mulhi` home
  (D36) and the multiplicative finalizer give the table its locality (half the slot loads hit L1),
  and so does con-ron's.
* **No hits in the parse.** Every `app` intern of the parse is new. A parse-specific "push without
  probing" would be unsound (the export may repeat a node), and con-ron probes too; the probe stays.

## 7. Landed: `szall` (lane presize)

`check_a` calls `presize_tables()` (`Checker/Presize.lean`) between `pb_check` and
`intern_reserved_pins`: `pow2_at_least(len(IN0) >> 6)`, `>> 9`, `>> 10` slots for the persistent
`app`, `lam`, `forallE` tables, through the cons library's `X_presize(n)` (`consPresizeG`,
`Arena/ConsPresize.lean`; con-ron's `HashMap2::with_capacity`), which writes tier 0's count word
only if the table is the fresh one and `n` is a layout (a multiple of 8, at least `SN0`, room for
`2 n + 2` words). Deviation **D42** (Deliberate): con-ron's tables start empty.

* **Proof** (~470 new lines, no `sorry`): `consPresize_spec` (the template's memory, `psMem`);
  `consR_initN`/`consR_initM` (an all-zero table whose count word is a layout of `n` slots is an
  empty table: `consR_init` with the zero hypotheses local to the table's arrays);
  `presizeTables_spec`; `arenaR_ps` (the loaded memory after the presize is still `ArenaR` of the
  twin's initial state: the three tables by `consR_initM`, the rest by `arena_build`'s frames);
  `irpStage_ps` (`irpStage_setG`'s proof from the presized memory, its frames composed with the
  presize's, which writes only store-tier slot arrays); `checkA_of_stages`/`checkA_err_of_stages`
  take the eighth stage. The table's internals stay behind `ConsR`; the start state's zeros come
  from `loadMem` as planned (§5).
* **Instructions** (parse-only, `Init`): 23.316 G → 21.650 G (−7.1 %, as the prototype's `szall`).
* **Wall** (40 paired rounds unless noted; `Init`; bases: the program without the call for the parse
  phase, master's `checker.s` for whole runs):

  | cell | base | Δ (median paired) | Wilcoxon p | 95 % CI | load |
  |---|---:|---:|---:|---:|---|
  | parse phase (46/94) | 2.12 s | **−6.4 %** | < 0.001 | [−6.9, −6.1] | 4–6 |
  | 16 threads (24–39) | 4.00 s | **−1.9 %** | < 0.001 | [−3.5, −0.6] | 4–12 |
  | one thread (44/92, 25 rounds) | 18.35 s | −0.1 % | 0.958 | [−6.8, +5.4] | 3–92 (median 12) |

  Smaller than the prototype's −9.3 % / −4.2 %, measured at load 4–54 (median 12) and 10–49: on a
  quiet machine the growth's zeroing and rehash (memory traffic) costs less wall time; the
  instruction count is the same.
* **Peak RSS** unchanged on `Init` (743.4 MB sequential, 1000.8 MB at 16 threads, 645.6 MB
  parse-only, both binaries) and on all 634 fixtures (`diff-e2e --log`, ±3 MB, sum 25 730 →
  25 735 MB). The table is sized by the input, not by its nodes, so an input that is long but has
  few nodes reserves more: `long_line_5mib` (5 MB) +1.2 MB sequential, +1.8 MB at 16 threads (the
  frozen image copies the whole persistent table), `complete_c04a_restart_70` (9 MB) +2.3 / +4.3 MB;
  the bound is the three tables' `16 n` bytes, about 0.3 × the input length.
* **Verdicts:** `diff-e2e --refs --parallel 16`: 634 agree, 0 UNSOUND/INCOMPLETE/CRASH/TIMEOUT/REFDIFF.

## 8. Landed: `rnat` (lane rnat)

`read_nat` (`Front/Fields.lean`) converts 1‥8 digits with one load of the 8 bytes ending at `e`,
masked to the digits' low nibbles (`0x0F…0F << 8 (8 − L)`), and three multiply-shift-mask steps;
9‥16 digits with two such loads (the words ending at `e − 8` and `e`); 17‥18 digits, `e < 8`
(resp. `e < 16`) or `e` past the input take the byte loop. Loading the word *before* `e` (not at
`v`) keeps both loads inside `[0, len)` with only `8 ≤ e ≤ len(IN)`, and needs no `L == 0` test
(`w = e − v − 1` wraps). No `bv_decide`.

* **Proof** (~330 new lines, no `sorry`): `ReadNatSwar.lean` (168 lines, ~2 s): `swar8_toNat`
  (eight digit values `≤ 9` in the bytes ⇒ `swar8` is `Σ xₖ·10^(7−k)`), lane by lane over `Nat`:
  `mul_shr` (a product whose lanes do not overflow, shifted, is the next lanes), `w8_and` (a mask
  acts byte by byte, from `Nat.and_div_two_pow`/`and_mod_two_pow`), `omega` for the lane sums;
  `w1_digits` (the masked word of `L` digits is `dval`, their value; 8 cases of `L`). In
  `Fields.lean`: the model `rdNatN` mirrors the code (`rdNatF`, `rdW1`, `rdW2`), `readNat_spec`
  keeps its statement (`r = [rdNatN b v e]`, plain `vcgen` + `simp`, ~3 s), and `rdNatN_digits`:
  on a digit run `v ≤ e` it is the old definition (`rdLoopN_dval`, `dval_add`). The precondition
  lives in the links, not in the callers' specs: `rdNat_link` and `rdNatN_lt` take the digit run,
  which their six call sites get from `numEnd_digits`/`numEndN_digits`/`skipDigitsN_digits`; none
  of the five L callers' proofs changed.
* **Deviation:** none (same value on every digit run, which is every call the links use).
* **Instructions** (`Init`): parse-only 21.652 G → 20.141 G (−7.0 %); whole run 241.21 G →
  239.70 G (−0.6 %).
* **Wall** (`Init`; bases: the program with the byte-loop `read_nat` for the parse phase, master's
  `checker.s` for whole runs):

  | cell | base | Δ (median paired) | Wilcoxon p | 95 % CI | load |
  |---|---:|---:|---:|---:|---|
  | parse phase (46/94, 40 rounds) | 2.00 s | **−7.6 %** | < 0.001 | [−7.8, −7.5] | 5–18 |
  | 16 threads (24–39, 40 rounds) | 3.82 s | **−3.6 %** | < 0.001 | [−4.1, −3.1] | 5–9 |
  | one thread (44/92, 25 rounds) | 18.31 s | **−1.1 %** | < 0.001 | [−2.6, +1.7] (mean) | 2–17 |
* **Verdicts:** `diff-e2e --refs --parallel 16`: 634 agree, 0 UNSOUND/INCOMPLETE/CRASH/TIMEOUT/REFDIFF.
