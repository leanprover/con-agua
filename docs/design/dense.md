# Lane dense: the dense layout, one array space, registration hints (scoping journal)

**Question.** The array abstraction has landed (`absarrays.md` §9): only the compiler knows the
layout. What should the compiler do with that freedom? This journal covers four things: the dense
layout (absarrays batch 7), byte and word arrays as one array space, the registration hints the
user proposed (a per-array minimum length, hot array bases, never-tiered arrays, per-array sizes),
and two prototypes, one for speed and one for the proof shape. No proof changed. Only this file
lands.

Base: master be052799 (`checker.s` byte-identical to hashtpl's base 387d835c). Scratch:
`_tmp/dense/`, outside the repository. It holds the scripts `scripts/arrprof.py`, `hoist.py` and
`rewrite.py`, the binaries, the bench logs, the kernel micro-benchmark `kern/` and the Lean sketch
`proto/MinProto.lean`.

**Answer, in short.**

* The one lever that pays is **`CTL`**, the array of control words. It carries 74 % of the
  executed constant-index bounds checks (3.83 of 5.17 G) and 43 % of the executed array-base
  loads (5.44 of 12.53 G).
* Two compiler features remove almost all of that cost:
  * (a) a **minimum length** per array, which the stubs establish as a layout fact;
  * (b) a **table-relative** placement of `CTL`, at a fixed offset from `r15`.
* Measured (§4), with an unproved rewrite of `checker.s`:
  * on Init, exact counts: −4.79 % of the instructions for `CTL` alone, −5.77 % with minimum
    lengths for every array;
  * on the default set (quiet, interleaved): −3.6 % of the cycles and −2.4 % of the wall time for
    `CTL` alone;
  * on Init the wall time moves by −1.3 to −4 %, but those rounds were noisy.
* Minimum lengths for the other arrays add little. A per-function base register (b, function-wide)
  is worth at most 0.7 % of the instructions, and the hottest functions have no free register for
  it.
* The dense layout and the single array space buy no speed. They shrink the table and the region,
  and they are the place where the hints live.

## 1. Where the array costs are (exact counts, Init)

The tool is `_tmp/dense/scripts/arrprof.py`. It reads hashtpl's block profile of the unchanged
`checker.s` (`asmprof.py`, Init `init435.ndjson`, 273.416 G instructions). It maps each
descriptor displacement back to its array through today's layout (`wpos`). A check is a `cmp`
followed by `jbe`/`jae ca_error`. "Constant" means an immediate index.

| | executed | share of instructions |
|---|---:|---:|
| constant-index checks | 5.168 G (2 instructions each) | 3.8 % |
| variable-index checks | 8.117 G | 5.9 % |
| array-base loads (`movq D(%r15), r`) | 12.533 G | 4.6 % |

Per array (top of the list; G = 10⁹ executions; "k" is the largest constant index executed):

| array | const checks | var checks | base loads | k |
|---|---:|---:|---:|---:|
| `CTL` | **3.826** | 1.611 | **5.437** | 240 |
| `ASLOT⟨t⟩` | 0.492 | 0.614 | 1.106 | 1 |
| `ILMEMO` | 0.355 | 0.726 | 1.082 | 2 |
| `AREC⟨t⟩` | 0 | 1.063 | 1.063 | |
| `SPN` | 0 | 0.695 | 0.612 | |
| `ADER⟨t⟩` | 0 | 0.427 | 0.427 | |
| `IN` (bytes) | 0 | 0.666 | 0 | |
| the other memos (`WSM`, `LPMEMO`, `CRM`, `INM`, `DEM`, `WKM`, `WCM`, …) | 0.27 in all | | | 0–2 |
| the other slot tables `X⟨t⟩` | 0.15 in all | | | 1 |
| `PINS` | 0.069 | 0.044 | 0.113 | 54 |

Three kinds of array have constant indices:
* `CTL`, with 1 010 check sites. These are the counters, tops, flags and epochs that every store
  and memo reads.
* The memo region headers `A[0..2]`.
* The cons tables' tier headers `X⟨t⟩[0..1]`.

**Hoisting bases** (`hoist.py`): for each function and array, keep the base in a register from the
function's entry, and count `max(0, loads − calls)`. The upper bound is 6.34 G, of which `CTL` is
2.59 G. Without `CTL`, and only in functions that leave a register unnamed (one array per free
register), the bound is **1.87 G (0.68 %)**. The three largest candidates (`app_find`,
`ilm_put`, `app_push`, 1.3 G together) already use all of `rbx r12 r13 r8–r11`.

## 2. The dense layout (absarrays batch 7)

### 2.1 Shape

Today the compiler maps arrays through `curNum`/`wpos` (`Compiler/Compile.lean`, `Tab.wl`). There
are `nw = 388` positions, and every number below `wK = 132` gets a tier-1 position whether the
array is tiered or not. Batch 7 replaces `Tab.wl` and `Tab.bl` by a layout read from the table:

* `Tab` gets a field `wmap : NTree` (code `2·arr + hi` ↦ position, the same search tree as
  `Prog.nrt`). It also gets the position count and the inverse list `wat : List TieredArray`,
  which the stubs walk instead of `wposInv`. `checkerTab` is a literal (`tab_lit%`, as today),
  generated from `checkerArrays`. The rows come in table order, a tiered row takes two adjacent
  positions, and a "hot" row (§3) comes first.
* `dom64 s := (wmap.find s.code).isSome`, `pos64 s := (wmap.find s.code).getD 0`. These are the
  same `WLay` fields (`pos_lt`, `pos_inj`, `adj`). They are proved once from a `Bool` check of the
  literal (`Tab.wmapOk`: the positions are a permutation of `[0, nw)`, and tier 1 sits at tier
  0's position plus 1), by `decide +kernel`, then made `@[irreducible]` as today (absarrays §8.4).
  No simulation proof reads a position today, so none changes.
* Count on master: 127 word arrays, 54 of them tiered, so **181 positions instead of 388**. The
  region needs 2 + (nb − 2) + 181 = 183 slots: `ca_region_size` goes from 13 400 297 963 536 to
  6 287 832 121 360 bytes (12.19 → 5.72 TiB). The descriptors take 2 944 bytes instead of 6 256.
  absarrays counted 115 arrays and 169 positions. The table has grown since.
* `abiSlot64`, `abiVals`, `seqVals` and `parDescB` iterate positions through `wat` instead of
  `wposInv`. `tierOff`, `wpos`, `wposInv`, `curNum` and `SeqLayout`'s `< tierOff` premises are
  deleted.

### 2.2 Kernel cost of the lookups

The code generator evaluates `pos64` at every descriptor reference. `checker.s` has 14 450 word
descriptor references and 792 byte ones, spread over 10 `AsmPart`s that take 15–21 s each. The
micro-benchmark (`kern/`) evaluates `(sites.map pos).sum` by `decide +kernel` over the 14 450
actual sites, with `profiler` on, in a small file:

| | kernel type checking |
|---|---:|
| the sum over `s.arr` (no lookup: traversing the list) | 8.8 s |
| today's `pos64` (`wpos ∘ curNum`) | 8.96 s, 9.1 s |
| a balanced `NTree` over the 181 codes | 9.04 s, 9.2 s |

Each lookup costs about the same as today's arithmetic: 0.2–0.4 s per 14 450, against about 180 s
for all `AsmPart`s. **Kernel cost: below 0.3 %.** absarrays' fallback (a closed form over a dense,
tiered-first numbering) is not needed.

### 2.3 Effect on `checker.s`

All of it is regenerated: every displacement changes, and so do the descriptor stores in the three
stubs (one store per position) and `ca_region_size`. Instruction shapes stay the same, so the
instruction count changes only in the stubs (about 2 × 207 fewer table words per entry, once per
run). No speed effect is expected beyond cache footprint: the descriptors shrink from 98 to 46
cache lines, and with a hot-first order the descriptors of `CTL`, the memos and the `app` tables
fit in two lines. This is not measured separately, because the table-relative `CTL` of §3(b)
takes most of the hot descriptor traffic away. All `AsmPart`s are re-checked, about 180 s of
kernel time, as for any compiler change.

## 3. Registration hints as compiler features

Each hint is a field of the table row (`declare_arrays … : word tiered min 256 at table`, or
similar) that the compiler copies into `Tab`. **The trust rule:** a hint never becomes an
assumption. It either changes only where the compiler puts an array, or it is a fact the entry
stubs establish and `sim_abiStub`/`Final` prove. L's semantics and every proof above the compiler
stay as they are: L still checks every access, and the compiler proves that the check cannot fail.

### (a) Minimum length

**Design.**
* The row carries `min k`; the table gets `Tab.min64 : TieredArray → Nat`, the same `k` for both
  tiers.
* `compile_correct` takes one new premise, `G.MinOk tab.min64`: every array the program may name
  has at least `min64 s` words in the machine layout. This is a fact about the `Layout` `G`, which
  is fixed for the run, so no simulation step has to preserve it.
* `MemRel.size64` turns it into `min64 s ≤ (m.arr64 s).size` (`MemRel.min_le`).
* `genLd`/`genSt`/`compileE` (constant index `k`): when `k < min64 a` (for a tiered access, both
  tiers), emit `mov d, [bs]; mov d, [d + 8k]` without the `cmp`/`jbe`.

**Who establishes the minimum.** The stubs, not the harness, and the theorem does not assume it:
* `ca_setup`: every word array gets `abiWords = 2^32` words (`abiLayout`'s `s64 _ := abiWords`),
  so the premise is `∀ s, min64 s ≤ 2^32`, a `decide` on the table (`abiLayout_minOk`, proved in
  the sketch).
* `ca_check_seq`: `OUT` and `CTLF` get 0 words and `HDRF` gets `hw = 132`. Their minima must be 0
  (respectively ≤ 132), a `decide`. Every other array keeps its 2^32 words.
* `ca_check_b`: an owned array gets 2^32 words, and an array outside the frozen and owned lists
  gets 0, so its minimum must be 0. A frozen array's length comes from the buffer. For a frozen
  array with a minimum (the slot tables' tier 0, `PINS`), the stub compares the buffer's length
  with the minimum and declines below it (`rdx = 1`, never accept). `bufLayout`'s premise then
  holds on the path that enters. This adds 3 instructions per such array per thread call. An
  alternative is to prove the buffer's lengths from `par_compact`'s semantics; it costs more and
  gains nothing.
* `cap_check` keeps its L-level checks (`ctlMin = 256`, `consMinWords`). They stay the L-side
  facts the refinements use. The compiler does not use them.

**Proof shape** (`_tmp/dense/proto/MinProto.lean`, checked against master's `SimGen`, no
`sorry`):
* `Layout.MinOk`, `MemRel.min_le`, `ld_ok_of_min`, `abiLayout_minOk`: 4 lines each.
* `ldMin_spec` is the constant case of `genLdW_spec` with the `ev_cmpAI`/`ev_jcc` steps removed:
  `ev_movRA`, `ev_movRM` and the address arithmetic, 15 lines. At the use site, `genLdW_spec`'s
  constant branch splits on `k < min64 a` and passes `ld_ok_of_min` as the bound.
* The tiered case uses the same lemma at `tierA a u`, since the minimum is per array.
* Estimate: `genLd`, `genSt`, `compileE`'s and `compileS`'s constant arms in `SimGen`/`SimExpr`/
  `SimStore` (about 6 arms, 30–60 lines each, mostly deletions of the error branch); the premise
  through `Correct`/`compile_correct_frame`/`enter_core`; the three stub proofs (`abi_harness`,
  `seq_*`, `buf_*`; the `ca_check_b` check is the largest piece, about 150 lines). **About
  +400–600 lines, 8–12 agent-hours.**

**Measured gain** (§4): for `CTL` alone −2.80 % of the instructions, and for every constant-index array −3.78 %.

### (b) Hot array bases

There are two forms.

**Program-wide, table-relative (recommended, for `CTL`).**
* The table's slot 0 is 2^35 bytes, and the table uses 44 856 bytes of it, the constant data
  included. A row marked `at table` (with a static size, see (d)) is placed in slot 0 just past
  the save area, at `T + c` with `c < 2^31`.
* The code addresses it from `r15`, which is already pinned: `mov d, [r15 + c + 8k]` for a
  constant index (one instruction instead of four, with the minimum of (a)), and
  `cmp i, [len]; jae; mov d, [r15 + c + 8i]` for a variable index (no base load).
* No register is reserved, so the leaves' nine registers (leafgen R) and calleesave's contract are
  unaffected. The descriptor still holds the base, so block copies and the stubs need no special
  case.

The correctness argument:
* There is one more `Layout` premise, `G.b64 (pos s) = G.T + c` for each table-relative array.
  `MemRel` does not change.
* `ldTab_spec` (sketch, 12 lines) reads `[r15 + c + 8k]` as `(m.arr64 s)[k]` through
  `Inv.r15` and `MemRel.get64`.
* `Layout.Ok` stays as it is: the array is just another region, disjoint from the table words
  (`tab_arr`), the save area, the stack and the other slots. The stub proofs get one region inside
  slot 0 instead of one slot.
* `CTL`'s length becomes a static 256 words. Everything L needs (`ctlMin = 256`) still holds, and
  `cap_check`'s `CTL` test still passes. The prototype runs every fixture with `CTL` at 256 words
  and gets the same verdicts.

This is the only form that gets `CTL`'s 5.44 G base loads (§1). A function-wide register catches
only 2.59 G of them, because most functions read `CTL` once or twice per call.

**Function-wide (not recommended now).**
* This means a base register per function and array, loaded once and live across the body: a
  register the allocator gives up (`Ctx` gets a `breg : List (TieredArray × Reg64)`, and `Inv`
  gets "`r` holds `b64 (pos a)`", kept by every step that does not write `r`).
* For leaves this competes with the nine local registers. For non-leaves, `rbx r12 r13` survive
  calls (the callee-saved contract of calleesave). Then the trampoline's restore is also the
  invariant's frame, which needs a `FunSim` post that keeps them. Today `FnSimAt` lets a callee
  clobber them, so this is the larger proof change.
* Upper bound 1.87 G (0.68 %) of the instructions (§1), and the base loads it removes are L1 hits.
  hashtpl's measurement suggests that checks and loads of this kind cost about a quarter of their
  instruction share in cycles, so expect at most 0.2–0.3 % of the wall time.

### (c) Never-tiered arrays

This needs no new hint: the table's `tiered` column already says it. Under `curLay` every number
below `wK = 132` gets a tier-1 position, which accounts for 78 holes among the low numbers. The
rest of the 388 − 181 = 207 holes come from the gap between `wK` and the tier-1 range. The dense
layout (§2) gives a non-tiered array one position, and `Prog.wf` already rejects a tiered access
to it (`dom64 (tier1 a)` is false). There is no speed gain, only the smaller table and region.

### (d) Per-array sizes

* Today every array gets one 2^35-byte slot (2^32 words). A size column would give the stub a
  prefix-sum layout: `b64 p = base + off p` and `s64 p = size p`. `Layout.Ok`'s disjointness
  follows from the prefix sums being monotone, instead of from slot arithmetic.
* **The capacity motive is weak.** ROADMAP's known limits put the 2^32-word limit behind the 2^27
  node cap (`EREC` reaches it at about 2 300× Init). A uniform larger slot exceeds the address
  space. Only a per-array exception (the pool at 2^40 words) would matter, and nothing is near it.
* **What does matter** is the special case "static small size", which the table-relative `CTL`
  of (b) needs: a size of 256 words, inside slot 0. That much is part of (b). The general form can
  wait until a capacity needs it.

## 4. The speed prototype

`_tmp/dense/scripts/rewrite.py` is an unproved rewrite of `checker.s`, for measurement only. Two
rewrites:

* **min** drops `cmpq $k, LEN(%r15[,%t,8]); jbe ca_error`:
  * `minctl`: only `CTL`'s checks with `k < 256` (1 010 sites);
  * `minall`: every constant-index check except on `OUT`, `CTLF`, `HDRF` (1 676 sites). In
    `ca_setup` and `ca_check_seq` all other arrays have 2^32 words. This is the most a minimum
    length can give.
* **tbl** places `CTL` at `T + 65536`, inside the table's slot, with a length of 256 words. The
  three stubs' `CTL` descriptor stores are changed (6 words). Each `movq 64(%r15), %R` is folded
  into the next instruction's address (`N(%R)` → `65536+N(%r15)`, `(%R,%i,8)` →
  `65536(%r15,%i,8)`), 1 356 sites. The two block copies that use the base as a value get
  `leaq 65536(%r15), %R`. `tbl` includes `minctl`, and `tblall` includes `minall`.

**Verdicts:**
* `scripts/diff-e2e.py --bin X --parallel 16`, for `minctl`, `minall`, `tbl` and `tblall`:
  634 fixtures, all agree (406 accepted, 228 not), no crash.
* `tblall` with `--jobs 4` (the threads, `ca_check_b` with the table-relative `CTL` in each
  worker's slot 0): 634 agree.

**Exact instruction counts** (Init, `perf stat -e instructions:u`, one run each):

| variant | instructions | Δ | predicted from §1 |
|---|---:|---:|---:|
| master | 273.416 G | | |
| `minctl` | 265.764 G | −7.652 G (−2.80 %) | 2 × 3.826 = 7.65 G |
| `minall` | 263.079 G | −10.337 G (−3.78 %) | 2 × 5.168 = 10.34 G |
| `tbl` (= `minctl` + table-relative `CTL`) | 260.328 G | −13.088 G (−4.79 %) | 3 × 3.826 + 1.611 = 13.09 G |
| `tblall` | 257.643 G | −15.773 G (−5.77 %) | 13.09 + 2 × 1.342 = 15.77 G |

The counts match the static prediction from the profile to within 0.01 G. The rewrite does what
§1 says, and nothing else moves.

**Wall time and cycles** (`scripts/bench.py --set init --reps 5`, then `--set default --reps 3`,
interleaved, `--cpus 40,41`, `--no-conron --no-ref`). The coordinator held the merge queue and the
other lanes' builds for the run. The load average was 11 at the start, 7 between the two sets and 4 at the end (bench.py reported load 7 and 4 when each set started). Logs and JSON are in `_tmp/dense/bench*`.

Init, 5 interleaved rounds. The rounds were noisy (spread 8–13 %; two of master's rounds ran
at 22.8 s), so the minimum is the measure here, as in perfgap and hashtpl:

| variant | instructions | cycles, min (median) | wall, min (median) |
|---|---:|---:|---:|
| master | 273.416 G | 88.0 G (98.6 G) | 19.92 s (22.29 s) |
| `minctl` | −2.80 % | 86.8 G (91.2 G), −1.4 % | 19.64 s (20.63 s), −1.4 % |
| `minall` | −3.78 % | 86.8 G (92.5 G), −1.3 % | 19.67 s (20.90 s), −1.3 % |
| `tbl` | −4.79 % | 86.9 G (91.5 G), −1.3 % | 19.67 s (20.68 s), −1.3 % |
| `tblall` | −5.77 % | 84.5 G (90.2 G), −4.0 % | 19.14 s (20.37 s), −4.0 % |

The default set (13 fixtures, 3 interleaved rounds, spread ≤ 2 % on the long fixtures). Geometric
means of the ratio to master:

| variant | instructions | cycles (median) | wall (median) |
|---|---:|---:|---:|
| `minctl` | 0.974 | 0.988 | 0.992 |
| `minall` | 0.964 | 0.974 | 0.980 |
| `tbl` | 0.959 | 0.964 | 0.976 |
| `tblall` | 0.948 | 0.959 | 0.975 |

The three longest fixtures, wall median, master → `tbl` → `tblall`:
* `complete_c04a_restart_70`: 2.415 → 2.334 → 2.323 s (−3.4 %, −3.8 %);
* `beta-ladder`: 2.460 → 2.427 → 2.421 s (−1.3 %, −1.6 %);
* `let-ladder`: 1.012 → 0.989 → 0.974 s (−2.3 %, −3.8 %).

**Reading.**
* Unlike the template's checks in hashtpl (1.1 % of the cycles for 4 % of the instructions), this
  change converts well. The table-relative `CTL` saves 2.4–3.6 % of the cycles and wall time on
  the quiet default set, and 1.3–4 % on Init (noisy).
* Most of it is the `CTL` part (`tbl`). The other arrays' minimum lengths (`tblall` − `tbl`) add
  about 1 % in instructions and 0–1 % in time.
* The minimum length alone (`minctl`) gets about a third of `tbl`'s time gain on the default set.
  The removed base loads (a dependent load before each `CTL` access) matter more for time than
  the removed checks (predicted, fused branches).

## 5. Byte and word arrays as one array space

**Semantics.**
* L's `Mem` keeps two typed maps, `bytes : ArrId → Array UInt8` and
  `words : TieredArray → Array Word`. One map over a sum type would turn every `arr8`/`arr64`
  read into a case analysis (absarrays §8.3).
* What becomes one is the **name space and the registry**: a name is a byte array or a word array,
  never both.
  * Today `IN` and `POOL` are both `0`. Byte arrays get numbers of their own, from one sequence
    with the word arrays.
  * `ArrTable.wf` checks distinctness over all rows.
  * `Prog.wf` checks the kind: `ld8 a` needs `kind a = byte`, the word operations need `word`.
* Above L nothing changes except numerals:
  * the 259 `arr8 IN` reads, the 56 `ld8` lines and the 26 `st8` lines read names;
  * the remaining positional sites (`bytes.set! 0`, `arr8 0`; 22 in `PreludeSim`'s
    `setIn`/`Keep`) take the name;
  * the test builders of absarrays batch 2 take the rest.

**Compiler.**
* One layout map `Lay` with `kind : Name → Kind` and one position space. Every position has a
  base column and a length column, so byte descriptors stop being interleaved pairs.
* `Layout` gets one `b s : Nat → Nat` family with an element width (`1` or `8`). `Layout.Ok`'s
  three disjointness fields (`arr8_disj`, `arr64_disj`, `arr8_64`) become one, and `InArr` loses
  a case.
* The ABI's fixed positions become `abi : pos IN = 0 ∧ pos PB = 1`, which only `AbiSim` and
  `Final` use (absarrays §8.3).
* The count on master is about 10 compiler and `Final` files: `In8`/`In64` 31 lines,
  `b8`/`s8` 43, `dbase8`/`dlen8` 35, `pos8`/`dom8` 94, plus the stub generators.

**Stubs.** The byte descriptors move into the shared columns: the input and the pin data at
positions 0 and 1, then the rest in layout order. `abiVals`, `seqVals` and `parDescB` lose their
byte loops.

**Scanner proofs.** No change. The scanners (`Front/`, `PreludeSim`) are proved against `arr8`,
`ld8` and `scan8`'s semantics, which keep their types. Their churn is the numerals above.

**Gain.** None in speed: byte accesses are 0.67 G variable-index checks on `IN` and no constant
ones. The gains are uniformity (one disjointness family), the hints for byte arrays too, and one
fewer layout map. It changes byte displacements in every scanner function, so it belongs in the
same `checker.s` regeneration as the dense layout.

## 6. Plan

| # | batch | what | agent-h | proof lines | `checker.s` |
|---|---|---|---|---|---|
| D1 | **minimum length (a)** | `min` column, `Tab.min64`, `MinOk` premise, the constant arms of `genLd`/`genSt`/`compileE`/`compileS`, the stub proofs (`ca_check_b`'s length check) | 8–12 | +400–600 | every function with a constant-index access; `ca_check_b` |
| D2 | **table-relative `CTL` (b) with its static size (d′)** | `at table` rows placed in slot 0 past the save area; `Layout` premise `b64 (pos s) = T + c`; `ldTab`/`stTab` arms (constant and variable index); the three stubs and `abiLayout`/`seqLayout`/`bufLayout`'s regions | 12–18 | +600–900 | all `CTL` accesses (1 356 sites), the stubs |
| D3 | **dense layout** (absarrays batch 7) | `wmap` literal from the table (tiered rows adjacent, hot rows first), `wmapOk` by `decide +kernel`, `wat` in the stubs, delete `tierOff`/`wpos`/`curNum` | 8–12 | ~500 changed, −100 net | full regeneration |
| D4 | **one array space** | one registry and number space, `Prog.wf` by kind, one layout map with kind, one descriptor family, one disjointness field | 10–15 | ~700 changed, −100 net | full regeneration (byte displacements) |
| D5 | function-wide base registers (b) | `Ctx.breg`, `Inv` field, allocator, the `FunSim` contract for callee-saved registers | 20–30 | +1 000–1 500 | hot functions |
| D6 | general per-array sizes (d) | prefix-sum layout in the stubs, size column | 8–12 | +300 | stubs only |

**Order.** D1, then D2 (D2 uses D1's minimum for `CTL`'s constant indices; together they are
the measured gain). D3 and D4 change the same stub loops and the same displacements, so they land
as one regeneration (or D3 first, then D4) after D1/D2. D1 and D2 do not depend on the layout map's
representation. They touch `genLd`/`genSt` and `SimGen`/`SimStore`, which no running lane edits.
mgen2's files (`L/ModelGen.lean` and the model conversions) do not intersect any batch.

**Risks.**
1. *Kernel cost of the dense map:* measured, below 0.3 % (§2.2).
2. *`ca_check_b`'s buffer lengths:* the stub check could decline a run that is fine today if
   `par_compact` writes a frozen slot table shorter than its minimum. The minima are 2 (slot
   tables) and 55 (`PINS`), against extents of at least `consMinWords = 18`. Run `diff-e2e.py
   --jobs 4` on every fixture before landing.
3. *`CTL` at a static 256 words:* any variable index ≥ 256 would now abort (`oob`) where today it
   reads a zero word. Every fixture agrees with the prototype. A proof-level guard is
   `cap_check`'s `ctlMin = 256`, which already assumes nothing beyond 256. Check that the generated
   `CTL` indices (the schemas' `cs` fields, `fzCtl`) are below 256 by a `#guard` over the table's
   schemas.
4. *Register pressure:* none for D1–D4. D5 has it.
5. *Merge pressure:* D1/D2 touch `SimGen`, `SimStore`, `SimExpr`, `Correct` and the stub proofs.
   That is narrower than leafgen G2, and every `checker.s` change is a regeneration.

**Go/no-go.**
* (a) minimum length: **go**, as part of D2 for `CTL`. On its own it gives about 1 % of the time. Minima for the other arrays (memo headers 3, slot tables 2, `PINS` 55) are worth another 1 % of the instructions and 0–1 % of the time. Include them only if `ca_check_b`'s length check is accepted (decision 2).
* (b) table-relative `CTL`: **go**. It is the largest single compiler lever found since leafgen: −4.8 % of the instructions, about −2.5 % of the wall time. It needs no register, and its proof is local (one `Layout` premise, the stubs' region inside slot 0).
* (b) function-wide registers: **no-go** for now (at most 0.68 % of the instructions, the hot
  functions have no free register, and it is the largest proof change).
* (c) never-tiered: **no separate work**. It is the `tiered` column, realized by the dense
  layout.
* (d) per-array sizes: **no-go** in general (not binding); the static-size special case goes
  with D2.
* Dense layout (D3): **go, but not urgent.** No speed gain is expected, the kernel cost is
  measured as negligible, and it is the cleanup that removes `tierOff`/`wpos` and halves the
  region. It is cheapest to do together with D4.
* One array space (D4): **go with D3** in the same regeneration, if the user wants the uniformity.
  It brings no speed.

## 7. Decisions for the user

1. **Table-relative arrays**: a new kind of placement (an array inside the table's slot, at a
   fixed offset from `r15`) for `CTL`. It is the biggest single lever found. Is a static `CTL`
   size of 256 words acceptable? L already requires at least 256 (`ctlMin`).
2. **Minimum lengths in `ca_check_b`**: a stub check on the frozen arrays' buffer lengths (cheap,
   proved locally). The alternative is a proof from `par_compact`'s semantics, which costs more
   and gains nothing.
3. **D3 + D4 as one regeneration**, after D1/D2, or not at all for now.
4. **Hint syntax** in `declare_arrays`: `min k`, `at table`, a `hot` order flag. The tiered flag
   exists already.

## 8. Journal of the implementation (lane dense-impl, D1 and D2)

The coordinator's decisions: `CTL` at a static 256 words; `ca_check_b` checks the frozen buffer
lengths in the stub; D3 and D4 later, as one regeneration; hints `min k` and `at table`, no `hot`.

### D1: minimum lengths (landed, #75)

* **Table.** `ArrDecl.min` (`… : word min k := n`), `ArrTable.mins` (keyed by
  `TieredArray.code`: tier 0, and tier 1 of a tiered row), `Tab.mins`, `Tab.min64`. A tiered
  access uses `Tab.min64t a`, the smaller of the two tiers. The minima in `Layout.lean`: `CTL`
  256, the memo headers 3, the slot tables 2, `PT0` 1, `PINS` 55, `HDRF` 4. Only arrays that
  `ca_check_b` gives memory (frozen or owned) can have one: the front end's arrays (`DECL`, `NIDS`,
  `HSEEN`, …) keep their checks.
* **The premise.** A new field `Layout.Ok.min64 : ∀ s, dom64 s → min64 s ≤ s64 (pos64 s)`. It is a
  field of `Layout.Ok`, not a separate hypothesis: every simulation lemma already takes
  `hG : G.Ok`, and the stubs already prove `Layout.Ok`. The final theorems are unchanged.
* **Code.** `genLd`/`genSt` take the minimum; a constant index below it emits the base load and the
  access without `cmp`/`jbe` (`genLdW_spec`, `genSt_tailWKm`, ~60 lines).
* **Discharged by the stubs.** `ca_setup`: every array has `abiWords` words, and `abiTabOk` checks
  every minimum below `2^31` (`abiTabOk_min`). `ca_check_seq`: `seqParamsOk` checks
  `min64 OUT = min64 CTLF = 0` and `min64 HDRF ≤ 132`. `ca_check_b`: `bufMinOk` (a `decide +kernel`
  over the positions) checks that every array with a minimum is frozen or owned; the stub's new
  entry `bufMinStub` compares each frozen array's length word `buf[9 + 2i]` with its minimum
  (`cmpq $k, 72(%rdi); jb ca_abi_decline`, 21 pairs) and declines below it, before writing
  anything (`sim_bufMinChk`; the decline returns `rdx = 1` with the memory unchanged, so
  `EntryPost` holds). `abiB_outcome` is now the tests, then `abiB_go`, the old proof.
* **`checker.s`:** 1 483 `cmpq $k, …; jbe ca_error` pairs gone (the prototype's `minall` removed
  1 676, including the front-end arrays), `ca_check_b` gained the tests and a `jmp
  ca_check_b_go`.
* **Measured.** Init 273.416 G → 263.095 G instructions (−3.78 %; prototype `minall` 263.079 G).
  Default set, 3 interleaved rounds, load 14: instructions 0.966, cycles 0.978, wall 0.986.
* Proof lines: about +300.

### D2: `CTL` table-relative

* **Table.** `ArrDecl.atTable` (`… : word min 256 at table := 1`; at most one row, a non-tiered
  word array with a minimum, `ArrTable.wf`), `Tab.tbl = some (CTL, c)`, `Tab.tbl64`. The offset is
  `Tab.tblBase`: past the table (no entry arguments) and the 32-byte save area, rounded to 64
  bytes; for the checker `c = 44 864`.
* **The premise.** A second new field `Layout.Ok.tbl64 : ∀ s c, dom64 s → tbl64 s = some c →
  b64 (pos64 s) = T + c`. `MemRel` is unchanged; the disjointness fields cover the new region.
* **Code.** `genLdT`/`genStT` (and `genSt64` choosing between the two for `st64`): a constant index
  is `[r15 + c + 8k]`, an index in a register `[r15 + 8r + c]`; the bounds check stays for a
  variable index (against the descriptor's length) and for a constant at or above the minimum.
  The descriptor still holds the base, so block copies and the fallback `compileE` path are
  unchanged. New step lemmas `ev_stT`/`ev_stTI` (stores through `tdesc`). `genLdTW_spec`,
  `sim_genStT`, `stT_disp`, `stT_idx`: ~350 lines.
* **Discharged by the stubs.** `abiOff`/`abiSz`/`ownOff` give the table-relative array `base + c`
  and `min64` words in all three layouts; `abiTabOk` checks `tabBytes + 32 ≤ c` and
  `c + 8·min ≤ 2^31` (`abiTblOk`), `seqParamsOk` that `OUT`, `HDRF`, `CTLF` are not it,
  `bufMinOk` that it is owned and not frozen. The region proofs got one more case: its bytes are in
  `InTbl` (past the table and the save area, below `base + 2^31`), apart from the table, the save
  area, the stack, every slot and the buffers (`abiLayout_in64`, `seq_in64`, `buf_in64`,
  `own_bytes`). L's initial and zero memories give every array `abiSz` words (`loadMem b pb
  (abiSz tab)`, `zeroMem tab`; `InputsOK` only needs sizes below `2^64`). `CTL`'s own slot stays
  reserved and unused (D3 removes it with the dense layout).
* **`checker.s`:** every `CTL` access loses its base load (`movq 64(%r15), %R; movq N(%R), …` →
  `movq 44864+N(%r15), …`), the three stubs write `CTL`'s descriptor as `base + 44 864`, 256 words.
* **Measured.** Init 257.658 G instructions (−5.76 % against D1's base; prototype `tblall`
  257.643 G). Default set, 5 interleaved rounds (load low at the start): instructions 0.950,
  cycles 0.964, wall 0.979 against the base (D1 alone: 0.966 / 0.978 / 0.985). The Init wall
  rounds ran at load 89 (spread over 80 %) and say nothing.
* Verdicts: `diff-e2e.py --refs` and `--jobs 4`, 634 fixtures agree, for D1 and D2.
* Proof lines: about +700 (`git diff --stat` of the lane).
