# Lane `tierarr`: tiered arrays (journal)

Branch `tierarr`, worktree `_tmp/wt/tierarr`. Phase 1: design and an unproved prototype. Background:
con-ron's handles (`ConRon/Arena/Handle.lean`) carry the tier in bit 27, and the index points into
that constructor's array for that tier (`Tbl` per tier, `EStore.pers`/`.scr`). L copied the handle
encoding but keeps both tiers interleaved in one word array (record `i` of tier `t` at
`ra[i * 2w + t * w + f]`, slot `j` at `sa[2 j + t]`, columns `col[2 c + t]`). This deviation is now
recorded as D34 in `docs/deviations.md`. It blocks the user's parallel design, because phase B
writes into every array that holds the frozen environment.

## 1. Design: tiered arrays as an L feature

**Semantics: nothing new in `Mem`.** Tier 1 of word array `a` is word array `a + tierOff`, a
program-wide constant (`tierOff = 256`; today's ids are all below 215). One tiered access chooses
the array from a run-time tier word:

```
tierA a t := a + tierOff * (t &&& 1).toNat
Expr.ld64t  (a : ArrId) (t i : Expr)     -- word i of array tierA a t
Expr.len64t (a : ArrId) (t : Expr)       -- len of array tierA a t
Stmt.st64t  (a : ArrId) (t i e : Expr)
```

Surface syntax: `AREC⟨t⟩.u64[i]`, `len(AREC⟨t⟩.u64)`, and for records `R⟨t⟩[i].f`. The tier is
masked rather than checked: `AREC⟨h >> 27⟩` takes the handle's bit 27 directly, with no `& 1` in
the source and no abort path. A constant tier is just the plain array (`ld64t a (const 1) i` =
`ld64 (a + 256) i`), so the compactor and the tests can still name one tier statically.

So the refinement proofs see **one array per tier**, which is con-ron's layout. A record is
`ra⟨t⟩[i * w + f]`, a slot is `sa⟨t⟩[...]`, and the tier never appears in an address. Two pushes
to different tiers write different arrays, so separating them is a `MemFrame` fact over array
ids, not address arithmetic (`Schema.ad_inj`'s tier half disappears).

**Compiler.** The descriptor of `a + 256` is `4096` bytes after that of `a`, so:

```
rdx := t ; and rdx, 1 ; shl rdx, 12
cmp rax, [r15 + rdx + len64(a)] ; jae ca_error
mov rcx, [r15 + rdx + base64(a)] ; mov rax, [rcx + rax*8]
```

This is three instructions more than a plain `ld64` when `t` is simple. The index arithmetic saves
about three (`i * 2 + f` instead of `i * 4 + t * 2 + f`), and the load needs no branch. The table
grows to `nw = 256 + (largest tiered id) + 1` descriptors (≈ 5 KB). The abi stub gives every id a
slot, so with ~300 ids the region is 10 TB of address space with `MAP_NORESERVE` (128 TB
available). Unused ids could instead get `(0, 0)` descriptors if address space ever matters.

**The compiler correctness statement does not change.** `Layout`, `Layout.Ok`, `MemRel` and
`compile_correct` are already stated per word array, with any bases, pairwise disjoint
(`Compiler/Rel.lean`). A tiered access is an access to array `tierA a t`, so the new proof
obligations are:
* `sim_ld64t`, `sim_st64t`, `sim_len64t`: the existing `ld64`/`st64`/`len64` cases plus one
  address lemma, `T + base64 a + 4096 (t & 1) = T + base64 (tierA a t)` under WF
  `a + tierOff < nw`.
* The structural functions: `tempsE`, `Expr.uses`, `Expr.roms`/`nglob`, WF/WFFast, `mapE`/`mapS`,
  `Expr.pval`/`evalE_spec`, ModelGen, and the write sets. `st64t a t` writes `{a, a + 256}`, or
  `{tierA a c}` for a constant tier `c`.
This is the obligation "once, in the compiler" that the user asked for.

**Entry stubs.**
* Sequential mode (`ca_start`): `abiVals` emits a slot for every id below `nw`, the tier-1 arrays
  included. Both bases lie in the one region, and nothing else changes.
* Entry 2 (sketch in §4): the descriptors of the frozen arrays point into the frozen buffer and the
  rest into the worker's own region. This is again just another `Layout`, and `Layout.Ok` needs
  only the buffer and the own region to be disjoint.

### How tiered arrays replace KSTP's in-array tier split

KSTP (lane kstp-proof) puts both tiers' slot tables in one array:
* meta words `2t`, `2t+1` at the front;
* tier 0 grows up from `4 + o₀` below `H = len/2`, and tier 1 grows down from `len - o₁` above `H`;
* each tier ping-pongs between offsets `0` and `2W`.

With a tiered slot array `sa⟨t⟩`, both tiers use **one formula**: meta words `0, 1` (that tier's
`n − SN0` and `o`), the table at `2 + o`, ping-pong `0 ↔ 2W` upward. Several things disappear:
* the `len - o₁` mirror arithmetic, the `H` bound and its region-disjointness obligations;
* the split capacity: each tier gets the whole array (2^32 words) instead of half.

The template change is local: KSTP's per-tier base (`r_t`) becomes the constant `2 + o`, and
`sa[...]` becomes `sa⟨t⟩[...]`. Request to kstp-proof: keep the tier-dependent base behind one named
function and model (`ksBase t`), so that the swap later touches only that function and its
lemmas. KSTP's other ideas are independent of this layout: the key word in the slot, growing only
the pushing tier, and no record reads in find.

### The limb pool

`POOL` is not tier-split today: it is append-only (D10), `scratch_reset` never restores `CTL[0]`,
and promotion makes persistent records share scratch-allocated slices (`Promote.peLit`, `pnArm`
pass `(o, l)` straight on). Tagging slices by the scratch flag is therefore wrong. Proposal: the
**pool tier is the phase, not the scratch flag**, and it is encoded in the offset:
* A slice's offset carries its tier in bit 40.
* Allocation uses `top⟨P⟩` with `P` a control word: `0` in sequential mode and in entry 1, `1` in
  entry 2.
* Reads are `POOL⟨o >> 40⟩[o & (2^40 − 1)]`.

In sequential mode every slice stays in tier 0, so the behaviour is today's. Entry 2's
allocations land in its own `POOL⟨1⟩`. This is the same compiler feature, with the tier
expression taken from the index. The proof side reads slices through one accessor
(`pv (m.arr64 (tierA POOL (o >>> 40))) …`) instead of `pv (m.arr64 POOL) o l`, which touches
every nat, name and level-list proof. That is the second-largest item in the cost estimate below.

## 2. Prototype (unproved): the app store, as a storage permutation

To measure layout and codegen without breaking the build, the prototype does not touch
`L/Syntax.lean`, the compiler or the store library. `ConAgua/Proto/TierCompile.lean` (not in the
lake globs; run with `scripts/lake env lean --run ConAgua/Proto/TierCompile.lean OUT.s`, ~10 s)
contains:
* A copy of `Compiler/Compile.lean` (namespace `L.CompilerT`). Its `ld64`/`st64` arms emit the
  tiered code above for carrier array ids `≥ 4096`.
* `tierify : Prog → Prog`. For each configured array (`TIER_ARRS="4:2,5:1"`: id and interleave
  width `w`) it maps every access to the interleaved index `E` to tier `(E >> log w) & 1` and word
  `(E >> (log w + 1)) * w + E mod w` of that tier's array. The hot shapes `X * 4 + T * 2 (+1)`
  and `J * 2 + T` are matched syntactically: tier `T`, index `X * 2 (+1)` / `J`. Other shapes are
  shuffled bitwise; a store with such an index gets two fresh locals. `len64 a` maps to `2 ×` the
  tier array's length.
* This is a bijection of the storage, so the binary behaves exactly as master. What it measures is
  the real feature's memory layout and an upper bound on its instruction cost: unmatched shapes pay
  for the shuffle, which the real source would not compute.
* With `TIER_ARRS=""` the output is byte-identical to `asm/checker.s` (checked).

Variants: `base` (master `ddbf054e`), `tier45` (AREC w=2, ASLOT w=1: 53 accesses on the fast path,
16 bitwise), `tier45d` (ADER, the app derived column, w=1, added: 55 / 18). Binaries:
`_tmp/tierarr/{base,tier45,tier45d}`. `_tmp/tierarr/main_pages.c` is `harness/main.c` plus a
`mincore` count of each listed array's resident pages after the run (`CA_PAGES=4,5,…`;
`CA_NOTHP=1` turns off THP so that pages are 4 KB).

### Verdicts

`bench.py --set all --reps 0 --no-conron --no-ref` (675 fixtures, three binaries): all 675 agree, base = tier45 = tier45d on every fixture (408 accept, 261 error, 3 reject-front, 2 timeout, 1 exhausted: `stack_fuel_offset`, as on master). The bijection with the bigger per-tier capacities lets `stack_fuel_offset` grow to ~9–10 GB before `app_push`'s 2^27 limit (base stops earlier), so with tiered arrays the e2e memory guard matters more. Log: `_tmp/tierarr/verdicts.log`.

### Touched pages (4 KB, THP off) and peak RSS

| fixture | array | base | tier45: tier 0 + tier 1 | tier45d |
|---|---|---:|---:|---:|
| `app-lam` | AREC (4 / 260) | 249 969 | 134 + 124 985 | same |
| | ASLOT (5 / 261) | 262 145 | 80 735 + 131 073 | same |
| | ADER (42 / 298) | 119 567 | (untiered) 124 985 | 67 + 62 493 |
| | **max RSS** | **3.18 GB** | **2.52 GB** | **2.27 GB** |
| `eager_open_nat_control` | AREC | 79 691 | 72 + 39 846 | same |
| | ASLOT | 131 073 | 40 759 + 65 537 | same |
| | ADER | 39 846 | 39 846 | 36 + 19 923 |
| | **max RSS** | **1.19 GB** | **0.93 GB** | **0.85 GB** |
| `c04a_restart_70` | AREC | 13 564 | 198 + 6 782 | same |
| | ASLOT | 16 385 | 8 187 + 8 193 | same |
| | ADER | 6 782 | 6 782 | 99 + 3 391 |
| | **max RSS** | **573 MB** | **546 MB** | **534 MB** |
| `irrel_commit` | AREC / ASLOT | 144 / 257 | 72+1 / 128+119 | |
| | max RSS | 17.8 MB | 17.8 MB | 17.7 MB |

Separate tiers halve the record array exactly, as appcap.md predicted: interleaving makes the
scratch tier touch both tiers' lines. For `app-lam`, 488 MB of `AREC` is saved and, with ADER,
another 244 MB. The 25 % RSS cut comes from just two arrays of one store. Per tier,
`eager_open_nat_control` now needs 2^25-word record arrays and `app-lam` 2^26, where the
interleaved layout needed 2^27.

ASLOT stays the same size in the prototype because the bijection keeps master's shared slot
count. The tier-0 table's pages are partly untouched only because tier 0 is sparse. With KSTP's
per-tier `n_t` on tiered arrays, tier 0 would stay at its own small size: tens of pages here
instead of 40–80 K.

### Speed

RESULT_BENCH

## 3. Inventory: the interleaved layout outside the store library

Library = `StoreLib`, `ConsLib*`, `SlotGrow*`, `StoreRel`, `Arena/*Store.lean`. Counts are from
grep; multi-line index expressions are missed, so they are lower bounds.

**L code: ≈ 400 interleaved accesses in ≈ 150 FunDecls, 32 files**, plus 291 tier-count reads
`CTL[NN + t]` and 171 handle decodes `(h >> 27) & 1`. By array: FAREC 59, LEREC 48, AREC 46,
CREC 45, PJREC 43, LAREC 40, REC 29, FVREC 15, SOREC 9, NSREC 8, BREC 8, DER columns 3–4 each,
hash columns 1–4 each, level/name/ls stores 1–3 each.
* **Generic views and decoders (first to go behind accessors):**
  * `IndIface.eView` decodes every expression kind, with 7 precomputed `k := x * 4 + t * 2`;
  * `ExprMk.derB` (all DER columns and hash columns) and `ExprMk.mk*`: `q := idx * 2 + tier`, plus
    `CTL[4] + CTL[5]` sums of both tiers' counts;
  * `LevelHeap.lvNode`, `LevelEquiv.lsNode`, `WhnfIota.exprViewOkL` (`CTL[c + t]`),
    `WhnfM2C.m2cConstViewL`;
  * `Checker/Entry.isProjFnShapeL` and `Front/IndApply.nameRecPre` (name decoders).
* **Walk dispatchers**, one copy per walk, 10 count checks each: `Walk.bbNode`,
  `WalkLeaves.flNode`/`lsbNode`, `WalkScope.wsNode`, `FVarRange.frNode`, `Lift.liftGo`,
  `WalkLift.i1lGo`, `Hoist.hoistWalkL`, `InstLP.lpGo`.
* **Per-kind arms** (2–3 accesses each): `Abs1.abs*`, `ArRange.ar*`, `Inst1.inst*`, `InstList.il*`
  / `ilg*`, `InstLP.lp*`, `Lift.lift*`, `WalkLift.i1l*`, `Hoist.hoist*L`.
* **Point readers:**
  * `DefEq` (43; `defeqProjPairL` reads under two tier variables);
  * `Infer` (17), `InferBody*`;
  * `WhnfDelta` (19), `WhnfCore`, `WhnfIota*`, `WhnfSpineArgs`, `WhnfCoreApp*`;
  * `PropRead` (12), `StrLit.strLitCtorL`, `Promote.pnArm`/`peLit`.
* **Store-adjacent:** `LpCol` (`hpBlk*`, `lsBlkC`, `lpBlkF`: the hash- and derived-column blocks
  spliced into the pushes; these move into the library).

**Proof side: ≈ 1 100 lines with raw `rdW (m.arr64 X) (… * N + …)`** in 97 files, and 506 lines with
raw count terms `rdW (m.arr64 CTL) (NN + t)`. The largest:
* InstList 74, WalkLeaves 54, ArRange 52, DefEqLeaves2 49, Abs1 48, DefEqLeaves 42,
  WalkLiftRefine 41, View 40, LiftRefine 39, WhnfDeltaRefine2 34;
* the views `View.lean:180–240`, `IndView.lean`, `ViewL.lean:32`, `LevelView.lean`;
* the columns `DerRelBase`, `DerRel`, `LpColRel` (literal `* 2 + 0` / `* 2 + 1`);
* named raw accessors outside the library: `lsO`/`lsL`, `nsQ`/`nsO`/`nsL`, `nnQ`/`nnU`,
  `ltK`/`ltO`/`ltL`, and the raw push model in `ExprMk.lean:206`.
Already through library accessors (fine): `fld` (48 lines), `Schema.ad` (36), `cntW`/`cntC`
(122), `slotW`, `pushRec`/`wrRec`. Each `*Refine.lean` has a bridge lemma `fld_X0 … = rdW (m.arr64
XREC) (i * 4 + t * 2)` after which downstream proofs use the raw form. These bridges are the
leaks: deleting them shows every dependent proof. `ArenaRel.lean` itself has no index arithmetic.

**Proposed accessors** (the user's rule: data structures behind L library functions plus abstract
predicates):
* L side: one macro per field, expanded inline so that it costs no call, e.g.
  `⟪appF h⟫ = AREC⟨h >> 27⟩.u64[(h & M) * 2]`, `⟪appA h⟫`, `⟪cnt app t⟫`, `⟪inTier app h⟫`
  (`idx < count`). Generated from the schema, like the ConsLib templates.
* Proof side: `fldH S m h f` (field `f` of the node handle `h` names), `cntW S m t`, `nodeOK S m h`.
  Each comes with one evaluation lemma from the library, and nobody outside the library unfolds
  them.
Doing this first, on today's layout, makes the switch to tiered arrays a library-only change. It
is also the user's encapsulation requirement independently of this lane.

## 4. Compaction (entry 1's tail) and entry 2's descriptors

**Which arrays are frozen.** Tier 0 of every store (records, slot tables, DER and hash columns),
`POOL⟨0⟩`, and the arrays phase B only reads: the environment index (132–137), `PINS` (128), the
declaration records phase B reads, and the control words. lane parallel's write-set analysis
(`closedG`, `GSetSplit`; phase B writes no global) lists the rest. Everything else lives in the
worker's own region: tier 1, memos, caches, stacks, scratch heaps and the worker's `CTL`.

**Entry 1 tail: `compact()`** (L, after `phase_a`). It writes into a new word array `OUT` (own
slot):
* header `[magic, k, (id₀, off₀, len₀), …]`;
* then each frozen array's live prefix `[0, eₐ)`, word for word. The extents: records
  `count₀ · w`, slot tables `2 + o₀ + 2 W₀` (KSTP meta at the front, so this is prefix-stable),
  columns `count₀`, pool `top₀`, the env index's counters, `CTLF` = `CTL` (256 words).
It returns `len` in `rax`; the harness reads `OUT` at `ca_w0 + OUT · ca_slot`, copies it into a fresh
allocation, unmaps the region and `mprotect`s the copy read-only. Cost: one copy loop, about 10
instructions per word. Init's tier 0 is ~100 MB, so this is ≈ 0.15 G instructions against phase
A's 60 G.

**Entry 2 stub** `ca_check(frozen, frozen_len, j, region, region_len)`:
* size checks;
* for each frozen id, `base := frozen + 8 · hdr.off`, `len := hdr.len`. These are loads from the
  header, ≈ 60 × 4 instructions, straight-line;
* every other id gets a slot in `region`, as `abiVals` does;
* `MODE := 2`, `PJ := j`, `jmp ca_enter`.
The L entry `check_b` first copies `CTLF` into `CTL` and sets the pool phase `P := 1`. Then it runs
`check_pending(j, PVIS)` (lane parallel's `PhaseBStart.step`, with `PVIS` read from `CTLF`).

**Theorems.**
* (a) `compact` satisfies `OUT[offₐ + k] = m.arr64 a [k]` for `k < eₐ` (one generic copy-loop
  lemma).
* (b) The phase-A invariant (`PhaseBStart`) holds of the truncated memory. One lemma per relation
  says it reads nothing beyond `eₐ` and nothing about tier-0 array lengths. A read beyond `eₐ` in
  entry 2 is an out-of-bounds abort, which never reads as accept, so no "stays in bounds" proof is
  needed.
* (c) Entry 2 is `compile_correct` at the two-place `Layout`. `Pres` (`SimStmt.lean`) already says
  that bytes outside the layout's arrays, stack and table are unchanged.
* (d) The frozen buffer is unchanged. Option **A** relies on `mprotect`: a write faults and the
  process dies, which the harness counts as a failure. That costs one trusted-harness assumption
  and no proof. Option **B** proves at the L level that, with `CTL[1] = 1`, phase B writes only
  tier-1 arrays: library lemmas for push, slot and growth, plus a static check that no
  non-library function stores to a tier-0 id. Then `MemRel` at the end gives the bytes. Recommend
  A first and B later.
* Composition as in lane parallel: `PooledAccepts` → `TwinAccepts`, now over frozen-buffer workers.
  Threads replace forks (no copy-on-write; the measured 1.5× CPU of COW and +370 MB PSS per worker
  go away).

Reusable from lane `parallel` (not landing): `phase_a` factored out of `install_then_check` with
`phaseA_refines`, `PhaseBStart.step`, the `MODE`/`PJ`/`PVIS` globals, `checkA_run`/`checkB_run`/
`parAccepts`, and the generic `Final/ParAbi` outcomes. The fork-specific parts (COW memory equals
the parent's) are replaced by (b)–(d).

## 5. Cost estimate (full conversion and proofs)

| step | what | size | lane-days |
|---|---|---|---:|
| 1 | compiler feature: syntax, semantics, notation, codegen, `sim_*t`, WF/WFFast, write sets, ModelGen, PureEval | ~800 lines | 3–4 |
| 2 | accessors on the TODAY layout: L macros and proof accessors; rewrite the 150 FunDecls (mechanical) and ~1 100 + 500 proof lines (mostly rewriting with the accessor equations; the views and DerRel by hand) | large, mechanical | 8–12 |
| 3 | library switch to tiered arrays: `Schema.ad`, `TierR`, `ConsLib*` templates, SlotGrow/KSTP base, LpCol, 19 tables; after kstp-proof lands | ~1 500 lines changed | 4–6 |
| 4 | pool tier by phase (bit 40), `pv` accessor through nat/name/level proofs | ~27 writers, many readers | 4–6 |
| 5 | `compact`, entry 2 stub, `check_b`, theorems (a)–(c), harness threads; reuse lane parallel | ~1 500 lines | 5–7 |
| 6 | optional: (d) option B | | 4–5 |

In all: **~25–35 lane-days** without step 6. Step 2 parallelises across 3–4 lanes by file family, so
the calendar time is shorter. Steps 1 and 2 can start now. Step 3 waits for kstp-proof. Step 2 alone
already meets the encapsulation requirement, and step 3 alone already brings the RSS cut measured
above.
