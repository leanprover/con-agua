# Lane lrecords: records and tagged handles, measured and scoped

**Question** (the user's principle): L sits between raw x86 and Lean. The compiler-correctness
proof covers one side and the per-function simulation proofs the other. Moving the slider so the
compiler does more, proved once, should leave less for the manual proofs. absarrays applies this to
array identity and layout. This lane asks whether the next step should be **records and tagged
handles**, and how it compares with other L improvements.

This file is the measurement and scoping result (master 460a1d89). It contains the measurements
(§1), the ranking of five candidates plus two that the measurements turned up (§2), the records
design (§3), the migration plan (§4), the risks (§5) and the decision points (§6). No proof changed.
The scripts and the prototype are outside the repository, in `_tmp/lrecords/`: `measure.py`,
`kinds.py`, `inventory.py` and `Proto.lean`.

**Short answer.** Records and handles are already mostly abstract *at the proof level*. Models and
relations read fields through `tfld`/`tcnt`, `TRec.ad` stays folded, and record loads are one
`evalE_tld` step for `vcgen`. What still unfolds offsets and encodings is small: about 1–2 % of the
proof lines and about 1–3 % of elaboration time, concentrated in the store library, the count slots
in `CTL`, packed halves, handle bounds and decoding. Full compiler ownership is feasible (§3,
prototype §3.7). It costs 90–150 agent-hours and needs three code-changing pre-batches so that the
switch itself stays byte-identical. Its saving per agent-hour is below that of the cheaper
candidates in §2. The proof cost sits mainly in the L ⊑ model specs (`vcgen` over locals) and in the
hand-written middle layer of models and specs.

## 1. Measurements

### 1.1 Method

* **Lines.** Every `ConAgua/**/*.lean` file is split into L code (`lfn`/`lblk` blocks, the rule of
  `scripts/loc.py`), comments, and other code ("proof lines"). The generated program files
  (`Checker/Prog*.lean`, `Asm*`, `PreLoopWSStages`) are left out. The proof lines are then cut into
  top-level declarations. Master 460a1d89 has 1 393 files, 18 687 L lines, **341 595 proof lines**,
  40 116 comment lines and 2 728 generated lines.
* **Concerns.** Each proof line is tagged with every concern whose vocabulary it uses (regular
  expressions at the top of `measure.py`). For example, `rec` matches `tfld`, `tcnt`, `TRec`, `tld`,
  `fld_*`, `wrRec`, `pushRec` and `R⟨…⟩`, and `hdl` matches `tierW`, `idxW`, `>>> 27`, `2 ^ 27`,
  `2 ^ 32`, `>>> 32` and `4294967295`. A line can carry several tags. This counts where a concern is
  *visible*, so it is a lower bound on what the concern costs: the tactic glue around such a line
  mentions nothing.
* **Time, module level.** Per-module elaboration seconds come from the cold build of 8a84fd4e, today
  (`_tmp/buildtime/after-cold.log`): 1 381 modules, 7 514 s summed. A module's seconds are spread
  over its concerns in proportion to their share of its proof lines (the "time proxy").
* **Time, declaration level.** These are the profiler runs in `_tmp/buildtime/prof/` (57 of the
  slowest modules). 2 855 s are in "elaborating proof of …" entries. 2 176 s of that match source
  declarations, and 679 s are in declarations that `l_model` or the elaborator generated. This
  sample is biased towards slow modules, which is the point: it shows where the time goes when it
  hurts.
* **Generated vs hand-written.** A function counts as generated if an `l_model` block names it, and
  as hand-written if a theorem with `⦃` in its text names it. The functions are those of
  `checkerProg` (1 837 parsed, 311 of them template instances such as `memoFindG abSch`).

### 1.2 Where the proof lines are, by layer

Declarations are classified by their statement, in this order (`kinds.py`): a triple `⦃` (spec,
L ⊑ word model); `ErrClaim`/`callE`/`Except` (error claim); twin vocabulary (`AM`, `ConRon`,
`decI`'s types, `…R` relations: refinement, model ⊑ twin); frames; equations about a `…W` model.

| layer | decls | lines | % | profiled s | % of profiled | module-time proxy |
|---|---:|---:|---:|---:|---:|---:|
| refinement (model ⊑ twin) | 4 323 | 116 243 | 34.0 | 245 | 11 | 21 % |
| other lemmas | 5 969 | 53 584 | 15.7 | 156 | 7 | 15 % |
| commands (`open`, `attribute`, `grind_pattern`, …) | 26 707 | 31 878 | 9.3 | – | – | (artefact of the proxy) |
| **spec (L ⊑ model)** | 2 169 | 31 585 | 9.2 | **1 654** | **76** | 12 % |
| model equations (arm lemmas of hand models) | 3 858 | 30 516 | 8.9 | 43 | 2 | 7 % |
| error claims | 467 | 21 673 | 6.3 | 77 | 4 | 6 % |
| other definitions | 4 279 | 18 103 | 5.3 | – | – | 6 % |
| word models (hand-written defs) | 2 864 | 15 083 | 4.4 | – | – | 6 % |
| frames and keeps | 832 | 10 872 | 3.2 | – | – | 2 % |
| relations, predicates | 1 258 | 5 525 | 1.6 | – | – | 2 % |
| `l_model` blocks | 487 | 1 942 | 0.6 | – | – | 3 % |

By module role (module names): code-and-mixed modules 2 711 s (36 %), `*Spec*` modules 2 131 s
(28 %), the error claims (`Verdict/`, 45 874 lines) 1 113 s (15 %), kernel checks (`AsmPart*`,
`ProgWf`, `ProgSkt`, closures) 908 s (12 %), refinement and link modules 492 s (7 %), and compiler, L
and Final 159 s (2 %). In the profiled modules the time splits into `grind` (all phases about 38 %),
`simp` 21 %, blocked 16 % and kernel type checking 11 %.

**Reading.** Most lines are refinements, but most of the *slow* time is the L ⊑ model specs: `vcgen`
over L, then `grind`/`simp` over goals with `setLoc` chains. The specs are where L's shape matters.
The refinements are where the data representation (records, handles, the twin bridge) matters, and
they are cheap per line.

### 1.3 Concerns (line-level vocabulary)

| concern | proof lines | % of proof lines | time proxy (s) | % | profiled decls containing it (s, % of 2 176) |
|---|---:|---:|---:|---:|---:|
| `rec` record fields, counts, store-library record words | 2 887 | 0.8 | 81 | 1.2 | 198 (9 %) |
| `hdl` handle tier/index decode, encode, bounds, packed halves | 5 136 | 1.5 | 152 | 2.2 | 325 (15 %) |
| `tag` tag dispatch (`>>> 28`), the expression view | 7 663 | 2.2 | 98 | 1.4 | 323 (15 %) |
| `tier` tiers and array identity (absarrays baseline) | 5 255 | 1.5 | 80 | 1.1 | 172 (8 %) |
| `ctl` the `CTL` array and globals | 3 458 | 1.0 | 84 | 1.2 | 186 (9 %) |
| `loc` locals, `setLoc` chains, result lists | 19 859 | 5.8 | 478 | 6.9 | 2 007 (92 %) |
| `err` error claims, `Except` glue | 8 044 | 2.4 | 171 | 2.5 | 433 (20 %) |
| `loop` loop specs, invariants, inductions | 4 764 | 1.4 | 150 | 2.2 | 919 (42 %) |
| `lookup` program lookups by name string | 6 241 | 1.8 | 253 | 3.6 | 652 (30 %) |
| `name` name stores, strings, `NIdx` | 4 091 | 1.2 | 69 | 1.0 | 236 (11 %) |
| `pool` the limb pool, tagged slice addresses | 5 617 | 1.6 | 160 | 2.3 | 1 656 (76 %) |

By directory, the record and handle vocabulary is almost all in `Arena/` (rec 2 413, hdl 4 139,
tag 6 573 lines) and `Verdict/` (352, 716, 912). Of the time sinks named in the proof-style
lessons, the `setLoc`/`Locals.init` crawl (`loc`) is the only concern that appears in nearly every
slow declaration. Hand-written `simp only [St.setLoc_loc, …]` sets occur 299 times in 115 files.

### 1.4 Generated vs hand-written models

* Plain functions (not template instances): 1 526. `l_model` covers **533 (35 %)**, and **993 (65 %)**
  have hand-written specs. The 311 template instances share generic hand-written specs.
* `l_model` is five days old (2026-10-22). Of the 993 hand-specified functions, 942 have an `lfn`
  text that the script found, and only 9 of those use something the generator does not support
  (two or more loops, block operations). The others are hand-written because they predate it.
* The hand-written middle layer: word models 15 083 lines, their arm and continuation equations
  30 516, spec theorems 31 585. That is **77 184 lines (22.6 % of the proof lines)**, about 75 lines
  per hand-specified function. For comparison, the `l_model` blocks take 1 942 lines for 533
  functions, 3.6 lines each. Hand-written defs named `…W`: 1 165, 7 301 lines.
* Elaboration: in the profiled modules, generated declarations take 679 s, against 1 654 s for
  source spec proofs. Per function that is not comparable (the sample is not matched), so the time
  advantage of generation is not established. The proof-style lessons record single specs that got
  10–40× faster when they moved from `sym … finish` to the `vcgen` + `simp_all` recipe that
  `l_model`'s `simp`/`locals` modes apply (RecGenSpec16 241 s → 11 s, IndInstallSpec28 209 s → 6 s).

### 1.5 L lines per function

1 450 plain functions with a matched `lfn`: mean **10.5** L lines, median 8, 90th percentile 18,
maximum 65 (15 221 lines). Named blocks are another 2 817 L lines. Against 341 595 proof lines this
is about **186 proof lines per function, or 18 per L line**.

### 1.6 The record and handle footprint (inventory)

Proof and L lines that state or unfold a layout or an encoding (`inventory.py`, non-generated
files):

| # | what | files | proof lines | where |
|---|---|---:|---:|---|
| I1 | `TRec` layout terms (`ad`, `wd`, `ex`, `adE`, `exE`, `tierX`, `ld`, `st`, `cntE`) | 8 | 67 | `L/TRec`, `StoreFields` |
| I2 | raw record-array reads (`rdW (m.arr64 (tierA R t)) …`, `tfld_hi0`) | 81 | 491 | `Arena` 456, `Front` 35 |
| I3 | accessor evaluation lemmas passed to `vcgen` (`evalE_tld`, `tld_eq`, `evalE_cnt`, …) | 155 | 430 | `Verdict` 262, `Arena` 166 |
| I4 | store-library record words (`S.w`, `wrRec`, `pushRec`, `fld_push*`, `recSize`) | 13 | 151 | `Arena` |
| I5 | count slots and `CTL` frames (`tcnt_set64_ne`, `.ca`, `set64 CTL k`, `c192_not_arena`-style) | 373 | 1 989 | `Arena` 1 784 |
| I6 | packed halves (`>>> 32`, `&&& 4294967295`) | 82 | 181 (+35 L) | `Arena` |
| I7 | tag decode `>>> 28` | 168 | 1 570 | `Arena` 1 432, `Verdict` 118 |
| I8 | tier/index decode (`tierW`, `idxW`, `tierE`, `idxE`, `>>> 27`) | 233 | 2 749 | `Arena` 2 279, `Verdict` 394 |
| I9 | handle bounds and encoding (`2 ^ 27`, `2 ^ 28`, `2 ^ 32`, `134217728`, `268435456`) | 317 | 1 314 | `Arena` 1 136 |
| I10 | the twin bridge (`decI`, `decE`, `.word.toUInt64`, `Idx.ofWord`) | 592 | 6 874 | `Arena` 5 592, `Verdict` 997 |
| I11 | the view check `viewOK` | 67 | 278 | `Arena` |

Per-tag arm lemmas (a hypothesis `h >>> 28 = k` or `viewOK m h R` in the statement): 420
theorems, 5 702 lines. `h.toNat < 2 ^ 32` hypotheses: 1 130 lines in 284 files.

L code (18 687 lines): `R⟨t, i⟩.f` 365 lines in 37 files, `R⟨t⟩.count` 299 lines in 35 files,
`⟦h⟧.tier`/`⟦h⟧.idx` 334 lines in 37 files, a tag test `h >> 28` 175 lines in 49 files, packed
halves 48 lines in 27 files. There are about 60 raw record-array accesses (`PJREC⟨t⟩[(w - 1) * 2]
& 4294967295`, `len(LSREC⟨t⟩) < (c + 1) * 3`), all in the store instances' key comparators and
room checks. A handle is built only in the cons template (`k := c * w`, the handle base). No L code
holds a precomputed handle constant: the pins hold handle words interned at run time.

**Reading.** The layout itself (I1–I4, I6) is visible on about 1 300 proof lines. The encodings
around it (counts in `CTL`, I5; handle decode and bounds, I7–I9) are on about 7 600. The twin bridge
(I10) is the largest item at 6 900 lines, but it *is* the relation (an L word is the twin's
`Idx.word`) and stays under any design that keeps the word (§3.1).

## 2. Ranking of candidates

All savings are estimates from §1. "Lines" are proof lines deleted if the change is carried
through. "Time" is the share of the 7 514 s module total. One agent-hour (h) is one agent working
one hour.

| rank | candidate | addressable (measured) | expected saving | cost | saving per h | pays off |
|---:|---|---|---|---|---|---|
| 1 | **(6, new) locals normal form**: a simproc or evaluator in L core for `setLoc`/`setLocs`/`Locals.init` chains, used by the `vcgen` recipes and `l_model` | `loc` 19 859 lines (5.8 %), time proxy 6.9 %, in 92 % of profiled slow time; 299 hand simp sets | time −3 to −10 % (to measure first, on the 57 profiled modules); lines −1 to −2 k | 5–12 h | highest (time) | at once, in every spec |
| 2 | **(2) model-generator coverage**: close the gaps (template `FunDecl`s with parameters, nested loops, byte stores, memory-only members, generated error models); then retrofit opportunistically, function by function, when a twin bump or a performance change touches it, and the slowest hand specs first | hand middle layer 77 k lines (22.6 %), about 75 per function; 933 of 993 hand functions are in the generator's scope already | per touched function −50 to −70 lines; gap closing alone saves nothing until used; a full retrofit (933 functions at 0.5–1.5 h) is not worth it | gaps 20–35 h | ~150–250 lines/h on touched code | every later change |
| 3 | **(3) constructs shaped like the twin's code**: a tag `match` with field binding (the twin's `match ← view h with`), error propagation shaped like the twin's `←`/`throw` (`x := call? f(…)`), bounded `for` | arm lemmas 420 / 5.7 k lines; `tag` 7.7 k; `Verdict` 45.9 k lines (15 % of time), its `callE` glue about 3.5 k; `loop` 4.8 k | −5 to −12 k lines once the generator supports them (depends on rank 2) | 40–80 h | ~120 lines/h | new and changed code; error claims |
| 4 | **(1a) records and handles as a proof API, no semantics change** (§4 batches R0, R1): no raw record reads outside the store library, counts out of `CTL`, a handle API (`tagW`, `tierW`, `idxW`, `mkW` with their laws, the `decI` bridge lemmas stated once) | I2, I5, I7–I9 about 8 k lines | −2.5 to −4.5 k lines; time −1 % | 25–40 h | ~100 lines/h | at once |
| 5 | **(5) leaner hash template** (fewer instance obligations: `RFrame`, `ColFree`, `KMono`, `ConsKeyOK`; one schema type for cons and memo) | hash libraries 10.0 k lines, store instances 6.9 k, memo instances 2.8 k; about 200 s (2.6 %) | −4 to −7 k lines; time −1 % | 30–50 h | ~130 lines/h | once; each new table |
| 6 | **(1) compiler-owned records and tagged handles** (this design, §3–§4: R0–R3 then the switch) | everything in 1a plus I1, I4, I6, field frames, `< 2 ^ 32` bounds from 32-bit fields | −4 to −7 k lines net (+1.0–1.5 k in L core and compiler); time −1 to −3 % | 90–150 h | ~45 lines/h | once; then 32-bit field loads, capacity hints, closer twin layout |
| 7 | **(7, new) function names as numbers**: `FnName` as a code with lookups by position by construction (today `chk_lk`/`prog_bundle` work around it) | `lookup` 6.2 k lines, time proxy 3.6 %; `lookup "…"` in 5 668 lines of 647 files; `ProgWf` 81 s | −2 to −4 k lines; time −2 to −4 % | 25–40 h (wide: `Prog`'s type) | ~90 lines/h | once |
| 8 | **(4) compiler optimisations proved once** (leafgen follow-ups, inlining) | proof cost only indirect: L written for speed (branch-free bodies, fused blocks, 2.8 k L lines of named blocks) | proof lines ±0; it is a performance lever (inlining small leaves: 6.3 % of cycles, perfgap) | 15–40 h each | ~0 for proofs | performance |

**Method notes.**

* The ranking orders by expected saving per agent-hour. Ranks 1–3 change the *per-function* cost of
  all later work (twin bumps, performance changes, verdict extensions). Ranks 4–7 are one-off
  reductions of the existing proof.
* Rank 1 was not in the brief. It comes from the profile: `setLoc` chains in 92 % of the profiled
  slow time, and the 442 s DeclCanonExpr case recorded in the proof-style lessons. Its estimate is
  the least certain. A one-day measurement (rewrite three slow specs with the simproc, interleaved
  timings) should come first.
* Rank 2's line saving is solid. Its time saving is not established (§1.4) and should be measured
  on the first retrofits.
* Rank 6 versus 4: most of the line saving of compiler ownership (counts out of `CTL`, the handle
  API, no raw reads) is available without changing L's semantics. The extra comes from the
  packed-half, address-arithmetic and bound lemmas that the 32-bit field arrays make unnecessary,
  about 1.5–2.5 k lines, for 60–110 more agent-hours. Its other benefits are not proof lines: a
  faster packed-field load (one 32-bit load instead of load plus shift or mask), the place for
  capacity and order hints, and records laid out like the twin's per-constructor tables.
* All line counts are vocabulary-based lower bounds for what a concern *touches*. The time proxy
  spreads module time by lines, which undercounts concerns that sit in slow declarations (`loc`)
  and overcounts commands.

## 3. Records design

### 3.1 What is semantic and what is layout

**Semantic** (fixed by L's semantics, bit-exact with con-ron):

* **The handle word.** con-ron's handle *is* its 32-bit word, `tag · 2^28 + tier · 2^27 + index`
  (`ConRon/Arena/Handle.lean`, `Idx.mk`, `tag`, `tier`, `index`). The relation is word identity
  (`decI h = ⟨h.toUInt32⟩`). L hashes the word in its cons tables and memos, packs two handle words
  into a cons key, stores handles in records, pins and frozen images, and compares them with `==`. An
  encoding chosen by the compiler would turn the relation into a bijection on every one of the
  6 874 bridge lines and gain nothing. So the encoding stays in the semantics, as *named*
  operations defined once in L core (`Hdl.mk`, `Hdl.tag`, `Hdl.tier`, `Hdl.idx` on `Word`). They are
  proved equal to con-ron's once, and are irreducible to proofs above L, which use their laws. The
  compiler owns how they are computed: as today, the shift and mask, with the tier fused into a
  tiered access (decision point 1).
* **Field widths.** con-ron's node fields that hold handles are `UInt32`, the others are wider.
  L gets the same: a field is `u32` or `u64`. Storing into a `u32` field keeps the low 32 bits, and a
  load gives a value below `2 ^ 32`. This is a fact about the data, not about the packing.
* **Per-tier node tables and counts**: node `i` of tier `t` of store `R`, and the node count of
  each tier. These are the twin's `tiers[t]`.

**Layout** (compiler-owned after the switch): the stride; which word holds which field; packing
two `u32` fields into one word; whether a column such as `ADER` is a separate region or a field of
`APP`; where counts live; the capacity descriptors; the regions. The pin data (`pins.bin`) holds
bytes and no records. The stub reads only descriptor positions. **The frozen buffer's images** are
the one place where the layout is an interface between two programs: entry 1 writes images of the
record regions and entry 2's descriptors point into them (§5, risk 3).

### 3.2 Surface

A registration next to `checkerArrays` (`ConAgua/Layout.lean`):

```lean
def checkerRecords : List RecDecl := [
  rec APP   (tiered) [f : u32, a : u32, der : u64],        -- der: today's ADER column
  rec LIT   (tiered) [kind : u64, o : u64, l : u64, h : u64],
  rec LET   (tiered) [ty : u32, v : u32, b : u32, der : u64],
  rec LVLS  (tiered) [o : u64, l : u64, h : u64, hp : u64], -- hp: today's LSHP column
  … ]                                                       -- the 19 stores of StoreFields.lean
```

Each record store declares its fields, their widths and that it is tiered. Every store has a count
per tier. The L syntax stays as it is: `APP⟨t, i⟩.a`, `APP⟦h⟧.f`, `APP⟨t⟩.count`, and
`APP⟨t, i⟩.f := e` in the store library. It gains `APP⟨t⟩.count := e`, `cap(APP⟨t⟩)` (the capacity
in records, replacing `len(AREC⟨t⟩) < (c + 1) * w`) and a whole-record write `APP⟨t, i⟩ := {f := x,
a := y}`. A one-word column becomes a field (`APP⟨t, i⟩.der`), or stays a separate store if a
column is ever written apart from its node (none is today).

### 3.3 Semantics: a record store is a set of abstract arrays

The design keeps L's memory model as absarrays leaves it (a map from `TArr` to arrays) and adds
almost nothing:

* **Each field is an abstract tiered array.** `APP.a` is the array name `APP_a`, so
  `APP⟨t, i⟩.a` means `ld APP_a⟨t⟩[i]`. Field arrays are distinct `TArr`s, so a store to one field
  leaves every other field, every other store and `CTL` alone *structurally*. This is absarrays'
  frame lemma, with no `TRec.ad`, no `R.Ok`, no `a ≠ R.arr ∧ a ≠ tier1 R.arr`.
* **A third array family, `u32`** (`Mem.halves : TArr → Array UInt32`; `ld32t`, `st32t`). A load
  zero-extends and a store truncates. This is where `< 2 ^ 32` comes from for free.
* **The count of tier `t` is an abstract tiered array of length 1**, `APP_cnt⟨t⟩[0]`. No new
  construct, and no aliasing with `CTL`.
* **Capacity** is the field arrays' common length: `len(APP_a⟨t⟩)`. The registration makes all
  fields of a store the same length (the layout relation of §3.5 requires it).
* **Handles**: `Hdl.*` as named functions. `⟦h⟧.tier`/`.idx`/`.tag` expand to them, and `R⟦h⟧.f`
  is `R⟨Hdl.tier h, Hdl.idx h⟩.f`. They could later become unary operators of `Expr`, so that
  `vcgen` sees them directly instead of through `fold` (optional; §4, H2).
* **One primitive whose semantics knows the layout**: `copyRecs!(D, di, R⟨0⟩, n)`, the frozen
  image of the first `n` records of `R` in the word array `D`. Its meaning is the registration's
  encoding of those records (§5, risk 3). Nothing else in L's semantics mentions a stride, an
  offset or a half.

Proof vocabulary after the switch: `tfld m R t i f` is `rdW (m.arr64 (tierA (R.fld f) t)) i` (or
the `u32` read), and `tcnt m R t` is `rdW (m.arr64 (tierA R.cnt t)) 0`. These are names over plain
reads, so every user that never unfolded them is unchanged.

### 3.4 Interaction with tiered arrays

Records live in tiered arrays today (`AREC⟨t⟩`). After absarrays, a tier is part of the array's
abstract name (`⟨a, hi⟩`). Field arrays are tiered arrays in exactly that sense, so the record
switch is a *use* of absarrays' memory model, not a change to it. The compiler's placement keeps
absarrays' one invariant: tier 1's descriptor sits next to tier 0's (`adj`), now per record region.
The constant-tier fold of absarrays §5 applies to field arrays unchanged. Parallel mode keeps its
shape: tier 0 of a store is frozen and tier 1 is the worker's own.

### 3.5 Compiler side

**The layout map grows a placement.** absarrays gives each `TArr` in the domain a descriptor
position `pos`. Records add a placement for the field and count arrays:

```lean
structure Place where
  region : Nat        -- the descriptor position of the record region (tier 1 adjacent, as `adj`)
  stride : Nat        -- words per record
  word   : Nat        -- the field's word in the record (< stride)
  half   : Option Bool -- for a u32 field packed with another: low (false) or high (true) half
```

Today's `StoreFields` rows are exactly one placement (`APP`: region `AREC`, stride 1, `f` low half
of word 0, `a` high half; `ADER`: its own region, stride 1). Counts are placed in their own arrays
(R1) and stay there.

**The theorem: a lowering pass, proved once, in front of the unchanged compiler.**

```lean
def lowerRec (reg : Registration) : Prog → Prog       -- field and count ops → region ops
theorem lowerRec_correct (hwf : reg.WF p) :
    run (lowerRec reg p) N f args (enc reg m) = (run p N f args m).map (encOut reg)
```

`enc` interleaves the field arrays into their regions (the relation `FRel` of the prototype, §3.7)
and leaves every other array as it is. The equation is exact because L is deterministic, and
`compile_correct` then applies to `lowerRec p` without change. **No existing compiler proof file
changes for the switch itself.** New files: `Compiler/LowerRec.lean` and `LowerRecSim.lean`
(expression, statement and call simulation; about 1 000–1 500 lines, mostly mechanical, with
`FRel`'s load, store, packed-store and frame lemmas at its core). The changes elsewhere:

| file | change |
|---|---|
| `L/Syntax.lean`, `L/Semantics.lean` | the `u32` family (`ld32t`, `st32t`, `Mem.halves`), `Hdl.*`, `copyRecs` |
| `L/TRec.lean` | deleted; `Layout.lean` gets `checkerRecords` and `Place` |
| `Arena/StoreFields.lean` | `tfld`/`tcnt` redefined over field arrays; the evaluation lemmas become one-liners |
| `Compiler/Compile.lean`, `SimExpr.lean`, `SimStore.lean`, `Rel.lean`, `Abi*.lean` | **R3 only** (before the switch): the capacity-checked record access `ldr`/`str` and a capacity column in the descriptor table |
| `Compiler/Main.lean`, `Final/*` (`DrvAbi`, `BufAbi`, `BufLayout`, `SeqLayout`) | compose `lowerRec_correct` with `compile_correct`; the frozen images through `enc` |
| `Checker/Asm.lean`, `AsmFileEq.lean` | `checkerAsm = compileProg checkerTab (lowerRec reg checkerProg)` (the kernel evaluates one more syntax traversal per function) |

**Why R3 is needed** (prototype finding). A field access must be out of bounds exactly when `i` is
not below the capacity. Today's lowered access computes `i * w + off` in 64-bit arithmetic and
compares that with the array's length. For `w ≥ 2` and `i ≥ 2^64 / w` the product wraps around, and
the lowered program reads a word where the source aborts. So `lowerRec_correct` is false for
today's code shape. The fix is a record access that checks the record index against a capacity
word (`i < cap`, with `cap = len / w` written by the stub), so the address cannot wrap. That is a
code change, and §4 does it in a pre-batch under today's semantics (R3), so that the switch is
byte-identical. Packed stores have the same issue: the lowering's whole-record write must be
`(x &&& 0xFFFFFFFF) ||| (y <<< 32)`, which matches `u32` truncation, where today's push writes
`x ||| (y <<< 32)` (R2).

### 3.6 Handles in the compiler

There is nothing to prove beyond today: `Hdl.tag h` lowers to `h >> 28`, `Hdl.tier h` to the
masked shift (fused into the tiered access as `TRec.tierX` does now), and `Hdl.idx h` to the mask.
The once-only facts are in L core: `Hdl.tag_mk`, `Hdl.tier_mk`, `Hdl.idx_mk`, `Hdl.lt`, and
`decI (Hdl.mk g t i) = Idx.mk g t i`, written in con-ron's arithmetic form so that `omega` proves
them (con-ron's `Handle.lean` explains why: the bitwise forms need `bv_decide`, which adds an
axiom).

### 3.7 Prototype (`_tmp/lrecords/Proto.lean`, 253 lines, checked on master a7aabf22)

It imports `ConAgua.Arena.StoreFields` and relates a field memory `fm : Nat → Array Word` (one
store, one tier) to today's record word array `A` by `FRel`: every field array has the capacity
`A.size / w` and holds its field's part (`TRec.ex`) of its word. Under a layout condition `LayOK`
(`w ≥ 1`, every field's word below `w`, distinct fields in distinct words except the packed pair),
it proves:

1. `ld`: the capacity check `i < A.size / w` implies today's word bounds check, with no wrap-around,
   and the field array reads what the lowered load reads;
2. `ad_ne`: distinct (record, field) pairs below the capacity have distinct addresses, except the
   packed pair;
3. `st_unpacked`: a field store preserves `FRel` (field `g`'s array updated, the word array updated
   at `R.ad i g`);
4. `st_packed`: the masked whole-word store of a packed record preserves `FRel`, with fields `0` and
   `hi` getting the 32-bit truncations;
5. the packing laws `pack_lo`, `pack_hi`. These were proved by `bv_decide`, which adds native
   axioms. The real file proves them through `toNat` or with the additive form, as con-ron does.

`ld`, `ad_ne` and `st_unpacked` use only `propext`, `Classical.choice` and `Quot.sound`. The
prototype also found the wrap-around problem behind R3: the first statement of `ld` needs
`i < A.size / w`, and it does not hold with today's bounds check alone.

## 4. Migration

### 4.1 Inventory of places that unfold offsets or encodings

| place | what | files | lines | batch |
|---|---|---:|---:|---|
| `L/TRec.lean`, `Arena/StoreFields.lean` | the layout, its evaluation lemmas, `tfld`, `tcnt`, `tierW`, `idxW` | 2 | 410 | S (rewritten), C (TRec deleted) |
| store library (`StoreLib`, `ConsLib`, `ConsLibRel`, `ConsLibSpec`, `StoreGrow`, `Scratch*`) | record words (`S.w`, `wrRec`, `pushRec`, `fld_push*`), the push `k := c * w`, record address bounds (`2 ^ 27 * 256`) | 13 | 151 (+ about 600 around them) | S |
| store instances (`*Store.lean`) | key comparators and room checks on raw record arrays (L), their specs | 20 | ~60 L, ~800 proof | R0 (L via accessors), S |
| raw record reads in proofs (I2) | `rdW (m.arr64 (tierA R t)) (i * w + f)` | 81 | 491 | R0 |
| count slots (I5) | `CTL[ca + t]`, `tcnt` vs `CTL` stores, count frames | 373 | ~1 000 of 1 989 | R1 |
| packed halves (I6) | `>>> 32`, `&&& mask`, the combined push word | 82 | 181 + 35 L | R2, S |
| handle decode and bounds (I7–I9) | `>>> 28`, `tierW`/`idxW` unfolding, `2 ^ 27`/`2 ^ 32` arithmetic | ~400 | 5 600 (most are uses that stay as API calls) | R0 (API), S (bounds from `u32`) |
| twin bridge (I10) | `decI`, `decE`, `.word.toUInt64` | 592 | 6 874 | stays; R0 adds the `Hdl`/`decI` laws |
| freeze and promote (`Freeze*`, `Promote*`, `FreezeTrunc*`) | `fzStores` with `(ra, sa, w, ca)`, record-region prefixes, the `CTL` seed | ~12 | ~1 500 | S (`copyRecs!`), R1 (counts in the seed) |
| `Final/Buf*`, `Final/SeqLayout` | frozen descriptors, images | 6 | ~1 300 | R3 (capacity column), S (`enc`) |
| generators | `checker_prog.py` (store names), `preloop_ws.py`/`core_fns.py` (write sets name `AREC` etc.) | 5 | – | S |
| docs | OVERVIEW §5.3 ("record accessors … fix the layout in one place"), §6.1, §6.2, §7.2 | 1 | – | C |

### 4.2 Batches

Each batch lands green on its own. R0–R2 work under today's semantics, after the absarrays switch
has landed (it edits about 200 proof files that R0 also touches).

| # | batch | what | agent-h | proof lines | `checker.s` |
|---|---|---|---|---|---|
| P | **prototype** (not landed) | Extend `Proto.lean` to a toy `lowerRec` on absarrays' memory: expressions, a statement sequence, a call; `lowerRec_correct` for a two-store program with a packed store, a count and a frame. Measure the kernel cost of evaluating `lowerRec` on `checkerProg` (`#reduce` of the lowered program's hash vs `compileProg` time). Go/no-go | 6–10 | (throwaway) | – |
| R0 | **API only** | Store-instance comparators and room checks through accessors and a `room(R⟨t⟩, c)` notation that expands to today's code; proofs read records only through `tfld`/`tcnt` outside the store library (I2); `TRec` rows by name; the handle API (`tagW`, `mkW`, laws, `decI` laws) with `l_model fold [tagW, …]`; `h >>> 28 = k` → `tagW h = k` mechanically | 10–16 | ~1 500 changed, −300 to −800 | unchanged |
| R1 | **counts out of `CTL`** | One tiered word array per store's count (`APP_cnt⟨t⟩[0]`, or one `RCNT` array), written through `R⟨t⟩.count := e`; the `CTL` frames lose their count side conditions; freeze seeds the count arrays | 8–12 | ~800 changed, −500 to −1 000 | count accesses (base and displacement) |
| R2 | **masked packed pushes** | The cons template writes `(x & 0xFFFFFFFF) \| (y << 32)` for the 8 packed stores; `consInternM_word` adapts | 3–5 | ~150 | +1 instruction per packed push |
| R3 | **capacity-checked record access** (`--wide`) | `Expr.ldr`/`Stmt.str` (array, tier, index, stride, word, part) with today's word semantics but bounds `i < len / stride`; the capacity column in the descriptor table, written by the stub; `tld`/`fld_*` bounds lemmas; `TRec.ld`/`st` expand to them | compiler 12–18, fallout 6–10 | ~600 changed | every record access's bounds check; the stub's table |
| H2 | handle operators (optional) | `Expr` unary `htag`/`htier`/`hidx`; `vcgen` sees `Hdl.*` without `fold` | 6–10 | ~300 | unchanged |
| S | **the switch** (`--wide`) | §3.3 and §3.5: the `u32` family, field arrays, `checkerRecords`, `lowerRec` and its proof, the composition, `tfld`/`tcnt` redefined, the store library's pushes and reads over fields, `copyRecs!` in freeze and promote, `Final/Buf*` through `enc`, generated lists regenerated | compiler and L core 20–33, above L 25–45 | ~150–250 files, 2 000–3 500 lines changed; net −2 000 to −3 500 | **unchanged, byte for byte** (`lowerRec` emits R1–R3's code); check `compileProg`'s output hash, as absarrays did |
| C | cleanup and docs | `TRec` deleted, OVERVIEW §5.3/§6.1/§6.2/§7.2, deviation wording, `StoreFields` doc | 3–5 | ~100 | – |
| O | 32-bit field loads (optional, a compiler optimisation) | `mov r32, [m]` for `u32` fields (Kraken has `W32` moves): one instruction instead of load and shift/mask; Step lemmas for `W32` | 8–12 | 0 above the compiler | packed-field loads |

**Total: 90–150 agent-hours** (P through C), about a third of it in the switch's fallout above L.
Expected net proof delta: −4 000 to −7 000 lines, plus 1 000–1 500 lines in L core and the
compiler. R0–R2 alone (25–40 agent-hours, candidate 1a of §2) bring about half of the line saving.

**Order.** absarrays switch (6) → R0, R1 and R2 in parallel → absarrays dense layout (7), if it is
done → R3 → P (can run any time; its go/no-go decides S) → S → C. R3 should come after absarrays
batch 7 because both rewrite the descriptor table and the stub (`Compile`, `Abi`, `Final/*Layout`).
Otherwise the two conflict file by file.

## 5. Risks

1. **`checker.s` byte identity through the switch.** It holds only if R1–R3 land first. Those three
   change code: count addressing, 8 packed pushes and every record bounds check. Each is measured
   when it lands (`scripts/bench.py`, wall time interleaved, plus instruction counts, as absarrays
   batch 5 did). R3's bounds check compares the index with a memory operand instead of computing
   the address first, so its instruction count should be about the same. If R3 is skipped, the
   switch changes every record access's code, and `checkerFile_eq` still re-establishes the
   theorem (decision point 3).
2. **Kernel cost.** `checkerFile_eq` evaluates `lowerRec` on each function before `compileProg`.
   That is one syntax traversal against a code generator that already does much more, so it is
   expected to be small, to be measured in P. The field arrays add about 45 `TArr` names (19 stores ×
   1–4 fields + 19 count arrays), and the write-set and read-set lists in the `decide +kernel`
   checks get longer. absarrays measured `TArr` membership at about `Nat`'s cost (13.2 s vs 12.4 s
   for 3 000 queries).
3. **Parallel mode, frozen buffers.** `par_compact` copies the prefix `R[0 ‥ count₀ · w)` of each
   record region into `OUT`, and entry 2 points the worker's descriptors at the images
   (`Arena/Freeze.lean`). After the switch the regions cannot be named in L. The image has to be
   written by `copyRecs!`, whose semantics is the registration's encoding. This is the one
   primitive whose meaning knows the layout, and it is deliberate: the image format is an interface
   between the two entries. Its users are the freeze proofs (`Freeze*`, about 1 500 lines) and the
   `Final/Buf*` proofs (about 1 300 lines), which show that a descriptor pointing at an image makes
   the worker's field arrays equal to the frozen fields (`enc` after decode). Budgeted at 15–25 h
   inside S. The alternative, images written by compiler-generated code, needs a dynamic-offset
   primitive and is not proposed.
4. **Twin fidelity.** Nothing L computes changes. The handle words are bit-exact (§3.1), and field
   widths follow con-ron's `UInt32` handle fields. Records as one array per field and tier are
   closer to con-ron's per-constructor tables than interleaved words are. No new deviation. D35's
   wording ("one word array per tier") changes. Masking the packed push (R2) changes nothing
   reachable, because every pushed handle word is below `2 ^ 32` (`consInternM_lt`).
5. **Sequencing after absarrays.** The design needs absarrays' `TArr` memory, so S cannot start
   before the absarrays switch lands. R0 touches many of the files that switch edits, so it waits
   for it as well. R3 waits for absarrays batch 7, or is done before it with the batch 7 lane told
   about it. No step here touches the absarrays lane's files while it runs.
6. **Merge pressure.** S changes the store library and every file that unfolded a record (about
   150–250 files after R0). As in absarrays, the pre-batches take most of the churn into small
   landings, and S lands alone (`--wide`).
7. **The saving is modest** (§2). The design is sound and the prototype supports its core. The
   reason to do it is the user's principle and what it enables (32-bit loads, capacity and order
   hints, fewer places that know a stride), not proof lines.

## 6. Decision points for the user

1. **Handle encoding: semantic (recommended) or compiler-chosen.** The twin's handle is its word,
   and L hashes, packs and stores the word. Recommendation: keep the encoding in L's semantics as
   named operations defined once and proved equal to con-ron's, with the compiler owning only how
   they are computed.
2. **How far to go.** (a) R0–R2 only, the proof API with counts out of `CTL` and masked pushes:
   about half the line saving for about a quarter of the cost, with no semantics change. (b) The
   full design through S. Recommendation: (a) now. Decide (b) after the prototype P and after ranks
   1–2 of §2 have shown what they save.
3. **Byte identity at the switch.** Pay for R3 as a pre-batch, so that S is a proof-only landing
   (recommended if a proof-only switch matters for review), or let S change every record bounds
   check (10–15 h cheaper).
4. **Frozen images:** `copyRecs!` with layout-defined semantics (recommended), or images written by
   compiler-generated code.
5. **Where counts live:** a tiered array of length 1 per store (recommended: no new construct), or
   one shared `RCNT` array.
6. **Ordering against the other candidates.** Recommendation: rank 1 (locals normal form, measured
   first) and rank 2 (generator gaps, then retrofit on touch) before any records work. The records
   pre-batch R0 can run alongside them once absarrays has switched.

## 7. Batches R0–R2 (lane records-api)

The user chose decision point 2(a): R0–R2 only. R3, H2, S and O are deferred.

### 7.1 R0, first landing: the handle API

**What changed.** The handle encoding and its bridge to the twin are now stated and proved once:

* `Arena/StoreFields.lean`, section "Handle words" (a `module`, so `module` files can use it):
  `hdW`, `tagW`, `tierW`, `idxW`; their values as numbers (`shr28_toNat`, `tierW_toNat'`,
  `idxW_toNat`, `mask32_toNat`); bounds (`shr28_lt`, `tierW_le`, `tierW_lt`, `idxW_lt`, `mask_lt`);
  and the laws of `hdW` (`hdW_toNat`, `hdW_lt`, `hdW_tag`, `hdW_tier`, `hdW_idx`).
* `Arena/Handle.lean` (new; `decE` lives in a non-`module` file, so the bridge cannot sit in
  `StoreFields`): `decI`, `hix`, `mk_eq`, injectivity (`decI_inj`, `decI_inj_iff`, `decI_beq`,
  `decI_bne`), `decI_mask`/`decE_mask`, tags (`decI_tag`, `decI_tag_eq`, `decI_tag_beq`,
  `decI_tag_eqW`, their `decE` forms, `tag_beq_w`, one lemma per `ETag` constant in use), indices
  and tiers (`decI_idx`, `decI_pers`, `isPersistent_decI`), and the list forms
  (`contains_map_decI`, `contains_map_decI_iff`, `findIdx_map_decI`, `map_decI_inj`,
  `map_decI_beq`). All through `toNat` and `omega`; no `bv_decide`.

**Naming decision.** §3.1 proposed `Hdl.mk`/`tag`/`tier`/`idx`. The proofs already used `hdW`,
`tierW` and `idxW` (about 2 700 lines), so the API keeps those names and adds `tagW`. Renaming
would have touched every one of those lines for no proof saving.

**What the measurement found.** The inventory's I7–I10 lines are mostly *uses* of the encoding
(`h >>> 28 = 4` as a hypothesis, `decI` in a relation), which stay. The unfolding was in
**duplicated lemmas**: about 75 local copies of a dozen facts, each proved again by unfolding
`>>> 28`, `% 2 ^ 27` or `toUInt32` (twelve copies of decI injectivity, six of `decI_beq`, about
thirty tag lemmas, six `contains`/`findIdx` list lemmas, four `mask` lemmas). They are deleted
and their call sites point at the API (about 360 changed lines, mostly mechanical renames; a few
needed the handle kind pinned, `(k := .level)`, where a local copy had fixed it).

| | lines |
|---|---:|
| deleted local copies and their call-site churn | −1 145 |
| the API (`Handle.lean` 280 lines with documentation, `StoreFields` +77) | +689 |
| **net** | **−456** (141 files) |

**Time.** Elaboration of the 139 changed modules that exist on both sides, `lake env lean` per
file, base and branch back to back per file, 8 files in parallel (load 15–20): 534 s on master
39fd7338, 527 s on the branch (+1 s for `Handle.lean`). A change of −1 %, within the noise. As
expected: the deleted lemmas were each cheap; the saving is in lines and in one place to look.
`checker.s` is unchanged.

**Left for R0.** About 40 proof files still prove handle arithmetic by hand (`Env.ixW_toNat`,
`DerRel.idxW_tierW_of_decE`, `ExprMk.hw_fields`, `LpColRel.idxW_hdW`, …); with
`idxW_toNat`/`tierW_toNat'`/`hdW_toNat` most become a line or two. The record side of R0
(raw record reads I2 through `tfld`, the comparators and room checks of the store instances
through accessors, `TRec` rows by array name) is next.

### 7.2 R2 deferred with S

An exact two-word key already aborts unless both words are below `2^32`
(`ConAgua/Arena/ConsLib.lean`, the `R_CAP_KEY` guard of the packed tables), so every word a packed
push writes has a zero high half in its low field: the mask `x & 0xFFFFFFFF` never changes a
stored word. Its only purpose is the switch's byte identity (`lowerRec`'s `u32` truncation, §3.5).
On its own it adds one instruction per packed push to `checker.s` and proof work (the record word
`vsM` and the key word `kwQ` would differ, so `ExactOK.vs` would need a `< 2^32` hypothesis
threaded through `ConsLibRel` and the 8 packed instances) for no proof saving. Deferred with S
(coordinator's decision, 2026-10-27).

### 7.3 R1 deferred with S: the count slots are not where the `CTL` cost is

Measured before starting (master 5f775d94; numeric `set64 CTL k` / `arr64 CTL k` in proof files):
of 2 141 references, **46** name a count slot (`CTL[2]`‥`CTL[41]`). Proofs reach the counts almost
only through `tcnt`/`cntW`/`cntC`, which R1 would redefine without changing their users;
count-specific side conditions (`ctl_ne`, `c192_not_arena`) are about 20 lines. The cost of R1 is
the frames: every `MemFrame` list of an interning writer would gain the count arrays (143 literal
lists in 136 files, plus `KeepPost`/`Apart` frames and `ArenaRel.storeCtl`), the store library's
pushes and models, the scratch reset, freeze and promote (19 more frozen images, or one `RCNT`),
the `Final/Buf*` proofs of the frozen buffer, and a `checker.s` change. Estimated net proof lines
0 to +200 for 8–15 h, a wide change. §1.6's I5 row counted all numeric `CTL` vocabulary; it is
dominated by the non-count slots of §7.5. Deferred with S (coordinator's decision): its value is
the switch's layout, not proof lines.

### 7.4 The record side of R0, measured and not pursued

The raw record reads of §1.6 I2 sit in the store instances: each `*Refine.lean` has a bridge from
the library's word `fld S` to raw reads (`fld_lit0`, `fld_la0`, …: 25 lemmas, about 70 lines)
and a raw form of its record relation (`NatRec_raw`, `ARecRel_raw`, …: 18 lemmas, about 95
lines), because the instances' models (`mtM`, `hsM`: `lamatchW`, `lahash`, …) read raw words. A
generic bridge (`Schema.Fits S R`, `fld S = tfld R` for unpacked records, the two halves for packed
ones; about 30 lines) was prototyped on `LitRefine.lean`: the bridge lemmas go, but every proof
that meets the raw model (`litMatchOK`, `litNewOK` over `matchW`, the pool slices) needs the raw
form back, so the per-store `_raw` lemmas stay unless the models move to `tfld` too. That is the
"leaner hash template" (§2, rank 5), not a records API. Net saving about 5 lines per store for
several hours; not done. The comparators and room checks through accessors (`APP⟨t, v - 1⟩.f`
instead of `AREC⟨t⟩[v - 1] & 4294967295`) are an L-text change that expands to the same `Expr`,
with no proof saving on its own; left for the rank-5 template work, where the models change anyway.

### 7.5 Scoping: the hot non-count `CTL` slots as named globals (not implemented)

**Counts.** Master 5f775d94, proof files (generated program files excluded): numeric references
`set64 CTL k` / `arr64 CTL k`, files, L accesses `CTL.u64[k]`, and `MemFrame _ [… k …]` lists
naming the slot.

| slot | what it is (from the code's comments) | twin | proof refs | files | L | frames |
|---:|---|---|---:|---:|---:|---:|
| 200 | top of the work pool `IW` of the inductive stage | L-specific (con-ron builds Lean values) | 572 | 125 | 7 | 114 |
| 136 | top of the spine stack `SPN` | L-specific (con-ron recurses, lists) | 461 | 61 | 123 | 56 |
| 1 | the scratch flag | con-ron `scratchOn` | 438 | 126 | 196 | 68 |
| 129 | top of the environment record pool `EREC` | L-specific layout (con-ron keeps the constant infos as nested values) | 139 | 41 | 2 | 41 |
| 0 | the pool top | con-ron's pool size | 139 | 35 | 60 | 11 |
| 192 | top of the level heap `LH` | L-specific | 66 | 18 | 21 | 21 |
| 128 | number of `ECON` entries (`env_push`) | the length of con-ron's `IFEnv` constants | 58 | 6 | 5 | 5 |
| 137 | top of the binder stack `BSTK` | L-specific | 31 | 4 | 9 | 2 |
| 133 | number of `ETAB` entries | the length of con-ron's `env.tables` | 30 | 8 | 3 | 0 |
| 130 | number of pending checks `PEND` | con-ron's pending records | 20 | 6 | 5 | 6 |

These ten slots carry 1 954 of the 2 141 numeric `CTL` references (91 %).

**What a named global changes.** L already has globals (`L.GVar`, `Arena/Globals.lean`: `MODE`,
`PLO`, `PHI`, `INIT`). In the proofs:

* *Frames.* A global lives outside the arrays. Every array write leaves it (`Mem.setG`, the
  `*_setG` lemmas are `rfl`) and a global write leaves every array, so the `x ∉ arenaCtl` side
  conditions and the slot entries of `MemFrame` lists go. Which functions may write a global is
  a syntactic check of the program text (`closedG`, `globsIn`, `L/GKeep.lean`), proved once per
  call-closed set by `decide +kernel`, instead of a semantic frame per function.
* *Reads.* `rdW (m.arr64 CTL) 136` becomes a global read: no bounds, no `oob` branch in `vcgen`.
* *Cost.* The references above are renamed (mechanical: about 1 950 lines in about 200 files),
  each `MemFrame` list loses the slot and the writers' frame statements gain a global-write
  clause (about 330 frame lists). Slots whose value crosses the two entries of parallel mode
  (`0`, `1`, `128`, `129`, `130`, `133`: the seed `CTLF` carries them to entry 2) need entry 2 to
  seed the globals from the frozen header, a change to the stub and to the `Final/Buf*` proofs.
  The slots that only live inside one call tree (`136`, `137`, `192`, `200`) do not.

**`checker.s`.** A constant-index `CTL[k]` read compiles to four instructions (`genLd`: compare
with `CTL`'s length word, branch, load the base, load), a global to one (`mov r, [r15 + off]`);
writes likewise. `CTL[1]` (196 L accesses) and `CTL[136]` (123, the spine stack in the whnf and
walk loops) are on hot paths, so a small speedup is expected; to be measured.

**Named length-1 arrays instead** (`SPTOP⟨⟩[0]`, absarrays-style) give the frame separation from
`CTL` but keep the bounds check and the base load, add an array to every writer's `MemFrame` list,
and still need seeding for the cross-entry slots. Globals are the better fit.

**Estimate.** The four per-call slots (`200`, `136`, `192`, `137`: 1 130 proof references, 193
frame lists, no seeding): 8–14 h, net proof lines −200 to −500 (side conditions and frame entries
go; the renames are line-neutral), wide, colliding with any lane in the inductive stage, spine or
level-heap proofs. The cross-entry slots add the seeding (4–8 h, `Final` proofs, statements
unchanged). A pilot on `CTL[136]` alone (61 files) would measure lines, elaboration time and the
`checker.s` instruction count before a decision.
