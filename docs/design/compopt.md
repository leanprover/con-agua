# Lane `compopt`: compiler optimisation prototypes (journal)

Branch `compopt`, worktree `_tmp/wt/compopt`. Nothing lands in this phase: prototypes stay on the
branch, one commit each, until the coordinator assigns proof agents.

## Tools

* `scripts/bench.py`: interleaved benchmark (per round fixtures in random order, per fixture the
  systems in random order), `instructions:u` (median), wall median and spread, peak RSS (one extra
  run, `wait4`). Systems: `--bin NAME=PATH` / `--asm NAME=X.s` (first = baseline), con-ron
  (`--jobs=1 --pins`, 1 variant), `e2e-ref --pins=1`; `--no-conron`, `--no-ref`. Sets `quick`
  (8 small/medium accepted fixtures, ~1 s per round per system), `default` (+ 5 big ones), `full`
  (+ c05b, app-lam, eager_open_nat_control). The warm-up round picks CA_WORDS per fixture (2^22,
  2^25, 2^27: the first that does not error) and records verdicts; L binaries that disagree are
  flagged `MISMATCH`.
* `scripts/asmprof.py`: **exact** dynamic instruction profile. `perf record -e instructions:u` is
  useless at instruction level on this machine (AMD EPYC 9455: no precise `instructions` event; in
  a sampled profile of c03d, `ab_find` got 29% and 87% of its samples on the instruction after one
  cache-missing load; its true share is 8.4%, `der_b` 22.5% instead of 7.4%). The script inserts
  `incq ca_bb+8i(%rip)` at every basic-block start of the `.s` (flags are never live across a
  label or after a jump in this compiler's code), dumps the counters at exit, and attributes every
  executed instruction to its function and to a code-generator pattern. Validated: instrumented
  run's `instructions:u` minus the executed `incq`s = the plain run's count (5 728 480 447 on c03d).

## Baseline (master `efb16f47`, 2026-10-23)

`bench.py --set default --reps 3 --cpus 88-91` (load ~50–70):

| fixture | CA_WORDS | L instr | L wall | L RSS | con-ron instr | con-ron wall | e2e-ref instr |
|---|---|---:|---:|---:|---:|---:|---:|
| irrel_commit | 2^22 | 123M | 0.053 s | 89 MB | 80M | 0.022 s | 309M |
| mutual_struct_proj | 2^22 | 273M | 0.089 s | 150 MB | 122M | 0.030 s | 459M |
| inmodel_nested | 2^22 | 361M | 0.100 s | 182 MB | 146M | 0.032 s | 548M |
| long_line_5mib | 2^25 | 2 268M | 0.168 s | 200 MB | 962M | 0.357 s | 553M |
| c03d_pi_depth_1030 | 2^25 | 5 728M | 1.32 s | 1.3 GB | 2 025M | 0.27 s | 8 190M |
| let-ladder | 2^25 | 13 806M | 2.73 s | 1.3 GB | 4 546M | 0.88 s | 20 007M |
| beta-ladder | 2^25 | 25 177M | 5.27 s | 1.5 GB | 8 365M | 1.66 s | 37 348M |
| c04a_restart_70 | 2^25 | 43 089M | 7.23 s | 2.2 GB | 14 934M | 2.52 s | 54 301M |
| c05b_nest30_pi1000 | 2^25 | 1 470 822M | 57.1 s | 1.6 GB | 9 519M | 0.80 s | 36 384M |

Geometric mean over the 14 fixtures: con-ron/L = 0.32 instructions, 0.30 wall (L ≈ 3.1×);
e2e-ref/L = 1.06 instructions, 0.85 wall.

**The e2e report's perf column is wrong for the 9 capacity-retry fixtures**: `scripts/e2e.py`'s
`perf_instr` runs the L binary with `env` (no `CA_WORDS`), i.e. at 2^22, where those fixtures stop
with a capacity error. Hence app-lam 0.12, c04a 0.77, let-ladder 0.81, beta-ladder 0.51 in
`docs/e2e.md`; at the capacity they accept with, L is ~2.9–3× con-ron (c05b ~155×). The
instruction counts do not depend on the capacity once it suffices (c04a 43.09/43.03/43.01 G at
2^25/2^26/2^27; c05b 1 471/1 456/1 455 G).

**c05b: an L hash bug, not the compiler.** 98% of its 1.47 T instructions are in `rf_find`
(179 060 instructions per call, ~1 500 probes). `replace_fvars_go` keys the banked memo `rf` on
`(h, CTL[219] << 32)`, and `memoFindG` hashes `k1 ^ (k2 << 32)`: the bank is shifted out of the
hash, so every bank's entry for the same `h` lands in one probe cluster, which only grows (old
banks' entries keep the current stamp). con-ron uses a fresh `HashMap` per `replaceFVars`. Fix
(owning lane): pass the bank unshifted, or hash `k2` so it survives (e.g. `k1 ^ k2 * golden'`).

## Init as a fixture (task 2)

`lean4export` at `caccfbe` (the arena corpus's pin), built with Lean v4.29.1 (the corpus
toolchain), `lean4export Init`: 324 561 407 bytes, 6 058 389 lines, 12 s
(`_tmp/compopt/init/`, recipe: clone, `echo leanprover/lean4:v4.29.1 > lean-toolchain`,
`lake build`, `lake env .lake/build/bin/lean4export Init > init.ndjson`).

* With **one** pin variant (`romgen OUT 1`, what e2e uses) both con-ron and L decline/abort
  already on the arena's `init-prelude` (`unsupported Nat.div/mod spelling: no pin variant
  matched [at def Nat.mod]`): v4.29.1 is not the repository toolchain's variant. With all three
  variants (`romgen OUT 3`, `pins3.con-ron-pins`) both accept.
* **L accepts all of Init**: con-ron `accepted 53093 declarations`; L `accept`.

| | instructions:u | wall | peak RSS |
|---|---:|---:|---:|
| con-ron `--jobs=1` | 174.5 G | 21.9 s | 0.53 GiB |
| L, CA_WORDS 2^25 | 649.5 G (3.72×) | 63.3 s | 6.1 GiB |
| L, CA_WORDS 2^26 | 649.1 G | 86.0 s | 9.4 GiB |
| L, CA_WORDS 2^27 | 649.3 G | 78.6 s | 14.4 GiB |
| init-prelude: con-ron / L | 1.11 G / 3.96 G (3.6×) | | |

(L runs on a loaded machine, single runs.)

**With the 1-variant buffer: export at the pinned toolchain.** The 1-variant buffer is con-leche's
first pin dump, the repository toolchain's (v4.35.0; `vendor/con-leche/pins/README.md`). Init
exported by lean4export `5a9a355` (its v4.35.0 bump, format 3.1.0): 345 690 182 bytes,
`_tmp/compopt/init/init435.ndjson`. Both checkers accept it with the default 1-variant pins, so the
3-variant requirement above came only from v4.29.1:

| | instructions:u | wall | peak RSS |
|---|---:|---:|---:|
| con-ron `--jobs=1`, 57 919 declarations | 186.2 G | 24.5 s | 0.53 GiB |
| L (master compiler), CA_WORDS 2^25 | 696.7 G (3.74×) | 84 s | 6.2 GiB |

`bench.py --set init` = this export plus the arena's `init-prelude` (v4.29.1, run with 3 variants). RSS grows with CA_WORDS because the memo tables use the
whole array (`n := len >> 2`) and random probes touch every page: at 2^27, arrays 5, 50, 74, 151,
155 are touched to the last page (`CA_HWM`).

## Profile (task 3), exact counts (`asmprof.py`)

c03d (5.73 G instructions, 45.9 M calls; 58% of the instructions in leaf functions):

| category | share |
|---|---:|
| frame load (`mov k(%rsp), %rax/rcx`) | 20.8% |
| frame store (`mov %rax, k(%rsp)`) | 19.0% |
| reg move (`mov %rax, %rcx`, …) | 9.9% |
| const (`mov $k, %rax`) | 8.3% |
| alu | 6.3% |
| prologue/epilogue (stack check, `sub/add rsp`) | 4.0% |
| zero locals | 3.3% |
| result registers zeroed (`mov $0, %rdi/r8–r11`) | 3.3% |
| cmp + jcc | 5.9% |
| fuel/stack check | 2.4% |
| result area zeroed (`movq $0, k(%r15)`, nres = 9) | 2.4% |
| param copy | 2.2% (+ the same in frame stores) |
| bounds check (cmp len + jae) + base load | 5.5% |
| array element load/store | 1.8% |
| call/ret/lea | 2.4% |

Same picture on c04a (43 G), init-prelude (3.96 G), irrel_commit (123 M), long_line_5mib: frame
load+store 38–41%, reg move ~10%, const 6–9%; per-call fixed overhead (prologue 5, param copy 2
per parameter, zeroing, 8 result writes, epilogue 2, call side 4–5) ≈ 25 instructions × calls
≈ 20% of the total.

Top functions (c03d): `der_b` 22.5% (8.8 M calls, 147 instructions each: a chain of
`if tag == k` tests, 7 instructions each because the constant goes through a temporary),
`ab_find` 8.4%, `ab_put` 6.3%, `abs_go` 4.9%, `mk_app` 4.3%, `abs_app` 4.2%, `app_push` 3.6%,
`e_view` 3.3%; the hash finds/puts and `der_b`/`e_view` are leaves.

Patterns (from `perf annotate` / the counts):
* every binary op and comparison spills its left operand to a temporary and reloads it, and moves
  the right operand through `rax` to `rcx`, even when it is a variable or constant: `x == k` is
  `mov x,rax; mov rax,t; mov $k,rax; mov rax,rcx; mov t,rax; cmp rcx,rax; jcc` (7 instead of 2).
* every return writes all `nres = 9` results (6 registers, 3 table words), mostly zeros.
* `ret e` evaluates into a temporary, then loads the result register from it.
* every call copies its arguments twice (caller temporaries, then callee frame).

## Prototypes (task 4)

All on branch `compopt`, one commit each, cumulative (each builds on the previous): the proofs are
not updated. `compopt-asm` (`ConAgua/E2E/AsmOpt.lean`, lakefile entry) is `e2e-l asm` without
the import of the compiler proof, so a prototype builds while the proof is broken. With the
prototypes, `ConAgua/Compiler/SimExpr.lean` (`sim_expr`, from the `var` case on) and
`ConAgua/Compiler/Tests.lean` (`#guard`s on compiled output) fail; everything importing them
(`SimStmt` … `Correct`, `Main`, `Final.Statement`, `e2e-l`) is not built.

| step | commit | what |
|---|---|---|
| A | 5e5d8c74 | right operand that is a variable/global/length/imm32 constant used in place (memory or immediate operand), others loaded straight into `rcx`/`rdx`; `x := x op k` as one read-modify-write |
| B | bb0e4f8b | per-function result count (`Stmt.nret`): a function sets only its longest `return`'s results, not all `nres = 9`; a caller reading more zeroes the extra ones |
| C | c1e135be | leaf functions keep up to 9 locals in registers (rbx r12 r13 rdi r8–r11 rsi; the trampoline saves rbx r12 r13); `cmp reg, op`; simple call arguments and return values without temporaries |
| D | e43bfe52, b8f108f2 | ≤ 9 arguments in registers (rdi r8 r9 r10 r11 rsi rbx r12 r13), a leaf's parameters stay in them; leaves without frame use get no frame and no stack check; return values computed into the result registers (result 0, `rax`, last); non-parameter locals prefer non-result registers |
| E1 | c79031ff | `x * 2^k` as a shift |
| E2 | 345dbb1a | zero only the locals that may be read before assigned (definite assignment over the structured body) |
| E3 | 550fab33 | temporaries of leaves in free non-result registers |

`bench.py --set default --reps 3 --no-ref --cpus 88-89` (13 fixtures, interleaved; load ~22),
geometric means relative to base:

| | instructions | wall |
|---|---:|---:|
| base | 1.000 | 1.000 |
| A | 0.666 | 0.930 |
| B | 0.610 | 0.886 |
| C | 0.564 | 0.861 |
| D | 0.513 | 0.841 |
| E1 | 0.506 | 0.808 |
| E2 | 0.479 | 0.827 |
| E3 | 0.472 | 0.817 |
| con-ron | 0.435 | 0.377 |

c03d (exact counts): 5.728 → 3.860 (A) → 3.532 (B) → 3.286 (C) → 2.988 (D) → 2.909 (E1) →
2.728 (E2) → 2.697 G (E3). Init (v4.35.0 export): base 696.7 G, E3 324.4 G (1.74× con-ron's
186.2 G).

**Wall time is memory-bound.** IPC is ~1.5 at base and ~0.9 after E3 on c04a: instructions fall
53%, user cycles ~25%. On the small fixtures (~50 ms) the wall time hardly moves at all: it is
kernel time for page faults (irrel_commit: 27 ms of 41 ms in the kernel, 45 000 faults, 91 MB of
pages touched for a 69 KB input).

**Verdict agreement.** Every prototype agrees with base on the quick set; the full 675-fixture
agreement check (`bench.py --set all --reps 0`) of A and of cumulative E2 against base: see below.

### Proof effort (estimates; the simulation relation is `Inv` in `Rel.lean`)

* **A** (+E1): low. `Inv` unchanged; new Kraken step lemmas for the memory/imm operand forms of
  add/sub/and/or/xor/imul/cmp and `shl/shr imm8`; `sim_expr`/`sim_cond` get a branch for
  `binSimple`/`cmpSimple`, `sim_set` one for `setInPlace` (a frame-slot RMW), `sim_st8/64` one for
  `loadInto rdx`. ~400–700 lines. Assigned to lane compproofA.
* **B**: medium. `ResOut` is stated with `G.tab.nres`; it becomes per callee (`Stmt.nret` of its
  body): needs `nrs = p.map …` lookup facts at call sites and `es.length ≤ Stmt.nret body` for
  every `ret` (structural). The entry's outcome (`Outcome.ofState`, `results`) reads `tab.nres`
  results; it must read the entry's count.
* **C**: medium–high. `Inv.frame` becomes a location map (register or slot per local); every
  lemma reading/writing locals splits on it. Callers are never leaves, so at call sites the map
  is all-memory and `SimCall` keeps its shape; the callee may clobber rbx r12 r13 rdi r8–r11 rsi,
  which the caller's `Inv` never mentions. The trampoline saves/restores rbx r12 r13 (ABI).
  `retDirect`'s hazard check needs a lemma that the values do not read registers written before.
* **D**: medium–high. New calling convention in `SimCall`/`SimFun` (arguments in registers instead
  of at `rsi`); frameless leaves need an `Inv` variant without `lo8`/frame (no call, no slot).
* **E2**: medium–high. Flow-sensitive relation: `Inv.frame` only for definitely assigned locals
  (or an L-level lemma that unassigned locals are never read, so their value is irrelevant).
* **E3**: small on top of C (temporaries get the same location map).

### Not pursued
* Self tail calls: calls into self-recursive functions are 6.1% (c03d), 8.0% (init-prelude),
  3.9% (c04a) of all calls.
* Non-leaf register allocation with callee-saved registers: non-leaf frame traffic is ~19% of
  c03d after E2; three callee-saved registers with push/pop per call net maybe ~4%; needs a
  whole-program "callee preserves rbx r12 r13" invariant.
* Transparent huge pages (`madvise(MADV_HUGEPAGE)` on the arrays): user cycles -16% on c04a, but
  the kernel zeroes 2 MB per touched huge page of the sparse tables: irrel_commit 0.07 → 0.43 s.

**Verdict agreement, full.** `bench.py --set all --reps 0` (675 fixtures), A vs base and cumulative
E2 vs base: 0 disagreements each.

**Init, per step** (`bench.py --set init --reps 2`, interleaved, wall spread 3–41%): base 696.7 G /
70.5 s; A 457.2 G / 64.5 s; B 420.6 G / 51.7 s; C 393.1 G / 51.4 s; D 354.8 G / 41.5 s; E1 348.7 G
/ 50.6 s; E2 328.9 G / 43.8 s; E3 324.4 G / 46.1 s; con-ron 186.2 G / 20.4 s. Coordinator's call:
A+E1 to a proof lane (compproofA), then B, then D (+ what it needs of C); E2/E3 skipped.

## The memory side

Instrumented first: wall time is memory-bound (IPC ~0.9 on c04a after E3), and on small fixtures it
is page faults. The harness already maps every array lazily (`MAP_NORESERVE`, zero pages on first
touch) and zeroes nothing; the faults come from what L touches. Per array (`CA_HWM`): the dense
record arrays (`AREC`, `ADER`, …: append-only) touch only what they use, at any capacity; the
**hash tables touch every page**, because they span the whole array (`n := len >> 2` or `>> 1`)
and a few thousand random inserts hit every page. irrel_commit (69 KB input): 98 arrays, 91 MB of
touched pages, 45 000 faults, 27 ms of 41 ms in the kernel.

Two kinds of hash tables:
* **memo tables** (the 43 `memoPutG` schemas; arrays 24, 41, 47–54, 75, 76, 96–106, 146–153, 155,
  201–207): caches with stamp clearing; they abort at 3/4 load.
* **intern slot tables** (`SLOT`, `ASLOT`, `SSLOT`, `ZSLOT`, `MSLOT`, `ISLOT`, `PSLOT`, `SOSLOT`,
  `CSLOT`, `LESLOT`, `BSLOT`, `LASLOT`, `FASLOT`, `NSSLOT`, `NNSLOT`, 72–74): hash-consing, must hold
  every node; abort when full.

Probe locality is already fine: slots interleave stamp/keys/value (one cache line), and finds cost
~1.0–1.05 probes on Init (sparse tables). The cost is one cache miss per lookup, because the table
is far larger than the cache (a memo table at 2^25 words is 256 MB); `app_find` takes a second miss
for the record behind the slot (`ASLOT` holds indices; storing the key in the slot would save it, a
layout change).

Experiments (harness: `CA_SIZES`/`CA_SMALL` per-array capacities, commit a6b6d0f7/36e6bc89;
program: `scripts/compopt/progedit.py flush` = memo put flushes at half load instead of aborting;
wrappers in `scripts/compopt/`):
* Memo tables at 2^16 words + flush (`flush16`): without the flush Init aborts at small sizes; with
  it, default set wall 0.714–0.732× of E3 (instructions 1.035×: more recomputation), c04a 6.3 →
  3.9–4.5 s, Init 0.74× (51.0/40.4 → 42.8/33.0 s in two runs), Init RSS 6.35 → 2.9 GB. At 2^20 a
  single Init run was slower (high load, long probe runs): keep load ≤ 1/2.
* Intern slot tables: the smallest size that accepts is workload-driven, not input-size-driven
  (`scripts/compopt/minslot.sh`): 2^16 words for every fixture up to 5 MB of the default set,
  but 2^22 for c03d (303 KB), 2^24 for let-ladder (468 KB) and c04a (9 MB), 2^25 for beta-ladder
  (461 KB), 2^24 for Init. So a harness heuristic from the input size cannot pick it; a retry
  ladder (double on a capacity error) wastes the failed runs (c03d: 1.16 s instead of 0.53 s).
  **Oracle sizing** (what growable tables would give; `scripts/compopt/oracle.sh`: records 2^27,
  memo 2^16 + flush, slot tables at their minimum): default set wall **0.505×** of E3 (con-ron
  0.431×); the small fixtures run at con-ron's speed (irrel_commit 28 ms, con-ron 24 ms; RSS 26 MB
  both); c03d 1.22 → 0.60 s, c04a 6.0 → 3.8 s; Init 0.69× (noisy; ≈ flush16: Init's slot tables
  need 2^24 anyway).
* Record capacity costs nothing (lazy, dense): irrel_commit at 2^18 or 2^25 record words alike.
* Huge pages only for the dense arrays (`madvise` where the array is not a table): no gain on c04a
  (3.50 → 3.49 s), irrel_commit 11 → 26 ms (2 MB zeroing). Not worth it.

**Proposals, with proof/twin impact:**
1. (Superseded: lane memoflush found the flush unsound for tables that are not caches, e.g. the
   hoist name index, visited sets, `RSET`; it does growable memo tables instead, as the twin,
   measured 0.692× wall on the default set.) Memo flush at half load: a memo is a cache, so the change is "clear instead of
   abort"; `memoPutG_spec` gets a second case (cleared table + the entry); callers only rely on
   "a hit is correct". Then memo arrays get a small fixed capacity (2^16 words) in the harness
   (sizes are inputs of the theorem: no proof). Gain ~27% wall on the default set and Init.
2. Growable intern slot tables: capacity in `CTL`, starting small; at load > 1/2 double (up to the
   array length) and rehash by walking the records (they are dense, so the walk is cheap). Twin:
   con-ron's `HashMap2` (`hashmap2.rs`, `try_resize`: "Double the slot count and rehash", the
   new table inherits the epoch) grows exactly like this, so L's fixed full-array tables are the
   deviation and growth makes L the closer twin; the rehash stays below the refinement (the slot invariant "every record is findable" is re-established
   by the rehash). Medium–high proof (one lemma per slot-table library if they share one). Gain on
   top of 1: default set 0.714 → 0.505× wall; small fixtures reach con-ron.
3. Inline keys in `ASLOT` (no second miss per app lookup): layout change, medium proof; not
   measured.
After 1+2 the remaining gap on the big fixtures (c04a 3.8 s vs con-ron 2.2 s, Init ~2×) is
instructions (Init 1.67× con-ron after E3) and the per-lookup misses.
3. Inline keys in `ASLOT`, measured (`progedit.py inlineaslot`: 4-word slots `value, f, a`, so
   `app_find` compares in the slot and never reads `AREC`; on top of the oracle sizing, array 5
   with four times the words): **no gain**. Default set wall 1.066× (instructions 1.007×), Init
   1.018× (noise), RSS up (Init 2.6 → 3.0 GB): the bigger slots touch more pages and the
   `AREC` read was mostly a hit anyway. Dropped.

## Summary (lane closed)

* **Tooling** (landed from branch `compopt-tools`): `scripts/bench.py` (interleaved benchmark,
  sets quick/default/full/init, `--reps 0` verdict agreement), `scripts/asmprof.py` (exact
  per-block instruction profile; `perf record` sampling is useless at instruction level here),
  `compopt-asm` (`ConAgua/E2E/AsmOpt.lean`: `e2e-l asm` without the proof imports),
  `harness/e2e.c` `CA_SIZES`/`CA_SMALL` (per-array capacities), `scripts/compopt/` (progedit.py:
  L-source prototypes on program files; flush16.sh/oracle.sh/minslot.sh: the sizing experiments,
  `CA_BIN` = a binary of a `flush` program).
* **Init** is a fixture: lean4export `5a9a355` at v4.35.0 (the 1-variant pins' toolchain), both
  checkers accept; master L 696.7 G instructions / ~70–84 s vs con-ron 186.2 G / ~21–24 s.
* **Compiler** (branch `compopt`, prototypes A–E3, no proofs): instructions 0.47× on the default
  set and Init, wall 0.82× (default) / ~0.65–0.70× (Init). Assigned: A+E1 → compproofA; B, then
  D (+ what it needs of C) queued; E2/E3 skipped (wall gain within noise).
* **Memory** (wall is memory-bound): hash tables spanning whole arrays touch every page and miss
  the cache on every lookup. Growable tables (memo: lane memoflush; intern slots: lane slotgrow,
  both twins of `hashmap2.rs try_resize`) give, measured with oracle sizing, 0.505× wall of the
  E3 binary on the default set, con-ron's speed on small fixtures. Remaining gap on the big
  fixtures (c04a 3.8 s vs 2.2 s; Init ~2×): instructions (Init 1.67× con-ron at E3) and the
  per-lookup misses.
* **Found on the way:** the e2e perf column measured the failing 2^22 run for capacity-retry
  fixtures (→ perfplot); the `rf` memo's bank shifted out of its hash, c05b 1.47 T instructions
  (→ rfhash); der_b only after a cache miss and tag order by frequency, Init -4.9% instructions
  (→ derb).
