# Lane lnext2: the next steps for L, re-ranked (analysis journal)

Question: since `lnext.md`, a lot has landed: the unified ok/error refinement (unifiede §3.57),
`vc_flat` + `grind` as the default closer (§3.59–3.61), the split model modules (§3.58), the
single-pass parser, presized tables, SWAR `read_nat`, packed 32-bit primitives (p32.md) and the
warnings gate. Where are the largest remaining gains, on speed, proof size and build time? Base:
master 9f71ffee. Nothing landed but this journal. Scratch: `_tmp/lnext2/` (`survey/`: lnext's survey
scripts rerun on this master; `prof/`: exact profiles; `cold.log`: a cold build; `ph.json`: phase
bench; `proto/Inline.lean`: lnext's inliner, patched for the 32-bit constructs; `wb1.json`,
`wb16.json`: paired wall benches).

## 1. Measurements

### 1.1 Wall time against con-ron, by phase

`phase.py` (after parsespeed's `phasebench.py`): 7 interleaved rounds of the four runs, under
`perf record -T`, on `Init`. Parse = the end of the last 50 ms window of the parsing thread with at
least 10 % scanner samples. Serial end = the first 50 ms window after the parse with 4 or more
threads sampled. 1-thread runs pinned to one core (both SMT threads), 16-thread runs to CPUs 24–39.
Load 4–31 (median 6). Medians:

| | ours | con-ron | ours ÷ con-ron |
|---|---:|---:|---:|
| 1 thread, whole run | 18.13 s | 18.38 s | **0.99** (paired median) |
| 1 thread, parse phase | 1.85 s | 1.65 s | 1.12 |
| 16 threads, whole run | 3.67 s | 3.36 s | **1.09** (paired median) |
| 16 threads, parse phase | 1.85 s | 1.65 s | 1.12 |
| 16 threads, serial part after the parse | 0.45–0.50 s | 0.45–0.50 s | 1.0 |
| 16 threads, parallel phase | 1.31 s | 1.17 s | 1.12 |

* **One thread is at parity.** The parse phase is 0.2 s slower, the rest is slightly faster.
* **At 16 threads the gap is 0.31 s.** The parse phase accounts for 0.20 s of it, the parallel
  phase for 0.14 s. The serial work between them is equal. lnext measured 1.3 s of gap here.
* **Other inputs** (OVERVIEW §3, master 54018587, not re-measured): app-lam 1.82×, c05b 1.85×,
  beta-ladder 1.63×, let-ladder 1.40×, eager_open 1.30×, c04a 1.31×. These are now the large
  gaps.

### 1.2 Exact instruction profiles (`asmprof.py`, `checker.s` of master)

**`Init`** (237.3 G instructions, 4.73 G calls; 50.5 % in leaves):

| function | share | calls | per call |
|---|---:|---:|---:|
| `der_b` | **10.3 %** | 613 M | 40 |
| `ilm_find` | 5.5 % | 238 M | 55 |
| `mk_app` | 4.9 % | 164 M | 71 |
| `app_find` | 4.2 % | 173 M | 58 |
| `ilg_app`, `intern_app`, `ilg_go` | 4.2, 4.1, 4.0 % | | |
| `ilm_put` | 3.5 % | 116 M | 71 |

By category of generated code:
* frame stores and loads (locals of non-leaf functions): 15.3 %;
* the fuel and stack check: 5.6 %;
* prologue and epilogue: 5.5 %;
* result registers: 5.8 % (loads 5.2 %, zeroing 0.6 %);
* bounds checks: 4.9 % (`cmp` 1.6 %, `jae` 3.2 %);
* `call` and `ret`: 3.4 %.

`der_b` has 18 call sites. Its 613 M calls come mostly from the walks (`ilg_go`, `il_go`,
`il_bvar`, `lp_go`, `inst_go`, …). Only about 146 M come from `mk_app`'s misses. Its code (in
`checker.s`) shows three generic leftovers:
* a linear chain of tag compares;
* a bounds check on `CTL[4 + tier]`-style indices whose range is known (`tier ∈ {0,1}`);
* a `min(x + 1, 32767)` computed by multiply-select (L has no select).

**app-lam** (50.2 G): `app_push` 23.4 % (366 per call) and `lam_push` 5.8 % (364). Both are
mostly the in-place table growth (D38; lnext §1: 18 % of all instructions). Next come `der_b`
12.3 % and `ilm_find` + `ilm_put` 21.2 %.

**c05b** (14.4 G): `e_view` 9.7 %, `forall_find` 7.9 %, and the memos `rf_put` / `rf_find` /
`crm_*` / `ta_*` / `ab_*`, together about 30 %. This is the same picture as in lnext.

### 1.3 Proof lines (lnext's survey, rerun)

`loc.py`: 338,720 proof lines (all lines that are not L code). Without comments and blanks
(the survey's count): **298,543**, against 339,025 at lnext's base.

| layer | lines | share | at lnext |
|---|---:|---:|---:|
| refinement (model ⊑ twin) | **108,287** | **36.3 %** | 116,077 |
| other lemmas | 49,678 | 16.6 % | 53,985 |
| commands, structures, other | 34,610 | 11.6 % | 36,116 |
| model equations | 28,721 | 9.6 % | 29,947 |
| spec (L ⊑ model) | 26,592 | 8.9 % | 30,471 |
| hand word models | 8,877 | 3.0 % | 13,187 |
| frames | 9,523 | 3.2 % | 10,788 |
| error claims | 5,451 | 1.8 % | 21,737 |

The unified refinement removed the error-claim layer, as planned. **What dominates now is the
refinement layer, and all of it is written by hand.** The L ⊑ model side is generated where the
generator reaches, and mgen.md §7–8 shows that its coverage is saturated: the remaining ~840
hand specs are blocked by reach, shape or time, not by generator features.

What a refinement proof is made of (4,157 theorems by the survey's regex; median 11 lines; 42 k
of the lines in theorems of 61–150 lines). Read in `ctor_ref` (`Arena/IndT/Sum4.lean`, 243
lines) and `bsrW_ok` (`IndPartsSpec/BsW.lean`), it is a lockstep walk. For each callee:
* split on the model's call (`rcases h : callW …` / `liftE_none` / `liftE_some`);
* take the callee's triple (`triple_of_callW`);
* apply its ok lemma;
* thread the invariant packages (`StageC.of_pstep`, `hg₁.trans hg₂`, `AbsOK` via `*_afr`);
* apply the twin bridge lemma;
* close with `RefE.bind_right`, and split the abort arm (`by_cases r.headD 0 = 0`, `.k_f.abort1`).

The idioms, counted:
* `liftE_none` 602;
* `triple_of_callW` 680;
* `RefE.bind_right` / `bind_left` 660;
* `RefE.of_cls0` 997;
* invariant `.trans` 864;
* `StageC` 826.

By line pattern, at least **27 %** of the lines in the 283 `RefE` theorems (25.2 k lines) are
this per-call and per-arm plumbing (a lower bound: most `have`/`obtain` lines of callee results
do not match the regex). `toNat` appears in the statements of theorems holding 77 k of the
108 k refinement lines.

Other patterns (same scripts as lnext §2):
* word ↔ `Nat`: 32.0 k lines (34.6 k at lnext);
* fuel: 15.6 k (18.4 k);
* abort plumbing: 9.9 k (12.6 k);
* glue: 17.8 k (`hp.get`/lookups 5.5 k, `vcgen` calls 3.4 k).

### 1.4 Build (cold build of this master, `LAKE_COLD=1 scripts/lake build`, 16 jobs, load 5–32)

* **Wall 452 s**; CPU 7,145 s user + 1,710 s system; 5,742 module-seconds (2,047 modules).
* **Critical path 327 s** (54 modules; `cp.py`, unlimited cores). buildtime.md had 421 s.
* **The whole-program modules** (`Checker/*`, `Final/*`): **1,253 module-seconds in 118 modules,
  22 % of the build**:
  * `ProgWf` 76 s, `ProgSkt` 74, `PrepProgChecker` 60, `AsmStubEq` 59, `PreLoopWSStages` 58;
  * `AsmPart0–5` 197 in all;
  * `LoopAll` 32, `Prelude` 32, `IndArmClosed` 40.
* **The critical path runs** `L → Scan → Front → Rom → Checker.ProgTab (20 s) → ProgWf (76 s) →
  PreludeSimProg (18 s) → … → Final`.
* **Rebuild after an edit** (`cp.py --touch`, these times):

  | edited module | rebuilt modules | module-seconds | critical path |
  |---|---:|---:|---:|
  | `Checker/Prog` (the generated program: every L change) | 81 | 1,110 | **199 s** |
  | `Arena/ExprMk` (a widely imported spec) | 1,039 | 4,064 | 278 s |
  | `Compiler/Compile` (the code generator) | **814** | 3,512 | 233 s |
  | `L/ModelGen` | 947 | 3,890 | 288 s |
  | `Arena/IndT/Sum4` (a typical refinement) | 24 | 69 | 53 s |

  So every landing that changes L code pays about 200 s of critical path in the whole-program
  kernel checks, whatever function it changed. An edit to the code generator rebuilds 814
  modules. restructure.md had brought a compiler-proof edit down to 46 modules; `Compile.lean`
  itself is imported far more widely (layout map, `Tab`).
* **Elaboration by module kind:**

  | kind | module-seconds |
  |---|---:|
  | modules with an `l_model` | 995 (190 modules) |
  | refinement modules (twin `.run`/`RefE`, no `l_model`) | 1,032 (365) |
  | whole-program | 1,253 |
  | vendored con-leche/con-ron | 908 |
  | other | 1,475 |
  | compiler | 79 |
* **CI** (GitHub, 4 cores): the last runs on master (2026-10-26/27) spent **65 min in `lake
  build`** of a 1 h 40 min run. Most of a run is a rebuild: any `.lean` change misses the cache's
  primary key, and a change to a widely imported module rebuilds most of the restored build.

### 1.5 The inliner, re-measured on this master

lnext's prototype (`proto/Inline.lean`, unproved), with shift and size arms added for `ld32t`,
`ld32h` and `st32t`. Size 0 gives a byte-identical `checker.s`. S = 80 with two rounds inlines 263
leaves:
* `skip_ws` and `key_end` are inlined;
* `der_b`, `e_view` and `key_at` are too large.

`diff-e2e --bin`: 634 of 634 agree. Instructions on `Init`: 237.32 G → 233.24 G (**−1.72 %**).

Wall, paired interleaved rounds (`internspeed/wb.py`, `wstats.py`):

| cell | n | base | median paired | Wilcoxon p | mean, 95 % CI | load |
|---|---:|---:|---:|---:|---:|---|
| `Init`, one thread (CPUs 44,92) | 14 | 18.26 s | **−3.4 %** | 0.013 | −4.3 % [−9.5, +1.3] | 6–47 (median 11) |
| `Init`, `--jobs=16` (24–39) | 30 | 3.68 s | **−2.8 %** | < 0.001 | −3.1 % [−4.6, −1.5] | 9–13 |

In lnext this was −2.9 % wall (load 9); parsespeed found −4.6 % on the parse phase. The code is
now instruction-bound (2.96 IPC on a quiet machine, OVERVIEW §3), so the saved instructions show
in the wall time. The one-thread interval is wide, and a quieter rerun should confirm it.

## 2. Ranked next steps

| rank | step | axis | key number | cost | taste |
|---:|---|---|---|---|---|
| 1 | L → L inliner, proved once | speed | −2.8 % wall at 16 threads (p < 0.001), −3.4 % at one thread (p 0.013) | 12–18 h, ~850 lines in `Compiler/` | fits |
| 2 | Refinement generator: the lockstep model ⊑ twin walk generated, closed by `grind` (pilot first) | proofs | refinement 108 k of 298.5 k lines (36 %); ≥ 27 % of `RefE` lines are plumbing | pilot 15–25 h; generator 30–50 h | fits |
| 3 | Whole-program checks split and kept off the critical path | build | an L change: 199 s critical path, 1,110 module-s; `ProgWf` 76 s on the cold path | 6–12 h | neutral |
| 4 | The 16-thread gap: `der` in the parser, then a profile of the parallel phase | speed (threads) | parse 1.85 vs 1.65 s; parallel 1.31 vs 1.17 s | `der` ~600 lines; analysis 3–4 h | fits |
| 5 | In-place forward table growth (no staging region) | speed (table-heavy inputs) | app-lam 1.82× con-ron; `app_push` 23 % at 366 per call | prototype 4–8 h; proof 12–20 h | fits; unparks D38 work without OS calls |
| 6 | Range-based check elimination and the other codegen leftovers, after 1 | speed | bounds checks 4.9 %, fuel 5.6 %, result registers 5.8 % of instructions; each ≤ 1–2 % wall | 10–25 h each | fits (proved once), small |
| 7 | Counted `for` with `Nat`-indexed loop models | proofs, L | −1.6 to −2.5 k lines (lconstructs §3) | 15–24 h | fits, small |

### 1. The L → L inliner, proved once

**What.** A `Prog → Prog` pass before `compileProg`. It inlines leaves of at most S nodes, as in
the prototype. One theorem, `inline_sound`: a run of the inlined program is a run of the original,
with no more fuel. The proof plan is parsespeed §6:
* shift lemmas;
* a tail-conversion lemma and a lemma for the `while true { …; brk }` wrapper, each against
  `exec`'s call rule;
* a program-level induction on fuel;
* wiring into `checkerFile_eq`.

**Why.** It is the one compiler change with a significant whole-run gain at 16 threads
(§1.5), and the gain is now also visible at one thread. With rank 4, a 16-thread result near
1.0× is in reach. It also means that small, twin-shaped helper functions cost nothing at run
time, so L can follow the twin's factoring more closely.

**Cost and risks.**
* About 850 lines, 12–18 h, all in `Compiler/`. No per-function proof changes: they are about
  `checkerProg`.
* The kernel evaluates the inliner once inside `asm_lit`/`checkerFile_eq`, which already lies on
  the 200 s whole-program path (rank 3); measure that evaluation first.
* Keep the pass in its own module that only `Checker/Asm*` and `Final/*` import. An edit to
  `Compiler/Compile` already rebuilds 814 modules (§1.4).
* Two smaller risks: the shift lemmas around the statements with implicit locals (`scan8`,
  `copy*`), and the layout effects of ±1 % that nlregs saw.

### 2. A refinement generator (pilot first)

**What.** For a function whose model is generated (`l_model … unified`), generate the model ⊑ twin
refinement as the uniform case chain that unifiede made the norm. Per call:
* split the model's continuation on the callee's outcome;
* use the callee's registered refinement (`@[refines]` / `RefE`) under the caller's invariant
  package;
* thread the package (`.trans`, `of_pstep`);
* step the twin through `RefE.bind_right` / `bind_left`;
* at each guard, prove that the L condition equals the twin's condition through the decode
  lemmas, closed by `grind` with the bridge and decode lemmas as hints.

The hand part that remains: the statement (relation, invariant package, decode hypotheses) and a
list of bridge lemmas.

**Why.** The refinement layer is the largest (108 k lines, 36 %) and the only layer that is
still hand-written everywhere. The generator has run out of functions to reach on the L side
(mgen §7–8). The `RefE` theorems now all have one shape (§1.3: ≥ 27 % of their lines match the
per-call and per-arm idioms, a lower bound). This is "the slider toward the compiler" for proofs:
written once in a generator, not per function.

**Expected gain** (uncertain until the pilot):
* the 283 `RefE` theorems (25 k lines) at −40 to −50 %: **−10 to −12 k lines**;
* extended to the ok-only refinements in `Arena/` (`RefAM` / `…W_ok` lemmas of the same lockstep
  shape), perhaps −20 to −35 k in all;
* every new or twin-synced function then costs its statement and its bridge lemmas only.

**Pilot.** The 3–5 `RefE` functions of one family (`IndT/Sum4`'s `ctor_ref`, `ctl_ref`, and
their callees). Measure lines and elaboration time against the hand proofs, three runs each.
Go if ≥ 40 % fewer lines and no slower modules.

**Risks.**
* High: the invariant packages differ by family (`StageC`, `StageR` + `IWGrow`, `AbsOK`, the
  memos);
* the twin side's `bind`s must be unfolded in step with the model's continuations, and where L
  merged or split twin functions the walk does not line up;
* `grind` on bridge goals may be as slow as §3.59's 60–100 ms per condition was before `hom`
  went off.

### 3. Whole-program checks off the critical path (build)

**What.** Split `ProgWf` (76 s, on the cold critical path), `ProgSkt` (74), `PrepProgChecker`
(60) and `PreLoopWSStages` (58) by a stable partition of the function list, as `AsmPart0–5`
already are, so the parts run in parallel. Check whether the `ProgTab → ProgWf → PreludeSimProg`
chain needs to be a chain at all.

**Why.** Every landing that changes L code pays about 200 s of critical path (81 modules,
1,110 module-s) whatever it changed. The whole-program modules are 22 % of all elaboration.

**Gain** (estimate, not measured): −40 to −80 s on the critical path of every L-changing
landing and of a cold build (327 s). It does not shorten the CI build, which is bound by total
CPU on 4 cores.

**Cost and risks.** 6–12 h; low risk (restructure.md and buildtime.md did the same kind of
split). A further step would make `Compiler/Compile`'s wide import fan-out (814 modules)
narrower, which matters once rank 1 and 6 edit the compiler.

### 4. The 16-thread gap: parse phase, then parallel phase

**What.**
1. Land internspeed's `der`: the parser keeps each id's derived word with its handle and passes
   the children's derived words to `mk_*`, so `der_b` is not called there. The prototype gave
   −5.5 % on the parse phase (p < 0.001); proof plan in internspeed §5, about 600 lines.
2. Profile the parallel phase per thread (`perf record -T` per worker, as lnext §1 did for the
   serial part): is its 1.12× load imbalance, or per-thread speed (`der_b`, the instantiate
   memos)?

**Why.** At 16 threads the remaining 0.31 s is 0.20 s in the parse and 0.14 s in the parallel
phase (§1.1). The inliner takes perhaps 0.08 s off the parse (parsespeed's −4.6 %), `der` about
0.10 s.

**Risk.** `der` changes the parser's id-table record, a twin deviation to record. The profile
of the parallel phase is cheap.

### 5. In-place forward growth (table-heavy inputs)

**What.** Replace D38's in-place absl rehash (mark pass, swap chains: 145 instructions per
re-insertion) with an order-preserving in-place doubling. Homes are `mulhi` (top bits), so after
the doubling an entry's new home is `2h` or `2h + 1`:
* a top-down sweep moves each entry to the first free slot from its new home, which is at or
  above its old index, unless its displacement exceeds its home;
* the few entries whose displacement exceeds their home (the first cluster, and wrapped
  entries) are deferred to a short bottom-up pass.

Unlike lnext §3.5's `back`, it needs no staging region, so peak RSS does not grow. The memory
note parks the growth work "unless an in-place variant … appears"; this is one.

**Why.** app-lam is 1.82× con-ron, beta-ladder 1.63×. `back` measured −17.5 % cycles on both,
and the cycles were in cache misses of the mark and swap passes. A sweep in order has the same
access pattern as `back`.

**Uncertain.**
* The deferred-entry pass and the wrap-around case are where the marks were needed: prototype
  before any proof (4–8 h in `_tmp/rehashproto/Grow.lean`'s harness).
* Proof 12–20 h (lnext §3.5's estimate for `back`).
* `Init` gains nothing (presize).

For the record: on app-lam, L's peak RSS is 1,920 MB against con-ron's 2,761 MB. Even `back`'s
+33 % (2,560 MB) would stay below con-ron's.

### 6. Codegen leftovers, after the inliner

**What**, all of it proved once in the compiler:
* **range-based bounds-check elimination**: an index `k + (t & 1)`, or one guarded by a dominating
  compare, against the `min` hint or the length;
* **dead result registers**: callers that use one of `der_b`'s three results;
* **fuel only on calls inside recursive SCCs and on loops** (lnext §3.3).

**Why.** Bounds checks are 4.9 %, fuel and stack checks 5.6 %, result registers 5.8 % of
`Init`'s instructions (§1.2). But nlregs and parsespeed showed that codegen changes under 2 %
of instructions rarely resolve in wall time. Fuel was estimated at ~1 % of cycles.

**Do it after rank 1**, because inlining changes which checks and results remain. Measure each
with the paired bench before a proof. A `select`/`min` primitive is not proposed: a WebAssembly-
style primitive for one 613 M-call function goes against "minimal primitives".

### 7. Counted `for` with `Nat`-indexed models

lconstructs ranks 2–3:
* `for j < n { … }` sugar plus a counted-loop rule (`Triple.forUp`) proved once in L core;
* an `l_model` option that models such loops by a `Nat` index.

64 counted loops; −1.6 to −2.5 k lines if all are reproved, otherwise on touch; 15–24 h; the
generated `checker.s` is unchanged.

Small. Its main value is as a first instance of "`Nat`-valued models", the direction that could
shrink the 32 k word ↔ `Nat` lines. Weigh it against rank 2's pilot: if the refinement generator
wants `Nat` indices, do it there.

## 3. Not on the list, and why

* **Non-leaf registers, IPRA, loop promotion**: nlregs and parsespeed measured no whole-run wall
  gain ≥ 2 %.
* **32-bit array family, records, tag `match`**: p32 and lconstructs settled these. The remaining
  record and handle footprint is 1–2 % of proof lines (lrecords).
* **Generator coverage (more `l_model`)**: saturated (mgen §7–8). The remaining hand specs do not
  pay for re-threading their refinements.
* **Peak RSS on `Init`** (744 vs 492 MB): 346 MB of it is the mapped input (w32 §1). Any fix needs
  an OS call (unmap) or a streaming ABI, and the first is excluded until there is a trusted OS
  semantics.

## 4. Honest summary

* **Speed.** One thread on `Init` is at parity. The 16-thread gap is 9 %, about two thirds of it
  in the serial parse. The inliner (rank 1) is measured and cheap to prove. With `der` (rank 4)
  it should bring 16 threads close to con-ron. The large remaining ratios are on synthetic,
  table-heavy inputs (rank 5), and they depend on whether an in-place growth without marks
  works.
* **Proofs.** The error-claim duplication is gone. What is left is the hand-written lockstep
  refinement, 36 % of all proof lines. A generator for it (rank 2) is the one large proof-size
  item left. Its size is uncertain until a pilot.
* **Build.** The cold critical path is 327 s. A third to two thirds of every L-changing landing's
  path is the whole-program kernel checks (rank 3).
