# Lane lnext: the next step for L, measured (scoping journal)

Question: after absarrays, namedarrays, dense, localsnf, mgen, lconstructs/lsugar and lrecords, where is
the next gain for L, on any of three axes (faster code, simpler L, smaller proofs), preferably by moving
work into the compiler or the generator ("proved once, not per function")? Base: master 10b60723.
Nothing landed but this journal. Scratch: `_tmp/lnext/` (profiles, prototype `proto/Inline.lean`,
`proto/Graph.lean`, bench logs), `_tmp/lnext/survey/` (proof-line scripts, one `.out` per script).

Machine: load average 3–20 during the measurements (others' jobs). Instruction counts are exact
(`asmprof.py`) or `perf stat` (`instructions:u`, deterministic). Cycles and wall times in this journal
come from `bench.py` with interleaving, pinned to CPUs 40–41, at load 8–9. Their spread is about
±5 %, so differences below 3 % are noise.

## 1. Where the time goes now

`perf stat`, one thread, L (`checker.s` of master) against con-ron (`_tmp/ref/con-ron-integrate`):

| input | L instr | con-ron instr | L cycles | con-ron cycles | L IPC | con-ron IPC |
|---|---:|---:|---:|---:|---:|---:|
| app-lam | 50.3 G | 27.3 G | 42.4 G | 23.0 G | 1.19 | 1.18 |
| c05b | 14.6 G | 9.6 G | 5.7 G | 3.2 G | 2.54 | 3.02 |
| beta-ladder | 13.7 G | 8.4 G | 10.3 G | 6.3 G | 1.32 | 1.35 |

Init is near parity in cycles (OVERVIEW §3: 1.06× wall). The large gaps are elsewhere:

* **app-lam / beta-ladder.** Both checkers are memory-bound (IPC 1.2–1.3), and L executes 1.6–1.85×
  the instructions. The exact profile of app-lam (`asmprof`, 50.3 G) breaks down as follows:
  * `app_push` 23.3 % (366 instructions per call);
  * `der_b` 12.3 %;
  * `ilm_find` 11.1 %;
  * `ilm_put` 10.0 %;
  * `mk_app` 7.6 %;
  * `app_find` 6.6 %;
  * `ilg_app` 6.6 %;
  * `lam_push` 5.8 % (364 per call).

  **The push functions' cost is table growth.** Blocks that run more often than the function is
  entered (the in-place re-insertion, `kgrowB`) take 7.3 G in `app_push` and 1.8 G in `lam_push`. That
  is **18.1 % of all instructions** on app-lam: 50.4 M re-insertions for 32.0 M pushes, about 145
  instructions per re-insertion. Growth is 8.3 % on c05b (mostly `rf_put`) and 0.0 % on Init. In
  cycles, con-ron's growth (`move_slots` + `ensure_slots` + `try_resize`) is about 9 % of app-lam and
  about 5.5 % of c05b. L's is about 14 % of app-lam's cycles (from `perf record`), so roughly twice
  con-ron's.
* **c05b.** L spends 29 % of its instructions in memo tables (`rf_*`, `crm_*`, `ta_*`, `ab_*`).
  con-ron's top entries are the walks themselves (`replace_fvars_go`, `target_abs_go`, 16 % each). Not
  analysed further here.
* **16 threads (Init 4.47 s against 3.19 s).** `perf record` per thread at `--jobs=16` shows that
  **almost all of the gap is serial**:
  * L's main thread runs 3.33 s before the workers start, con-ron's 2.12 s;
  * the parallel phase takes 1.38 s against 1.14 s.

  In the serial phase the scanner (`next_member`, `key_end`, `skip_ws`, `read_nat`, `key_at`,
  `skip_digits`, `value_at`, `num_end`, `slot_nat`, …) takes 54 % of L's samples (about 1.8 s), against
  48 % of con-ron's (about 1.0 s). L's scanner executes about 28 G instructions on Init, con-ron's
  frontend 11.8 G (6.4 % of its 184.5 G). con-ron inlines the small scanners into
  `scan_line_loop`/`next_member`. L calls them: 144 M calls of `skip_ws` at 21 instructions each, 62 M
  of `key_end` at 51. **The scanner alone is about 0.8 s of the 1.3 s wall-time gap at 16 threads.**
* **Code generator leftovers (Init, exact).**
  * Non-leaf functions are 125.8 G of the 257.7 G instructions. 56.1 G of their instructions touch the
    frame, 43.9 G of those are plain moves.
  * Fuel decrements: 6.0 G (×2 instructions, 4.7 %). 78 % of the calls go to functions outside
    recursive SCCs.
  * The probe step `j := (j + 1) * u64(j + 1 < n)` is 0.5–1.0 % of instructions.

## 2. Where the proof lines are now (helper survey, `_tmp/lnext/survey/`)

The survey uses lrecords.md §1's method, rerun on master: 339,025 proof lines (341,595 on 10-27).

**Refinement (model ⊑ twin) is 116.2 k lines (34 %).** The other layers:
* spec (L ⊑ model): 30.5 k, down 1.1 k;
* model equations: 30.0 k;
* error claims: 21.8 k (19.5 k of them in `Verdict/`);
* frames and keeps: 10.8 k;
* hand-written word models: 13.4 k, down 1.7 k.

`l_model` names 647 of the 1,837 functions.

**What a function costs now.** An `l_model` function costs about 130 proof lines:
* refinement 48;
* error claim 28;
* spec 15;
* model equations 12.

A hand-specified function costs about 96. Generating the model removed the spec and model work, but
**the refinement and the error claim stay per function**, and they are now most of the cost.

Repeated patterns (regex counts, approximate; a line can be in several groups):

| pattern | lines | note |
|---|---:|---|
| error path proved a second time | 21.8 k (layer) | 132 functions have both an ok refinement (17.9 k) and an error claim (14.3 k) |
| word ↔ `Nat` (`toNat`, no-wrap, `< 2^64`, bounds) | 34.6 k | 14.7 k of them in refinements; 4,293 theorems mention `toNat` |
| frames (frame/keep lemmas, read-over-write, preservation conjuncts) | ≈ 20 k | 1,218 frame/keep declarations |
| restated specs (2nd–8th spec of one function) | 6.1 k | 342 functions |
| restated refinements (the same refinement under another invariant package) | 7.8 k | 213 twin functions |
| abort / `Option` plumbing | 12.6 k | 4.7 k in word models, 3.9 k in refinements |
| strictly fuel (zero arms, `induction n`, `n ≤ 2^62`, monotonicity) | ≈ 9.8 k | 775 fuel inductions |
| program-lookup bundles (`…Prog`, `…Fns`, `hp.get "…"`) | ≈ 10.5 k | |

**Example: `target_major_nfs`** (`l_model`, 13 L lines, 632 proof lines). Its four large theorems
are one proof done four times:
* `tmnW_okC` (112 lines) and `tmnW_okPC` (132), the ok refinement under two invariant packages;
* `tmnE_claim` (128) and `tmnE_claimP` (141), the error claim under the same two packages.

The error claim repeats the ok refinement's induction, hypotheses, slice decoding and case splits
line for line. It even calls `tmnW_okC` for the ok prefix of each step. What it adds per callee is
an `| error e => ErrClaim.bind_left …` arm of 3–6 lines.

## 3. Prototypes

### 3.1 L → L inlining (speed; `_tmp/lnext/proto/Inline.lean`, unproved)

The prototype transforms `checkerProg`, then compiles and prints it exactly as `AsmEmit` does. Size 0
gives a byte-identical `checker.s`. The transformation:
* replaces every call to a leaf whose body has at most S nodes by the callee's body, with the
  callee's locals shifted past the caller's;
* turns the callee's returns into assignments to the call's result locals, through a tail
  conversion when the returns are in tail position, and through a `while true { …; brk }` wrapper
  otherwise;
* sets the parameters from the arguments and zeroes the callee's `needZero` locals.

Fuel: the wrapper's loop charges one unit where the call did. The inlined body runs one fuel level
higher, so it needs at most the original's fuel. With S = 80 and two rounds, 261 leaves are inlined.
`diff-e2e.py --bin`: 634 of 634 fixtures agree.

`bench.py --set init --reps 3 --cpus 40-41`, load 9:

| variant | instructions | cycles | wall |
|---|---:|---:|---:|
| base (master) | 1.000 | 1.000 | 1.000 |
| S = 20, 1 round | 0.983 | 0.976 | 0.981 |
| S = 80, 2 rounds | 0.979 | 0.973 | 0.971 |

On app-lam and beta-ladder it changes nothing (−0.0 %), and on c05b −1.0 % instructions: the hot
store functions are not inlined.

Why the gain is small: an inlined leaf lands in a non-leaf caller, whose locals live in the frame.
`next_member` with its scanners inlined still executes 143 instructions per call, against 64 + 51 +
29 + … before. Only the call, the fuel check and the prologue are saved, about 5 instructions per
removed call, and 0.9 G calls are removed. compopt2 saw the same with its naive inliner.

### 3.2 Register allocation in non-leaf functions (speed; estimate from the exact profile)

The estimate puts the K most-used frame slots of every non-leaf function into callee-saved registers,
and charges 2K instructions per call for saving and restoring them. Net, on Init, for K = 3–6: −5.3 to
−5.5 G (**−2.1 %**). App-lam: −2.0 %. c05b: −0.9 %. Below the bar on its own. It would raise
inlining's gain (§3.1), because inlined code then lands in registers. Not prototyped.

### 3.3 Fuel only on recursive calls and loops (semantics and speed; static count)

`proto/Graph.lean` (the call graph of `checkerProg`):
* 1,838 functions, 541 of them in recursive SCCs (the largest SCC has 125 functions);
* 306 functions with loops;
* 1,011 functions that are neither recursive nor have a loop;
* only **326** functions whose whole downward closure is fuel-free.

Dropping the fuel check on calls out of the SCC saves about 3 % of the instructions on Init (about 1 %
of the cycles: the checks are predicted). It would let only the models of those 326 functions lose
their fuel parameter. The strictly-fuel proof lines (9.8 k) sit mostly in recursive and loop
functions, which keep their fuel. The change is wide (`exec`'s termination measure, `L/Semantics.lean`)
and the payoff small. No-go now.

### 3.4 The other speed items, counted and dropped

* **Probe step by mask** (`(j + 1) & (n - 1)`; slot counts are powers of two): 0.5 % of Init, 0.9 % of
  app-lam, 1.0 % of c05b.
* **Hash template**: `hashtpl.md` (0.34 %) stands.

## 4. Ranked candidates

| rank | candidate | axis | gain (measured or estimated) | cost | risk |
|---:|---|---|---|---|---|
| 1 | **One refinement per function for both outcomes**: an `l_model … unified` mode whose `Except` model is also the ok model (`fW = (fE).toOption` generated, so callers keep their `Option` specs), and one theorem per function proving the twin's `.run` agrees on `.ok` and gives `ErrClaim` on `.error` | proofs | Error-claim layer 21.8 k lines. Pilot sketch on `target_major_nfs`: 4 theorems / 513 lines → 2 / about 260 (−50 %). Over the 132 functions with both halves (32.2 k lines): **−8 to −13 k lines when migrated**. Verdict modules are 15 % of build time, perhaps half of that saved. Every later function in the verdict closure (298 functions) costs one proof instead of two. | generator 6–10 h; pilot 3 functions 4–6 h; migration 0.5–1 h per function, done on touch | Medium. The `E` model must call callees' `E` models (today callees go through `callE_spec`), so a unified function's callees need unified specs first: bottom-up. |
| 2 | **Table growth by copy-free forward placement** (doubling with `mulhi` homes keeps home order, so a re-insertion sweep needs no marks and no swap chains) | speed | app-lam: growth is 18.1 % of instructions at about 145 per re-insertion, about 2× con-ron in cycles. Halving it: **−9 % instructions on app-lam and beta-ladder, −4 % on c05b, 0 on Init**. | prototype 3–4 h (template in the `Inline.lean` harness, measured unproved); proof: replaces `SlotRehash.lean` (487 lines) and the growth part of `ConsLibSpec`, 15–30 h | Medium: a new invariant proof; RSS unchanged (still in place). |
| 3 | **Frames from write footprints** (`WriteSet`/`Agree` per function, one generic theorem: a predicate over unwritten state is kept; emitted by `l_model` as a fact) | proofs | frames 10.8 k, restated refinements 7.8 k, restated specs 6.1 k, preservation conjuncts 2 k: **≈ 10–20 k addressed** | after deadpred lands (it edits `MemFrame`/`PoolOK` now); design 1 day | High: it overlaps deadpred's records; re-proof is per family. |
| 4 | **L → L inlining proved once** (a `Prog → Prog` pass before `compileProg`; theorem: an accepting run of the inlined program is an accepting run of the original, with more fuel) | speed, L style | **Init −2.7 % cycles, −2.9 % wall** (prototype, §3.1); app-lam 0; c05b −1 % instructions. Small twin-shaped helpers then cost nothing at run time. | proof 10–20 h (one lemma per statement form, fuel monotonicity exists in `FuelMono.lean`) | Low, but the gain is small unless 3.2 comes too. |
| 5 | **Checked index arithmetic** (an aborting `+?`/`*?`; `l_model` emits `Nat`-valued index models) | proofs, L | word ↔ `Nat` lines 34.6 k, ≈ 15–20 k of them in refinements and model equations (upper bound, regex) | semantics change (`L/Semantics.lean`, deadpred's file) plus generator, 20–40 h before the first saving | High: the saving is speculative until a pilot; it changes every model's shape. |
| 6 | Non-leaf register allocation | speed | −2.1 % Init instructions (estimate) | 15–25 h compiler proof | Low gain. |
| 7 | Fuel only on recursive calls and loops | speed, proofs | about −1 % cycles; 326 models fuel-free | wide semantics change | No-go now. |
| 8 | Program-lookup bundles generated (`ProgHas` by `decide` over `checkerProg`) | proofs | about 10 k lines addressed (helper estimate, not checked here) | unknown; lrecords rank 7 is the same item | Re-scope before any lane. |

Not on the list: the scanner's serial cost (0.8 s at 16 threads) has no L-level fix that measured
well. Inlining saves about 5 instructions per call there. What remains is non-leaf frame traffic
(rank 6), and inlining with registers together (4 + 6) is the route to it. A pilot of 4 + 6 on the
scanner alone would say whether the serial phase can lose a third.

Honest summary:
* Speed beyond 2–3 % is left only in table growth, and only on app-lam/beta-ladder/c05b-like inputs.
  Init is at parity in cycles.
* The proof side has one large, mostly mechanical duplication left: the error path proved separately
  from the ok path. Rank 1 attacks it with a generator mode, which is the "prove it once" direction.

## 5. The first lane: `unifiedE`

1. **Generator.** Add `l_model … unified`: the `errors` model, with every callee called through its
   own unified model (not `callE_spec`) when it has one. Also generate the equation `fW_toOption : fW n … =
   (fE n …).toOption` (`Option` view, `none` for every error). Then existing callers that use `fW` and
   its spec are untouched. Tests in `ModelGenTest.lean` (two calls, a recursive call, an abort,
   an error passing through).
2. **The unified refinement statement** (`Arena/Verdict.lean`, next to `ErrClaim`): `RefE fE twin R`
   says that
   * `fE … = .ok (r, m')` gives `∃ y a', twin.run a = .ok (y, a') ∧ R …`;
   * `fE … = .error e` with `e.code ≠ 0` gives `ErrClaim twin a e`.

   Two lemmas: `RefE.ok` gives today's ok refinement, and `RefE.err` today's error claim. So
   `@[refines]` theorems and the verdict closure keep their statements.
3. **Pilot.** Three functions with both halves, bottom-up:
   * `ctors_have_name` (leaf);
   * `target_class_match`;
   * `target_major_nfs`.

   Replace `tmnW_okC`/`tmnE_claim` by one `tmn_refE`. Measure lines and elaboration time of the old
   and new declarations in isolated files, three runs each (as in lconstructs.md §5).
4. **Go/no-go.** Go if the pilot saves at least 40 % of the lines of the pairs it replaces and no
   module gets slower. Then migrate on touch (twin bumps, performance changes), plus a batch of the
   largest pairs (Verdict's top 10 files by lines) if the per-function rate exceeds about 70 lines/h
   (the bar hashtpl.md used).

Speed, as a parallel and independent lane: prototype rank 2 in `_tmp/lnext/proto/` (a variant of
`kgrowB` in the harness, unproved, `bench.py --set full`). Go to a proof lane only if app-lam improves
by at least 5 % in cycles.
