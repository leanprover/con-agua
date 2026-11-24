# Lane compare: verified --compare on two lean4export files

Lane of 2026-11-23 (Opus), from master after ronsync8; mirrors con-ron 8021ddac (#165) and con-leche bc667610 (#612).

## 0. Stage 0: the design

**What con-ron does** (`crates/con-ron-core/src/driver/compare_json.rs`, twin
`Arena/Justify.lean`, `Arena/Needs.lean`, capstone `MainTheorem/Stages.lean` §4b, twin-side
glue `Bridge/Compare/Stages.lean` `stagesC_model`/`stagesC_no_False`). One `AState`, one store:

```
intern_reserved_pins → builtin_prelude_e → parse C → parse S → prelude_ix_dup → prepare S
  → pins → check_phase S (build_index, freeze, workers, thaw: the index IS back) → prepare C
  → side_records (holes → axioms) → solution_of(IS, recsC) (+ record mates)
  → check_phase C with Some(sol) (build_index IC from empty, workers: recordJob J = some sol)
```
A job with a solution: `justifiable(d)` (a non-built-in, non-pinned axiom) takes
`checkJustified` (`justifyWhy`: the solution's constant of the same name, same statement up to a
level renaming, and the cone of its type, `coneGo` over `entryNeeds`/`needsGo`, every name a
`refinesB` copy with the same projection table), else `checkDecl`. No `jsonReach` in con-ron
(that is con-leche's #612 rule; con-ron checks the whole challenge). con-ron agrees with
con-leche's 14 verdict rows; the 4 usage rows are exit 3.

**L's mirror: one store, two indices.**

* *Two inputs.* The frontend reads byte array `IN` (descriptor 0) only. The compare driver is
  several L runs of `check` on one region `R` (as `ca_start` is two), and between the parse of C
  and the parse of S the driver stub points descriptor 0 at S's buffer. The parse records of C
  (`DECL`/`DLP` past the prelude's) are stashed in two new arrays and the prelude part kept
  (`preC`, the twin's `prelude_ix_dup`), then `front_reset`; L plumbing (con-ron: two
  `ParseResultD` values).
* *The solution's check phase* = the flat one: `build_index` S, then `par_compact(1)` (the frozen
  buffer in `OUT`), then S's jobs on a separate worker region `W` via the existing `ca_check_b`
  (one call per job, in order: one worker, `SeqAccepts`). `R` is untouched by the worker (the
  jobs write only owned arrays, which live in `W`; `MemFrame` + `bufKept_of_memRel`), so the
  driver continues from exactly the twin's `sF` (con-ron: `freeze_tier`, workers, `thaw_tier`
  = identity on the driver state). Not in place: after in-place jobs the caches and memos are no
  longer `sF`'s (the index build's level-equality entries), and `preparePrelude C` runs from `sF`.
* *Thaw = the index moved to the solution's arrays.* `IS` lives in `EIX*`/`TIX*` (rows by name
  index). A new L function walks S's records' constants and tables (as `build_index` did) and
  moves each row to new arrays `SIXA/SIXS/SIXN`, `STXA/STXS/STXN` (same encoding), zeroing it
  in `EIX*`/`TIX*`; so C's index is built from empty in the same arrays and every job reads its
  base index exactly as on the flat path. Cost O(S's constants), as the index build.
  `ISolution.find?`/`findTable?` read `SIX*`/`STX*` (every row visible). The record mates
  (`recordMatesGo`) are rows by name index (`MATES*`) pointing at pool slices.
* *The flag.* `record_job` reads one global `SOL` (0 on the flat path) before `check_decl`: at 0
  the flat path is the same code with one load and branch per record (con-ron: the `match J`).
* *C's jobs* run in place (`ca_check_seq`, as the flat sequential driver), since nothing follows.

**Machine level.** `ca_compare(c, c_len, pins, pins_len, base, base_len, s, s_len)`: the first
six registers exactly as `ca_start`'s (so `AbiCall bC pb` holds verbatim), S's buffer the two
stack arguments. The region is `drvNeed + workerNeed` (W is its tail). Modes: `4` (cap, pb,
presize, reserved pins, prelude, parse C, stash), stub swaps descriptor 0 to S, `5` (parse S,
prepare S, pins, build_index S, par_compact(1); returns `2^63 + kS`), `ca_check_b` for
`j < kS` on `W`, `6` (thaw/move, restore C's records, prepare C, side records, mates,
build_index C, `SOL := 1`, par_compact(0); returns `2^63 + kC`), `ca_check_seq [0, kC)`.

**Twin functions with L counterparts** (new, ~45): Needs.lean 15 (`nidxAppend`, `litNeeds`,
`needsGo`, `NeedsSt.{expr,names,name,exprs,rule,rules,const,table}`, `pinFootprint{,Nat,Reduce}`);
Justify.lean 28 (`builtinAxiomName`, `sideRecordVal`, `sideRecord`, `sideRecordsGo`,
`justifiable`, `levelsRenaming`, `sameCvUpToLevels`, `tableBeqP`, `IConstantInfo.isStmtKind`,
`copyB`, `refinesB`, `matesInsert`, `recordMatesGo`, `solutionOf`, `ISolution.find?`,
`ISolution.findTable?`, `recNames`, `entryNeeds`, `coneEntry`, `coneGo`, `justifyWhy`,
`checkJustified`, `checkRecord`; `recordCheck`, `recordJob`, `runJob`, `checkJobList` change
from `J = none` to `J`; `declLabel` n/a, messages). Existing blocks reused: `mentions_const`,
`ci_eq`, `cv_eq`, `ci_at_lps`, `cv_at_lps`, `sl_nodup`, `nat_op_name`, `basis_names_ok`,
`check_constant_val`, `lit_guard_names`, `nat_op_deps`, the env lookups, `pin_at`.
Driver: `prelude_ix_dup` (the kept prelude part), the stash/move plumbing (con-ron: none).

**Helper split** (after the interface is on the branch: arrays, encodings, `SolRel`, the `SOL`
flag, the L signatures): H1 Needs (L + models + refinements); H2 the comparison and the cone
(`copyB` … `checkJustified`, `checkRecord`); H3 side records, mates, the move, the stash. Lead:
the modes, the stage chain at L level (`PhaseC`, the compare analogue of `PhaseA`/`FoldAt`),
the driver stub and its machine proof, the harness, the final theorems.

**Perf plan.** Self-compare of Init (a copy of `init435.ndjson` under a second name: the same
path twice is a usage error), one thread, `instructions:u`, peak RSS, wall, against con-ron
8021ddac `--compare --jobs=1`; the flat Init run against master (expected: one load per record).

## 1. Progress log

* 16:15 start (worktree, reading). 17:00 stage 0 sent to the coordinator.
* 17:00–17:10 the interface (`Arena/JustifyIface.lean`): the arrays `SIXA‥CWK` (210‥222, declared
  outside the checker's table until the wiring, so no full rebuild now), the control words
  `CTL[224‥228]` (not globals: `MemFrame` covers `CTL` but says nothing about globals, so a
  relation reading a global would not survive the existing frame lemmas), `SolR`/`OptSolR` and
  their frame (`SolR.growF`), `NeedsR`, `ConeR`, the memo schemas, `sol_find`/`sol_find_table`
  refining `ISolution.find?`/`findTable?`.
* 17:10 helpers started: `compare-needs` (H1, Needs.lean), `compare-cone` (H2, the comparison,
  the cone, `checkJustified`), `compare-side` (H3, the move, the side records, the mates);
  briefs `_tmp/compare/brief-*.md`.
* 17:15–17:40 the compared run's entries (`Checker/CompareEntry.lean`: modes 4, 5, 6, `cmp_stash`,
  `cmp_restore`), the driver stub `ca_compare` (`Compiler/AbiCmp.lean`, code only, emitted after
  the compiled code), the harness (`run_compare`). Wiring commit: the arrays as table rows
  (`SIXA`‥`CWK`, `CDECL`, 210‥223), `record_job`'s branch on `CTL[224]`, `check`'s dispatch on
  modes 4–6, the new arrays in `parOwned` (not frozen: the solution's rows are read only by the
  challenge's jobs, which run in place; so the frozen buffer's header is unchanged).
* Helpers' first milestones merged: H1 (15 Needs functions + generated models; Option models:
  every Needs error is `.internal`, class 0; the list recursions are loops), H3 (the move as three
  loops over `2 · count` of the name stores, the side records in place (kind word to axiom), the
  mates, `builtin_axiom_name`), H2 (the comparisons, the cone as a loop over a stack, `justify_why`,
  `check_justified`, `check_record_sol`; reason `R_NOT_JUSTIFIED_BY`). Reviewed against the twin
  line by line: faithful.
* Design changes from stage 0: the move is over the name stores' counts, not over the solution's
  records (H3: re-walking `decl_constants` would allocate again and needs an invariant tying rows to
  records; the stores' counts bound every row through `IndexKeysIn`, `FreezeTrunc.lean`).
* 17:50 first binary with `--compare` (WIP, unproved wiring): `diff-e2e --tests` at con-leche
  bc667610: **766/766 agree** (the 748 file rows plus the 18 argument rows, which
  `diff-e2e.py` now runs: `arg_rows`), UNSOUND/INCOMPLETE/CRASH/TIMEOUT 0.
* First measurements (one run each, load ≈ 1; `_tmp/compare/perf1.sh`):

  | run | instructions:u | wall | peak RSS |
  |---|---:|---:|---:|
  | flat `Init`, master `d84b7c756` | 202 631.7 M | 14.52 s | 627 MB |
  | flat `Init`, compare | 202 631.8 M (+0.0001 %) | 14.77 s | 628 MB |
  | `--compare` `Init` against itself, compare | 408 327 M | 29.23 s | 1 259 MB |
  | con-ron 8021ddac `--jobs=1 --compare`, same | 333 863 M | 28.87 s | 367 MB |
  | con-ron 8021ddac `--jobs=1`, flat `Init` | 165 590 M | 14.17 s | 388 MB |

  The compared run costs 2.015 flat runs (con-ron: 2.016). Its peak RSS is twice the flat run's:
  the solution's jobs run on the worker region over a copy of the frozen arrays, and both stay
  resident (con-ron moves its tier to the workers and drops them).
* 18:00–18:25 helpers' results. H1 (Needs, 15 functions) done, zero `sorry`; H3 (move, side records,
  mates) done, zero `sorry`; H2 then H2b (the comparisons, the cone, `justify_why`,
  `check_justified`, `check_record_sol` = `crs_ref`) done, zero `sorry`, with three facts left to
  discharge on the checker: `ConeProg.cmpClosed` (a closure check), `CrsKeep` (semantic frames
  stated on the models), and the solution counter's bound. The rejection claims of
  `check_justified` take the guard `JwGuard` (the twin's message reads names back; only the error
  branch needs it; it matters only for a compare verdict theorem).
* 18:05 H4 (`compare-abi`: the file equation with the tail, `CmpCall`, `CmpGuard` as a premise
  (L-level: the buffer's geometry after mode 5, the workers keep the frozen arrays), `CmpAccepts`,
  `cmp_outcome`) and H5 (`compare-integ`: the tree building again, `JobM` with `J`) started;
  18:25 H6 (`compare-chain`: the L-level chain, `CmpAccepts → TwinComparesAccepts`).
* `WalkMem` (the walks' memos between jobs) added to the interface for H2b and H5.
* 18:45 H5 done, merged: the tree builds again (except `AsmFileEq`, H4's), the job relation takes
  `J` (`JSol J m`: the flag/rows, and at `J = some` `WalkMem` and the counter bound), `recordJob_ref`
  at both branches (`crs_ref` through `CrsSpec`, `Arena/JobsCrs.lean`, `Checker/CrsProgPB.lean`),
  four write sets narrowed (no job writes the solution's rows), the threaded path at `J = none`
  only. Open: `CrsKeep` (given to H7, `compare-keep`).
* 19:05 first step landing prepared: the L code of `--compare`, the wiring, the refinements of
  every new function (zero `sorry`), the job relation at `J`, the harness and the driver stub
  (unproved), H4's machine-level building blocks (`Final/CmpStub`, `CmpAbi`, `CmpOutcome`,
  `CmpLoop`, built, zero `sorry`). `Final/CmpMain.lean` (the driver theorem, work in progress) is
  not in this landing (it stays on H4's branch). OVERVIEW and `main.c` say that no final
  theorem covers `--compare` yet.
* 19:40 H4 done, merged: `cmp_outcome(_regs)` (`Final/CmpMain.lean`): from `CmpCall` (`AbiCall` plus the
  solution's buffer as the two stack arguments), the L-level premise `CmpGuard` and `cmpNeed < 2^64`,
  every run of `ca_compare` returns to the caller with the callee-saved registers restored, and
  `rdx = 0, rax = ACCEPT` means `CmpAccepts` (the chain of L runs), `rdx = 2` means `CmpErr`. The
  setup stub on a region holding an L memory (`memRel_restub`), the worker loop (`cmp_loop`), the
  file equation with the tail. `AbiCall` became `AbiCallM` in the setup stub's theorem (callers
  pass `hc.toM`); no other Final statement changed. 0 `sorry`.
* H6 (modes 4, 5; the stage lemmas generalised: `StagesOut`, `pinsStage_gen`, `buildR_of_out`) done
  and merged; H6b continues (mode 6, the jobs, the composition, the guard). H8 makes the gates green
  for a first step landing.
* 20:05 **What went wrong: the buffer's "kept" premise.** H4's machine theorem needed every solution
  worker to leave the frozen buffer as it found it (as the threaded mode assumes, by `mprotect`,
  route A). At the L level that is a tier-0 invariant the job proofs never state (check_decl's
  write set includes tier 0 of every store). Instead of a new trusted fact or that invariant, the
  workers are now treated as the in-place jobs are: each runs on the buffer as the previous one left
  it, the relation to the twin is carried by the job relation, and the machine only needs the
  buffer's header unchanged (a closure fact: no phase-B function stores to `HDRF`/`CTLF`). Helper
  H9 (`compare-redesign`) rewrites `CmpJobs`/`cmp_loop`/`cmp_outcome` and the solution's job chain
  accordingly; H6b does mode 6.
* 20:55 **step landing 1** (`compare-land` 91e5c9aef, #325, master 2165b2ead): everything above up to
  modes 4–5 and the machine building blocks; H8 made the gates green (55 unused imports, a name
  clash `recOK_congr`, `leafFns` regenerated, an anchor).
* Later: H9 (no "kept" premise; `CmpHdrKeep`, `cmpSJobs_twin`, `checker_cmpGuard`), H10 (the guard under
  the setup stub's size checks; `checkerFile_compare_runs_regs`), H6c (mode 6, `checkC3_run`; the job
  lemmas over `FoldOn`/`StagesOut`), H6d (`JobM` at `J = some`, the challenge's jobs by a `J = some`
  list induction mirroring con-ron's `pooledAcceptsJ_bridge`, `cmpAccepts_twin`) merged; the lead's
  `Final/CompareTwin.lean` and the end-to-end theorems in `Final/Compare.lean`. 0 `sorry`.
  (The times in this log after about 18:30 are approximate.)

## 2. What is mirrored

| con-ron (8021ddac) | L |
|---|---|
| `compare_json` (`driver/compare_json.rs`): one store, the challenge's parse, the solution's, its preparation, the pins, its check phase, the challenge's preparation, side records, `solution_of`, its check phase with the solution | `check_c1`‥`check_c3` (`Checker/CompareEntry.lean`) and the driver `ca_compare` (`Compiler/AbiCmp.lean`): the solution's jobs on a worker region over the frozen buffer (`ca_check_b`), the challenge's in place (`ca_check_seq`) |
| `freeze_tier`/`thaw_tier` (the index handed back) | the index's rows moved to the solution's rows `SIX*`/`STX*` (`index_to_solution`), so the challenge's index is built from empty in the flat arrays |
| `Needs.lean` (15 functions) | `Arena/Needs.lean`, generated models, `NeedsRef*.lean` |
| `Justify.lean` (`builtinAxiomName` … `checkRecord`, `recordCheck`/`recordJob`/`runJob`/`checkJobList` at `J`) | `Arena/Justify.lean`, `JustifySide.lean`, `JustifyIface.lean` (`ISolution.find?`, `findTable?`), `record_job`'s branch on `CTL[224]`; refinements `JustifyRef1‥7`, `JustifySideRef*`, `Jobs.lean` at `J` |
| the usage checks (two files, two different files) | `main.c` `run_compare`, exit 3 |
| `model_exists_compare`, `no_False_compare` (twin side: `stagesC_model`, `stagesC_no_False`) | `checkerFile_compare_model`, `checkerFile_compare_no_False` (through `twinComparesAccepts_model`/`_no_False`) |

Loops where the Rust has loops (the cone walk, the side records, `solution_of`, the move); the
Rust's cursor recursions over lists are loops too (same behaviour, less stack); `needsGo` and
`matesInsert` recurse as the Rust does. Not mirrored: the messages (D16), `--jobs` (D51), the
move instead of the tier's move (D52), `--olean --compare` and the modular modes (D44, D50).

## 3. Final statements (new; no existing headline statement changed)

`Final/CompareTwin.lean`: `SeqAcceptsJ`, `TwinComparesAccepts` (the text in the coordinator message
of 20:15 and in the file), `twinComparesAccepts_model`, `twinComparesAccepts_no_False`.
`Final/CmpAbi.lean`: `CmpCall` (`AbiCall` of the challenge and the pins, plus the solution's buffer
`sa`/`bS.size` as the two stack arguments, apart from the region, the other buffers and the stack
window). `Final/Compare.lean`: `checkerFile_compare_runs_regs` (the machine theorem at the L level),
`checkerFile_compare_accepts(_regs)`, `checkerFile_compare_model`, `checkerFile_compare_no_False`;
all pinned at propext, Classical.choice, Quot.sound. Changed: `Final/Abi.lean`'s `abi_harness` and
`abi_start_outcome` take `AbiCallM` (`AbiCall` without the zero region; callers pass `hc.toM`);
`code_of_checkerFile_par` is a prefix lemma (the file has a tail). No trusted fact or axiom was
added; unlike the threaded mode, no harness hypothesis either.

## 4. Performance

`Init` (`init435.ndjson`, its hard link under a second name for the solution), one thread,
`perf stat -e instructions:u`, `time -f "%e %M"`, load below 1, two rounds for the flat runs
(identical to ±0.0001 %), 2026-11-23 20:20; master = `d84b7c756` (before step 1), con-ron = 8021ddac.

| run | instructions:u | wall | peak RSS |
|---|---:|---:|---:|
| flat `Init`, master | 202 631.66 M | 14.64 s | 626 MB |
| flat `Init`, compare | 202 631.83 M (+0.0001 %) | 14.77 s | 628 MB |
| `--compare` `Init` with itself | 408 327 M | 29.39 s | 1 259 MB |
| con-ron `--jobs=1 --compare`, same | 333 863 M | 28.93 s | 368 MB |

The compared run costs 2.015 flat runs (con-ron 2.016) and 1.016 con-ron's wall; its RSS is two
flat runs' (D52).

## 5. What went wrong

* **The buffer's "kept" premise** (above): an early machine design needed a fact the L proofs
  cannot give; replaced by chaining the solution's workers like in-place jobs (H9). Two helper
  shifts went into it.
* **Helper context.** The chain took four shifts (H6, H6b, H6c, H6d), the cone two (H2, H2b); the
  hand-overs worked.
* **Integration fallout** after the wiring: the closure lists, `import all` in the whole-program
  checks, the dispatch proofs, a `maxRecDepth` in the generated `checkerProg` (its list grew past
  the code generator's default), name clashes between helpers' files (`pinW_frame`, `rdW_dw`,
  `recOK_congr`), 55 unused imports, a stale `leafFns`.
* **Open, not blocking:** the challenge's job driver (`Checker/CompareJobs.lean`, `*_seqR`) repeats the
  `vcgen` parts of the flat `*_seqO` ones; deriving the flat ones from it would rebuild the flat
  chain, left for a later cleanup.

## 6. Checks before the final landing

* `scripts/gates.sh` all 16 steps OK on `compare-land2` d68fb96e5 (master merged; H11: 26 unused
  imports, 5 warnings, 3 anchors).
* `diff-e2e --refs --parallel 16 --tests` at con-leche bc667610 (con-ron 8021ddac, con-ron-lean-twin
  at this branch): **766/766 agree** (447 accepted, 319 not), UNSOUND/INCOMPLETE/CRASH/TIMEOUT/REFDIFF
  0; 7 skipped (`--max-nat-size`, D49).

## 7. compare2: threads and verdicts (lane compare2, 2026-11-23/24)

The user's answers (2026-11-23): the statements of §3 approved; `--compare` takes `--jobs` like
con-ron (D51 removed), the threaded compared run proved as the flat threaded mode is; the compare
verdict theorem (reject/decline lines) required in the first landing, sequential and threaded.

**Design.** The threaded compared run: `ca_compare_a` (modes 4, the descriptor swap, 5: the
solution's frozen buffer) → the flat mode's worker threads (`ca_check_b`, unchanged, route A) →
`ca_compare_b` (mode 7 = mode 6 with `par_compact(1)`, on the driver region as the first call
left it: the challenge's frozen buffer) → the same worker threads at `J = some`. The challenge's
jobs read the solution's rows (`SIX*`, `STX*`, `MAT*`), so they move from the owned arrays to the
frozen ones, their extents gated by the flag `CTL[224]` (empty in the flat buffer and the
solution's). The sequential driver `ca_compare` stays. Twin side: `TwinComparesAcceptsPooled`
(con-ron's `PooledAccepts`/`PooledAcceptsJ`), `twinCompareRun` (con-ron's `compareJsonTail`
order, `checkStreamJ`), `TwinCompareVerdict`, `TwinCompareVerdictPooled`.

### Progress log
* 23:15 start (branch `compare2` from `compare-land2` 6a6e84fbb). 23:20 the twin statements
  (15cf26fa7), sent to the coordinator. 23:22 helpers H1 `compare2-verdict`, H2
  `compare2-freeze`, H3 `compare2-abi` (briefs `_tmp/compare2/brief-*.md`).
* 23:35–23:50 helpers' plans. H1: `JwGuard` is dischargeable (the twin's `justifyWhy` runs ok on L's
  abort path; the names read back denote: the record's name, and the cone's culprit by a
  `coneGo` induction; the mates need a new store-level fact `CvMatesDen`); `JobGs` loses its
  `JwGuard` conjunct. H2: the 9 rows appended to `frozen` with extents `CTL[224] · 2 · count`
  (the mates' slices are in the frozen `EREC` image; the walks' memos are fine on a fresh worker);
  `frozen.length` 63 → 72, `hdrW` 136 → 154; mode 7 = `check_c3(1)`. H3: **no new driver stubs**:
  the threaded harness calls the existing mode entries `ca_start_a4`, `ca_start_a5` and a new
  `ca_start_a7` (one directive more), whose machine theorems (`abiMode_outcome`,
  `abiModeM_outcome`) exist; the cost is three trusted first returns and the region carried
  between the calls (harness facts of `ThreadsAcc.next`'s kind) instead of ~250 lines of stub
  proof.
* H1: the justification guard discharged (0edecae38, merged): `JwGuard` is no hypothesis anywhere;
  `CrsG` is program-only; the cone's culprit denotes (`Arena/CmpVCone.lean`), the mates by
  `CvMatesDen` (`Arena/CmpVMates.lean`). Debt: `Arena/CmpVRoots.lean` carries con-ron's
  `Bridge/Modular/Roots.lean` needs-walk lemmas (the vendored module's modular half does not build
  at our pin, so it cannot be imported); to be deleted when it does.
* H3: the harness and `ca_start_a7` wired (5114a9f40); `CmpThreadsRun` and the threaded accept,
  model, no-`False` theorems drafted (fb0ead731), sent to the coordinator.
* 2026-11-24: H2's frozen rows (7282b8ad9; flat `Init` instructions unchanged at 1 and 16
  threads: 202 633.5 M both), H1b's L-level verdict claims (`cmpErr_twin` complete; modes 6 and 7
  claim nothing, class 0; the solution's threaded jobs `cmpV_tjobS`) merged.
* **The harness shape, redone.** The user rejected the three-entry harness (keep facts across
  three driver calls). Options weighed: (A) one buffer frozen after the challenge's preparation
  (the solution's jobs on an extended store: the approved twin statement changes; and two
  indices keyed by the same names: a selector in every lookup), (B) the flat entries with an
  optional solution and a phase loop in `main.c`, and the user's "bank switching" (an L primitive
  swapping two arrays' descriptors: the compiler's simulation fixes one layout per run, so that
  is a change to the whole simulation chain). Chosen (A'): bank switching in the header. One
  entry-1 call freezes the solution's buffer (mode 5) and, after the challenge's preparation
  (mode 7), the challenge's self-contained buffer right after it; entry 2 reads the phase from the
  buffer and the global job index, so `main.c` is the flat loop. Each phase's jobs see exactly
  their mode's frozen image, so the twin statements stay. One pool for both phases: the reported
  failure is the smallest failing index, and every solution index is below every challenge
  index, so the verdict is con-ron's.
* H2: the challenge's threads at `J = some` (`cmpThreadsC_pooledJ`, `Checker/CmpThreadsC.lean`,
  `CmpThreadsPool.lean`: the multi-worker pool with a solution; `JobM.truncJ`, `SolR.trunc`,
  `JSol.fresh`) merged (d28e0d7b9; 0 `sorry`, the whole tree builds).
* A' in detail (H3's hand-over, H3b, H4, H2): shrinking `OUT` for mode 7 would cost days (the
  mode-6 chain's frames fix every array's size), so L does the chaining: mode 7 reads
  `base := OUT[1]`, writes the challenge's buffer at `OUT[base‥)` (`par_compact` with a base;
  0 for the flat run and mode 6), sets `OUT[5] := base` and `OUT[1] := base + LC`. Entry 2
  (`ca_check_b`) gets a prologue: `j ≥ buf[2]` and `buf[5] ≠ 0` shift the buffer, the index and
  the region to the second phase and its worker sub-region (`ca_worker_size = 2 · workerNeed`);
  the flat path never shifts. The solution's jobs see the whole buffer, which agrees with mode
  5's on its prefix except header words 1 and 5 (`BufAgreeS`).
