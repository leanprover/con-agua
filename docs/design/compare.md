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
