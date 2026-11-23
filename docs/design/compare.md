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
