# Lane `verdicts-b`: proving reject and decline (journal)

Step (b) of `docs/design/verdicts.md`: when the compiled checker returns an abort of class 1
(reject) or 2 (decline), the twin's pipeline fails with an error of that kind (`invalid`,
`notImplemented`). No converse.

## Re-check of the scoping against the synced twin (con-ron ed864140)

* The twin no longer recovers inside a pin-variant attempt (`orElseAttempt` is gone, con-ron
  #129); `ATT` and the class masking of `fail R` are retired (lane consync). The scoping's D4 and
  its `ATT` machinery are moot: every `fail R` is a plain `abort R`.
* The verdict closure on `checkerProg` (a `#eval` over the program, `_tmp/verdicts-b/Closure.lean`):
  1835 functions, 655 with an `abort`; **87 functions with a class-1/2 site (164 sites)**; the
  closure (those and every function that calls one) is **298 functions**, 141 of them with abort
  sites of their own; every abort's code is a constant. The other 1537 functions get the claim
  from the text (`NoVerdict`).

## Framework

* `L/ErrSpec.lean`: `Err.cls`, error triples (`M.of_run_err`, `M.triple_of_run'`,
  `Triple.and_err`), `callE`/`callE_spec`, `triple_of_callE(_err)`, and `NoVerdict`
  (`Stmt.noV`, `closedNV`, `invoke_nv`, `callE_nv`).
* `Arena/Verdict.lean`: `twinCls`, `ErrClaim` and its kit (`bind_left`, `bind_right`, `fail`,
  `of_cls0`, `of_callE_nv`), `callW_of_callE`, `CoreSpecE` (the error half of `CoreSpec`),
  `TwinFailsV`/`ErrClaimV` (twin stages that report failures as values).
* `Arena/KnotE.lean`: the five slots' error claims, `KnotOKE`, the error knot's induction
  (`knotE_upTo` from a step `KnotStepE`, the ok knot available at every fuel).
* `Final/TwinVerdict.lean`: `twinRun` (the pipeline `TwinAccepts` lists, as one computation,
  `twinRun_of_accepts`), `TwinVerdict chunks c`, the stage constructors, `TwinVerdictPooled`.
* `Final/DrvAbi.lean`: `drv_outcome` also states the error case (`DrvErr`: entry 1's run, or
  entry 2's after entry 1 returned `2^63 + k`, fails with the code in `rax`).
* `Checker/VerdictTop.lean`: the obligations `SeqVerdicts` (entry 1 and entry 2, as L runs).
* `Final/VerdictFinal.lean`: `checkerFile_verdict`, the driver's verdict theorem, from
  `SeqVerdicts checkerProg` (a hypothesis until the bulk proves it).
* `l_model … errors` (`L/ModelGen.lean`): the models are `Except L.Err`, an `abort R` is
  `.error (.abort R)`, a callee's error passes through its continuation, and every callee without
  a spec is called through `callE_spec p n "f"` (its whole run). The spec's exceptional post is
  `fun ε => ε.code ≠ 0 → fE … = .error ε` (an out-of-bounds read, where the model reads a
  default, has code `0` and claims nothing). The `Option` models of the ok proofs are untouched.

## Calibration

* `ensure_sort`: `l_model … errors` generates `ensureSortE` and its spec in 3 s with no hint;
  the error refinement (`CoreSpecE` at fuel `n + 1` from the ok knot and the `whnf` slot's
  error claim) is 45 lines: propagation (`bind_left`), the reject site (`bind_right` on the ok
  `whnf` run, the twin's tag test, `ErrClaim.fail`), two class-0 sites.

## Relabelling by the twin (batch 1, and after)

The coordinator's arena list (five bad tests at exit 3 where con-ron rejects) and a Sonnet audit of
every class-0 site against the synced twin. Relabelled: the projection miss in `infer_proj`
(`projMissError`: a table means the index is out of range; an indexed structure-like type
declines; else reject), an unresolved constant in `infer_const` (`unknownConstError`: `sorryAx`
declines, else reject), and the four level comparisons whose `none` is the twin's `liftFueled`
decline (`lvl_eq_fueled`, `check_value_group`, `check_field_sort_bound`, `target_major_of_outside_tail`;
the second and third also got their reject). Four of the five arena tests now exit 1 with
con-ron's message. The fifth (`014_selfProof`) is the consts-resolve site of `install_value_guards`
(also `install_header`, `class_const_ok_header`, `class_rule_ok`): the twin decides there between
"string literals before String" (decline), `sorryAx` (decline) and an unknown constant (reject),
which needs a `has_str_lit` walk in L (helper `rl`).

`apply_decl` checked a declaration's safety (declines) before resolving its name, type and level
parameters, which the twin's `processLineCoreD` does first (`parseCVD`, failing `internal`): it now
resolves first (`decl_cv`), so a decline is never claimed where the twin fails internally.

## Calibration (2026-10-26)

| piece | model | time | notes |
|---|---|---|---|
| `ensure_sort` | generated, 3 s | (pilot) | 45 lines |
| `infer_const`, `infer_proj`, `infer_proj_at` | one generated, two by hand | 17, 30, 10 min (Opus) | record decoding for `projIndexedStructLike` |
| `check_thm_val`, `check_value_group` | generated (`simp []`; `gen 20 instances 4000`) | 40, 75 min (Opus) | most time in model generation |
| `check_div_mod_pin(_loop)` | generated (`simp`) | 40 min both (Sonnet) | |
| `decl_kind`, `vi_unsafe` | generated | 20, 10 min (Sonnet) | verdict values (`VerdictClaimR/L`) |
| `check_field_sort_bound`, `nest_cont_key` | generated | 25, 35 min (Sonnet) | |
| `check_pending_go` (+ `Entry2Verdict`) | generated | < 1 h (Opus) | the ok loop invariant reused unchanged |

The error proof copies the ok proof's case chain (`cases` on each callee's `callE`: `.error` the
callee's claim and `bind_left`, `.ok` the ok refinement through `callW_of_callE` and `bind_right`),
so the cost follows the ok proof's length. The friction is generating the `Except` model: `finish`
fails on most functions with many paths; `simp []` mode works on most of the rest; a few are written
by hand in the generator's shape. A sweep over the closure (`_tmp/verdicts-b/gen/`): about 110 of 292
generate with `finish` as is.

## Bulk

Families (closure functions): infer 25, whnf 66, defeq 43, declarations 37, inductives 97,
frontend 27, entry 3. One helper per family (inductives two), up to six at once.

* infer (Opus, 40 min): all 22, `inferSlots_stepE`, the stage entries `inferTypeCore_refinesE`,
  `ensureSortCore_refinesE`.
* frontend (Opus, 2.5 h with forks): all, and the two stage specs `checker_preludeStageE`,
  `checker_frontStageE` (`Entry1StagesE.prelude`/`.front`).
* defeq (Opus, 75 min): all 43, `KnotAllProg.defeqSlotE_all`, `isDefEqCore_stageE`; open: the whnf
  family's claims (`DefeqWhnfE`).
