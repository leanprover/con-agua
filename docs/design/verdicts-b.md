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
