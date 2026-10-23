# Lane `loopt2`: LoopT, continued

Journal of lane `loopt2` (decisions, measurements, findings, open ends). Only this lane edits this
file. Continues lane `loopt` (`docs/design/loopt.md`), its open ends in order: (1) the
`StoreDen.proj` blocker, (2) `DeclCallees checkerProg`, (3) the quotient block's readers, (4)
`lvlEqStub_spec` and the arms off `stubM`.

## Landing 1: the declaration texts' program hypotheses are satisfiable

`CvgProg`, `IvProg`, `ArmProg` (and `CheckDeclProg`'s `natText`, `dgClosed`) asked a program to
agree with the texts `cvgProg`, `ivProg`, `armText` on every function their write-set check
covers. The texts have lane `induct`'s stubs (and `DeclArmsNat`'s) where the checker's program has
real code, so `DeclCallees checkerProg` was false. Compared by `reprStr` of the lookups (a scratch
`#eval`, not committed), `checkerProg` differs from the texts exactly on:

* `cvgFns`: `infer_type_core`, `ensure_sort_core`, `is_def_eq_core`, `loose_bvars_bounded_fast`,
  `has_fvar_fast`, `all_level_params_defined`;
* `ivFns`: `is_proj_fn_shape`, `loose_bvars_bounded_fast`, `has_fvar_fast`,
  `all_level_params_defined`;
* `armFns`: those, plus `rom_cv`, `rom_ci`, `rom_expr_pin`, `rom_basis_decls`,
  `rom_basis_decls_a`;
* `natGateFns`: `nat_lit_supported`, `is_def_eq_core`; `dgFns`: `rom_pin_sets`.

(`consts_resolve_ffast` is a stub in both.) None of the proofs reads these lookups: their callers'
specs are `stubM_spec` or the readers' own refinements (`RomRefs`). The lookups were there only for
the write set (`closedW_of_agree` from the text's `decide +kernel`).

**Change.** `DeclCvg.lean`: `openFns` (the 14 names above), `StepIn p fs` (some call-closed
superset of `fs` has a step's write set, `stepA`/`stepC`; `StepIn.memFrame` is
`invoke_memFrame` for it) and `TextProg p q fs` (agreement with `q` on `fs` but `openFns`, and
`StepIn p fs`). `CvgProg`, `IvProg`, `ArmProg` are structures extending `TextProg`; `natText` and
`dgClosed` are `StepIn`; `natGateSpec` and `divGateSpecD` take `StepIn`. The four texts'
`*_closed` decides are gone (nothing used them any more).

**For the checker's program** (`ConAgua/Checker/LoopDecl.lean`): `declLoopFns` = the texts' five
lists, `stageCoreFns` and `declExtFns` (the open callees' own callees outside both: the ROM
readers' `rci_*`/`rom_*` helpers, the walks' `apd_*`/`alpd_*`), 759 functions reached; every one
has a step's write set (per-chunk checks as `LoopCore.lean`), so `checkerProg_cvgIn`, `_ivIn`,
`_armIn`, `_natGateIn`, `_dgIn`.

**Agreement halves** (after landing 1, at the coordinator's request): one `rfl` per lookup
(`checkerProg_cvgOwnK`, `_ivOwnK`, `_armOwnK`, chunks of 12 names; the elaborator and the kernel
walk `checkerProg`'s list comparing names, about 0.5 s per lookup; the whole of `LoopDecl.lean`
builds in ~90 s), and membership of `fs` minus `openFns` in the chunks by `decide +kernel`. So
`checkerProg_cvg : CvgProg checkerProg`, `checkerProg_iv`, `checkerProg_arm` are theorems.

## Landing 2: `StoreDen.proj` over the environment's tables (open end 1)

**Statement.** `StoreDen.proj : ∀ c tbl, fe.find? c = some (.projInfo tbl) → (sort, guards below
`numFields`, level parameters read back)`, instead of "at every `EREC` offset where `decTbl`
decodes". No clause of `StoreDen` reads the memory any more: `StoreDen.mem` (any `m'`);
`StoreDen.frameE`, `of_internSort`/`of_internConst`/`of_views` keep their `EREC` hypothesis as an
unused `_he` (callers unchanged); `StoreDen.mono` and `StoreDen.of_arena` lost theirs (callers
adjusted).

**Consumers.** `ProjFound` returns also `∃ c, fe.find? c = some (.projInfo tbl)` (its proof,
`projFound`, reads the row `EnvR.find?_eq` relates to `fe.find?`: `decCI_six` gives that the
decoded constant is `.projInfo tbl`). `FireOkOK`, `FireOkOKD`, `rpFire_refines`,
`rpHead_refines`, `inferProjAt_refines` take that membership beside the `decTbl` fact;
`ProjSortDen`/`FireDen` take only the membership. `cv_lps`'s projection case is
`StoreDen.proj` directly (its `he`/`hci` now unused).

**Twin side.** `TwinMem.proj` is gone: `TwinOK.of_fold` takes the clause from con-ron's
`IFEnvOK.hit` (`denoteProjTable` gives the sort, the guards' list and the level parameters,
`denoteProjTable_parts`) and `IFEnvOK.proj` (`guards.length = numFields`). `TwinOK.frame` no
longer asks the writer to leave `EREC` alone: **every `EREC` writer that keeps the core memos and
the environment keeps `TwinOK`** (lane `indproofs3`'s stage writers). A writer that extends the
environment (`env_push` of a `projInfo`) needs the new table's readbacks, which the twin's
`IFEnvOK` at the new environment gives.
