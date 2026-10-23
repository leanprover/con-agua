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

## Open end 3 (quotient refs): analysis, deferred into open end 4

The reader's L code interns `Quot`'s `sortZ` name `u` (the twin keeps it as a value), so
`romBasisRef_quot` needs (i) `dn k = some u` for `u`'s handle (a state-free loop-start fact, to be
added to `TwinMem` and discharged at startup), and (ii) that re-interning `u` inside the block
read hits `k` without changing the state: `NStoreWF` and name-store extension tracked through the
block reader (`RInv` gets two fields; `internName_denote_run` gives the hit). (ii) needs `TwinOK`
at the reader call, i.e. the two consumers (the quotient arm's `qphW_ok`, the axiom arm) under
`StageT`: open end 4. `romBasisARef_quot` has no consumer (`check_basis_decl` excludes kind 4).

## Open end 4: findings

* **`TwinOK.of_check`** (was `of_fold`): `TwinOK` from con-ron's `CheckOK` (not only `FoldOK`)
  and `TwinMem`; `TwinOK.mem`, `TwinMem.step` (sizes, core memos, a name store that only grows).
* **`CoreMemos` mirrors no twin cache**: arrays 49/50 (`instantiateListFast`, `abstract1Fast`),
  52‥54 (`instLP`), 151‥153 (`wscopedBFast`, `leafGuard`) are walk-local memos; con-ron's walks
  start from `∅` each time, L clears by an epoch bump on entry, sound only on a well-formed memo.
  `CoreMemos` is that well-formedness. Resetting them in `flush_caches` cannot be O(1) (an epoch
  bump needs well-formedness; establishing it from arbitrary memory means zeroing), so it is
  carried: only `TwinOK`-preserving (`StageT`) code carries it across core calls.
* Consequently `StageT` at `check_decl`'s entry closes only when the whole `check_decl` tree
  preserves `TwinOK`: phase A's tree moves to `StageT` in one piece.
* The loop's closure (`install_then_check`, 1373 functions of `checkerProg`) writes neither
  `PINS` nor bytes, and every `CTL` index it writes is below 1024: a step keeps the pin flag and
  every array's size (a decided write set, as `LoopDecl`).

## Landing 3: models over a call reading; `check_value_group` under `StageT`

* **`CallM`** (`DeclCvg.lean`): a model reads a call of the core's entry points (and `lvl_eq_c`)
  through a parameter `c : CallM` (`Nat → FnName → List Word → Mem → Option …`): `stubCall` (the
  stubs' opaque `stubM`, for the existing `StageR` proofs) or `realCall p` (`callW p`, for the
  `StageT` ones); `CallSpec p c` is the L side (`stubCall_spec`, `realCall_spec`). `cvgW`,
  `ccvW`, `dvW`, `tvW` take it; the `StageR` lemmas instantiate `stubCall` and are unchanged
  otherwise. One model serves both proofs, no copy.
* **`cvgW_okT`** (`DeclCvgT.lean`): `check_value_group` from `StageT` to `StageT`, the core's
  entry points from `KnotStageProg`, `lvl_eq_c` from `lvlEqC_simT` (the sort's level reads back
  by `ensureSort_view` and `StoreDen.sort`, the pinned zero by `StoreDen.zero`), the pool writers by
  `StageT.of_iw`. `install_value_guards` under `StageT` is still a hypothesis (`IvgT`), until
  lane `indproofs3`'s `StageT` contracts of the four walks land (`IndStubsT.lean`).
* `LoopDecl.lean`'s agreement proofs are split into `LoopDeclAgree.lean` (cvg, iv),
  `LoopDeclArm1.lean`, `LoopDeclArm.lean` (arms): 7.4 GB in one module, under 5 GB each now
  (RSS of `lake env lean`, `scripts`-less measurement with `resource.getrusage`).

## Landing 4: value checks under `StageT`, `TwinOK` across store growth, the loop's write set

* **`DeclValT.lean`**: `check_defn_val`/`check_opaque_val` (`dvW_okT`) and `check_thm_val`
  (`tvW_okT`) from `StageT`; after the final `env_push` the stage relation at the extended
  environment and `CoreMemos` (`envPushW_frame`: index rows 132‥134, `ECON`, `CTL[128]`), which is
  what the loop needs after an arm (the arms' posts need not give `TwinOK`: no core call follows
  the push). `lvl_eq_fueled`'s model is `lfW cl n` (over a call reading; `lfW_stub` is lane
  `induct`'s `lveW`), `lfW_okT` through `lvlEqC_simT`. `install_value_guards` under `StageT` is
  still the hypothesis `IvgT`.
* **`TwinStep.lean`**: `TwinOK.of_grow`/`TwinOK.of_istep`, and `StageS` (`StageT` ∧ `StateOK`, for stretches without a core call; shared with lane `indproofs3`), `StageS.of_istep`: `TwinOK` across any twin step that
  grows a well-formed store and keeps the caches and pins (con-ron's `IStepS`, which every
  interning operation's `*_sstep` lemma gives from `StateOK`): the parts reading the old store by
  `Ext`, the parts over every node from the new store's well-formedness. The memory's half is the
  caller's.
* **`LoopFns.lean`, `Checker/LoopAll.lean`**: `loopFns` (the 1392 functions `install_then_check`
  reaches), `LoopClosed p` (none of them writes `PINS` or bytes; decided for `checkerProg` per
  chunk, 4.1 GB, 16 s), `LoopMem` (sizes, pin flag, persistent `dnN`) and `LoopMem.step` (by the
  write set and `PExt`; `TwinFold.step_pext` exposes the `PExt` of decls4's step). Not yet wired
  into the fold: that is the final switch, with `CoreMemos`.
* Helper `loopt2-quot` works on open end 3 (quot readers under `StageR ∧ StateOK ∧ QuotDn`).
