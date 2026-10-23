# Lane `indstaget`: the inductive stage from `StageR` to `StageT`

Journal of lane `indstaget` (decisions, measurements, findings, open ends). Only this lane edits
this file. Start: master `4114f77c`. Goal: replace the core-entry stub contracts
(`L.Ind.inferTypeCore_spec`, `ensureSortCore_spec`, `isDefEqCore_spec`, `whnf_spec`, and with them
`stubM_spec`/`stubM_memoFrame` for the core names) in the inductive stage by the knot's `StageT`
sims (`KnotEntry.lean`'s `KnotStageProg`).

## Scope (measured at the start)

Reverse closure of the four core contracts over the built environment (a scratch `#eval` over
`getUsedConstantsAsSet`, the stage's modules imported): **115 stage theorems** (outside the
`Decl*` files) depend on them, 20 levels deep; tops `checkBlock_refines` (level 16) and
`classesCtors_refines` (level 20). Direct users (level 1): `domsW_ok` (IndInstallSpec),
`p2ctW_ok` (IndPos2SpecM), `frameOK_step`/`posOK_step` (IndPos2SpecS), `csfW_ok` (IndSumSpec11),
`wtW_ok` (IndSumSpec2A), `tptW_ok` (RecCheckSpec), `pdsR_ok` (RecCheckSpec11), `ccoW_sim`
(RecGenSpec3), `cruleW_ok` (RecGenSpec4), `tmpW_ok` (RecCheckSpec5), `rtoW_sim` (RecGenSpec7).
Their proofs use 118 further `StageR`-producing callee lemmas, each needing a `StageT` companion.

Models with a core call through `stubM` live in 15 files (IndInstallSpec, IndInstallSpec33,
IndPos2SpecM/N/S, IndSumSpec2A/11, RecCheckSpec/5/10/11, RecGenSpec3/4/7/19); models above them
call their callees through triples, so a `CallM` parameter (lane `loopt2`'s pattern) stays local.

## Route (approved): `StageC` with con-ron's per-twin specs

First plan was pure `StageT` (keep-ops by `StageT.lift_keep`, interns through master's `CoreS`
refinements, core calls by the knot's sims). **Wrong for the growers**: under `StageT` an intern of
a `sort`/`const`/`param`/level list needs its children to denote (`internSort_core`'s `hdu`,
`internParam_core`'s `hdn`; `StoreDen`'s `sort`/`constLs`/`lvlAll` clauses), and the stage interns
those at ~17 twin sites and inside its growers; that route would need a level-validity invariant
for every stage record and relational re-proofs of every grower.

**Route C** (coordinator's go, 2026-10-23): carry `StageC` (`StageR` + con-ron's `CheckOK` +
`TwinMem` + pin flag) plus con-ron's spec preconditions (the con-leche denotations of the inputs).
con-ron's `Bridge/Inductives/*` has a `PSpec`/`PSpecP`/`PSpecL`/`CSpec(F)` for each of the ~110
inductive twins (pre: `StateOK`/`CheckOK` and the inputs' denotations; post: `PStep`/`CoreStep`
and the answer's denotation). So:

* a **core-free grower or leaf** lifts in one line: our `StageR` `RSim` + con-ron's `PSpec`
  (`PStep`: `StateOK`, `Ext`, `CacheFrame`, pins) + the L frame ⇒ `StageC` after
  (`StageC.of_leaf` pattern);
* a **core-calling** theorem (~60 outside thin wrappers) is re-proved relationally, its twin side
  transcribed from con-ron's own spec proof of the same op; at a core call `StageC.stageT` → the
  knot's sim (`StageT` after), `CheckOK` after from con-ron's `KnotSpec` (`CoreSpec.of_core`);
* **top**: con-ron's `checkIndRoute_bridge` (`Bridge/Inductives/Decl.lean`: `indParamsOk`,
  `blockParts?`, `checkBlock_bridge`), preconditions `CoreSpec` (closed), `FoldOK`, the block's
  `denoteCIList` (from `denoteDecl`), `basisPinHit b = none` — all from `IndArmSpec`'s premises
  (gap list sent to the coordinator: none).

Models: the core's calls read through `cR : CallM` (`IndCallM.lean`, moved from `DeclCvg.lean`);
the `StageR` proofs instantiate `stubCall` (statements unchanged), the new ones `realCall p`.
The parameter follows the models' direct model-call chains (rtoW → ccoW, rtsW → rtoW, …).

## Landing 1 (pilot)

* `IndCallM.lean`; `ccoW`, `rtoW`, `rtsW` over `cR`.
* `IndT/Base.lean`: `KPT`, `Sim.rsim`, the four entry points as `RSim`s of `realCall p`.
* `IndT/RecGen3.lean`: `classConstOk_of_ih` (twin: on success `installHeader`'s guards leave the
  state `classConstOk`'s own guards leave; they differ in messages only), `ccoW_simT`,
  **`classConstOk_refinesT`** (`StageT`; the census link; the `StageR` theorem is deleted). Its
  remaining sorry comes through `IndStubsT` (`constsResolveFFastT_spec`,
  `allLevelParamsDefinedT_spec`) in `ihW_okT`.
* `lake`'s `.+` glob is not understood by `scripts/modules_check.py`: the `IndT` modules are
  listed one by one in `lakefile.toml`.

## Landing 2: `AbsOK` carries `WkOK`; the `StageC` lifts

* **`WkOK m`** (`IndStubs.lean`): `WalkMemos m` (arrays 151‥153, 52‥54), the sizes of `EREC`, `SPN`
  and array 145 below `2^63`, the pin flag. `AbsOK m` (lane `indproofs4`'s walk memos) gets it as a
  fifth conjunct, `memoFreeA`/`memoFreeC` exclude the pins and those arrays/epoch words too, so
  every `AFr` model frame (143 lemmas, `afr_auto`) carries the whole memory half of `TwinOK` with no
  new per-model lemma (a `KFr` family cloned from the `_afr` lemmas was the alternative). Fixed
  sites: `AbsOK.frameD`, `WkOK.frame`, `abF_ok`, `i1lF_ok`, `crfF_ok`, `pinternW_afr`,
  `TwinOK.absOK` (takes the pin flag), `cidFreeA`/`cidFreeC` (IndInstallSpec42).
* `IndT/Lift.lean`: `StageC.of_pstep` (`StageC` across a twin step con-ron calls a `PStep`, the
  memory half from `AbsOK` after), **`RSim.liftP`/`liftPP`/`liftPL`** (a core-free callee's
  `StageR` `RSim` whose post gives `StageR ∧ AbsOK` after, lifted by con-ron's
  `PSpec`/`PSpecP`/`PSpecL`), **`RSim.liftC`** (a core-calling callee's `StageT` `RSim`, `CheckOK`
  after from con-ron's `CSpec`).

## Landing 3: the first chain under `StageC` (`classRecTyOk`, `classRecTysOk`)

* **The core's write set** (`IndTwin.lean`'s `coreStageA`/`coreStageC`, decided for `checkerProg`
  in `Checker/IndCore.lean`) now also excludes arrays 51, 155 and the stage memos 201‥208 (CTL 52,
  158, 202‥219): `absOK_core` (`AbsOK` across a core call), `RSim.coreAbs`.
* `IndT/Lift.lean`: the four entries under `StageC` (`inferC_rsim`, `whnfC_rsim`,
  `ensureSortC_rsim`, `isDefEqC_rsim`): the knot's sim, con-ron's `*_crun` (`CoreStep`, the answer
  denotes and is scoped), `AbsOK` after.
* `rgW_sim`'s continuation also gets the twin's run of `targetMajorAt` (`RSim.withRun`), so a
  `StageC` caller gets the `PStep` from con-ron's `targetMajorAt_spec`.
* `IndT/RecGen3.lean`: `ccoW_simT` threads `AbsOK`. `IndT/RecGen7.lean`: `ccoW_simC`,
  **`rtoW_simC`**, **`rtsW_simC`** (by induction; the extension after one recursor from con-ron's
  `classRecTyOk_spec` applied to its run), `classRecTyOk_refinesC`, `classRecTysOk_refinesC`
  (census links; `classRecTyOk_refines` deleted, `classRecTysOk_refines` untagged, still used by
  `genRecCheck` under `StageR`).
* **The pattern** (for helpers): a core-calling theorem's `StageC` version copies the `StageR`
  proof; at a core-free callee `RSim.liftP*` with con-ron's spec of its twin (preconditions from
  the theorem's con-ron preconditions, moved along by con-ron's `*_ext` lemmas over the `Ext` of the
  steps so far); at a core call `*C_rsim`; at an L-only step `of_pstep … (PStep.refl …)`; for a
  sub-theorem already under `StageC`, `RSim.withRun` on it and con-ron's spec of its twin on the run
  for the `Ext`/`CoreStep` the next preconditions need.

## Landing 4: target list; the declaration side's census links

* `docs/stagec-targets.txt`: the lane's 59 census targets (those whose sorry sources included one
  of the four core contracts at the start). Done: the target's sorry sources contain none of the
  four (lane `e2emeter` counts it).
* The eight declaration-side targets had their `@[refines]` on `StageR` theorems through the core
  stubs although lanes `loopt2`/`loopt3` had proved `StageT`/`StageC` versions; the tags moved:
  `checkConstantVal_refinesT`, `checkThmVal_refinesT` (tagged), `checkDefnVal_refinesT`,
  `checkOpaqueVal_refinesT` (new, from `dvW_okT`; `DeclArmT.lean`), `certW_okT` (was a
  `refines_part`; `certifyNatEqs` now proven), `cmC`, `cpaC` (`DeclDivGateT2.lean`), `crpW_okT`
  (`DeclCrpT.lean`). The `StageR` theorems stay (their arms still use them), untagged.
* Threaded `cR`: `tptW` (RecCheckSpec), `tmpW` (RecCheckSpec5), with the `StageR` frame lemmas in
  RecGenSpec19.

## Landings 5‥7: the rules chain, the RecCheck chain, the classes

* **Rules chain** (mine): `cruleW`/`cr1W`/`crsW`/`crrW` over `cR` (RecGenSpec4/9/10);
  `IndT/RecGen4` (`cruleW_okC`, `classRuleOk_refinesC`: the guards' twin chain from con-ron's
  `classRuleOk_spec` — `RC.looseBVarsBoundedFast_pstep`, `RC.hasFvarFast_pstep`,
  `allLevelParamsDefined_run`, `constsResolveFFast_pstep`, `infer_crun`, `ReadOK.flush`,
  `stripLams_pstep`, `allM_domains_resolve` at the restricted index), `IndT/RecGen9`
  (`cr1W_relC`, `crsW_simC`, `classRulesOk_refinesC`), `IndT/RecGen10` (`crrW_simC`,
  `classRecsRulesOk_refinesC`). `StageC.of_check` (Lift): `StageC` after any twin step con-ron
  gives `CheckOK` for (`CoreStep`, a flush), the store extended.
* **Helper `tpt`**: `IndT/RecCheckPins` (`targetPinTys`, `targetMajorPins`: both now proven),
  `IndT/RecGen19` (`classMajors`; `StageC.of_cstep`; `AFr` frames for `target_major_of`'s models).
* **Helper `pds`**: models of RecCheckSpec10‥15 over `cR`; `IndT/RecCheck{Tpd,Tcm,Tmn,K53}`,
  `IndT/RecGen{23,24,27,28}`: targetParamsDefEq (proven), targetClassMatch, targetMajorNfs,
  targetK53, classNodesAgree, classFieldsAgree, classCtorOf, classCtorsOf, classesCtors, classesNfs.
* **Mine**: `IndT/RecGen21` (`cbcW_simC`, `checkBlockClasses_refinesC`: a `callW`-level chain;
  the walk memos across the callees by `AbsKeep` program facts), `IndT/StreamRecs` (`csrW` over
  `cR`; `check_constant_val` real: `checkConstantVal_refinesT` + con-ron's
  `checkConstantVal_bridge`).
* Census after 87ddba90: phase 8 137 proven / 80 sorry; `inferTypeCore_spec` blocks 22 (46 at the
  start), `ensureSortCore_spec` 22, `isDefEqCore_spec` out of the top ten.
* **Interfaces agreed** (via the coordinator, with lane indproofs4): the arm theorem `cidW_okC`
  (new IndT file) takes IndArmSpec's premises (`StageT`, `FoldOK`, the record's denotation,
  `IndMemos m`) and gives `… run ∧ StageR dn (r.headD 0) fe' m' a' ∧ CoreMemos m' ∧ IWGrow m m' ∧
  IndMemos m'`; con-ron's `IndOut` the loop gets from `indSpec_of_bridge` on the run. `CtorSums`
  goes away by an L capacity guard in `nest_ctor_entry_strip` (helper pos).

## Landing 8: the block's top under `StageC` (all 59 targets done)

* **Helper `grc`**: `IndT/GenRec1‥3` (`genRecCheck_refinesC`, `checkBlockRec_refinesC`).
  **Helper `cbpos`**: `IndT/Positivity` (`cbposW_okC`, `checkBlockPositivity_refinesC`; no fuel
  premise beyond `n + 2 ≤ 2^62`).
* **Mine**: `IndT/Tail` (`ictlW_simC`, `checkBlockTail_refinesC`; `StageC.of_parts`: `StageC` from
  `StageR`, `CheckOK`, `AbsOK` and the name decoder), `IndT/Pass` (`icpW_simC`,
  `checkBlockPass_refinesC`), `IndT/Block` (`icbW_simC`, `checkBlock_refinesC`). Each copies the
  `StageR` proof (IndInstallSpec35/36/37) and runs con-ron's step specs beside it
  (`checkBlockInds_spec`, `ReadOK.flush`, `checkBlockCtors_specF`, `blockNestCtx_spec`,
  `classesStage`, `checkBlockPositivity_spec`, `seedsStage`) for the next callee's preconditions
  and for `CheckOK` across the core-free steps. The pass's post adds `StageC` at the formers'
  index and `PassTwin` (what the tail takes: con-ron's `checkBlockPass_of` on the whole run); the
  tail's post stays `StageR` (no core call after the tables).
* Interface changes against the `StageR` versions: fuel `n + 4 ≤ 2^62` instead of
  `2^31 + (n + 4) ≤ coreWalkFuel`; `AllVis` dropped (unused); `passKeepCalleesC` adds
  `class_read`, `class_read_classes`, `check_block_classes_keys` (the classes' `AbsKeep`);
  `checkBlock_refinesC` takes `ValProg p`, `AbsKeep p "check_constant_val"` (the tail's recursor
  stage) and con-ron's preconditions (`IFEnvCoh fe`, `denoteFEnv`, `dShape`, `denoteCIList`).
* The `@[refines]` tags moved off IndInstallSpec34/35/36/37's `StageR` theorems.
* Census (worktree, after merging master f38d6f00): phase 8 141 proven / 76 sorry; all 59
  targets of `docs/stagec-targets.txt` free of the four core contracts. `checkBlockPass`/
  `checkBlock` still depend on `L.Ind.checkConstantVal_spec` (not one of the four).

## Landing 9: the real constant check in the block chain; the arm under `StageC`

* `check_constant_val` in the `StageC` chain is the program's own call:
  - `ctsW`'s and `ctorW`'s calls now go through `cR` (IndSumSpec3: `ctsK1‥4` take `cR k`; IndSumSpec12: `ctorW`'s first call is `cR (n + 2)`).
  - `IndT/Sum2`, `IndT/Sum4` and `IndT/Install3` use `checkConstantVal_refinesT` (`StageT`) with con-ron's `checkConstantVal_bridge` for `CheckOK` (`StageC.of_T`); the walk memos are kept by `AbsKeep p "check_constant_val"`.
  - Every `StageC` theorem above them takes `hV : ValProg p` and `hkc` (threaded through Install3/4/7, Sum2/4/5, Pass, Block).
  - The `StageR` proofs read `stubCall`, which unfolds to the old stub.
* `IndT/CheckIndDecl`: `cidW_okC` (`refines_part` of `checkDecl`, replacing `cidW_ok`'s tag).
  - Premises: `cidW_ok`'s, with `StageT` + `FoldOK V env fe a` in place of `StageR` + `StateOK`, and the record's denotation (`∃ x, denoteDecl …`) in place of `AllVis`, plus `n ≤ 2^62`.
  - `check_block` runs at the call's own fuel `j + 5`, lifted by `callW_mono` only when the fuel is below 5 (from indproofs4's suggestion).
  - `CheckOK` before `check_block` comes from con-ron's `basisPinHit_run` (`PStep.of_caches`), `indParamsOk_spec` and `blockParts?_spec`.
  - The post is `cidW_ok`'s.
* Census (worktree): phase 8 is 141 proven / 76 sorry. `checkConstantVal_spec` is no longer a sorry source of the block chain's targets.

## Landing 10: the arm's memos (`cidW_okC`'s post as `IndArmSpec` takes it)

* `cidW_okC`'s premise is now `hM : IndMemos m`. CidMemos is derived inside:
  - PosMR/maMR/taMR come from `IndMemos.stage`;
  - `AbsOK` comes from `StageT.absOK` with `I1Memo` and `CrOK`;
  - `CoreMemos m` comes from `TwinOK.memos`.
* The post is `… StageR … ∧ CoreMemos m' ∧ IWGrow m m' ∧ IndMemos m'`.
* Write sets measured on `checkerProg` (`check_ind_decl`'s closure):
  - every memo array or epoch word of `IndMemos`/`CoreMemos` is written only by its own `…_put`/`…_clear`;
  - `mcMR` (array 208, `CTL[216‥217]`) is written by nothing;
  - `maMR` is written only by `block_raw_rec`;
  - in the tail, the recursor memos are written by `check_block_rec` (through the prep's classes walks) and `hb` by `check_block_tables`.
* How each part of the post is obtained:
  - `RcMR` is threaded through `grpCW`/`grpBW`/`grpW`/`gckW` and genRecCheck/checkBlockRec (C).
  - The calls after the classes' walks keep it by `RcMR.ofClosed`. Their names are in `grcRcCallees`, a program fact `hfRc`.
  - The tail returns `RcMR` (`cons_block_recs_tf` by `RcMR.ofClosed`; `check_block_tables` by `RcMR.ofClosedHb`, a frame outside the recursor memos but `hb`'s, with `hb` from its post).
  - Block returns `RcMR` and `maMR` (`block_raw_rec`'s post, then a `maFree` frame across pass and tail).
  - The arm frames `mcMR` across `check_block` (`mcFree`). The basis branch and the frame callees go by `armMemos_call` (`cidFree`).
  - `CoreMemos`, `I1Memo` and `CrOK` after `check_block` come from `AbsOK`.
* `StageMemos` lost its `ep` clause (epochs + 2 ≠ 0): a clear (which aborts at the last epoch) does not keep it, and nothing used it. This was approved by the coordinator; indproofs4 owns LoopT.lean.
* New program facts on `cidW_okC`. All are `closedA` frames or memberships, to be decided for `checkerProg`:
  - `hfB : "check_basis_decl" ∈ fsC`;
  - `hfRc`;
  - `hclH`/`hfH` (`rcHbFree`, `check_block_tables`);
  - `hclM`/`hfM` (`maFree`, pass and tail);
  - `hclMc`/`hfMc` (`mcFree`, `check_block`).
