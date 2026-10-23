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
