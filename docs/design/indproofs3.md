# Lane `indproofs3`: Phase 8: open block functions, StageT, Rec* targets

Journal of lane `indproofs3` (decisions, measurements, findings, open ends). Only this lane edits this file.

Landings 1–2 are in `DESIGN.md` ("Phase 8 proofs, round 4 (2026-10-22, lane `indproofs3`)").

### Landing 3: `StageT`, the core's write set, the entry points under `StageT`
Coordinated with the coordinator (and lane `decls4`'s note: `decls4` does not change `StageR`):
`StageR` keeps its shape; **`StageT`** (`ConAgua/Arena/IndTwin.lean`) is a separate relation by
named components — `stage : StageR`, `twin : TwinOK` (lane `decls4`'s `DeclLvlStage.lean`: the
readback caches, `NStoreWF`, `StoreDen` incl. lane `defeq2`'s new `recRules`, the walk memos, three
capacities), `flag : pinW m 0 ≠ 0` — and a file migrates to it only where a core callee is reached.
* `StageT.core`: `StageT` is `CoreS` (eager bit `0`), so every `CoreS`-level refinement applies.
* **The core's write set from the text**: `CoreStageClosed p` (no function the stage's core entry
  points reach writes `IW`, `EREC`, `PINS`, `CTL[129]`, `CTL[200]`), decided for `checkerProg` in
  `ConAgua/Checker/IndCore.lean` (`decide +kernel`, as lane `whnf3`'s `CoreErec`). With it
  `StageT.of_core`: a core run's `CoreAfter` is `StageT` after and the pools are unchanged
  (`IWGrow`); `StageT.sim_core` turns any `CoreSpec` into a `Sim` on the call's run.
* **The entry points as `Sim` facts under `StageT`** (the "whnf adapters"; each replaces the
  `IndStubs` contract of the same name for a caller carrying `StageT`), sorry-free:
  `whnfTop_simT` (`whnf_top`, from the knot's `whnf` slot; the adapter `whnfTopL` had no spec
  before), `inferTypeCore_simT`, `isDefEqCore_simT`, `ensureSortCore_simT` (from `KnotSlot`'s and
  `InferLeaves`' entry refinements), `lvlEqC_simT` (lane `whnf`'s `lvlEqC_refines`). Program
  hypotheses: `KnotEntryProg p`, `p.lookup "whnf_top"`, `∀ n, KnotOK p n` (lanes `whnf4`/`defeq2`'s
  `knot_all`), `CoreStageClosed p`; L fuel `n ≤ 2^62` (the twin's `checkFuel`). `lvlEqC_simT` takes
  the two handles' readbacks, which a caller gets from `StoreDen.lvlAll`/`.sort`/`.zero`.
* **Frames by component**: `TwinOK.frame_iw` (no part of `TwinOK` reads `IW`/`CTL[200]`, so every
  pool writer keeps it), `StageT.of_iw` (a pool writer's `StageR` lemma + its frame), and
  `StageT.of_coreRef` (a master callee's `StageR` lemma + its `CoreS` refinement `CoreRef`, at a
  frame that leaves `PINS` alone); instances `internSort_stageT`, `internFVar_stageT` (from
  `IndMaster`'s `_stage` and `InferBodyIntern`'s `_core`).
* **Not done, and why** (the migration's open ends, in the order a successor meets them):
  1. *The stage's entry.* `StageT` at `check_ind_decl` must come from the declaration loop: `LoopR`
     carries neither `TwinOK` nor the flag. `decls4`'s `TwinFold` gives `StateOK` at the arm, but
     `TwinOK`'s caches/`StoreDen`/memos are `CoreS` facts after the previous declaration's core
     calls; the loop's arms run their core callees through stubs with `KeepPost` posts, so nothing
     carries them yet. Until the loop does, every stage theorem stated under `StageT` has a
     hypothesis its top caller cannot discharge (not vacuous: true in every state the checker
     reaches, by the twin's own invariants).
  2. *Stubs under `StageT`.* A stage function with a stub callee (`fvar_type_d`, `strip_pis`,
     `open_pis_at_fvars_f`, …) cannot move to `StageT` while the stub's contract only gives `StageR`
     after. Either the stubs get L code (9 of them still abort in `checkerProg`: `lv_zero_caps`,
     `name_rec`, `name_rec_i`, `rec_rule_bits`, `reserved_rec_name`, `open_pis_at_fvars_f`,
     `intern_ls_iw`, `fvar_b`, `consts_resolve_ffast`) or one generic `sorry`'d contract "a stub
     keeps `TwinOK`" in the style of `stubM_memoFrame`.
  3. *Record-pool writers.* `StoreDen.proj` quantifies over every `EREC` offset that decodes as a
     projection table (`decTbl (m.arr64 EREC) q`), so appending a record can break it;
     `StoreDen.frameE` needs `EREC` unchanged. `erec_alloc`/`cv_new`/`env_push` need `proj`
     restricted to records below `CTL[129]` (owner: lane `defeq2`, `StoreDen.lean`) or a per-writer
     argument.
  4. *`lv_leq_top`, `lv_zero_caps`, `blockLargeElimAllowed`.* `lv_leq_top` has a heap-level relation
     (`leqTopW_ok`, `LvR`); under `StageT` it needs `denoteL_lvR` at the two handles and the
     `readLevelM` runs (`readLevelM_run'`, `CoreS.withReadLC`) — the same pattern as `lvlEqC_simT`,
     not done. `lv_zero_caps` has no L code (an `abortStub` in `checkerProg`). `blockLargeElimAllowed`
     (`lv_nz` on the result sort) would follow the same pattern; its readback of `resSort` needs
     the shape's result sort to be a `sort` view's level (`StoreDen.sort`), which
     `blockShape?`'s refinement does not record yet.
* **A hypothesis no caller could discharge, removed.** `numCtorsOf_refines`,
  `blockShapeNumCtors_refines` and `blockShapeAllCtors_refines` (lane `indproofs`' helper `parts`)
  took `hsmall : ∀ i v, iwN m i = some v → v + 3 < 2^64`, a statement about *every* `IW` word that
  `StageR` does not give. It is only needed at the decoded member pointers, where `decMS` already
  reads `IW[v + 3]`, so `v + 3 < size < 2^64`: `numCtorsOfW_ok` now takes the pool's size bound
  (`IWOK`) instead, and the three census theorems follow.

### Landing 4: `lv_leq_top` under `StageT`; the generator again
* `lvLeqTop_simT` (`IndTwin.lean`, sorry-free): `lv_leq_top` refines the two readbacks then
  `Level.leq` under `StageT`, from master's heap relation (`leqTopW_ok`, `denoteL_lvR`) and the twin's
  `readLevelM_run'` (the caches stay `ReadLCOK`, `CoreS.withReadLC`); `StageT.of_heap` keeps
  `StageT` across the level heap's writes (`MemFrame [LH] [192]`). Replaces
  `IndStubs.lvLeqTopStub_spec` for a caller carrying `StageT`.
* For lanes `decls*`: `StageT.twin.den.dnN` ties the record pool's name decoder `dn` to the name
  store (`dn k = some x → denoteN … k = some x`), what `romBasisRef_quot`'s level readback needs.
* **`scripts/checker_prog.py` on master**: it builds the whole library first now (the dump sees
  only modules with an olean; a partial build made it fail with "`builtin_prelude` calls
  `pre_front_run`, …"), and it stopped on an import clash `L.Arena.decRule_fire` between
  `RecFireEnv` (lane `defeq2`) and `PromoteCIRef2`, which master meanwhile fixed the same way
  (`decRule_fireE`). `checker_prog.py --check` passes on this landing.

### The plan for `LoopT` (the loop carrying `TwinOK` and the pin flag), for its own lane
`StageT` (above) holds at the stage's entry only if the declaration loop carries `TwinOK` and
`pinW m 0 ≠ 0`. What that takes, from reading the code (lane `indproofs3`, at master `b3519c32`):
* **(a) The arms call the core through `stubM` in their models.** `DeclCvg`'s `check_value_group`
  model has `stubM "infer_type_core"`, `"ensure_sort_core"`, `"lvl_eq_c"`, `"is_def_eq_core"` (and
  `loose_bvars_bounded_fast`, `has_fvar_fast`, `all_level_params_defined`, `consts_resolve_ffast`)
  inline (`cvgK1`‥`cvgK8`, `ivgK1`‥`ivgK5`). `TwinOK` cannot be carried across a `stubM` step (the
  stub contracts give `StageR` only, and a generic "stubs keep `TwinOK`" contract would be false
  for an arbitrary twin op). The models must call `callW p n f` and use the real `Sim`s under
  `StageT` (`IndTwin.lean`: `inferTypeCore_simT`, `ensureSortCore_simT`, `lvlEqC_simT`,
  `isDefEqCore_simT`, `whnfTop_simT`, `lvLeqTop_simT`); `all_level_params_defined` has lane
  `decls3`'s real refinement (`ApdEnv`: `NStoreWF` and `StoreDen`'s level fields — both in
  `TwinOK`). Nine callees have no L code (`abortStub` in `checkerProg`: `consts_resolve_ffast`,
  `lv_zero_caps`, `name_rec`, `name_rec_i`, `rec_rule_bits`, `reserved_rec_name`,
  `open_pis_at_fvars_f`, `intern_ls_iw`, `fvar_b`): the real program aborts there, so `callW` is
  `none` and any `Sim` through them is trivial — the models should call them by `callW` too, and
  the stub contracts go away as their L code lands.
* **(b) The loop's own steps**, each needs a `TwinOK`/flag lemma: `flush_loop` (caches reset:
  `ReadLCOK` holds of empty caches; `StoreDen.caches`), `enter_loop` (`enableScratch`: a cached
  scratch handle must stay a readback — provable now from lane `decls4`'s `StateOK`/`LsWF` via
  `TwinFold.enterAM`, which is what killed `indproofs2`'s first attempt), `drop_loop`, the
  promotion (`promoteVG`/`promoteNew`), `pendPush`, the pending checks, the pin install
  (`DeclPins`), `andPinOk`, and the arms (axiom, quotient: no core call but canon; definition/
  theorem/opaque: (a); inductive: the stage, under `StageT`).
* **(c) The start.** `TwinOK` of the state after the pin stage (`StoreDen` of the store the pins
  interned, `CoreMemos` of the memory as the pipeline leaves it, empty caches) from the pipeline's
  stage theorems (lanes `romload`/`integrate`), and the flag from the pin stage's post.
* **Order**: define `LoopT := LoopR ∧ TwinOK ∧ flag` as a separate predicate (`LoopR` unchanged);
  (b)'s bracket lemmas first (they unblock `lvlEqStub_spec` at `DeclCvg`'s call sites); then the
  axiom and quotient arms; then (a) for `check_value_group`; then the start (c); last the
  inductive arm (`check_ind_decl` under `StageT`, which needs the stage's theorems restated under
  `StageT` — `StageT.of_iw`, `StageT.of_coreRef`, `internSort_stageT`, `internFVar_stageT` are the
  frames for that, and the stage's remaining stubs block it the same way as (a)).
* For `romBasisRef_quot`/`romBasisARef_quot` (`rom_basis_decls` kind 4: a level read back through
  `dn`): `StageT.twin.den.dnN` is the link `dn k = some x → denoteN … k = some x`.

### Landing 5: helper `tail` — `checkBlockTables`; the tail, pass and block prepared
* Helper `indproofs3-tail` (~3 h, ~1.8k proof lines, `IndInstallSpec24‥31`):
  **`checkBlockTables_refines`** (`@[refines]`, through the existing stubs; callees
  `struct_proj_guards`, `block_shape_lps`, `check_struct_proj_table`). Preconditions beyond the
  stage relation: `HbMemo s₀.mem` (the `has_loose_bvar_b` memo holds some memo; returned after),
  and `2^31 + n ≤ coreWalkFuel` (from `structProjGuards_refines`). `HbMemo` comes from the stage's
  entry: lane `loopt`'s clause "the stage memos hold some well-formed memo" (arrays 201‥208, `CTL`
  202‥219; the twin starts each walk from `∅`, L clears by an epoch bump whose lemma
  `memoRV_clear` needs some memo before).
* Prepared, not tagged: `decBPass` (the 19-word `BlockPass` record, `OMono`), word models and
  `vcgen` specs of `check_block_pass(_rec)`, `check_block_tail(_rec)`, `check_block`;
  `ictlW_sim` (the tail's model refines `checkBlockTail` given a `Sim` for `cons_block_recs_tf`,
  `ConsRecsTFSim p`, which helper `rec` is proving); `PosMR.ofClosed`/`HbMemo.ofClosed` (memo
  preservation from the callees' write sets in the text, `closedA`).
* L: `check_block_tables` loop → self-recursion; capacity guard `nP + nF + 1 ≤ nP → abort`;
  `check_block_pass_rec`, `check_block_tail_rec` split off (without the splits `vcgen` + `finish` ran
  > 20 min).
* Open for `check_block`: `blockRawRec` needs `maMR` (the mentions-any memo; part of the same
  `loopt` clause); `class_seeds` has no refinement yet and writes the walk memos.

### Landing 5 also: helper `rec` — nine `RecCheck` targets
* Helper `indproofs3-rec` (4 h 8 min, ~4.5k proof lines, `RecCheckSpec9‥20`), all `@[refines]`
  through stubs: `eraseFVarTys`, `targetCanonParams`, `targetCtorsOf`, `targetParamsDefEq`,
  `targetClassMatch`, `targetMajorNfs`, `targetK53`, `tgtStoredRules`, `consBlockRecsTF`.
  `bvar_b` enters through its real function (`bvbW_stageC`), `env_push` through lane `decls2`'s.
* New stub contract (`sorry`) `lvlsEqStub_spec` (`RecCheckSpec12`) for `lvls_eq_c`, shaped like
  `lvlEqStub_spec`: the real `lvls_eq_c` is refined under `CoreS` only; under `StageT` it would be
  a `Sim` like `lvlEqC_simT` (follow-up).
* Preconditions to be supplied at the stage's entry (lane `loopt`): `RcMR m` (`PosMR` plus the
  `target_abs` memo; every walk theorem takes and returns it, parents carry it by write sets);
  `CtorSums fe` (`targetCtorsOf`, inherited from `nestContainer_refines`: discharge at the stage
  entry, or remove by a capacity guard in `nest_container`).
* **L bugs fixed**: `tgt_stored_rules` rebuilt an outside major's rules with the fire's `IW`
  offsets, but rule records read their fire slices from `EREC` (`decRule`): now copied with
  `er_from_iw`. `target_params_def_eq` returned `false` up front on different lengths, skipping
  the twin's callees: now the twin's list recursion. Nine loops to self-recursion (D18 rows),
  capacity/handle guards after `target_abs`, `intern_const`, the depth `pfl + ftl`, `rl < 2^32`.
* Not done: `targetRecPins` (its callee `blockRecLpsOk_refines` takes `hlpb`, a statement over
  all of `EREC` that no caller can discharge — the same kind as the `hsmall` fixed in landing 3;
  needs re-proving first), `genRecCheck` (needs `classesNfs`, `classesCtors`,
  `blockLargeElimAllowed`), `targetMajorOf`. `RecCheckSpec14` takes ~380 s (`tka_spec`).

### The `StageT` migration: approach (agreed with the coordinator, not started)
* **Blocked until** lane `loopt2` restates `StoreDen.proj` over the environment's tables (today it
  quantifies over every `EREC` offset at which `decTbl` decodes, so no `EREC` writer keeps
  `TwinOK`; see `docs/design/loopt.md`). After it, `TwinOK` is a memory half (the `EREC`, `SPN`,
  array-145 sizes, `CoreMemos`: frames) and a twin half (readback caches, `NStoreWF`, `StoreDen`).
* **(1) A wrapper for callees whose twin op leaves the store and caches alone** (checks, readers,
  pool and record writers): `StageR` `Sim` + "the op keeps `store`/`caches`" + the memory frame ⇒
  `StageT` `Sim`; one line per existing theorem.
* **(2) Restatement under `StageT`** only for the theorems whose chains intern (the stage's
  interns, the nest walks, the record builders): bottom-up, the interns through
  `StageT.of_coreRef` + the master `_core` lemmas, the core callees through `KnotEntry`'s
  `KnotStageProg` sims (lane `knotwire`), the remaining true stubs through `StageT` versions of their
  contracts (same `sorry` status; to be added with (1)).
* At the stage's entry `StageT` comes from lane `loopt`'s `LoopT.stageT`.

### Landing 6: `StageT.lift_keep`; stub contracts under `StageT`
* `ConAgua/Arena/StageTLift.lean`: `KeepPostT` (`KeepPost` with `StageT` after),
  `TwinOK.withMemos` (`TwinOK` does not read the per-call memos `a.memos`), and
  **`StageT.lift_keep`**: a `StageR` `Sim` whose twin op changes at most `a.memos` and whose L run
  leaves the core memos and the pins alone (lane `loopt`'s `TwinOK.frame`, which after lane
  `loopt2`'s `StoreDen.proj` fix allows `EREC` writers) is a `StageT` `Sim`.
* `ConAgua/Arena/IndStubsT.lean` (for lane `loopt2`'s `install_value_guards`): `StageT` versions
  of four stub contracts, `sorry` like the originals — `constsResolveFFastT_spec`,
  `hasFvarFastT_spec`, `looseBVarsBoundedFastT_spec`, `allLevelParamsDefinedT_spec`.

### Landing 7 (being integrated): helpers `pos`/`pos-cls`, `stubs`, `rec2`
* Helper `pos` (+ sub-helper `pos-cls`, ~70 min + 5 h 15 min): **`checkBlockPositivity_refines`**
  (posts chain into `nestSeeds_refines`: `StageR`, `IWGrow`, `PosMR` after, kinds/normal forms as
  `PSlR`, walk state `NSB`), **`nestHolesGo_refines`** (hypotheses discharged by its one caller),
  and from `pos-cls` `targetCanonParams`, `classKeyCanon`, `classKeyOf`, `classSeeds`,
  `targetMajorOf`, `classMajors` (`RecGenSpec13‥20`), all through stubs. Preconditions for the
  stage entry: `PosMR` (lane `loopt`'s `StageMemos`), `CtorSums fe` (`nPc + nF < 2^64` per stored
  constructor; nothing in the stage establishes it — the fix is an L wrap guard in
  `nest_ctor_entry_strip` and dropping `hcs` at ~70 sites; not done), the fuel bound
  `2^31 + (n+2) ≤ coreWalkFuel`. `checkBlockCtors_refines` gained the member slices' bounds
  (`PSlR decCNSB`) in its post (needed by `CssAt`). L: capacity guard in `block_nest_ctx`; the
  positivity split replaced by `check_block_positivity_nfs(_member)` (D18); five loops to recursion
  in the class group. Open: `checkBlockClasses` (pieces proved untagged; `class_read`'s `RecsDec`
  needs `R.mI + 1 < 2^64`), `classCtorOf(s)`, `classesCtors`, `classesNfs`, `classFieldsAgree`,
  `classNodesAgree`. Files `IndInstallSpec32‥34` (renamed from 24‥26 at the merge: helper `tail`
  had used the same numbers).
* Helper `stubs` (2 h 15 min): **`strip_pis`, `strip_lams` refine `stripPis`/`stripLams`**
  (`StripTeleSpec.lean`, sorry-free) and **`instantiate1_fast`** is a real fact under `StageR`
  (`StageInst1.lean`, from lane `exprops4`'s `inst_entry`); every use of the three stub contracts
  switched and the contracts deleted. Newly sorry-free: `structUsedLater(Go, List)`, `instPisWith`,
  `targetPiDomsWith`. Models call fuel-free `stripF`/`i1F := callF i1Prog …` (`CallF.lean`: a
  program agreeing with a call-closed list runs those functions identically; runs are monotone in
  fuel), so swaps were textual; 121 spec files got `noncomputable section`. Not done:
  `abstract1_fast` (its `AbsR` memo invariant is in neither `StageR` nor the stubs' write set),
  `instantiate1_lift_fast` (no refinement exists). The 17 GB build was an inline
  `decide +kernel` over the write-set lists (now separate lemmas).
* Helper `rec2` (2 h 35 min): **`hlpb` removed** from `blockRecLpsOk_refines`/`blockShapeLps_refines`
  (an empty level-parameter slice may sit anywhere: the bound comes from the decoded slice),
  **`blockShapeAllCtors_refines`** takes only `StageR` + the shape `DecB` (a capacity guard in
  `num_ctors_of` replaces `hnum`; `hoff`/`hbd`/`hbd2` derived), `blockRecNameSetOk_refines`
  (members slice bound only when non-empty), **`targetRecPins_refines`** (`RecCheckSpec21‥24`, only
  decodings the caller holds). Reported, not fixed (same empty-slice kind): `targetCtorAt_refines`,
  `IndSumSpec3`'s `hsl`/`hslTa`, `blockShapeMemberNames_refines`' `hsrc`, `BSOK` component 2.
* Integration (helper `integ`, 35 min): the four branches built together after three fixes —
  `target_k53` moved to `stripF` (`K53Look.strip`), `TabsProg.hst`, and helper `pos-cls`'s models
  follow helper `rec`'s L changes (`target_canon_params` records offset 0 for an empty prefix;
  `target_major_of_member` calls `block_shape_lps`) — and lemma renames where helpers had used the
  same names (`cbpos*`, `lpsW_mfrT`, `…P`). Left as is: `targetCanonParams` has two `@[refines]`
  theorems (helper `rec`'s under `RcMR`, `pos-cls`'s `targetCanonParams_refinesP` under `PosMR`);
  `lpsW_mfr` exists in three copies.

### The lane's close: the open list for a successor (start here)
All files `ConAgua/Arena/`. "Through stubs" = census `sorry` only via `IndStubs.lean` contracts.

**Open phase-8 targets, bottom up.**
* `classCtorOf`, `classCtorsOf`, `classesCtors`, `classesNfs`, `classFieldsAgree`,
  `classNodesAgree` (L: `RecGen.lean`). No theorem yet. Were blocked on `targetK53` and
  `targetMajorNfs`, which helper `rec` has since proved (`RecCheckSpec13‥16`): unblocked. Template:
  helper `pos-cls`'s `RecGenSpec13‥20` (memo relation `RcMR`/`PosMR` threaded pre→post).
* `checkBlockClasses` (`RecGen.lean`, `check_block_classes`): the keys and one-per-member pieces are
  proved but untagged (`RecGenSpec*`, helper `pos-cls`). Missing: memo-frame lemmas (`MFr`) for
  ~15 models inside `class_read`; `class_read`'s `RecsDec` needs `R.mI + 1 < 2^64` — add an L
  capacity guard (no deviation row) rather than a hypothesis.
* `blockLargeElimAllowed` (`IndParts.lean`, `block_large_elim_allowed`: `lv_nz` on the shape's
  `resSort`). The twin reads the level back (`readLevelM`), so the proof needs `ReadLCOK` and the
  readback of `resSort`: not available under `StageR`. Do it under `StageT` with
  `lvLeqTop_simT`'s pattern (`IndTwin.lean`: `denoteL_lvR`, master's `nzW_ok` in
  `LevelSimpRel.lean`, `readLevelM_run'`, `CoreS.withReadLC`, `StageT.of_heap`); the readback of
  `resSort` from `StoreDen.lvlAll` once the shape's result sort is known to be a level the store
  holds (record it in `blockShape?`'s refinement: it comes from a `sort` view). Its caller is
  `genRecCheck`, so either `genRecCheck` moves to `StageT` or this needs a `StageR` stub contract
  (true of the real function; not preferred).
* `genRecCheck` (`RecGen.lean`, 7 `l_impl` pieces; `genRecCheckAnyNoMember_refines` in
  `RecGenSpec2` is a part): needs `classesNfs`, `classesCtors`, `blockLargeElimAllowed`. When done,
  replace `genRecCheck_pending` (`IndInstallSpec21.lean`, `sorry`) by it at `checkBlockRec`.
* `checkBlockTail` (`IndInstall.lean`): `ictlW_sim` (`IndInstallSpec31`) is the proof given
  `ConsRecsTFSim p` (a `Sim` for `cons_block_recs_tf`); helper `rec` proved `consBlockRecsTF`
  (`RecCheckSpec18‥20`): derive `ConsRecsTFSim p` from it and tag. Hypotheses: `HbMemo m` (lane
  `loopt`'s `StageMemos`), the pass record (`BPassR`) and block (`decEBlk`) decoded, and a write-set
  fact `closedA p hbFreeA hbFreeC fs` (checked by `#eval` on `checkerProg`, 801 functions; the
  decided theorem is not written — use lane `erecfix`'s chunked `WriteSetSplit`, never one inline
  `decide`).
* `checkBlockPass` (`IndInstall.lean`; models/specs `IndInstallSpec28‥29`, record `decBPass`):
  needs `checkBlockClasses`; the rest is proved (`checkBlockInds`, `checkBlockCtors`,
  `blockNestCtx`, `checkBlockPositivity`, `classSeeds`, `nestSeeds`). Carry `PosMR` in and out.
* `checkBlock` (`IndInstall.lean`, model/spec `IndInstallSpec29`): needs pass and tail;
  `blockRawRec` needs `maMR` (in `StageMemos`); `blockShapeAllCtors_refines` is fixed (helper
  `rec2`); `blockShapeMemberNames_refines`' `hsrc` must come from the shape's builder.
* `checkDecl`'s `.indDecl` arm (`check_ind_decl`, `IndParts.lean`; today `@[refines_part checkDecl]`
  pieces): above `checkBlock`. **Target shape** (lane `loopt2`'s ind arm calls it):
  `∀ n m a …, (ind_block_to_erec's post) → StageT dn vis fe m a → callW p n "check_ind_decl" [vis,
  o, l, w] m = some (r, m') → ∃ fe' a', (checkIndDecl …).run a = .ok (fe', a') ∧ StageR dn (r.headD
  0) fe' m' a' ∧ CoreMemos m' ∧ IWGrow m m'`.
* Hypotheses still to remove or discharge at the stage entry: `CtorSums fe` (`nPc + nF < 2^64`
  per stored constructor; used by `nestRoot`, `classMajors`, `targetMajorOf`, `targetCtorsOf`;
  fix: an L wrap guard in `nest_ctor_entry_strip`, then drop `hcs` at ~70 sites in
  `IndPos2Spec*`); the memo predicates `PosMR`, `maMR`, `HbMemo`, `RcMR` (lane `loopt`'s
  `StageMemos` supplies them); the fuel bound `2^31 + n ≤ coreWalkFuel`; the empty-slice-offset
  kind reported by helper `rec2` (`targetCtorAt_refines`, `IndSumSpec3`'s `hsl`/`hslTa`, `BSOK`
  component 2). Duplicates to clean: `targetCanonParams` has two `@[refines]` theorems
  (`RecCheckSpec9` under `RcMR`, `RecGenSpec13`'s `…_refinesP` under `PosMR`); `lpsW_mfr` in three
  copies.

**Stub contracts still in use** (`IndStubs.lean`, all `sorry`; plus `lvlsEqStub_spec` in
`RecCheckSpec12`, `genRecCheck_pending` above): `stubM_spec`, `stubM_memoFrame`, the core entry
points (`whnf_spec`, `inferTypeCore_spec`, `ensureSortCore_spec`, `isDefEqCore_spec` — real only
under `StageT`: `KnotEntry.lean`'s `KnotStageProg` sims), `lvlEqStub_spec`, `lvLeqTopStub_spec`
(real under `StageT`: `lvlEqC_simT`, `lvLeqTop_simT`), `checkConstantVal_spec`,
`constsResolveFFast_spec` (lane `tails` helper coming), `openPisAtFvarsF_spec`, `getAppFn_spec`,
`getAppArgs_spec`, `mkAppN_spec`, `piResult_spec` (adapters in `WhnfEntry.lean`, no refinement yet),
`fvarTypeD(s)_spec`, `instLPFast_spec`, `instPisAtLift_spec`, `instantiate1LiftFast_spec`
(dischargeable now from `i1lFast_refines`, `WalkLiftRefine.lean`, pre `ArenaI = ArenaD ∧ I1R`),
`abstract1Fast_spec` (`abs_entry` needs its `AbsR` memo in the relation), `bvarB_spec` (real
`bvbW_stage` exists; remaining uses in `RecGenSpec2`/`RecCheckSpec2`), `fvarB_spec`,
`hasFvarFast_spec`, `looseBVarsBoundedFast_spec`, `allLevelParamsDefined_spec` (lane `decls3`'s real
one needs `ApdEnv`: `TwinOK` facts), `internLsIw_spec`, `nameRec(I)_spec`, `projTableName_spec`,
`isProjFnShape_spec`, `reservedRecName_spec` (dischargeable now from lane `tails`'
`L.Stubs.reservedRecName_refines`, `StubNamesRefine.lean`), `recRuleBits_spec` (dischargeable now from lane `tails`' `L.Stubs.recRuleBits_refines`, `StubIndRefine.lean`, bundle `RrbProg`), `indParamsOk_spec`,
`lvZeroCaps_spec`, `internNanonStub_spec`. Since the abort-stub lane, every one of these functions
has L code in `checkerProg` (0 `abortStub`s).

**The `StageR` → `StageT` migration** (the way to make the core callees real; the target shape
above needs it). Tools on master: `StageT`, `StageT.of_core`, `StageT.sim_core`, the entry sims
(`IndTwin.lean`, `KnotEntry.lean`), `StageT.of_iw`/`of_coreRef`/`of_heap`, `StageT.lift_keep` and
`KeepPostT` (`StageTLift.lean`), `IndStubsT.lean` (StageT stub contracts), lane `loopt2`'s
`TwinOK.of_grow`/`of_istep`, `StageS`, `StageC` (`StageR` + con-ron's `CheckOK` + `TwinMem` + flag,
`StageC.of_leaf`, `StageC.of_T`, `callW_leafFrame`: `TwinStep.lean`, `StageC.lean`) and the
`CallM`/`stubCall`/`realCall p` model pattern (`DeclCvg.lean`: one model for the `StageR` (stub)
and the `StageT` (real) proof). Plan: (1) callees whose twin op keeps store and caches: wrap their
`StageR` theorems with `lift_keep` (one line each); (2) interning chains: restate bottom-up, the
growers through `StageC`'s `CheckOK` route where a core call precedes the interning (lane `loopt2`
does the same in the arms — do not invent a third route), the interns through `of_coreRef`/
`TwinStep`; (3) the remaining true stubs through `StageT` versions of their contracts
(`IndStubsT.lean`) until their real refinements land; (4) models via `CallM` so the `StageR` proofs
keep working during the migration. Top: `check_ind_decl` in the shape above.

**Numbers at the close** (`scripts/census.py --no-build`, this branch at master `b382c51e`):
phase 8 **88 proven, 117 sorry (all proven locally, i.e. only through stub contracts), 12 written,
6 todo** of 223 (lane start: 79 / 108 / 30 / 6); totals 972 proven / 158 sorry of 1352. Lane:
~7 landings, five helpers (tail, rec, pos with pos-cls, stubs, rec2) plus an integration helper,
at most three at a time; ~15k proof lines added by the helpers. Lessons: helpers numbering spec
files in parallel collide (`IndInstallSpec24‥26` twice) — give each helper a number range; three
helpers each turned the same `while` loop into recursion — assign L functions, not just targets;
generated files (`Prog.lean`, `AsmPart*`, `loopFns`, `leafFns`, `coreFns`) conflict on every merge:
take master's and regenerate.
