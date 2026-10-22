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
