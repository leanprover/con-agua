# Lane `indproofs4`: Phase 8: discharge stub contracts, open block functions, StageT

Journal of lane `indproofs4` (decisions, measurements, findings, open ends). Only this lane edits
this file. Start: master `048f8e8d`, phase 8 88 proven / 117 sorry / 12 written / 6 todo of 223.

## Discharging a stub contract from a real refinement (the recipe)

`IndStubs.lean`'s contracts are about the opaque `stubM f`; a caller's model contains
`stubM f m args`. A real refinement (another lane's `RefAM p f … (StageR …) op post` under a program
bundle) replaces the contract like this (`Arena/IndReal.lean`, precedent `StageInst1.lean`):

1. `P : Prog`, the callee's call-closed function list, and `closedA P A C (P.map (·.1)) = true`
   (`decide +kernel`, a small list: well under a second);
2. the model `xF := callF P f` (program- and fuel-free), `xF_spec` under `ProgHas p P`;
3. `xF_ok : RelW xF args pre op post := relW_callF (owner's refinement at p := P)`, the owner's
   program bundle at `P` by `by constructor <;> rfl`;
4. at the use sites: `stubM "f"` → `xF`, `stubM_spec p "f" n` → `xF_spec p hx n`, the contract →
   `xF_ok` (same argument order), and the bundle `hx : XF p` added to the spec's section variables
   and the program-bundle structure the caller already threads (`RpLook`, `TsrLook`, …);
5. `ProgHas checkerProg P` in `Checker/IndReal.lean`: `.cons rfl <| … .nil`, one `rfl` per
   function (seconds, ~3.5 GB);
6. delete the contract from `IndStubs.lean`.

Files whose models now contain a `noncomputable` `callF` need `noncomputable section`
(`RecCheckSpec17‥24` got it).

## Landing 1
* `reserved_rec_name` (`rrnF`, from lane `tails`' `reservedRecName_refines`) and `rec_rule_bits`
  (`rrbF`, from `recRuleBits_refines`): both write nothing (`closedA … [] []`). Uses switched in
  `IndPartsSpec4` (`block_rec_names_unreserved`) and `IndSumSpec10` (`sum_rules`); bundles `RpLook.rrn`,
  `TsrLook.rrb`. Contracts `reservedRecName_spec`, `recRuleBits_spec` deleted. Newly proven:
  `blockRecNamesUnreserved`, `sumRules` (phase 8: 90 / 115).
* Found on master: `lakefile.toml` lost the globs `ConAgua.Arena.DeclArmT`, `ConAgua.Arena.LeafFns`,
  `ConAgua.Arena.StageC`, `ConAgua.Checker.LeafAll` at `059f3aec` (merge of `tails`); restored here.
* Landed as `7d763a9a` (phase 8: 90 proven / 115 sorry).

## Landing 2 (landed as `9a3cbebf`, phase 8: 91 / 116)
* **`checkBlockTail_refines`** (`IndInstallSpec35`): `ConsRecsTFSim p` discharged from helper
  `rec`'s `consBlockRecsTF_refines` (`consRecsTFSim_of`; the `hb` memo after from the write set).
  Census: written → sorry (proven locally; the sorry comes through `genRecCheck_pending` and stubs).
* **`checkBlockClasses_refines`** (`RecGenSpec21`): `class_read`, `class_read_classes`, the keys,
  the majors, one class per member. Glue: `slots_ok` (stable slots → decoding + `SlotsExt`),
  `ccRes_pslR` (keys below the tops, `decCK_truncM`); the walk memos across `class_read` /
  `class_read_classes` by `PosMR.ofClosed` (program fact `closedA p posFreeA posFreeC fs`: checked
  by `#eval` for `checkerProg`'s closures of both, 103 functions; the decided theorem for
  `checkerProg` is not written yet — chunked, as `IndCore.lean`).
* **Stable decodings lie below the top** (`RecGenSpec22`, finishing helper `pos-cls`'s
  `RecGenSpec20`): generic `word_lt_of_stab`/`iwN_lt_of_stab` (a word every growth keeps is below
  the top — perturb it, `perturb`), `ptr_lt_of_stab` (a pointer whose perturbation to `2^64-1`
  breaks the decoding), then `stab_decCS_decB` and `stab_decCR_decB`: a stably decoded class
  reading (`class_read`'s `decRead`) is `DecB`, as the pass's record wants.
* **Capacity guard** in `class_read_rec_cls` (`if mI + 1 == 0 { abort }`): `RecsDec` no longer
  needs `R.mI + 1 < 2^64` (no deviation row: a capacity). Model `crW` got the arm `crW_big`.
* Helper `walks` (126 min, ~50 work): `bvar_b`, `fvar_b`, `has_fvar_fast`,
  `loose_bvars_bounded_fast` contracts (and the two `StageT` ones) discharged
  (`IndRealWalk(T).lean`, `Checker/IndRealWalk.lean`); `fvar_b`/`has_fvar_fast` via `fvbW_okD`
  under `ArenaD` (the `ArenaA` refinements need `AbsR`, not in `StageR`). Touched lane
  `loopt2`'s decl bundles (`CvgProg`, `IvProg`, … got `bvb`/`hf` fields). Newly proven:
  `nestWalkStack`.
* Memo invariants outside `StageR` (decision pending): `consts_resolve_ffast` needs `CrOK`
  (array 155), `instantiate1_lift_fast` needs `I1R` (array 51, `CTL[52]`), `abstract1_fast` needs
  `AbsR` (array 49, `CTL[48]` = `CoreMemos`' `coreAbSch`, so `StageT` has it). Plan: take them as
  memory-only hypotheses (like `StageMemos`) where the switched callee is used, or switch those
  callers to `StageT` (its `TwinOK.memos` holds `CoreMemos`); `CrOK`/`I1R` would go into the
  memo clause lane `loopt2` carries.

## Helper `indproofs4-names`: the name and level-list interning stubs

Discharged (contracts deleted): `internNanonStub_spec`, `internLsIw_spec`, `nameRec_spec`,
`projTableName_spec`, `isProjFnShape_spec`, `isProjFnShapeT_spec`. Models and facts:

* `Arena/IndRealNames.lean`: `naF` (`intern_nanon`, master's `nainternW` and `internNAnon_stage`),
  `nrF` (`name_rec`: `pool_room`, the bytes `rec`, master's `intern_nstr`), `ilF` (`intern_ls_iw`:
  `pool_room`, `iw_pool`, master's `intern_ls`), `ptF` (`proj_table_name` under `StageR`; lane
  `whnf`'s `projTableName_refines` is under `CoreS`, the proof is the same minus `nwf`). Each body
  is a model over its callees' runs (`callW`), related through the callees' word models; the
  pool scratch is a growth (`grows_top`, `grows_set_above`, `iwpW_ok`), so `ArenaD.grow` and
  `StageR.of_walk`/`stage_of_name` give `StageR` after. Handle bounds: an `intern_*` model's
  handle is below `2^32` by the store relation alone (`internM_lt`: a hit is a node below the
  count, an append the count, both below `2^27`); `intern_nanon` and `intern_nnum` need it (no
  abort in the L code).
* `Arena/IndRealIpf.lean`: `ipfF` (`is_proj_fn_shape`) and `ipfW_run` (the `num`/`str` views and
  the string bytes against `"proj"`/`"projTable"`), `isProjFnShape_refines` (census). Kept apart
  from `IndRealNames.lean`: importing that into `DeclHeader.lean` brought `L.Ind.fuelW` (`RecSim`)
  and `L.Arena.inferTypeCore_spec` (`KnotSlot`) into the declaration files and made their names
  ambiguous. Its `vcgen` spec needs `L.evalC_spec` (the `||` chains; plain `evalC` timed out).
  `ipfF_okT` (`StageT`) is in `IndStubsT.lean`: nothing changes, no `lift_keep` needed.
* Bundles: `NaF`/`NrF`/`IlF`/`PtF`/`IpfF` fields added to `MjProg`, `CrrProg`, `IndPartsProg`
  (`nr`), `IndPartsProg5` (`na`, `il`), `NbLook`, `RpLook` (`rna`), the `param_levels` bundles
  (`il`/`hil`), `TblProg` (`hpt`), `DmProg2` (`lIl`), `IhProg` and `IvProg` (`ipf`);
  `Checker/IndRealNames.lean` proves them for `checkerProg`. `IndStubs.stubNames` no longer lists
  `intern_nanon`.
* Not done: `name_rec_i` (needs the decimal digits of `i` from the `mulhi` loop and `dec_len`
  against `Nat.repr`, two inline `while` loops; `targetRecPins` has other stubs too, so it would
  not turn a target proven); `lv_zero_caps` (its op is `readLevelM`: the level's readback needs the
  twin's `readL` facts, which `TwinOK`/`StageT` carries and `StageR` does not).
* Census: phase 8 95 proven / 110 sorry (from 90 / 115): `targetMajorAt`, `targetMajorDefault`,
  `BlockShape.nestCtx`, `paramLevels`, `blockRecNameSetOk` proven; phase 2 `NIdx.isProjFnShape` proven
  (`isProjFnShape_refines`).

## Landing 3 (landed as `eff51a9c`, phase 8: 120 proven / 89 sorry)
* **`checkBlockPass_refines`** (`IndInstallSpec36`): the eight callees chained by hand (as
  `cbcW_sim`); the record by `bpRec_bpassR` (a fresh 19-word record of parts decoded below the tops
  is `BPassR`; `bpMem = wrIW`, `recMem_post`); `CtorSums` across the formers' environment
  (`checkBlockInds_ctorSums`: `checkBlockInds` pushes `.indInfo` only; needs the environment's rows
  all visible, `AllVis` — an unrestricted environment, as the loop's). New hypotheses at the pass:
  `AllVis fe`, `CtorSums fe`, `PosMR`, the posFree write set of `passCallees`.
* Helpers `spine` (165 min, ~75 work: `get_app_fn_f`, `pi_result_f`, `mk_app_n_f`; one bundle
  `AdF`; `get_app_args_f` open: `getAppArgs_refines'` assumes `SPN.size < 2^63`) and `names`
  (180 min, ~75 work) merged; phase 8 to 120 / 89.

## Landing 4 (in progress)
* **`checkBlock_refines`** (`IndInstallSpec37`): names distinct (`block_shape_all_ctors` via
  `acW_ok` for its frame, `block_caps_ctor_names` via `ctorNamesW_dec`/`_room`, member names via
  `memberNamesW_room`, `slNodup_refines` twice), flush, `blockRawRec_refines` (the
  `mentions_any` memo across the IW writers and the flush by `maMR_mfr`), pass, tail.
  `ShapeCV.grow`.

## Reply to the coordinator / lane loopt3: `IndArmSpec` premises (2026-10-23 ~09:30)
(SendMessage cannot reach the coordinator from this lane; answering here.)
* **Yes**, the stage needs `StageMemos m` and `CrOK m` as premises, and should return both in the
  post (only the stage writes arrays 201‥208; `consts_resolve_ffast` keeps `CrOK`).
* Also needed: **`∃ mp, MemoRG i1lSch lfKey decE m mp`** (`instantiate1_lift_fast`'s memo, array
  51 / `CTL[52]`; not in `CoreMemos`, whose `coreIlSch` is 50/50) — premise and post.
  `abstract1_fast`'s memo (49/48) is `CoreMemos`' `coreAbSch`: covered.
* Two environment facts at the arm: **`AllVis fe`** (`∀ n e, fe.idx[n]? = some e → e.1 <
  fe.visibleBelow`, an unrestricted environment; `IndInstallSpec36`) and **`CtorSums fe`**
  (`IndPosSpec2`: every stored `ctorInfo` has `nPc + nF < 2^64`). If `FoldOK` implies them, a
  pointer to the lemma suffices; otherwise please add them (`CtorSums` could later go away with an
  L wrap guard in `nest_ctor_entry_strip`).
* Landed as `234f3294` (checkBlock; helper `cls`'s class group, proven locally).

## `IndArmSpec`'s post `CoreMemos m'` (analysis, 2026-10-23 ~10:00)
The stage's refinements are `StageR`-level; nothing in them carries `CoreMemos` (the core walks'
memos, arrays 49/50/52‥54/151‥153). A `StageR` proof of `check_ind_decl` therefore cannot give
`CoreMemos m'` without one of:
1. **The `StageT` migration** (the plan's step 3): `StageT` contains `TwinOK.memos : CoreMemos`, the
   core entry points' `StageT` sims return it, `IndStubsT` contracts return it — but every
   refinement on the path from `check_ind_decl` down must then be restated under `StageT`.
2. **An invariant-closure lemma** (generic, L level, as `run_frame`): if every function of a
   call-closed set `fs` other than a set `E` writes outside `P`'s footprint, `P` is stable under such
   frames, and every returning call of an `E` function from a `P` memory ends in a `P` memory, then
   every returning call of an `fs` function keeps `P`. With `P := CoreMemos` and `E` := the core
   entry points and the memo walks that write the core arrays (`abs_entry`, the `instLP` walk …),
   `CoreMemos m'` follows from a write-set fact of `check_ind_decl`'s closure plus `CoreMemos`
   preservation by `E`. The catch: `E`'s preservation must hold from any `CoreMemos` memory (the
   walks clear by epoch and keep `MemoRG`; for `whnf_top` & co. it needs to be extracted from the
   knot's proofs, which run under `CoreS`).
Proposal: (2) for the memo predicates (`CoreMemos`, `StageMemos`, `CrOK`, `I1R`), which also removes
the stage-memo threading; I can write the generic lemma. Until then the arm theorem will be stated
with `CoreMemos` as a hypothesis-preserved-by-stubs contract (`sorry`, like `stubM_memoFrame`).
