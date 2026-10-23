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

## Helper `indproofs4-fvt`: `fvar_type_d`, `fvar_type_ds`, `get_app_args_f`

Discharged (contracts deleted): `fvarTypeD_spec`, `fvarTypeDs_spec`, `getAppArgs_spec`.

* `Arena/IndRealFvtD.lean`: `ftdF` (`fvar_type_d`: the tag test, `e_view`'s third word against
  `viewFVarTy`; writes nothing, twin state unchanged). Its own file with imports below
  `IndInstallSpec` (which calls `fvar_type_d` in `check_block_doms_at`): `IndRealFvt.lean` needs
  `DeclNatBase`, which sits above `IndInstallSpec`. `eViewW_head1` moved here from `RecClassSpecA`.
* `Arena/IndRealFvt.lean`: `ftdsF` (`fvar_type_ds`; its loop named `ftdsLoop`, `fvarTypeDsL_eq`
  by `rfl`; the memory after is `wrIW (allocMem m l) q ws`, `recPost_wr` + `slice_keep`) and
  `gaaF` (`get_app_args_f`: `getAppArgs_refinesR`, `get_app_args` without the whnf lane's bound
  `|SPN| < 2^63` (the room checks give `top + n ≤ len64 SPN < 2^64`; `fillW_okR` likewise); the
  stack slice into a fresh pool slice by `spn_to_iw` (`s2iW_wr`); the top put back). The whnf
  lane's lemmas are untouched (changing them would rebuild most of the tree). `stageR_hi`,
  `decHL_word` moved here from `IndRealSpine.lean`.
* **`fvarTypeDs`' pre strengthened** by `0 < l → o + l ≤ iwTop m`: a slice straddling the pool's
  top overlaps the fresh output slice and the loop would read a word it wrote; the contract as
  stated was false there. All callers had the bound (from `decRL`, or `DecB` in `RecClassSpecM`).
* Bundles: `GaaF`/`FtdF`/`FtdsF` are fields of `AdF` (`gaaF_spec`, `ftdF_spec`, `ftdsF_spec` in
  `IndRealSpine.lean`); files below `IndRealSpine` take `FtdF p` (`IndInstallSpec`, `IndSumSpec2A`,
  `IndSumSpec11`, `CfoProg.ftd`); `AgreeProg.ad`, and `had : AdF p` on `classBinder`,
  `classGenBinder`, `classGenIhParts`, `checkBlockAgreeOne`. `Checker/IndRealFvt.lean` proves the
  three for `checkerProg`. Frames: `MFr.ofFtdF`/`ofFtdsF`/`ofGaaF` (`IndPosMemo`), `rec2NoMR_ftd`.
* **Not done: `open_pis_at_fvars_f`.** `opf_go` calls `inst_list` (`instantiateListFast`), whose
  refinement needs `ArenaL = ArenaD ∧ ILR`: the memo relation of array 50 / `CTL[50]` (`coreIlSch`),
  in particular every slot stamp `≤` the epoch, so that `ilm_clear`'s epoch bump empties it.
  `StageR` does not constrain array 50; with a stale slot stamped at the new epoch `inst_list`
  returns a wrong hit. `StageT` carries it (`CoreMemos.1`). Needs the pending decision (memory-only
  hypothesis `∃ mp, MemoRG ilSch lfKey decE m mp` in the contract's pre and post, or `StageT`).
