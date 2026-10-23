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

## Landing 1 (in progress)
* `reserved_rec_name` (`rrnF`, from lane `tails`' `reservedRecName_refines`) and `rec_rule_bits`
  (`rrbF`, from `recRuleBits_refines`): both write nothing (`closedA … [] []`). Uses switched in
  `IndPartsSpec4` (`block_rec_names_unreserved`) and `IndSumSpec10` (`sum_rules`); bundles `RpLook.rrn`,
  `TsrLook.rrb`. Contracts `reservedRecName_spec`, `recRuleBits_spec` deleted. Newly proven:
  `blockRecNamesUnreserved`, `sumRules` (phase 8: 90 / 115).
* Found on master: `lakefile.toml` lost the globs `ConAgua.Arena.DeclArmT`, `ConAgua.Arena.LeafFns`,
  `ConAgua.Arena.StageC`, `ConAgua.Checker.LeafAll` at `059f3aec` (merge of `tails`); restored here.

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
