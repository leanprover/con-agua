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

## Status for the coordinator: `check_ind_decl` / `IndArmSpec` (2026-10-23 ~11:00)
* Done (StageR, generic `p` + bundles): `checkBlock`, `checkBlockPass`, `checkBlockClasses`,
  `checkBlockTail`, `indParamsOk` (real), `blockParts?`, `checkShapeless`, `checkBasisDecl` (lane
  decls3). In flight: helper `grc` (`genRecCheck`, replacing `genRecCheck_pending`), helper `abs`
  (`abstract1_fast` etc. with memory-only memo predicates).
* Next (me): `check_ind_decl` at `StageR` (model + `Sim`): needs `basisPinHit` — no refinement
  exists (phase 2, `written`; ROM-based like `checkBasisDecl`): a stub contract first; and
  `ShapeSrc` for `block_parts`' shape (strengthening `ShapeR` in `IndPartsSpec15`). ETA for the
  `StageR` arm theorem: a few hours.
* **Blockers for `IndArmSpec` exactly as stated**: (1) the post's `CoreMemos m'` — the stage is
  `StageR`-level and nothing carries `CoreMemos` (see "IndArmSpec's post CoreMemos m'" above):
  needs either the `StageT` migration or an invariant-closure lemma plus `CoreMemos`-preservation
  of the core entry points (from the knot's proofs). (2) Premises the stage needs that the spec
  lacks: `StageMemos m`, `CrOK m`, the `i1lSch` memo (array 51), and the instantiateList memo
  (`ilSch`, array 50 — in `CoreMemos.1`, so derivable from `StageT`), `AllVis fe`, `CtorSums fe`
  (see "Reply … IndArmSpec premises" above). Proposal: I deliver `IndArmSpec`'s shape with these
  as extra premises and `CoreMemos m'` from a documented `sorry`'d contract ("every stage
  function keeps `CoreMemos`", true of the real code) until (1) is done.

## Helper `abs`: `abstract1_fast` (the `AbsOK` memo predicate)

* **Model** `abF := callF abProg "abstract1_fast"` (`Arena/IndRealAbs.lean`; `abProg` = the adapter
  `abstract1FastA`, the `abstract1` walk, `abs_entry`; write set `absA`/`absC`), `abF_spec`,
  `abF_frame`, and **`abF_ok`**: `RelW abF [CWF, e, d, k] (StageR ∧ AbsOK) (abstract1Fast …)
  (KeepPost … ∧ AbsOK)`. The twin's run from `a` is definitionally the run from `a` with any
  `abs1C` (the entry clear), so `absEntry_refines` applies at `a` with `abs1C := mp` (`ArenaD.memo_irrel`).
  Contract `abstract1Fast_spec` deleted; bundle `AbF` (`Checker/IndRealAbs.lean`: `checkerProg_ab`).
* **`AbsOK m := ∃ mp, MemoRG ⟨49, 48⟩ lfKey decE m mp`** (`IndStubs.lean`, with the new sorry contract
  `stubM_absOK`: every stub keeps it; true of the real functions — the core keeps `CoreMemos`).
  `TwinOK.absOK`/`StageT.absOK` (`Arena/IndRealAbsT.lean`): `CoreMemos` contains it, so the `StageT`
  migration gets it for free.
* **Threading.** `AbsOK` as a hypothesis and a post through every theorem whose proof reaches an
  `abstract1_fast` call (≈80, from `abstractPrefix`/`closeTelescope`/`closeLams` up to
  `checkBlockTeles`/`Inds`/`Tail`/`Pass`/`Positivity` and the nest-positivity block `NbOK`, whose eleven
  statements now carry `PosMR m → AbsOK m → … ∧ PosMR m' ∧ AbsOK m'`). Across a callee: `AFr m m'`
  (`AbsOK m → AbsOK m'`) from the model, by `afr_auto h [callee lemmas]` (mirror of `mfr_auto`) and
  `afr_set` (chains of `set64` apart from array 49/`CTL[48]`); positivity models' `AFr` lemmas in
  `Arena/IndRealAbsPos.lean` (generated from their `MFr` frames, plus the walks `noGoW`/`dpGoW`, …).
  `RSim.withF`/`Sim.withFr` add the fact to a chain's post (`IndRealAbsSim.lean`; kept out of
  `IndRealAbs.lean`: `RecSim`/`IndRealNames` make `fuelW`/`inferTypeCore_spec` ambiguous in the
  declaration files).
* **Program facts** at the install layers: `AbsKeep p f` (every run of `f` in `p` keeps `AbsOK`)
  for the `callW` callees outside the cascade (`indsKeepCallees`, `posKeepCallees`,
  `tailKeepCallees`, `passKeepCallees`), taken as hypotheses like `closedA … hbFreeA …`; true of
  `checkerProg` (from the callees' refinements once they carry `AbsOK`, or from `StageT`).

## Reply to the coordinator: the phase-8 split (2026-10-23 ~12:00)
* **OK** with the split (loopt3: StageR→StageT migration + core-entry contracts `stubM_spec`,
  `inferTypeCore_spec`, `isDefEqCore_spec`, `ensureSortCore_spec`, `whnf_spec`, `stubM_memoFrame`;
  indproofs4: block functions, `genRecCheck`, `blockLargeElimAllowed`, `check_ind_decl` →
  `IndArmSpec`, the walk/leaf contracts).
* Already done here (landing with this commit): `abstract1Fast_spec` (memory-only `AbsOK`
  threaded through ~80 theorems, new contract `stubM_absOK`, program hypotheses `AbsKeep p f`),
  `fvarTypeD(s)_spec`, `getAppArgs_spec`, `isProjFnShape(T)_spec`, `indParamsOk` (real).
* In flight: helper `grc` (branch `indproofs4-grc`: `genRecCheck`, files `IndInstallSpec38+`,
  edits `IndInstallSpec21/35/37`, `IndStubs.lean` for a `blockLargeElimAllowed` contract). Next
  here: `check_ind_decl` (new `IndInstallSpec4x`, `IndPartsSpec15`'s `ShapeR`), then the
  memo-needing contracts (`instantiate1LiftFast` — `I1R` array 51; `constsResolveFFast` — `CrOK`
  array 155; `openPisAtFvarsF` — `ILR` array 50, which is `CoreMemos.1`): note for loopt3 —
  `AbsOK` (array 49) and `ILR` are parts of `CoreMemos`, so under `StageT` they come for free; if
  the migration reaches those callers first, the memory-only threading becomes unnecessary.
* ETA `IndArmSpec`: the `StageR` arm theorem today; the exact `IndArmSpec` statement needs
  `CoreMemos m'` after (StageT migration, loopt3) and the extra premises listed above.

## Helper `indproofs4-grc`: `genRecCheck`

`genRecCheck_refines` (`IndInstallSpec41`, census: proven locally) replaces the pending contract
`genRecCheck_pending` (deleted); `checkBlockRec_refines` now goes through it (moved from
`IndInstallSpec21` to `IndInstallSpec41`; `IndInstallSpec31` imports it).

* **L fixes in `RecGen.lean`** (no deviation rows: the twin's behaviour): `gen_rec_check_prep`
  tested the large flag with `== 1`, the twin (and `decBS`) with `!= 0`; `gen_rec_check_minor_ok`
  summed the constructor counts mod `2^64` (now `return 0` past `2^64`, above every slot count).
* Files: `IndInstallSpec38` (the loops `gen_rec_check_former_tys`, `_former_tys_c`, `_minor_ok`;
  helper fork), `39` (`gen_rec_check_pop_all`, `struct_elim_level` under `StageR` with the handle
  bound, and the **stub contract `blockLargeElimAllowed_spec`** (`sorry`: true of the real function,
  which stores nothing — its closure is checked to have an empty write set; the twin reads the level
  back, `StageT`)), `40` (`gen_rec_check_prep`'s model: right-nested suffix blocks `grpB`, `grpC`,
  `grpS2`, `grpS2b`, `grpS3`, `grpD`, one `vcgen` each; the flat 25-call body timed out at 4M
  heartbeats; middle blocks change the `seq` association, suffixes do not), `41` (the twin cut into
  continuation-passing parts `grcTwinA…R`, `genRecCheck_split` by `rfl`; the sims; the glue).
* `RecGenSpec28`'s `CnsRec` carries its source class pointer (`CnsSrc`), so that `ClassesLp`
  passes through `classes_nfs` (`classesNfs_refinesLp`).
* New hypotheses: `genRecCheck_refines`/`checkBlockRec_refines`: `RecsB` (the shape's recursor
  slice below the top, also when empty), `ClassesLp` (`classes_ctors`' own), `bs.nP < 2^63`, IW
  size `< 2^63`, `RcMR`, `GrcProg p`, `closedA p rcFreeA rcFreeC fsR` (`target_rec_pins`,
  `class_stream_recs`). `checkBlockTail_refines`: the same on the pass record (`RecsB`/`ClassesLp`
  at its words 3, 15/16, the shape's nP word), `RcMR`, the size, `closedA … rcFree` with
  `tailRcCallees`. `checkBlock_refines`: `∃ taMR`, `RecsB`, `ShapeLp` (the members' constructors'
  level-parameter slices in `EREC`), `bs.nP < 2^63`, the size, `closedA p taFreeA taFreeC fsT`
  (`block_raw_rec`, `check_block_pass`), `closedA … rcFree`, and the **pending program fact
  `PassGrcOK p`** (the pass's record satisfies the tail's three record conditions given the input's:
  to be discharged from the pass's refinement). The `closedA` facts were checked by `#eval` on
  `checkerProg` (empty violation lists); the decided theorems are not written.
