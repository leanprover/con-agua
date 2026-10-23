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

## Landing 2 (in progress)
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
