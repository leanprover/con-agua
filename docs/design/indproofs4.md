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
