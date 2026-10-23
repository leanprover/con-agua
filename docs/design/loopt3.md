# Lane `loopt3`: the declaration loop, continued

Journal of lane `loopt3` (decisions, measurements, findings, open ends). Only this lane edits this
file. Continues lane `loopt2` (`docs/design/loopt2.md`, its table "`PipelineRefines checkerProg`:
remaining obligations", items 7, 10, 11, 12, 12a and option (a)). Start: master `c92f106b`.

## Item 7: the loop over the front's records (`DeclsF`)

`LoopR.decls` is `DeclsF` (the front's relation, inductive records included) instead of `DeclsR`
(one-constant kinds only). Every arm lemma that took `DeclsR` takes `DeclsF`: on a concrete
one-constant record `DeclAtF` unfolds to `DeclAt`, so the arms' proofs are unchanged.
`DeclsR` is gone (`StateDR.lean`: unused after the switch); `declAt_of_F` (`DeclBase.lean`) gives
`DeclAt` of a record that is not an inductive block.

## Landing 1: `install_then_check` under `StageT` end to end

All of phase A's and phase B's callees run from `StageT`; the interim contract
`stubArm_keepsCoreMemos` and the `StageR` arm specs with the quotient readers' `sorry`s
(`DeclCheckLoop.lean`'s `checkDeclAxiom_loop`, `checkDeclQuot_loop`, …) are gone, and so are the
`StageR` phase B (`checkValueGroup_spec`, `checkPending_refines`, `checkPendingGo_refines`,
`checkPendingGo_worker`), which went through the core's stubs.

* **Kind 6 (items 10, 11).** `checkDecl_loopT` handles the inductive records: `indArm_callWT`
  (`ind_block_to_erec` by `indBlockToErec_ok`, which writes only `EREC` and its top, so `TwinOK`
  and the flag stay by `TwinOK.frame`; then `check_ind_decl` by the contract `IndArmSpec`).
  **`IndArmSpec p dn`** (CheckerT.lean) is lane `indproofs4`'s eventual top theorem in the shape
  `docs/design/indproofs3.md` records ("Target shape"), plus the twin facts the loop has at the
  arm (`StateOK`, `FoldOK`, the record's denotation, `FrontBlock`); it is a field of
  `LoopCallees`. If indproofs4's theorem needs `StageMemos`/`CrOK` at the arm, the fold must carry
  them (not done: every other step would need their frame). `istgW_ok` routes kind 6 to
  `check_decl` (twin: `installStepGo`'s fall-through arm). `and_pin_ok` on an inductive record
  (`andPinOk_refinesT`) by `andPinOkInd_refines` (lane `decls4`), `TwinOK` by `TwinOK.of_grow`
  from con-ron's `andPinOk_run`, `FoldOK` by `FoldOK.step`, the scratch flag by
  **`andPinOk_scratch`** (`AndPinScratch.lean`, new: combinators `KeepsScr` over `AM`; interning
  keeps `EStore.scratchOn`, canon's comparisons only read and intern names). The twin's fold step
  (`TwinFold.step_pext`) was already generic over the record kind. `FrontDecls ds` (the front's
  blocks have `FrontBlock` shape) is a hypothesis from the loop's start on.
* **The arms (option (a)).** Helpers `loopt3-nat` (`DeclNatGateT.lean`: the structural-`Nat` gate
  under `StageC`, `StageC.of_run`; `DeclDefnT.lean`: `cdfW_okT`), `loopt3-div`
  (`DeclDivGateT*.lean`: `divGateSpecC`, the `Nat.div`-family gate under `StageC`) and `loopt3-axq`
  (`DeclAxQuotT.lean`: `cdaW_okT`, `cdqW_okT`; their callees are leaves but for the constant
  check, so no `CheckOK` is needed; `cdaW_gen`/`cdqW_gen` generalize the `StageR` proofs over the
  constant check's spec). New loop-start facts: **`QuotDn dn`** (Quot's `u` has a handle under
  `dn`; with `TwinOK.den.dnN` it gives the readers' `NamesDn`) and `PinsDenote` at each step
  (from `TwinFold.pinsD`, carried across `and_pin_ok` and the bracket by `PinsDenote.pmono`).
  `check_decl_defn`'s whole-call frame by `StepIn p indFns` (it is in no text list).
* **Phase B (items 12, 12a).** Helper `loopt3-phaseb` (`PhaseBT.lean`): con-ron's phase-B invariant
  `TwinPend` (`FoldOK` at the final environment, `PendRel` per remaining record; from
  `installFold_bridge`), `checkPendingGo_refinesT`, the worker form `checkPendingGo_workerT`.
  `TwinPend.caches` is `pend ≠ [] → caches empty` (`installFold_cachesOr`: the fold ran no record
  or ends in `dropScratch`), because the parse before the loop leaves the caches non-empty (con-ron's
  `FoldOK_of_start` note): no caches hypothesis at the loop's start.
* **`installThenCheck_refines`** now ends in the shape of lane `pipeline`'s `SeqAccepts`: `∃ k fe
  pend a' s'', installFold … a₀ = .ok (.ok (k, fe, pend), a') ∧ checkPendingList … a'.worker =
  .ok (.ok (), s'')`. Hypotheses: `LoopCallees dn p` (now with `andInd`, `indIn : StepIn p
  indFns`, `indArm : IndArmSpec p dn`, `quotDn : QuotDn dn`), `FrontDecls ds`, the lookups, fuel
  `n ≤ 2^62`, `TwinFold` at the start, `LoopR`, `LoopMem`, `CoreMemos`.
* After merging master: lane `indproofs4`'s 67aab388 moved the walks onto real models; helper
  `loopt3-fix` ported `DeclDivGateT1.lean` (`lbbF_okT`, `hffF_okT`).

**Open (item 5 and 13):** the R7 → loop-start lemma and `LoopStage` (requests to lane `pipeline`
via the coordinator: the fuel premise `n ≤ 2^62` in `LoopStage`'s `RelSpec`; in R7 `CoreR m
a.caches`, `PinsR`, `IWOK`, the untouched index rows/pending count/promotion memo; from the twin's
prefix `FrontDecls ds` and `u`'s persistent handle); `StepIn checkerProg indFns` and the other
new `LoopCallees` fields at `checkerProg`.

## Landing 2: the loop's start and `LoopStage` modulo named facts

* **`Arena/LoopStart.lean`**: `LoopZero m` (the arrays/`CTL` words the loop needs zero: the core's,
  the inductive stage's and `consts_resolve_ffast`'s memos, the index rows 132‥134, the pending
  count `CTL[130]`, the number of constants `CTL[128]`, the promotion memo 146‥149 / `CTL[140‥147]`)
  gives `CoreMemos`, `StageMemos`, `CrOK`, `PMemoR m PMemo.empty`, `PendR m #[]`,
  `EnvR dn m 0 (mkIFEnv IEnv.empty)`. **`dnOf st`**: the name decoder at the loop's start, the start
  store's persistent `denoteN` (`dnOf_inj` by con-ron's `denoteN_inj`); `loop_start`: `LoopR`,
  `LoopMem`, `CoreMemos` at the start from `ArenaD`, `CoreR m a.caches`, `PinsFull`, `DeclsF`,
  `PinSetsR`, `IWOK`, `LoopZero`, the pin flag and three sizes; `installThenCheck_start`.
* **`Checker/LoopStage.lean`**: `twinFold_of_prefix` (`TwinFold` from `TwinPrefix` by
  `stages_frame`), `loopZero_of_since` (`Since`'s frame over `preLoopA`/`preLoopC`, decided over
  `Nat` lists, and `loadMem_rd`), **`loopStage_of`**: `LoopStage checkerProg checkerRels` from the
  loop's program hypotheses (`LoopCallees` for every injective `dn` with `QuotDn dn`,
  `LoopTopProg`), the R7 facts lane `pipeline` is adding (`CoreR m sE.caches`: the prefix leaves the
  caches as `AState.init`'s, `PinsFull`, `IWOK`) and two facts of the twin's prefix (`FrontDecls ds`,
  `u`'s persistent handle).
* Lesson: `omega` does not see through `abbrev ArrId := Nat` (a goal or hypothesis over `ArrId`
  gives "no usable constraints"); state such predicates over `Nat`.
* **The ROM.** Helper `loopt3-prog` found `L.Rom.RomRefs checkerProg` unprovable (the readers read
  `PB`; `romRefs_of` is for `checkerProg.subPB bs`) and `CoreWalkProg.i1` asking `instEntry` where
  `checkerProg` binds `inst1` to the wrapper `inst1A`. So `loopStage_of` takes the loop's program
  hypotheses at `checkerProg.subPB bs` and transfers the run with `triple_subPB` (R7 fixes `PB`).
* **`Final/Remaining.lean`**: `checkerAsm_accepts_remaining`, `checkerAsm_accepts` from exactly
  the hypotheses still open (`#print axioms` in the module: the stub contracts' `sorryAx`).

## Landing 3: `LoopStage` from the loop's program hypotheses alone

`loopStage_of` now takes only `hLC` (`LoopCallees` at `checkerProg.subPB bs`) and `hTop`
(`LoopTopProg` there): `FrontDecls` from lane `pipeline`'s `prefix_frontDecls`, `QuotDn` from
`prefix_quotU`, `PinsFull`/`IWOK` from `R7`, and **`core_of_R7`**: `CoreR m sE.caches` from
`prefix_caches` (the prefix leaves `AState.init`'s caches), lane `inits`' `cachesEmpty_refines` at
the loaded memory and `CoreRM.frame` over the pre-loop write set (it avoids arrays and `CTL` words
96‥127). `Final/Remaining.lean`'s `checkerAsm_accepts_remaining` assumes exactly `hLC`, `hTop`.
Also removed: the arms' unused `StageR` loop specs (`checkDecl*_loop'`, `checkDeclThm_loop`).

## Landing 4: the loop's program hypotheses at `checkerProg` (item 13 for the loop)

Helper `loopt3-prog` (`Checker/LoopProgInd.lean`, `LoopProgTac.lean`, `LoopProg.lean`):
`checkerProg_indIn : StepIn checkerProg indFns` (call-closed superset `loopFns` minus a
hand-written list `loopStepOut` of 58 names that reach a write outside the step's write set,
compared by name codes; if a new loop function reaches such a write the per-chunk check fails and
the name must be added); `checkerProg_loopCalleesPB bs (RomOK bs) (romData prefix) : ∀ dn, DnInj
dn → IndArmSpec (checkerProg.subPB bs) dn → QuotDn dn → LoopCallees dn (checkerProg.subPB bs)` and
`checkerProg_loopTopPB` (general lemmas: write sets and lookups across `subPB`, the seven `PB`
readers, `romRefs_of` for the substituted readers; tactic `prog_bundle`, lookups from
`checkerProg_nodup` and positions, ~50 ms each). **Fix in another lane's file**
(`Arena/CoreWalks.lean`, coordinator's go-ahead): `CoreWalkProg.i1` asked
`checkerProg.lookup "inst1" = some instEntry`, false for `checkerProg` (it binds the wrapper
`inst1A`); now `inst1W` (same text as `inst1A`), `inst1OK` re-proved through the call
(`inst1_wrap`). **The end-to-end theorem** (`Final/Remaining.lean`, `checkerAsm_accepts_remaining`)
now assumes only `IndArmSpec (checkerProg.subPB bs) dn` for injective `dn` (beside the stub
contracts' `sorry`s).
