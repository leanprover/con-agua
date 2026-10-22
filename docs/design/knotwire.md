# Lane `knotwire`: Cashing in the closed knot

Journal of lane `knotwire` (decisions, measurements, findings, open ends). Only this lane edits this file.

## Landing 1: the tagged whnf statements through the knot, the entry points for callers (2026-10-22)

* **Stubs gone.** `whnfCallees_stub`, `coreCallees_stub`, `iotaCallees_stub` (bundles, `sorry`) and
  `supKeep_twin` (`sorry`) are deleted. The 20 census-tagged statements that instantiated them
  (`whnfCoreStep`, `whnfCoreLoop`, `whnfCoreBody`, `whnfCoreStepProj`, `reduceProjCore`,
  `projLitToCtor`, `whnfApp`, `constValAt`, `unfoldDefinition`, `whnfStep`, `constTyAt`,
  `ruleRhsAt`, `instSpinePins`, `recFireArgs`, `andRescueSlots`, `fabScopeOk`, `litMajorToCtor`,
  `majorToCtor`, `prepareMajor`, `iotaRecAt`; all `L.Arena.*_refines`, names and tags unchanged)
  moved to the new **`ConAgua/Arena/KnotTagged.lean`** (downstream of `DefEqKnot`). Each statement is
  the old one with its program hypotheses (`WhnfCoreProg`, `IotaProg'`, `M2CProg'`,
  `WhnfDeltaProg'`, `hcl`) replaced by `hq : KnotAllProg p`; the proofs are the primed theorems
  over `KnotAllProg.whnfC/coreC/iotaC/projC`, `supKeep_of`. Nobody used the unprimed versions.
  Axioms: `propext`, `Classical.choice`, `Quot.sound`.
* **`knot_all` is `@[refines ConRon.Arena.coreKnot]`** (was `refines_part "the five slots"`): it has
  no hypothesis but the program's.
* **The entry points (`ConAgua/Arena/KnotEntry.lean`).**
  - `L.Arena.KnotTopProg p` = `KnotAllProg p` + `KnotEntryProg p` + `whnf_top`'s lookup.
    `KnotTopProg.whnfTop_core`, `.inferTypeCore_core`, `.isDefEqCore_core` (`CoreSpec` at L fuel
    `n + 1`, `n + 1 ≤ 2^62`, twin at `.verified` and any `F ≥ n`) and `.ensureSortCore_core`
    (L fuel `n + 2`, `F ≥ n + 1`), all under `CoreS … 0`; tagged `@[refines]` of `whnf`,
    `inferTypeCore`, `isDefEqCore`, `ensureSortCore` (verified mode only: deliberate D15).
    `KnotTopProg.knotOK : ∀ n, KnotOK p n`.
  - `L.Ind.KnotStageProg p` = `KnotTopProg p` + `CoreStageClosed p`. `KnotStageProg.whnfTop_sim`,
    `.inferTypeCore_sim`, `.isDefEqCore_sim`, `.ensureSortCore_sim`: `Sim (callW p n f args m)
    (twin at checkFuel) a (StageT after ∧ IWGrow m m' ∧ dec)` for every `n ≤ 2^62`, from
    `StageT` (lane `indproofs3`'s `IndTwin` `*_simT` with `hK := knot_all`).
* **What they cover of the `IndStubs` contracts.** Same shape as `RelAM f args pre op (KeepPost …)`
  with `stubM f m args` replaced by `callW p n f args m`: pre `StageT` instead of `StageR` (needs
  `TwinOK` and the pin flag: lane `indproofs3`'s `StageT` plan), post `StageT` (implies
  `StageR`) ∧ `IWGrow` ∧ the same decoder (`decW0E`, `decW0L`), except `is_def_eq_core`: `decBool r
  = b` (no `r[0] ≤ 1`, which `decW0B` adds; `CoreSpec`'s `ResH` gives only `< 2^32`).
  The L side: `callW_spec p n f` in `vcgen` in place of `stubM_spec p f n`.
* Census before (master `e5b38274`): phase 5 109 proven / 17 sorry / 6 written / 10 todo;
  phase 6 22/0/6/3; phase 7 21/0/5/1; total 816 proven / 165 sorry.
* Census after (master `d5532d09`, `--no-build`): phase 5 **133 proven / 0 sorry / 0 written / 9 todo**
  (+24 proven: the 17 sorry and 6 written targets, plus one covered); phase 6 **31/0/0/0** (+9: the
  `*Set` setters, `enter/leaveEager` and `coreKnot`, covered through `knot_all`); phase 7
  **26/0/0/1** (+5: `whnf`, `inferTypeCore`, `isDefEqCore`, `ensureSortCore`, `pureFnsA`). Phases
  5–7: +38 proven, −17 sorry. Total 865 proven / 148 sorry (other lanes' landings included).
  The phase-2 and phase-8 `sorry`s go through `IndStubs` (`stubM_spec`, `inferTypeCore_spec`, …);
  they go when the callers switch to `KnotStageProg.*_sim` (with `StageT`).
* **Memory note** (coordinator's question): this lane's first full build ran `Checker.CoreErec` and
  `Checker.IndCore` at ~22 GB each because the branch had merged master before lane `erecfix`
  landed; the files were untouched here. Merging master again brought `WriteSetSplit` in (3 GB).
