import ConAgua.Checker.PipeRest

/-!
# The seven stages before the declaration loop, at the checker's program (lane `pipeline`)

The relations between the stages entry 1 (`check_a`) runs before phase A, at the checker's
program (`checkerRels`: `R1`‥`R7`, `PipeStages.lean`, `PipeRest.lean`), and the seven stage specs,
proved at `checkerProg`. Entry 1's run (`Checker/CheckARun.lean`) composes them
(`stageSpecs_of_rels`) with phase A's fold from `R7`.
-/

namespace L.Checker

open L L.Arena L.Front L.Rom ConAgua.Final
open ConRon.Arena ConRon.Arena.Frontend

/-- **The relations the checker keeps between its stages.** -/
def checkerRels (b pb : ByteArray) (sz : TieredArray → Nat) : PipeRels b pb sz where
  R1 := R1 (loadMem b pb sz)
  R2 m := R2 (loadMem b pb sz) m pb
  R3 m a := R3 (loadMem b pb sz) m pb a
  R4 m pre a := R4 (loadMem b pb sz) m pb pre a
  R5 m pre rc a := R5 (loadMem b pb sz) m pb pre rc a
  R6 m ds a := R6 (loadMem b pb sz) m pb ds a
  R7 m ds ipins a := R7 (loadMem b pb sz) m pb ds ipins a

theorem checker_capStage : CapStage checkerProg checkerRels :=
  fun b pb sz h => capStage_checker b pb sz h.2.2.2

theorem checker_pbStage : PbStage checkerProg checkerRels :=
  fun b pb sz h => pbStage_checker b pb sz h.2.2.1

theorem checker_irpStage : IrpStage checkerProg checkerRels :=
  fun b pb sz h => irpStage_checker b pb sz h.2.2.1

theorem checker_preludeStage : PreludeStage checkerProg checkerRels :=
  fun b pb sz a h => preludeStage_checker h.1 b pb sz a

theorem checker_frontStage : FrontStage checkerProg checkerRels :=
  fun b pb sz pre a h => frontStage_checker h.1 b pb h.2.1 sz pre a

theorem checker_prepareStage : PrepareStage checkerProg checkerRels :=
  fun b pb sz pre rc a _ => prepareStage_checker b pb sz pre rc a

theorem checker_pinsStage : PinsStage checkerProg checkerRels :=
  fun b pb sz sA pre sB rc sC ds a h hpx =>
    pinsStage_checker b pb sz h.2.2.1 sA pre sB rc sC ds a hpx

end L.Checker
