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
def checkerRels (b pb : ByteArray) (s8 s64 : List Nat) : PipeRels b pb s8 s64 where
  R1 := R1 (loadMem b pb s8 s64)
  R2 m := R2 (loadMem b pb s8 s64) m pb
  R3 m a := R3 (loadMem b pb s8 s64) m pb a
  R4 m pre a := R4 (loadMem b pb s8 s64) m pb pre a
  R5 m pre rc a := R5 (loadMem b pb s8 s64) m pb pre rc a
  R6 m ds a := R6 (loadMem b pb s8 s64) m pb ds a
  R7 m ds ipins a := R7 (loadMem b pb s8 s64) m pb ds ipins a

theorem checker_capStage : CapStage checkerProg checkerRels :=
  fun b pb s8 s64 h => capStage_checker b pb s8 s64 h.2.2.2

theorem checker_pbStage : PbStage checkerProg checkerRels :=
  fun b pb s8 s64 h => pbStage_checker b pb s8 s64 h.2.2.1

theorem checker_irpStage : IrpStage checkerProg checkerRels :=
  fun b pb s8 s64 h => irpStage_checker b pb s8 s64 h.2.2.1

theorem checker_preludeStage : PreludeStage checkerProg checkerRels :=
  fun b pb s8 s64 a h => preludeStage_checker h.1 b pb s8 s64 a

theorem checker_frontStage : FrontStage checkerProg checkerRels :=
  fun b pb s8 s64 pre a h => frontStage_checker h.1 b pb h.2.1 s8 s64 pre a

theorem checker_prepareStage : PrepareStage checkerProg checkerRels :=
  fun b pb s8 s64 pre rc a _ => prepareStage_checker b pb s8 s64 pre rc a

theorem checker_pinsStage : PinsStage checkerProg checkerRels :=
  fun b pb s8 s64 sA pre sB rc sC ds a h hpx =>
    pinsStage_checker b pb s8 s64 h.2.2.1 sA pre sB rc sC ds a hpx

end L.Checker
