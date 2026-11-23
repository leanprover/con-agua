module

public import ConAgua.Checker.BuildStage
public import ConAgua.Checker.CompareChain
import ConAgua.Checker.TwinCaches
import ConAgua.Checker.TwinShapeFront
import ConAgua.Checker.TwinShapeQuot
import ConAgua.Checker.TwinPins
import ConRon.Bridge.Compare.Stages
import ConRon.Bridge.Checker.Pins
import ConRon.Bridge.Frontend.Prepare
import ConRon.Bridge.Frontend.Chunks
import ConRon.Bridge.Specs

@[expose] public section

/-!
# The twin's facts of the compared run's stages (lane compare)

The compared run's twin runs, from the driver's start, the pins, the prelude, the challenge's
parse, the solution's parse, the solution's preparation and the pin variants (`CmpPfx2`, then
`internAllPins`). Its states satisfy what the flat run's do: `PinsPre` before the pins
(`PinsPre.cmp`), `StagesOut` after them (`StagesOut.cmp`, from con-ron's `stagesC_frame`).
-/

namespace L.Checker

open L L.Arena L.Front ConAgua.Final
open ConLeche ConRon.Arena ConRon.Arena.Frontend
open ConRon.Bridge ConRon.Bridge.Frontend
open L.Checker.TwinCaches

/-- **The twin's compared run up to the solution's preparation**, from the driver's start. -/
def CmpPfx2 (bC bS : ByteArray) (sA : AState) (pre : PreludeIx) (sB : AState) (rC : ParseResultD)
    (sC : AState) (rS : ParseResultD) (sC' : AState) (dsS : Array IDeclaration) (sD : AState) : Prop :=
  CmpPfx1 bC sA pre sB rC sC ∧ parseChunks [bS] sC = .ok (.ok rS, sC') ∧
    preparePrelude pre rS.decls sC' = .ok (dsS, sD)

theorem PinsPre.cmp {bC bS : ByteArray} {sA : AState} {pre : PreludeIx} {sB : AState}
    {rC : ParseResultD} {sC : AState} {rS : ParseResultD} {sC' : AState} {dsS : Array IDeclaration}
    {sD : AState} (h : CmpPfx2 bC bS sA pre sB rC sC rS sC' dsS sD) : PinsPre sD := by
  obtain ⟨⟨hA, hB, hC⟩, hCS, hD⟩ := h
  have hok0 : StateOK (AState.init EStore.empty) := ⟨EStore.empty_wf⟩
  obtain ⟨hokA, -, hpinsA, hppA, hoffA, -, -⟩ := internReservedPins_run hok0 rfl hA
  obtain ⟨hstep1, hpersPre, preC, hrelPre⟩ := builtinPreludeE_run hokA hoffA hpinsA hB
  obtain ⟨hstep2, -, -, -, -⟩ :=
    parseChunks_run hstep1.ok (by rw [hstep1.scratch, hoffA]) (hpinsA.mono hstep1.ext hstep1.pins) hC
  obtain ⟨hstep2', hpersRS, _rcS, _hclS, hrelS⟩ :=
    parseChunks_run hstep2.ok (by rw [hstep2.scratch, hstep1.scratch, hoffA])
      (hpinsA.mono (hstep1.trans hstep2).ext (hstep1.trans hstep2).pins) hCS
  have h12 := (hstep1.trans hstep2).trans hstep2'
  obtain ⟨hstep3, -, -⟩ :=
    preparePrelude_run (preC := preC) hstep2'.ok (by rw [h12.scratch, hoffA])
      (hpinsA.mono h12.ext h12.pins)
      (denoteDeclArray_ext (hstep2.ext.trans hstep2'.ext) hrelPre) hpersPre hrelS.decls hpersRS hD
  have h13 := h12.trans hstep3
  exact ⟨hstep3.ok, by rw [h13.scratch]; exact hoffA, hpinsA.mono h13.ext h13.pins,
    hppA.mono h13.pins, by rw [h13.pins]; exact L.Rom.internReservedPins_maxNatSize hA⟩

theorem StagesOut.cmp {bC bS : ByteArray} {sA : AState} {pre : PreludeIx} {sB : AState}
    {rC : ParseResultD} {sC : AState} {rS : ParseResultD} {sC' : AState} {dsS : Array IDeclaration}
    {sD : AState} {pins : List NatOpPinSet} {ipins : List INatOpPinSet} {sE : AState}
    (h : CmpPfx2 bC bS sA pre sB rC sC rS sC' dsS sD)
    (hE : internAllPins pins maxNatSizeDefault sD = .ok (ipins, sE)) : StagesOut sE dsS ipins pins := by
  have hP := PinsPre.cmp h
  obtain ⟨⟨hA, hB, hC⟩, hCS, hD⟩ := h
  obtain ⟨hoff, hdrv, hpp, hpdn, hpps, hpd, -, -, _rcC, _rcS, _preC, -, -, -, -, hden⟩ :=
    stagesC_frame (chunksC := [bC]) (chunksS := [bS]) hA hB hC hCS hD hE
  have hok0 : StateOK (AState.init EStore.empty) := ⟨EStore.empty_wf⟩
  obtain ⟨-, -, -, -, -, -, hcA⟩ := internReservedPins_run hok0 rfl hA
  obtain ⟨hcB, -⟩ := keeps_builtinPreludeE.run hB
  obtain ⟨hcC, -⟩ := (keeps_parseChunks [bC]).run hC
  obtain ⟨hcCS, -⟩ := (keeps_parseChunks [bS]).run hCS
  obtain ⟨hcD, -⟩ := (keeps_preparePrelude pre rS.decls).run hD
  obtain ⟨-, -, -, -, -, -, -, hcE, -⟩ := internAllPins_run hP.ok hP.pins hP.pers hP.off hE
  refine ⟨hoff, hdrv, hpp, hpdn, hpps, hpd, ⟨_, hden⟩, by rw [hcE, hcD, hcCS, hcC, hcB, hcA], ?_,
    internAllPins_u hP.ok hP.pins hP.off hP.max hE⟩
  have hpre := builtinPreludeE_front hB
  have hrs := parseChunks_front hCS
  intro i hi blk nP e
  have hmem : IDeclaration.indDecl blk nP ∈ dsS.toList := by rw [← e]; simp
  rcases post_preparePrelude pre rS.decls sC' dsS sD hD _ hmem with hm | hm
  · exact hpre _ hm
  · exact hrs _ hm

end L.Checker
