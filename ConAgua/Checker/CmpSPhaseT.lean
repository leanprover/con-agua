module

public import ConAgua.Checker.CompareTwinC
public import ConAgua.Arena.PoolJobsJ
public import ConAgua.Arena.PoolJobs
import ConRon.Bridge.Compare.Stages
import ConRon.Bridge.Compare.Side
import ConRon.Bridge.Checker.Index
import ConRon.Bridge.Checker.Pool
import ConRon.Bridge.Checker.Pooled
import ConRon.Bridge.Inductives.Decl
import ConRon.Bridge.Specs
public import ConAgua.Final.CompareTwin
import ConRon.Bridge.Checker.Install

@[expose] public section

/-!
# The twin's side of both phases' jobs at the challenge's index state (lane compare2, design (i))

Both check phases start from `sI`, the state after the challenge's index build.

* `poolHypsS_I`: the facts `pool_twin` takes (`PoolHyps`) for the solution's records `dsS`, its
  index `IS`, at `sI`: the solution's index build's facts carried to `sI` by `Ext`/`PExt`
  monotonicity (as `stagesCPooled_model`).
* `poolHypsJ_ofPI`: `poolHypsJ_ofP` from the solution's pool at `sI` (`PoolJobs`): the solution's
  records' distinct names by `pooled_fold_records` from `sI` (as `stagesCPooled_model`).
-/

namespace L.Checker

open L L.Arena ConAgua.Final
open ConLeche ConRon.Arena ConRon.Arena.Frontend
open ConRon.Bridge ConRon.Bridge.Frontend

local notation "VM" => ConLeche.CheckMode.verified

/-- **The solution's pool facts at the challenge's index state**: after the challenge's index
build (`sI`), the solution's records and pins denote, its index denotes, for any worker step. -/
theorem poolHypsS_I {bC bS : ByteArray} (PC : PhaseC bC bS)
    {IC : IStreamIndex} {sI : AState} (hidx : buildIndex PC.recsC.toArray PC.sG = .ok (.ok IC, sI))
    {σ : Type} (Rel : σ → AState → Prop) (Call : Nat → σ → σ → Prop) :
    ∃ (pinsP : List ConLeche.NatOpPinSet) (dsP : List ConLeche.Declaration),
      StateOK sI ∧ RecordSpec PC.ipins pinsP ∧ PersPinSets PC.ipins ∧
      (∀ x ∈ PC.dsS.toList, PersDecl x ∧ ∃ d, Frontend.denoteDecl sI.store x = some d) ∧
      PinsDenote sI.store PC.ipins pinsP ∧
      IndexDenotes sI.store PC.IS (ConLeche.Cached.buildIndex dsP.toArray) ∧ PersIFBase PC.IS.base ∧
      sI.store.scratchOn = false ∧
      ((∀ (k : Nat) (r r' : σ) (a : AState) (hk : k < PC.dsS.size), Rel r a → Call k r r' →
        (∃ env, FoldOK env (PC.IS.view k) (AM.st enterScratch a)) →
        ∃ a', recordJob VM PC.ipins none PC.IS k PC.dsS[k] a = .ok ((), a') ∧ Rel r' a') →
      PoolHyps (pins := PC.ipins) (pinsP := pinsP) (ds := PC.dsS) (dsP := dsP) (I := PC.IS)
        (s₁ := sI) Rel Call) := by
  -- the solution
  have ho := StagesOut.cmp PC.pfx PC.pinsR
  obtain ⟨dsSP, hdenS⟩ := ho.den
  obtain ⟨-, hxF, -, -, hIS, hpIS⟩ :=
    buildIndex_run constsSpec tablesSpec ho.drv ho.pp ho.off ho.pd hdenS PC.idx
  -- the challenge
  obtain ⟨-, hxFG, -, -, hoC⟩ := PC.out
  obtain ⟨_, hdenC⟩ := hoC.den
  obtain ⟨hstI, hxGI, hpI', hoffI, -, -⟩ :=
    buildIndex_run constsSpec tablesSpec hoC.drv hoC.pp hoC.off hoC.pd hdenC hidx
  have hxEI : Ext PC.sE.store sI.store := hxF.trans (hxFG.trans hxGI)
  have hIS' := hIS.pmono hpIS (PExt.of_ext (hxFG.trans hxGI))
  obtain ⟨hlen, hget⟩ := denoteDecls_getElem hdenS
  have hden' : ∀ (i : Nat) (hi : i < PC.dsS.size), ∃ hi' : i < dsSP.length,
      Frontend.denoteDecl sI.store PC.dsS[i] = some dsSP[i] := fun i hi => by
    obtain ⟨hi', h⟩ := hget i (by simpa using hi)
    exact ⟨hi', Frontend.denoteDecl_ext hxEI (by simpa using h)⟩
  have hrec : RecordSpec PC.ipins PC.pins :=
    recordSpec CoreSpec.of_core ConRon.Bridge.Inductives.indSpec_of_bridge
  have hPD := PinsDenote.mono hxGI PC.ipins PC.pins hoC.pinsDn
  refine ⟨PC.pins, dsSP, hstI.state, hrec, ho.pps, fun x hx => ⟨ho.pd x hx, ?_⟩, hPD, hIS', hpIS,
    hoffI, fun hstep =>
    { hrec := hrec, hpush := kernelPushes _, hpp := ho.pps,
      hpinsOK := hoC.drv.pins.pmono hoC.pp (PExt.of_ext hxGI) hpI',
      hpersPins := hoC.pp.mono hpI', hpins := hPD, hpd := ho.pd, hlen := by simpa using hlen,
      hden := hden', hI := hIS', hpI := hpIS, hstep := hstep }⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  obtain ⟨_, hd⟩ := hden' i (by simpa using hi)
  exact ⟨_, by simpa using hd⟩

/-- **The challenge's pool facts, from the solution's pool at the challenge's index state**
(`poolHypsJ_ofP` with the solution's jobs from `sI`). -/
theorem poolHypsJ_ofPI {bC bS : ByteArray} (PC : PhaseC bC bS)
    {IC : IStreamIndex} {sI : AState} (hidx : buildIndex PC.recsC.toArray PC.sG = .ok (.ok IC, sI))
    (hPS : PoolJobs VM PC.ipins none PC.IS PC.dsS sI)
    {σ : Type} (Rel : σ → AState → Prop) (Call : Nat → σ → σ → Prop) :
    ∃ (pinsP : List ConLeche.NatOpPinSet) (dsP dsSP : List ConLeche.Declaration)
      (matesU : Std.HashMap ConLeche.Name (Array ConLeche.Name)),
      StateOK sI ∧ JobSpec PC.ipins pinsP (some (solutionOf PC.IS PC.recsC)) sI ∧
      PersPinSets PC.ipins ∧
      (∀ x ∈ PC.recsC.toArray.toList, PersDecl x ∧ ∃ d, Frontend.denoteDecl sI.store x = some d) ∧
      PinsDenote sI.store PC.ipins pinsP ∧
      ((∀ (k : Nat) (r r' : σ) (a : AState) (hk : k < PC.recsC.toArray.size), Rel r a → Call k r r' →
        (∃ env, FoldOK env (IC.view k) (AM.st enterScratch a)) →
        ∃ a', recordJob VM PC.ipins (some (solutionOf PC.IS PC.recsC)) IC k PC.recsC.toArray[k] a =
          .ok ((), a') ∧ Rel r' a') →
      PoolHypsJ (pins := PC.ipins) (pinsP := pinsP) (ds := PC.recsC.toArray) (dsP := dsP) (I := IC)
        (s₁ := sI) (J := solutionOf PC.IS PC.recsC) (dsS := dsSP) (matesU := matesU) Rel Call) := by
  -- the solution
  have ho := StagesOut.cmp PC.pfx PC.pinsR
  obtain ⟨dsSP, hdenS⟩ := ho.den
  obtain ⟨-, hxF, -, -, hIS, hpIS⟩ :=
    buildIndex_run constsSpec tablesSpec ho.drv ho.pp ho.off ho.pd hdenS PC.idx
  -- the challenge
  obtain ⟨-, hxFG, -, -, hoC⟩ := PC.out
  obtain ⟨dsP, hdenC⟩ := hoC.den
  obtain ⟨hstI, hxGI, hpI', -, hI, hpI⟩ :=
    buildIndex_run constsSpec tablesSpec hoC.drv hoC.pp hoC.off hoC.pd hdenC hidx
  have hxEI : Ext PC.sE.store sI.store := hxF.trans (hxFG.trans hxGI)
  have hxFI : PExt PC.sF.store sI.store := PExt.of_ext (hxFG.trans hxGI)
  have hIS' := hIS.pmono hpIS hxFI
  -- the solution's pure fold, from its pool at `sI`
  obtain ⟨partsS, hcovS, -, hincS, haccS⟩ := hPS
  obtain ⟨hlenS, hgetS⟩ := denoteDecls_getElem hdenS
  obtain ⟨F, hpure⟩ := pooled_fold_records
    (recordSpec CoreSpec.of_core ConRon.Bridge.Inductives.indSpec_of_bridge) (kernelPushes PC.pins)
    ho.pps hstI.state (hoC.drv.pins.pmono hoC.pp (PExt.of_ext hxGI) hpI') (hoC.pp.mono hpI')
    (PinsDenote.mono hxGI PC.ipins PC.pins hoC.pinsDn) ho.pd (by simpa using hlenS)
    (fun i hi => by
      obtain ⟨hi', h⟩ := hgetS i (by simpa using hi)
      exact ⟨hi', Frontend.denoteDecl_ext hxEI (by simpa using h)⟩)
    hIS' hpIS partsS hcovS hincS haccS
  have hndS := pure_nodup hpure
  have hmates := (solutionOf_mates (I := PC.IS) hoC.drv.state.wf hdenC
    (fun x hx => hoC.pd x hx)).mono hxGI
  have hcvm : CvMatesDen sI.store (solutionOf PC.IS PC.recsC).mates :=
    (cvMatesDen_solutionOf hdenC (fun x hx => hoC.pd x hx)).ext hxGI
  obtain ⟨hlen, hget⟩ := denoteDecls_getElem hdenC
  have hden' : ∀ (i : Nat) (hi : i < PC.recsC.toArray.size), ∃ hi' : i < dsP.length,
      Frontend.denoteDecl sI.store PC.recsC.toArray[i] = some dsP[i] := fun i hi => by
    obtain ⟨hi', h⟩ := hget i (by simpa using hi)
    exact ⟨hi', Frontend.denoteDecl_ext hxGI (by simpa using h)⟩
  have hrec : RecordSpecC PC.ipins PC.pins (solutionOf PC.IS PC.recsC) (ConLeche.streamEnv dsSP)
      (ConLeche.Cached.recordMates dsP.toArray) :=
    recordSpecC CoreSpec.of_core ConRon.Bridge.Inductives.indSpec_of_bridge
  have hPD := PinsDenote.mono hxGI PC.ipins PC.pins hoC.pinsDn
  refine ⟨PC.pins, dsP, dsSP, _, hstI.state,
    ⟨_, _, hrec, fun s hs hx => ⟨solView_ok hIS' hpIS hndS hs hx, (hmates.pmono hx).toDen hs.wf,
      (hcvm.pmono hx)⟩⟩,
    hoC.pps, fun x hx => ⟨hoC.pd x hx, ?_⟩, hPD, fun hstep =>
    { hrec := hrec, hpp := hoC.pps, hpinsOK := hoC.drv.pins.pmono hoC.pp (PExt.of_ext hxGI) hpI',
      hpersPins := hoC.pp.mono hpI', hpins := hPD, hpd := hoC.pd, hden := hden', hI := hI,
      hpI := hpI, hIS := hIS', hpIS := hpIS, hndS := hndS, hmates := hmates, hstep := hstep }⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  obtain ⟨_, hd⟩ := hden' i (by simpa using hi)
  exact ⟨_, by simpa using hd⟩

end L.Checker
