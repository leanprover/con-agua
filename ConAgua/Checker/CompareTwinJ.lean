module

public import ConAgua.Checker.CompareTwinC
public import ConAgua.Arena.PoolJobsJ
public import ConAgua.Arena.Jobs
import ConRon.Bridge.Compare.Stages
import ConRon.Bridge.Compare.Side
import ConRon.Bridge.Checker.Index
import ConRon.Bridge.Checker.Pool
import ConRon.Bridge.Inductives.Decl
import ConRon.Bridge.Specs

@[expose] public section

/-!
# The twin's side of the challenge's jobs (lane compare)

`poolHypsJ_of`: after the challenge's side records (`PhaseC`), with the solution's jobs accepted
(the twin's `checkJobList` without a solution over every solution record, the sequential
driver's) and the challenge's index built, the facts `pool_twinJ` takes (`PoolHypsJ`) at the
solution `solutionOf IS recsC`, and what the jobs' step takes of it (`JobSpec`): con-ron's
`stagesC_model`, the part before `Arena.pooledAcceptsJ_bridge`.
-/

namespace L.Checker

open L L.Arena ConAgua.Final
open ConLeche ConRon.Arena ConRon.Arena.Frontend
open ConRon.Bridge ConRon.Bridge.Frontend

local notation "VM" => ConLeche.CheckMode.verified

/-- **The challenge's pool facts** (`stagesC_model`'s part before `pooledAcceptsJ_bridge`). -/
theorem poolHypsJ_of {bC bS : ByteArray} (PC : PhaseC bC bS)
    (hS : ∃ s'', checkJobList VM PC.ipins none PC.IS PC.dsS (List.range PC.dsS.size) PC.sF.worker =
      .ok (.ok (), s''))
    {IC : IStreamIndex} {sI : AState} (hidx : buildIndex PC.recsC.toArray PC.sG = .ok (.ok IC, sI))
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
  obtain ⟨F, hpure⟩ := Arena.pooledAccepts_bridge CoreSpec.of_core
    ConRon.Bridge.Inductives.indSpec_of_bridge ho.drv ho.off ho.pp ho.pps ho.pinsDn ho.pd hdenS
    ⟨[List.range PC.dsS.size], PC.idx,
      fun t ht => ⟨_, List.mem_singleton_self _, List.mem_range.mpr ht⟩,
      fun w hw t ht => by rw [List.mem_singleton] at hw; subst hw; exact List.mem_range.mp ht,
      fun w hw => by rw [List.mem_singleton] at hw; subst hw; exact List.pairwise_lt_range,
      fun w hw => by rw [List.mem_singleton] at hw; subst hw; exact hS⟩
  have hndS := pure_nodup hpure
  obtain ⟨-, hxF, -, -, hIS, hpIS⟩ :=
    buildIndex_run constsSpec tablesSpec ho.drv ho.pp ho.off ho.pd hdenS PC.idx
  -- the challenge
  obtain ⟨-, hxFG, -, -, hoC⟩ := PC.out
  obtain ⟨dsP, hdenC⟩ := hoC.den
  obtain ⟨hstI, hxGI, hpI', -, hI, hpI⟩ :=
    buildIndex_run constsSpec tablesSpec hoC.drv hoC.pp hoC.off hoC.pd hdenC hidx
  have hxFI : PExt PC.sF.store sI.store := PExt.of_ext (hxFG.trans hxGI)
  have hIS' := hIS.pmono hpIS hxFI
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
