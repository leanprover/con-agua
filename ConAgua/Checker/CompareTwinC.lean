module

public import ConAgua.Checker.CompareChain5
import ConAgua.Checker.TwinCaches
import ConAgua.Checker.TwinShapeFront
import ConAgua.Checker.TwinShapeQuot
import ConRon.Bridge.Compare.Stages
import ConRon.Bridge.Compare.Side
import ConRon.Bridge.Frontend.Prepare
import ConRon.Bridge.Checker.Index
import ConRon.Bridge.Specs

@[expose] public section

/-!
# The twin's facts of the challenge's stages in the compared run (lane compare)

After the solution's index build (`PhaseS`), the compared run's twin prepares the challenge's
records (`preparePrelude pre rC.decls sF`) and turns them into the records a fold with a solution
checks (`sideRecordsGo`, `PhaseC`). Its state then satisfies what the flat run's does before the
index build (`OutC`, `StagesOut` without the caches' value): con-ron's `stagesC_model`, middle part.
-/

namespace L.Checker

open L L.Arena L.Front ConAgua.Final
open ConLeche ConRon.Arena ConRon.Arena.Frontend
open ConRon.Bridge ConRon.Bridge.Frontend
open L.Checker.TwinCaches

/-- **The compared run's twin through the challenge's side records**: the solution's phase,
then the challenge's preparation from the solution's index state and its side records. -/
structure PhaseC (bC bS : ByteArray) extends PhaseS bC bS where
  dsC : Array IDeclaration
  sG : AState
  recsC : List IDeclaration
  sH : AState
  prep : preparePrelude pre rC.decls sF = .ok (dsC, sG)
  side : sideRecordsGo [] dsC.toList sG = .ok (recsC, sH)

/-- **The twin's facts before an index build** (`StagesOut` without the caches' value). -/
structure OutC (s : AState) (ds : Array IDeclaration) (ipins : List INatOpPinSet)
    (pins : List ConLeche.NatOpPinSet) : Prop where
  off : s.store.scratchOn = false
  drv : DriverOK s
  pp : PersPins s
  pinsDn : PinsDenote s.store ipins pins
  pps : PersPinSets ipins
  pd : ∀ x ∈ ds.toList, PersDecl x
  den : ∃ dsP, denoteDecls s.store ds.toList = some dsP
  front : L.Arena.FrontDecls ds
  quot : ∃ k : NIdx, k.isPersistent = true ∧ ConRon.Arena.denoteN s.store.ns k = some (ConLeche.Name.str .anonymous "u")

theorem StagesOut.outC {s : AState} {ds : Array IDeclaration} {ipins : List INatOpPinSet}
    {pins : List ConLeche.NatOpPinSet} (h : StagesOut s ds ipins pins) : OutC s ds ipins pins :=
  ⟨h.off, h.drv, h.pp, h.pinsDn, h.pps, h.pd, h.den, h.front, h.quot⟩

/-- The side records are the records, or axioms. -/
theorem sideRecordsGo_mem : ∀ (ds out r : List IDeclaration) (s s' : AState),
    sideRecordsGo out ds s = .ok (r, s') → ∀ x ∈ r, x ∈ out ∨ x ∈ ds ∨ ∃ cv, x = .axiomDecl cv
  | [], out, r, s, s', h, x, hx => by
    simp only [sideRecordsGo] at h
    obtain ⟨rfl, -⟩ := AM.pure_ok h
    exact .inl hx
  | d :: ds, out, r, s, s', h, x, hx => by
    simp only [sideRecordsGo] at h
    obtain ⟨d', s₁, h1, h2⟩ := AM.bind_ok h
    rcases sideRecordsGo_mem ds _ r s₁ s' h2 x hx with h | h | h
    · rcases List.mem_append.mp h with h | h
      · exact .inl h
      · simp only [List.mem_singleton] at h
        subst h
        unfold sideRecord at h1
        split at h1
        all_goals first
          | (obtain ⟨rfl, -⟩ := AM.pure_ok h1; exact .inr (.inl List.mem_cons_self))
          | (unfold sideRecordVal at h1
             obtain ⟨b, s₂, -, h3⟩ := AM.bind_ok h1
             split at h3
             · obtain ⟨rfl, -⟩ := AM.pure_ok h3; exact .inr (.inl List.mem_cons_self)
             · obtain ⟨_, s₃, -, h4⟩ := AM.bind_ok h3
               obtain ⟨b', s₄, -, h5⟩ := AM.bind_ok h4
               split at h5
               · obtain ⟨rfl, -⟩ := AM.pure_ok h5; exact .inr (.inr ⟨_, rfl⟩)
               · obtain ⟨rfl, -⟩ := AM.pure_ok h5; exact .inr (.inl List.mem_cons_self))
    · exact .inr (.inl (List.mem_cons_of_mem _ h))
    · exact .inr (.inr h)

/-- **The challenge's twin facts before its index build** (con-ron's `stagesC_model`, middle):
the side records' state is the preparation's, it extends the solution's index state with the same
pins and caches, and satisfies `OutC` at the side records. -/
theorem PhaseC.out {bC bS : ByteArray} (PC : PhaseC bC bS) :
    PC.sH = PC.sG ∧ Ext PC.sF.store PC.sG.store ∧ PC.sG.pins = PC.sF.pins ∧
      PC.sG.caches = PC.sF.caches ∧ OutC PC.sG PC.recsC.toArray PC.ipins PC.pins := by
  obtain ⟨⟨hA, hB, hC⟩, hCS, hDS⟩ := PC.pfx
  obtain ⟨hoff, hst, hpp, hipins, hpps, -, hpersPre, hpersRC, rcC, rcS, preC, hclC, -,
    hrelPre, hrelC, -⟩ := stagesC_frame (chunksC := [bC]) (chunksS := [bS]) hA hB hC hCS hDS PC.pinsR
  have ho := StagesOut.cmp PC.pfx PC.pinsR
  obtain ⟨_, hdenS⟩ := ho.den
  obtain ⟨hstF, hxF, hpF, hoffF, -, -⟩ :=
    buildIndex_run constsSpec tablesSpec hst hpp hoff ho.pd hdenS PC.idx
  obtain ⟨hstepG, hpersC, hclPrepC⟩ :=
    preparePrelude_run (preC := preC) hstF.state hoffF (hstF.pins)
      (denoteDeclArray_ext hxF hrelPre) hpersPre (denoteDeclArray_ext hxF hrelC) hpersRC PC.prep
  have hdenC : denoteDecls PC.sG.store PC.dsC.toList =
      some (ConLeche.Frontend.preparePrelude preC rcC.decls).toList :=
    denoteDeclArray_iff.mp hclPrepC
  have hside := PC.side
  obtain ⟨hHG, hdenR, hpersR⟩ := sideRecordsGo_run hstepG.ok (hstF.pins.mono hstepG.ext hstepG.pins)
    PC.dsC.toList [] PC.recsC _ [] rfl hdenC hside
  have hHG' : PC.sH = PC.sG := hHG.symm
  simp only [List.nil_append] at hdenR
  have hpR : ∀ x ∈ PC.recsC, PersDecl x :=
    hpersR (fun _ h => nomatch h) (fun x hx => hpersC x (by simpa using hx))
  have hstG : DriverOK PC.sG := DriverOK.of_check
    (hstF.monoF hstepG.ok hstepG.ext hstepG.cframe hstepG.pins) hstepG.pins
  have hxEG : Ext PC.sE.store PC.sG.store := hxF.trans hstepG.ext
  obtain ⟨hcG, hpG⟩ := (keeps_preparePrelude PC.pre PC.rC.decls).run PC.prep
  refine ⟨hHG', hstepG.ext, hpG, hcG, by rw [hstepG.scratch]; exact hoffF, hstG,
    hpp.mono (by rw [hstepG.pins, hpF]), PinsDenote.mono hxEG _ _ hipins, hpps,
    fun x hx => hpR x (by simpa using hx), ⟨_, by simpa using hdenR⟩, ?_, ?_⟩
  · have hpre := builtinPreludeE_front hB
    have hrc := parseChunks_front hC
    intro i hi blk nP e
    have hmem : IDeclaration.indDecl blk nP ∈ PC.recsC := by
      rw [← e]; simp
    rcases sideRecordsGo_mem _ _ _ _ _ hside _ hmem with h | h | ⟨_, h⟩
    · simp at h
    · rcases post_preparePrelude PC.pre PC.rC.decls PC.sF PC.dsC PC.sG PC.prep _ (by simpa using h)
        with hm | hm
      · exact hpre _ hm
      · exact hrc _ hm
    · cases h
  · obtain ⟨k, hk, hd⟩ := ho.quot
    exact ⟨k, hk, denoteN_ext hd hxEG⟩

end L.Checker
