module

public import ConRon.Bridge.Checker.Names
public import ConRon.Bridge.Checker.DeclVal
public import ConRon.Bridge.Frontend.Chunks
public import ConRon.Bridge.Checker.Basis
public import ConAgua.Checker.Pipeline
import ConRon.Bridge.Checker.Pins
public import ConRon.Bridge.Frontend.Prepare
import all ConRon.Bridge.Frontend.Prepare
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-!
# The twin's prefix interns the universe name `u` (lane `pipeline`)

`prefix_quotU`: after the twin's five stages before the fold (`TwinPrefix`), some persistent name
handle denotes `u` (`.str .anonymous "u"`, con-leche's `uN`). Neither pin table holds it
(`pinNames`, `reservedBasisNameValues`); the first basis block `internAllPins` interns, the raw
`Eq` block (`BasisKind.decls .eqK`), does: `Eq.{u}`'s level parameter. The handle is persistent
because the scratch tier is closed at that point, and it keeps its denotation to the end of the
walk because the rest of the walk only extends the store (`internAllPins_tail`, the second half of
con-ron's `internAllPins_run`, from the state after the first block).
-/

open ConLeche ConRon.Arena ConRon.Arena.Frontend
open ConRon.Bridge ConRon.Bridge.Frontend

namespace L.Checker

/-! ## A denoted `indInfo` names its level parameters -/

theorem denoteNList_single {st : NStore} {hs : List NIdx} {n : ConLeche.Name}
    (h : ConRon.Arena.Frontend.denoteNList st hs = some [n]) :
    ∃ k, hs = [k] ∧ denoteN st k = some n := by
  match hs, h with
  | [], h => simp [ConRon.Arena.Frontend.denoteNList] at h
  | [k], h =>
    refine ⟨k, rfl, ?_⟩
    simp only [ConRon.Arena.Frontend.denoteNList] at h
    split at h <;> simp_all
  | k :: k' :: ks, h =>
    simp only [ConRon.Arena.Frontend.denoteNList] at h
    split at h
    · rename_i x xs _ hxs
      simp only [Option.some.injEq, List.cons.injEq] at h
      obtain ⟨-, rfl⟩ := h
      split at hxs <;> simp_all
    · simp at h

theorem denoteCV_lps {st : EStore} {cv : IConstantVal} {x : ConstantVal}
    (h : denoteCV st cv = some x) :
    ConRon.Arena.Frontend.denoteNList st.ns cv.levelParams = some x.levelParams := by
  simp only [denoteCV] at h
  split at h
  · rename_i n lps ty _ hl _
    cases h; exact hl
  · simp at h

theorem denoteCI_ind {st : EStore} {ci : IConstantInfo} {cv : ConstantVal} {caps : IndCaps}
    (h : denoteCI st ci = some (.indInfo cv caps)) :
    ∃ v c, ci = .indInfo v c ∧
      ConRon.Arena.Frontend.denoteNList st.ns v.levelParams = some cv.levelParams := by
  cases ci with
  | indInfo v c =>
    simp only [denoteCI] at h
    split at h
    · rename_i x y hx _
      cases h; exact ⟨v, c, rfl, denoteCV_lps hx⟩
    · simp at h
  | axiomInfo v => simp [denoteCI] at h
  | defnInfo v e hh => simp only [denoteCI] at h; split at h <;> simp at h
  | thmInfo v => simp [denoteCI] at h
  | ctorInfo v a b => simp [denoteCI] at h
  | recInfo v a b rs => simp only [denoteCI] at h; split at h <;> simp at h

/-- The raw `Eq` block, interned, holds a handle denoting `u`. -/
theorem eqBlock_u {s s' : AState} {r : List IConstantInfo} (hok : StateOK s)
    (hrun : ConRon.Arena.BasisKind.decls .eqK s = .ok (r, s')) :
    IStepS s s' ∧ ∃ k, denoteN s'.store.ns k = some (.str .anonymous "u") := by
  simp only [ConRon.Arena.BasisKind.decls, ConRon.Arena.internCIList] at hrun
  obtain ⟨p, s₁, hgo, hrest⟩ := AM.bind_ok hrun
  obtain ⟨hv, hst⟩ := AM.pure_ok hrest
  subst hst
  obtain ⟨hstep, hden, -⟩ := Frontend.internCIList_sstep (ConLeche.BasisKind.decls .eqK) hok
    (Frontend.EMemoOK.empty s.store) hgo
  refine ⟨hstep, ?_⟩
  match hp : p.2, hden with
  | [], hden => simp [denoteCIList, ConLeche.BasisKind.decls, eqBasis] at hden
  | ci :: cis, hden =>
    simp only [denoteCIList, ConLeche.BasisKind.decls, eqBasis] at hden
    split at hden
    · rename_i x xs hx _
      simp only [Option.some.injEq, List.cons.injEq] at hden
      obtain ⟨rfl, -⟩ := hden
      obtain ⟨v, c, -, hv⟩ := denoteCI_ind hx
      obtain ⟨k, -, hk⟩ := denoteNList_single hv
      exact ⟨k, hk⟩
    · simp at hden

/-- The walk after its first block: one scratch-agnostic step (con-ron's `internAllPins_run`,
links two to thirty-four, from the state after the first block), then the pin variants. -/
theorem internAllPins_tail {ps : List NatOpPinSet} {r : List INatOpPinSet}
    {s s' : AState} (hok : StateOK s) (hpins : PinsOK s) (hoff : s.store.scratchOn = false)
    (hrun : internAllPins ps s = .ok (r, s')) :
    ∃ u0 : AState, (∃ r0, ConRon.Arena.BasisKind.decls .eqK s = .ok (r0, u0)) ∧
      IStepS s u0 ∧ Ext u0.store s'.store := by
  sorry

/-- **The walk interns `u`**: a persistent handle denoting `u` at the end of `internAllPins`. -/
theorem internAllPins_u {ps : List NatOpPinSet} {r : List INatOpPinSet}
    {s s' : AState} (hok : StateOK s) (hpins : PinsOK s) (hoff : s.store.scratchOn = false)
    (hrun : internAllPins ps s = .ok (r, s')) :
    ∃ k, k.isPersistent = true ∧ denoteN s'.store.ns k = some (.str .anonymous "u") := by
  obtain ⟨u0, ⟨r0, q0⟩, a1, hx⟩ := internAllPins_tail hok hpins hoff hrun
  obtain ⟨-, k, hk⟩ := eqBlock_u hok q0
  exact ⟨k, PersN_of_denote a1.ok.wf (by rw [a1.scratch]; exact hoff) hk, denoteN_ext hk hx⟩

/-- **The twin's prefix interns `u`**, in the persistent tier. -/
theorem prefix_quotU {b : ByteArray} {sA : AState} {pre : PreludeIx} {sB : AState}
    {rc : ParseResultD} {sC : AState} {ds : Array IDeclaration} {sD : AState}
    {pins : List NatOpPinSet} {ipins : List INatOpPinSet} {sE : AState}
    (h : TwinPrefix b sA pre sB rc sC ds sD pins ipins sE) :
    ∃ k, k.isPersistent = true ∧ denoteN sE.store.ns k = some (.str .anonymous "u") := by
  obtain ⟨hA, hB, hC, hD, hE⟩ := h
  have hok0 : StateOK (AState.init EStore.empty) := ⟨EStore.empty_wf⟩
  have hoff0 : (AState.init EStore.empty).store.scratchOn = false := rfl
  obtain ⟨hokA, -, hpinsA, -, hoffA, -, -⟩ := internReservedPins_run hok0 hoff0 hA
  obtain ⟨hstep1, hpersPre, preC, hrelPre⟩ :=
    builtinPreludeE_run hokA hoffA hpinsA hB
  obtain ⟨hstep2, hpersR, rc', hclR, hrelR⟩ :=
    parseChunks_run hstep1.ok
      (by rw [hstep1.scratch, hoffA]) (hpinsA.mono hstep1.ext hstep1.pins) hC
  obtain ⟨hstep3, -, -⟩ :=
    preparePrelude_run (preC := preC) hstep2.ok
      (by rw [hstep2.scratch, hstep1.scratch, hoffA])
      (hpinsA.mono (hstep1.trans hstep2).ext (hstep1.trans hstep2).pins)
      (denoteDeclArray_ext hstep2.ext hrelPre) hpersPre
      hrelR.decls hpersR hD
  have hoff3 : sD.store.scratchOn = false := by
    rw [hstep3.scratch, hstep2.scratch, hstep1.scratch]; exact hoffA
  exact internAllPins_u hstep3.ok
    (hpinsA.mono ((hstep1.ext.trans hstep2.ext).trans hstep3.ext)
      (by rw [hstep3.pins, hstep2.pins, hstep1.pins])) hoff3 hE

end L.Checker
