import ConAgua.Checker.Pipeline
import ConRon.Bridge.Checker.Pins
import ConRon.Bridge.Frontend.Prepare

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
  simp only [ConRon.Arena.internAllPins] at hrun
  obtain ⟨r0, u0, q0, w0⟩ := AM.bind_ok hrun
  have a1 : IStepS s u0 := BasisKind.decls_sstep hok q0
  refine ⟨u0, ⟨r0, q0⟩, a1, ?_⟩
  have a0 : IStepS u0 u0 := IStepS.refl a1.ok
  obtain ⟨_, u1, q1, w1⟩ := AM.bind_ok w0
  have a2 := a0.trans (BasisKind.declsA_sstep a0.ok q1)
  obtain ⟨_, u2, q2, w2⟩ := AM.bind_ok w1
  have a3 := a2.trans (BasisKind.decls_sstep a2.ok q2)
  obtain ⟨_, u3, q3, w3⟩ := AM.bind_ok w2
  have a4 := a3.trans (BasisKind.declsA_sstep a3.ok q3)
  obtain ⟨_, u4, q4, w4⟩ := AM.bind_ok w3
  have a5 := a4.trans (BasisKind.decls_sstep a4.ok q4)
  obtain ⟨_, u5, q5, w5⟩ := AM.bind_ok w4
  have a6 := a5.trans (BasisKind.declsA_sstep a5.ok q5)
  obtain ⟨_, u6, q6, w6⟩ := AM.bind_ok w5
  have a7 := a6.trans (BasisKind.decls_sstep a6.ok q6)
  obtain ⟨_, u7, q7, w7⟩ := AM.bind_ok w6
  have a8 := a7.trans (BasisKind.declsA_sstep a7.ok q7)
  obtain ⟨_, u8, q8, w8⟩ := AM.bind_ok w7
  have a9 := a8.trans (BasisKind.decls_sstep a8.ok q8)
  obtain ⟨_, u9, q9, w9⟩ := AM.bind_ok w8
  have a10 := a9.trans (BasisKind.declsA_sstep a9.ok q9)
  obtain ⟨_, u10, q10, w10⟩ := AM.bind_ok w9
  have a11 := a10.trans (internCI_fresh a10.ok q10).1
  obtain ⟨_, u11, q11, w11⟩ := AM.bind_ok w10
  have a12 := a11.trans (internCI_fresh a11.ok q11).1
  obtain ⟨_, u12, q12, w12⟩ := AM.bind_ok w11
  have a13 := a12.trans (internCI_fresh a12.ok q12).1
  obtain ⟨_, u13, q13, w13⟩ := AM.bind_ok w12
  have a14 := a13.trans (internCI_fresh a13.ok q13).1
  obtain ⟨_, u14, q14, w14⟩ := AM.bind_ok w13
  have a15 := a14.trans (internCI_fresh a14.ok q14).1
  obtain ⟨_, u15, q15, w15⟩ := AM.bind_ok w14
  have a16 := a15.trans (internCI_fresh a15.ok q15).1
  obtain ⟨_, u16, q16, w16⟩ := AM.bind_ok w15
  have a17 := a16.trans (internCV_fresh a16.ok q16).1
  obtain ⟨_, u17, q17, w17⟩ := AM.bind_ok w16
  have a18 := a17.trans (internCV_fresh a17.ok q17).1
  obtain ⟨_, u18, q18, w18⟩ := AM.bind_ok w17
  have a19 := a18.trans (internCV_fresh a18.ok q18).1
  obtain ⟨_, u19, q19, w19⟩ := AM.bind_ok w18
  have a20 := a19.trans (internCV_fresh a19.ok q19).1
  obtain ⟨_, u20, q20, w20⟩ := AM.bind_ok w19
  have a21 := a20.trans (internCV_fresh a20.ok q20).1
  obtain ⟨_, u21, q21, w21⟩ := AM.bind_ok w20
  have a22 := a21.trans (internCV_fresh a21.ok q21).1
  obtain ⟨_, u22, q22, w22⟩ := AM.bind_ok w21
  have a23 := a22.trans (internCV_fresh a22.ok q22).1
  obtain ⟨_, u23, q23, w23⟩ := AM.bind_ok w22
  have a24 := a23.trans (internCV_fresh a23.ok q23).1
  obtain ⟨_, u24, q24, w24⟩ := AM.bind_ok w23
  have a25 := a24.trans (internCV_fresh a24.ok q24).1
  obtain ⟨_, u25, q25, w25⟩ := AM.bind_ok w24
  have a26 := a25.trans (internCV_fresh a25.ok q25).1
  obtain ⟨_, u26, q26, w26⟩ := AM.bind_ok w25
  have a27 := a26.trans (Frontend.internExpr_sstep a26.ok q26).1
  obtain ⟨_, u27, q27, w27⟩ := AM.bind_ok w26
  have a28 := a27.trans (Frontend.internExpr_sstep a27.ok q27).1
  have b28 := a1.trans a28
  obtain ⟨_, u28, q28, w28⟩ := AM.bind_ok w27
  have a29 := a28.trans (reservedBasisNames_sstep a28.ok (hpins.mono b28.ext b28.pins) q28)
  have b29 := a1.trans a29
  obtain ⟨_, u29, q29, w29⟩ := AM.bind_ok w28
  obtain ⟨rfl, -⟩ := natOpNames_run (hpins.mono b29.ext b29.pins) q29
  obtain ⟨_, u30, q30, w30⟩ := AM.bind_ok w29
  obtain ⟨rfl, -⟩ := natDivModNames_run (hpins.mono b29.ext b29.pins) q30
  obtain ⟨_, u31, q31, w31⟩ := AM.bind_ok w30
  obtain rfl := reduceOpNames_state (hpins.mono b29.ext b29.pins) q31
  obtain ⟨_, u32, q32, w32⟩ := AM.bind_ok w31
  obtain ⟨p32, -⟩ := pinAt_run (x := ConLeche.sorryAxName) (hpins.mono b29.ext b29.pins) rfl q32
  rw [p32] at w32
  obtain ⟨_, u33, q33, w33⟩ := AM.bind_ok w32
  obtain ⟨p33, -⟩ := pinAt_run (x := ConLeche.quotSoundName) (hpins.mono b29.ext b29.pins) rfl q33
  rw [p33] at w33
  obtain ⟨-, hx', -⟩ :=
    internPinSets_run a29.ok (by rw [b29.scratch]; exact hoff) w33
  exact a29.ext.trans hx'

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
