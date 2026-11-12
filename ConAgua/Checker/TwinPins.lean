module

import ConRon.Bridge.Checker.Names
import ConRon.Bridge.Checker.DeclVal
public import ConRon.Bridge.Checker.Basis
import ConRon.Bridge.Checker.Pins
import ConRon.Bridge.Checker.NatOpNames
public import ConRon.Arena.Checker

@[expose] public section

/-!
# `internAllPins` leaves the pin table (lane `pipeline`)

con-ron's `internAllPins_run` walks the stage's steps (`IStepS`, which keep the pin table) but
does not export `s'.pins = s.pins`; `internAllPins_pins` is that walk for that conjunct.
-/

namespace L.Checker.TwinCaches

open ConRon.Arena ConRon.Arena.Frontend

section pins
open ConLeche ConRon.Bridge

/-- con-ron: ConRon/Bridge/Checker/Pins.lean:614-724 ConRon.Bridge.internAllPins_run — **the same walk**,
-- con-ron: CHANGED since 01ecb31c — `ConRon.Bridge.internAllPins_run` is gone upstream; re-check the L code and its proofs, then delete this line
split after its first block (`Eq`'s): the first block one scratch-agnostic step, the rest of the
basis and the pinned names one more, ending in the pin sets, which extend the store and leave the
pin table. -/
theorem internAllPins_steps {ps : List NatOpPinSet} {r : List INatOpPinSet}
    {s s' : AState} (hok : StateOK s) (hpins : PinsOK s) (hoff : s.store.scratchOn = false)
    (hrun : internAllPins ps s = .ok (r, s')) :
    ∃ u0 u : AState, (∃ r0, ConRon.Arena.BasisKind.decls .eqK s = .ok (r0, u0)) ∧
      Frontend.IStepS s u0 ∧ Frontend.IStepS u0 u ∧ Ext u.store s'.store ∧ s'.pins = u.pins := by
  simp only [ConRon.Arena.internAllPins] at hrun
  obtain ⟨_, u0, q0, w0⟩ := AM.bind_ok hrun
  have b1 := BasisKind.decls_sstep hok q0
  have a1 : Frontend.IStepS u0 u0 := Frontend.IStepS.refl b1.ok
  have hp0 : PinsOK u0 := hpins.mono b1.ext b1.pins
  obtain ⟨_, u1, q1, w1⟩ := AM.bind_ok w0
  have a2 := a1.trans (BasisKind.decls_sstep a1.ok q1)
  obtain ⟨_, u2, q2, w2⟩ := AM.bind_ok w1
  have a3 := a2.trans (BasisKind.decls_sstep a2.ok q2)
  obtain ⟨_, u3, q3, w3⟩ := AM.bind_ok w2
  have a4 := a3.trans (BasisKind.decls_sstep a3.ok q3)
  obtain ⟨_, u4, q4, w4⟩ := AM.bind_ok w3
  have a10 := a4.trans (BasisKind.decls_sstep a4.ok q4)
  obtain ⟨_, u10, q10, w10⟩ := AM.bind_ok w4
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
  obtain ⟨_, u28, q28, w28⟩ := AM.bind_ok w27
  have a29 := a28.trans (reservedBasisNames_sstep a28.ok (hp0.mono a28.ext a28.pins) q28)
  obtain ⟨_, u29, q29, w29⟩ := AM.bind_ok w28
  obtain ⟨rfl, -⟩ := natOpNames_run (hp0.mono a29.ext a29.pins) q29
  obtain ⟨_, u30, q30, w30⟩ := AM.bind_ok w29
  obtain ⟨rfl, -⟩ := natDivModNames_run (hp0.mono a29.ext a29.pins) q30
  obtain ⟨_, u31, q31, w31⟩ := AM.bind_ok w30
  obtain rfl := reduceOpNames_state (hp0.mono a29.ext a29.pins) q31
  obtain ⟨_, u32, q32, w32⟩ := AM.bind_ok w31
  obtain ⟨p32, -⟩ := pinAt_run (x := ConLeche.sorryAxName) (hp0.mono a29.ext a29.pins) rfl q32
  rw [p32] at w32
  obtain ⟨_, u33, q33, w33⟩ := AM.bind_ok w32
  obtain ⟨p33, -⟩ := pinAt_run (x := ConLeche.quotSoundName) (hp0.mono a29.ext a29.pins) rfl q33
  rw [p33] at w33
  obtain ⟨-, hx', -, -, -, hpe, -, -⟩ :=
    internPinSets_run a29.ok (by rw [a29.scratch, b1.scratch]; exact hoff) w33
  exact ⟨u0, _, ⟨_, q0⟩, b1, a29, hx', hpe⟩

/-- con-ron: ConRon/Bridge/Checker/Pins.lean:614-724 ConRon.Bridge.internAllPins_run — the conjunct
-- con-ron: CHANGED since 01ecb31c — `ConRon.Bridge.internAllPins_run` is gone upstream; re-check the L code and its proofs, then delete this line
that lemma does not export: `internAllPins` leaves the pin table (it builds the pin SETS, its
result). -/
theorem internAllPins_pins {ps : List NatOpPinSet} {r : List INatOpPinSet}
    {s s' : AState} (hok : StateOK s) (hpins : PinsOK s) (hoff : s.store.scratchOn = false)
    (hrun : internAllPins ps s = .ok (r, s')) : s'.pins = s.pins := by
  obtain ⟨u0, u, -, h0, h1, -, hp⟩ := internAllPins_steps hok hpins hoff hrun
  rw [hp, h1.pins, h0.pins]

end pins

end L.Checker.TwinCaches
