import ConAgua.Front.IndInstallRefine5
import ConAgua.Front.IndApplySpec3
import ConAgua.Front.IndFieldsLink3
import ConAgua.Front.IndApplyRefine9
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# `apply_ind` refines `processLineCoreD`'s `.ind` arm

`applyIndW_twin`: on con-leche's `ok` path of the block's scan (`scanIndDecl`), a successful
`apply_ind(v)` is the twin's `.ind` arm: `ind_fields` gives the three lists (`indFields_link`),
`validate_ind_d` the twin's `validateIndD` verdict `.inr (ordered, nPd)` (`validate_ref`),
`install_ind_d` its `installIndD` (`installW_twin`).
-/

open L.Arena
open ConRon.Arena
open ConRon.Arena.Frontend
open ConLeche.Frontend (IndCtorRec IndTypeRec IndRecRec CVRec RuleRec DeclRec scanIndDecl)


namespace L.Front.Ind

/-- **`apply_ind` refines the `.ind` arm of `processLineCoreD`.** -/
@[refines_part ConRon.Arena.Frontend.processLineCoreD "inductive"]
theorem applyIndW_twin {p : Prog} (hAL : IndApplyLookups p) {b : ByteArray} (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63)
    {n : Nat} {m m' : Mem} {a : AState} {st : StateD}
    (hA : ArenaD m a) (hD : StateDR m st) (hok : ConRon.Bridge.StateOK a) {v : USize}
    {tys : List IndTypeRec} {cts : List IndCtorRec} {rcs : List IndRecRec} {e : USize}
    (hscan : scanIndDecl b v = .ok (.ind tys cts rcs) e)
    (h : applyIndW p n b.data m v.toUInt64 = some m') :
    ∃ st', (processLineCoreD st (.ind tys cts rcs)).run a = .ok (.inl st', a) ∧
      ArenaD m' a ∧ StateDR m' st' ∧ (ModeOK m → ModeOK m') := by
  cases n with
  | zero => simp [applyIndW] at h
  | succ n =>
  simp only [applyIndW] at h
  cases h1 : indFieldsW b.data m v.toUInt64 with
  | none => rw [h1, lK_none] at h; cases h
  | some x =>
  obtain ⟨r, m₁⟩ := x
  rw [h1, lK_some] at h
  have hifs := hD.ifs
  obtain ⟨to, tn, co, cn, ro, rn, rfl, hF, hfR⟩ :=
    indFields_link b h64 hsize m m₁ ⟨by omega, by omega⟩ v tys cts rcs e hscan _ h1
  have hfr1 : MemFrame [IFR, IFL] [] m m₁ := hfR.1
  have hRoom : Room m₁ := hfR.2
  simp only [List.headD_cons, List.tail_cons] at h
  cases h2 : callW p n "validate_ind_d" [to, tn, co, cn, ro, rn] m₁ with
  | none => rw [h2, lK_none] at h; cases h
  | some x =>
  obtain ⟨q, m₂⟩ := x
  rw [h2, lK_some] at h
  have hA1 : ArenaD m₁ a :=
    ⟨ArenaR.frame_ext _ _ (by simp [IFR, IFL]) (by simp) _ _ hfr1 _ hA.1,
      DerR.frameT hfr1 (by simp [IFR, IFL]) hA.2⟩
  have hD1 : StateDR m₁ st := hD.frame hfr1 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hs1 : (m₁.arr64 IFR).size = (m.arr64 IFR).size := hfr1.size IFR
  have hs1' : (m₁.arr64 IFL).size = (m.arr64 IFL).size := hfr1.size IFL
  have hT1 : TopOK m₁ := ⟨by have := hRoom.2.1; exact this, Nat.le_of_lt hRoom.2.2.2⟩
  have hIFR1 : topN m₁ IFR < 2 ^ 62 := by have := hRoom.2.2.1; omega
  obtain ⟨s2, hs2, -, hV⟩ := RefC.run_okW (validate_specE p hAL n ⟨m₁, Locals.init []⟩ to tn co cn ro rn)
    (validate_ref hA1.1 hD1 hok hT1 hF hIFR1 p n (st := st)) h2
  rw [hs2] at hV
  obtain ⟨⟨ordered, V1, V4, V7⟩, V2, V3, V5, V6, V8⟩ := hV
  dsimp only at V1 V2 V3 V4 V5 V6 V7 V8
  generalize q.headD 0 = oo at h V1 V5 V6 V7
  generalize q.tail.headD 0 = np at h V1 V8
  have hfr2 := V2.frame
  have hA2 : ArenaD m₂ a :=
    ⟨ArenaR.frame_ext _ _ (by simp [IFL, LH]) (by simp) _ _ hfr2 _ hA1.1,
      DerR.frameT hfr2 (by simp [IFL, LH]) hA1.2⟩
  have hD2 : StateDR m₂ st := hD1.frame hfr2 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hifr2 : m₂.arr64 IFR = m₁.arr64 IFR := V2.ifr
  have hs2' : (m₂.arr64 IFL).size = (m.arr64 IFL).size := by rw [hfr2.size IFL, hs1']
  have hIFR2 : topN m₂ IFR < 2 ^ 62 := by unfold topN wd; rw [hifr2]; exact hIFR1
  have hIFL2 : topN m₂ IFL < 2 ^ 62 := by have := V3.2; omega
  obtain ⟨st', I1, I2, I3, I4⟩ := installW_twin hA2 hD2 (hF.ext V2) hIFR2 hIFL2 V4 (by omega) V7 h
  refine ⟨st', ?_, I2, I3, fun hmo => MemFrame.modeOK I4 (by simp) (by simp)
    (MemFrame.modeOK hfr2 (by decide) (by decide) (MemFrame.modeOK hfr1 (by simp) (by simp) hmo))⟩
  unfold processLineCoreD
  simp only []
  rw [run_bind _ _ a _ V1]
  simp only []
  rw [run_bind _ _ a _ I1]
  rfl

end L.Front.Ind
