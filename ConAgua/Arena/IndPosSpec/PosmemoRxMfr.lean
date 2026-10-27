import ConAgua.Arena.IndPosSpec.CrLook
import ConAgua.Arena.IndPosSpec.RpGoStep

/-!
# PosmemoRxMfr

`rpMkW_mfr`, `posmemo_rpMk_rx`, `posmemo_rx_mfr`, `rxW_mfr`.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem rpMkW_mfr {m m' : Mem} {g a2 x2 c2 y x r : Word} (h : rpMkW m g a2 x2 c2 y x = some (r, m')) : MFr [] [] m m' := by
  unfold rpMkW at h
  mfr_auto h [fun h => MFr.of_low (mkAppW_low h), fun h => MFr.of_low (mkLamW_low h),
    fun h => MFr.of_low (mkForallW_low h), fun h => MFr.of_low (mkLetW_low h), fun h => MFr.of_low (mkProjW_low h)]

theorem posmemo_rpMk_rx {m m' : Mem} {g a2 x2 c2 y x r : Word} (h : rpMkW m g a2 x2 c2 y x = some (r, m')) :
    RxFr m m' := (rpMkW_mfr h).up

theorem posmemo_rx_mfr (n : Nat) :
    (∀ (m m' : Mem) (f i a b : Word), rxMapW n m f i = some (a, b, m') → RxFr m m') ∧
    (∀ (m m' : Mem) (ctx po pl nn i a b : Word), rxImgW n m ctx po pl nn i = some (a, b, m') → RxFr m m') ∧
    (∀ (m m' : Mem) (ctx po pl n1 i a b : Word), rxFrameW n m ctx po pl n1 i = some (a, b, m') → RxFr m m') ∧
    (∀ (m m' : Mem) (f o l a b : Word), rxDsW n m f o l = some (a, b, m') → RxFr m m') ∧
    (∀ (m m' : Mem) (f o l q j : Word), rxDsGoW n m f o l q j = some m' → RxFr m m') ∧
    (∀ (m m' : Mem) (f e r : Word), rxW n m f e = some (r, m') → RxFr m m') ∧
    (∀ (m m' : Mem) (f fu h r : Word), rxGoW n m f fu h = some (r, m') → RxFr m m') ∧
    (∀ (m m' : Mem) (f f1 g x y z r : Word), rxNodeW n m f f1 g x y z = some (r, m') → RxFr m m') := by
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;>
      simp_all [rxMapW, rxImgW, rxFrameW, rxDsW, rxDsGoW, rxW, rxGoW, rxNodeW]
  | succ n ih =>
  obtain ⟨iMap, iImg, iFr, iDs, iDsGo, iRx, iGo, iNode⟩ := ih
  have pfr : ∀ (m m' : Mem) (ctx po pl n1 h a b : Word),
      pfrK1 n ctx po pl n1 (some (h, m)) = some (a, b, m') → RxFr m m' := by
    intro m m' ctx po pl n1 h a b hh
    simp only [pfrK1, pfrK2.eq_def, pfrK3.eq_def, frK4.eq_def, frK5.eq_def] at hh
    mfr_auto hh [posRecW_mfr, iDs _ _ _ _ _ _ _, fun h => MFr.of_low (ceinternW_low h), MFr.ofMknF]
    simp only [Option.some.injEq, Prod.mk.injEq] at hh; obtain ⟨-, -, rfl⟩ := hh; exact MFr.refl _ _ _
  refine ⟨fun m m' f i a b hh => ?_, fun m m' ctx po pl nn i a b hh => ?_,
    fun m m' ctx po pl n1 i a b hh => ?_, fun m m' f o l a b hh => ?_, fun m m' f o l q j hh => ?_,
    fun m m' f e r hh => ?_, fun m m' f fu h r hh => ?_, fun m m' f f1 g x y z r hh => ?_⟩
  · simp only [rxMapW, erK1.eq_def, erK2.eq_def, erK3.eq_def] at hh
    split at hh; · exact iImg _ _ _ _ _ _ _ _ _ hh
    split at hh; · obtain ⟨-, -, rfl⟩ := Prod.mk.inj (Option.some.inj hh); exact MFr.refl _ _ _
    split at hh
    · split at hh; · cases hh
      split at hh; · cases hh
      split at hh; · cases hh
      split at hh; · cases hh
      obtain ⟨-, -, rfl⟩ := Prod.mk.inj (Option.some.inj hh)
      exact (MFr.of_low ((sointernW_low ‹_›).trans (fvinternW_low ‹_›))).up
    split at hh <;> obtain ⟨-, -, rfl⟩ := Prod.mk.inj (Option.some.inj hh) <;> exact MFr.refl _ _ _
  · simp only [rxImgW, rxRootW, rtK1.eq_def, rtK2.eq_def] at hh
    mfr_auto hh [iImg _ _ _ _ _ _ _ _ _, iFr _ _ _ _ _ _ _ _ _, fun h => MFr.of_low (ceinternW_low h), MFr.ofMknF]
    all_goals simp only [Option.some.injEq, Prod.mk.injEq] at hh; obtain ⟨-, -, rfl⟩ := hh; exact MFr.refl _ _ _
  · simp only [rxFrameW, frK0.eq_def] at hh
    split at hh; · exact pfr _ _ _ _ _ _ _ _ _ hh
    split at hh; · cases hh
    rename_i h1; rcases h2 : posRecW _ [_, 0] with _ | ⟨k, m2⟩ <;> rw [h2] at hh; · simp [pfrK1] at hh
    exact ((posRecW_mfr h1).trans (posRecW_mfr h2)).up.trans (pfr _ _ _ _ _ _ _ _ _ hh)
  · simp only [rxDsW, dsA.eq_def, dsB.eq_def] at hh
    mfr_auto hh [allocW_mfr, iDsGo _ _ _ _ _ _ _]
    simp only [Option.some.injEq, Prod.mk.injEq] at hh; obtain ⟨-, -, rfl⟩ := hh; exact MFr.refl _ _ _
  · simp only [rxDsGoW, dgK.eq_def] at hh
    mfr_auto hh [iRx _ _ _ _ _, fun h => (MFr.set_iw _ _ _).up.trans (iDsGo _ _ _ _ _ _ _ h)]
  · simp only [rxW, rxK1.eq_def] at hh
    refine (MFr.trans ⟨_, _, benterG_frame 218 m, by simp, by simp⟩ ?_ : RxFr _ _)
    mfr_auto hh [iGo _ _ _ _ _ _]
    simp only [Option.some.injEq, Prod.mk.injEq] at hh; rw [← hh.2]
    exact ⟨_, _, MemFrame.setCtl _ 219 _, by simp, by simp⟩
  · simp only [rxGoW] at hh
    split at hh; · cases hh
    simp only [rxG1] at hh
    split at hh; · cases hh
    split at hh; · rw [← (Prod.mk.inj (Option.some.inj hh)).2]; exact MFr.refl _ _ _
    split at hh
    · rcases hm : rxMapW n m f _ with _ | ⟨ok, r1, m1⟩ <;> rw [hm] at hh; · cases hh
      rw [rxH_some] at hh; rw [← (Prod.mk.inj (Option.some.inj hh)).2]; exact iMap _ _ _ _ _ _ hm
    simp only [rxG3] at hh
    split at hh; · cases hh
    split at hh; · rw [← (Prod.mk.inj (Option.some.inj hh)).2]; exact MFr.refl _ _ _
    simp only [rxG4.eq_def, rxG5.eq_def] at hh
    split at hh; · cases hh
    rename_i hn; split at hh; · cases hh
    rename_i hs; rw [← (Prod.mk.inj (Option.some.inj hh)).2]
    exact (iNode _ _ _ _ _ _ _ _ _ hn).trans ⟨_, _, msetG_frame rfSch rfSch_wf _ _ _ _ _ hs, by simp [rfSch, RFM], by simp [rfSch]⟩
  · simp only [rxNodeW, rxB1.eq_def, rxB2.eq_def, rxL1.eq_def, rxL2.eq_def, rxL3.eq_def, rxP1.eq_def] at hh
    mfr_auto hh [iGo _ _ _ _ _ _, posmemo_rpMk_rx]

theorem rxW_mfr {n : Nat} {m m' : Mem} {f e r : Word} (h : rxW n m f e = some (r, m')) : RxFr m m' :=
  (posmemo_rx_mfr n).2.2.2.2.2.1 _ _ _ _ _ h

end L.Ind

end
