module

public import ConAgua.Arena.IndPosSpec.CrLook
import ConAgua.Arena.IndPosSpec.RpGoStep
public import ConAgua.Arena.IndPosSpec.Rx

@[expose] public section

/-!
# PosmemoRxMfr

`rpMkW_mfr`, `posmemo_rx_mfr`, `rxW_mfr`.
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
      simp_all [rxMapW.eq_1, rxImgW.eq_1, rxFrameW.eq_1, rxDsW.eq_1, rxDsGoW.eq_1, rxW.eq_1, rxGoW.eq_1,
        rxNodeW.eq_1]
  | succ n ih =>
  obtain ⟨iMap, iImg, iFr, iDs, iDsGo, iRx, iGo, iNode⟩ := ih
  have pfr : ∀ (m m' : Mem) (ctx po pl n1 h a b : Word),
      rxFrameW.j1 n ctx po pl n1 h m = some (a, b, m') → RxFr m m' := by
    intro m m' ctx po pl n1 h a b hh
    simp only [rxFrameW.j1.arm1, rxFrameW.k_rec5.eq_def, rxFrameW.k_nest_hole_img_ds.eq_def,
      rxFrameW.k_intern_const.eq_def, rxFrameW.k_mk_app_n_f.eq_def] at hh
    mfr_auto hh [posRecW_mfr, iDs _ _ _ _ _ _ _, fun h => MFr.of_low (ceinternW_low h), MFr.ofMknF]
    simp only [Option.some.injEq, Prod.mk.injEq] at hh; obtain ⟨-, -, rfl⟩ := hh; exact MFr.refl _ _ _
  refine ⟨fun m m' f i a b hh => ?_, fun m m' ctx po pl nn i a b hh => ?_,
    fun m m' ctx po pl n1 i a b hh => ?_, fun m m' f o l a b hh => ?_, fun m m' f o l q j hh => ?_,
    fun m m' f e r hh => ?_, fun m m' f fu h r hh => ?_, fun m m' f f1 g x y z r hh => ?_⟩
  · simp only [rxMapW.eq_2, rxMapW_kImg, rxMapW.k_pin_word.eq_def, rxMapW.k_intern_sort.eq_def,
      rxMapW.k_intern_fvar.eq_def] at hh
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
  · simp only [rxImgW.eq_2, rxMapW_kImg, rxRootW, rxRootW.k_intern_const.eq_def,
      rxRootW.k_mk_app_n_f.eq_def] at hh
    mfr_auto hh [iImg _ _ _ _ _ _ _ _ _, iFr _ _ _ _ _ _ _ _ _, fun h => MFr.of_low (ceinternW_low h), MFr.ofMknF]
    all_goals simp only [Option.some.injEq, Prod.mk.injEq] at hh; obtain ⟨-, -, rfl⟩ := hh; exact MFr.refl _ _ _
  · simp only [rxFrameW.eq_2, rxFrameW.k_rec4.eq_def] at hh
    split at hh; · exact pfr _ _ _ _ _ _ _ _ _ hh
    split at hh; · cases hh
    rename_i h1; rcases h2 : posRecW _ [_, 0] with _ | ⟨k, m2⟩ <;> rw [h2] at hh
    · simp [rxFrameW.k_rec2.none] at hh
    rw [rxFrameW.k_rec2.arm1] at hh
    exact ((posRecW_mfr h1).trans (posRecW_mfr h2)).up.trans (pfr _ _ _ _ _ _ _ _ _ hh)
  · simp only [rxDsW.eq_2, rxDsW.k_iw_alloc.eq_def, rxDsW.k_nest_hole_img_ds_go.eq_def] at hh
    mfr_auto hh [allocW_mfr, iDsGo _ _ _ _ _ _ _]
    simp only [Option.some.injEq, Prod.mk.injEq] at hh; obtain ⟨-, -, rfl⟩ := hh; exact MFr.refl _ _ _
  · simp only [rxDsGoW.eq_2, rxDsGoW.k_replace_fvars.eq_def, rxDsGoW_kGo] at hh
    mfr_auto hh [iRx _ _ _ _ _, fun h => (MFr.set_iw _ _ _).up.trans (iDsGo _ _ _ _ _ _ _ h)]
  · simp only [rxW.eq_2, rxW.k_replace_fvars_go.eq_def, rxW.j1, show (218 : Word) + 1 = 219 from rfl] at hh
    refine (MFr.trans ⟨_, _, benterG_frame 218 m, by simp, by simp⟩ ?_ : RxFr _ _)
    split at hh; · cases hh
    split at hh; · cases hh
    rename_i hg; refine MFr.trans (iGo _ _ _ _ _ _ hg) ?_
    split at hh; · cases hh
    split at hh
    · split at hh; · cases hh
      simp only [Option.some.injEq, Prod.mk.injEq] at hh; rw [← hh.2]
      exact MFr.trans (⟨_, _, MemFrame.setCtl _ 219 _, by simp, by simp⟩ : RxFr _ _)
        ⟨_, _, mclearG_frame rfSch _, by simp, by simp [rfSch]⟩
    · simp only [Option.some.injEq, Prod.mk.injEq] at hh; rw [← hh.2]
      exact ⟨_, _, MemFrame.setCtl _ 219 _, by simp, by simp⟩
  · by_cases hf : fu = 0; · rw [rxGoW.abort1 (hc1 := hf)] at hh; cases hh
    by_cases hv : eViewW m h = []; · rw [rxGoW.abort2 (hc1 := hf) (hc2 := hv)] at hh; cases hh
    by_cases hl : (eViewW m h).headD 0 = 0 ∨ (eViewW m h).headD 0 = 2 ∨ (eViewW m h).headD 0 = 8 ∨
        (eViewW m h).headD 0 = 3
    · rw [rxGoW_leaf hf hv hl] at hh; rw [← (Prod.mk.inj (Option.some.inj hh)).2]; exact MFr.refl _ _ _
    simp only [not_or] at hl; obtain ⟨h0, h2, h8, h3⟩ := hl
    by_cases h1 : (eViewW m h).headD 0 = 1
    · rw [rxGoW_fvar hf hv h1] at hh
      rcases hm : rxMapW n m f _ with _ | ⟨ok, r1, m1⟩ <;> rw [hm] at hh; · cases hh
      rw [rxGoW_kMap] at hh; rw [← (Prod.mk.inj (Option.some.inj hh)).2]; exact iMap _ _ _ _ _ _ hm
    by_cases hfd : mfindG rfSch m h (rdW (m.arr64 CTL) 219 <<< 32) = []
    · rw [rxGoW.abort3 _ _ _ _ _ hf hv h0 h2 h8 h3 h1 hfd] at hh; cases hh
    by_cases hk : (mfindG rfSch m h (rdW (m.arr64 CTL) 219 <<< 32)).headD 0 ≠ 0
    · rw [rxGoW.arm6 _ _ _ _ _ hf hv h0 h2 h8 h3 h1 hfd hk] at hh
      rw [← (Prod.mk.inj (Option.some.inj hh)).2]; exact MFr.refl _ _ _
    rw [rxGoW.arm7 _ _ _ _ _ hf hv h0 h2 h8 h3 h1 hfd (Classical.not_not.mp hk)] at hh
    rcases hn : rxNodeW n m f _ _ _ _ _ with _ | ⟨r1, m1⟩ <;> rw [hn] at hh; · cases hh
    rw [rxGoW_kNode] at hh
    rcases hs : msetG rfSch m1 h _ r1 with _ | m2 <;> rw [hs] at hh; · cases hh
    rw [← (Prod.mk.inj (Option.some.inj hh)).2]
    exact (iNode _ _ _ _ _ _ _ _ _ hn).trans ⟨_, _, msetG_frame rfSch rfSch_wf _ _ _ _ _ hs, by simp [rfSch, RFM], by simp [rfSch]⟩
  · simp only [rxNodeW.eq_2, rxNodeW.k_replace_fvars_go.eq_def, rxNodeW.k_replace_fvars_go_2.eq_def,
      rxNodeW.k_replace_fvars_go_3.eq_def, rxNodeW.k_replace_fvars_go_4.eq_def,
      rxNodeW.k_replace_fvars_go_5.eq_def, rxNodeW.k_replace_fvars_go_6.eq_def,
      rxNodeW.k_replace_fvars_go_7.eq_def, rxNodeW.k_replace_fvars_go_8.eq_def,
      rxNodeW.k_replace_fvars_go_9.eq_def, rxNodeW.k_replace_fvars_go_10.eq_def] at hh
    mfr_auto hh [iGo _ _ _ _ _ _, fun h => MFr.of_low (mkAppW_low h), fun h => MFr.of_low (mkLamW_low h),
      fun h => MFr.of_low (mkForallW_low h), fun h => MFr.of_low (mkLetW_low h), fun h => MFr.of_low (mkProjW_low h)]

theorem rxW_mfr {n : Nat} {m m' : Mem} {f e r : Word} (h : rxW n m f e = some (r, m')) : RxFr m m' :=
  (posmemo_rx_mfr n).2.2.2.2.2.1 _ _ _ _ _ h

end L.Ind

end
