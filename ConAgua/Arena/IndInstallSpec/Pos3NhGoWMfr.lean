module

public import ConAgua.Arena.IndInstallSpec.PartsShapeFacts
import ConAgua.Arena.IndPosSpec.FgW
import ConAgua.Arena.IndPosSpec.SnocWMfr
public import ConAgua.Arena.IndPosSpec.NoGoStep
public import ConAgua.Arena.IndPosSpec.Pos2CvLpsWStage
import ConAgua.Arena.IndPosSpec.RpGoStep

@[expose] public section

/-!
# Pos3NhGoWMfr

`pos3_nameCopyW_mfr`, `pos3_nIdxsCopyW_mfr`, `pos3_memberNamesW_mfr`, `pos3_nIdxsW_mfr`, `pos3_lpsW_mfr`, `pos3_pinternW_mfr` and the lemmas only they use.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Pieces -/

theorem pos3_nameCopyW_mfr : ∀ (n : Nat) (m m' : Mem) (d s l : Word), nameCopyW n m d s l = some m' →
    MFr [] [] m m'
  | 0, _, _, _, _, _, h => by simp [nameCopyW] at h
  | n + 1, m, m', d, s, l, h => by
    by_cases hl : l = 0
    · rw [nameCopyW.arm1 n m d s l hl] at h; cases h; exact MFr.refl _ _ _
    · rw [nameCopyW_step n m d s l hl] at h
      exact (MFr.set_iw _ _ _).trans (pos3_nameCopyW_mfr n _ _ _ _ _ h)

theorem pos3_nIdxsCopyW_mfr : ∀ (n : Nat) (m m' : Mem) (d s l : Word), nIdxsCopyW n m d s l = some m' →
    MFr [] [] m m'
  | 0, _, _, _, _, _, h => by simp [nIdxsCopyW] at h
  | n + 1, m, m', d, s, l, h => by
    by_cases hl : l = 0
    · rw [nIdxsCopyW_nil n m d s l hl] at h; cases h; exact MFr.refl _ _ _
    · rw [nIdxsCopyW_step n m d s l hl] at h
      exact (MFr.set_iw _ _ _).trans (pos3_nIdxsCopyW_mfr n _ _ _ _ _ h)

theorem pos3_memberNamesW_mfr {n : Nat} {m m' : Mem} {p : Word} {r : List Word}
    (h : memberNamesW n m p = some (r, m')) : MFr [] [] m m' := by
  unfold memberNamesW at h
  split at h; · cases h
  rename_i q m1 hal
  split at h; · cases h
  rename_i m2 hc
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  exact (allocW_mfr hal).trans (pos3_nameCopyW_mfr _ _ _ _ _ _ hc)

theorem pos3_nIdxsW_mfr {n : Nat} {m m' : Mem} {p : Word} {r : List Word}
    (h : nIdxsW n m p = some (r, m')) : MFr [] [] m m' := by
  unfold nIdxsW at h
  split at h; · cases h
  rename_i q m1 hal
  split at h; · cases h
  rename_i m2 hc
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  exact (allocW_mfr hal).trans (pos3_nIdxsCopyW_mfr _ _ _ _ _ _ hc)

theorem pos3_lpsW_mfr {n : Nat} {m m' : Mem} {p : Word} {r : List Word}
    (h : lpsW n m p = some (r, m')) : MFr [] [] m m' := by
  cases n with
  | zero => simp [lpsW] at h
  | succ n =>
    by_cases h0 : rdW (m.arr64 IW) (p + 1) = 0
    · rw [lpsW_nil n m p h0] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]; exact MFr.refl _ _ _
    · rw [lpsW_cons n m p h0] at h
      exact erToIwW_mfr h

theorem pos3_pinternW_mfr {m m' : Mem} {u w : Word} (h : pinternW m u = some (w, m')) : MFr [] [] m m' := by
  exact MFr.of_low ⟨_, _, consInternM_frame paramCS_wf h,
    by simp [tier1, ConsSch.wset, paramCS, PREC, PSLOT], by simp [paramCS]⟩

theorem pos3_plgW_mfr : ∀ (k : Nat) (m m' : Mem) (o l : Word) (r : List Word), plgW k m o l = some (r, m') →
    MFr [] [] m m'
  | 0, _, _, _, _, _, h => by simp [plgW] at h
  | k + 1, m, m', o, l, r, h => by
    by_cases hl : l = 0
    · rw [plgW_nil k m o l hl] at h
      cases ha : allocW m 0 with
      | none => rw [ha] at h; simp [plK0] at h
      | some x =>
        obtain ⟨q, m1⟩ := x
        rw [ha, plK0_some] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.2]; exact allocW_mfr ha
    · rw [plgW_cons k m o l hl] at h
      cases hp : pinternW m (rdW (m.arr64 IW) o) with
      | none => rw [hp] at h; simp [plK1] at h
      | some x =>
        obtain ⟨u, m1⟩ := x
        rw [hp] at h
        by_cases hu : 4294967296 ≤ u
        · rw [plK1_big k m1 o l u hu] at h; cases h
        rw [plK1_ok k m1 o l u hu] at h
        cases hr : plgW k m1 (o + 1) (l - 1) with
        | none => rw [hr] at h; simp [plK2] at h
        | some y =>
          obtain ⟨r2, m2⟩ := y
          rw [hr] at h
          simp only [plK2] at h
          cases hc : consW k m2 u (r2.headD 0) (r2.tail.headD 0) with
          | none => rw [hc] at h; simp [plK3] at h
          | some z =>
            obtain ⟨r3, m3⟩ := z
            rw [hc] at h
            simp only [plK3, Option.some.injEq, Prod.mk.injEq] at h
            rw [← h.2]
            exact ((pos3_pinternW_mfr hp).trans (pos3_plgW_mfr k _ _ _ _ _ hr)).trans (consW_mfr hc)

theorem pos3_plW_mfr {k : Nat} {m m' : Mem} {o l : Word} {r : List Word} (h : plW k m o l = some (r, m')) :
    MFr [] [] m m' := by
  cases k with
  | zero => simp [plW] at h
  | succ k =>
    rw [plW_succ] at h
    cases hg : plgW k m o l with
    | none => rw [hg] at h; simp [plW.plK4] at h
    | some x =>
      obtain ⟨r1, m1⟩ := x
      rw [hg, plK4_some] at h
      cases hs : ilF m1 [r1.headD 0, r1.tail.headD 0] with
      | none => rw [hs] at h; simp [plW.plK5] at h
      | some y =>
        obtain ⟨r2, m2⟩ := y
        rw [hs, plK5_some] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.2]
        exact (pos3_plgW_mfr k _ _ _ _ _ hg).trans (MFr.of_frame (ilF_frame hs) (by simp [tier1, POOL, POOL1, LSREC, LSSLOT, LSHP]) (by simp))

theorem pos3_fieldCopyW_mfr : ∀ (n : Nat) (m m' : Mem) (d s l k : Word), fieldCopyW n m d s l k = some m' →
    MFr [] [] m m'
  | 0, _, _, _, _, _, _, h => by simp [fieldCopyW] at h
  | n + 1, m, m', d, s, l, k, h => by
    by_cases hl : l = 0
    · rw [fieldCopyW.arm1 n m d s l k hl] at h; cases h; exact MFr.refl _ _ _
    · rw [fieldCopyW_step n m d s l k hl] at h
      exact (MFr.set_iw _ _ _).trans (pos3_fieldCopyW_mfr n _ _ _ _ _ _ h)

theorem pos3_formersW_mfr {n : Nat} {m m' : Mem} {p : Word} {r : List Word}
    (h : formersW n m p = some (r, m')) : MFr [] [] m m' := by
  rcases n with _ | n
  · simp [formersW] at h
  rw [formersW.arm1] at h
  obtain ⟨⟨q, m1⟩, hal, h⟩ := of_K h (formersW.k_iw_alloc.none ..)
  rw [formersW.k_iw_alloc.arm1] at h
  obtain ⟨m2, hc, h⟩ := of_K h (formersW.k_member_field_copy.none ..)
  rw [formersW.k_member_field_copy.arm1] at h
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  exact (allocW_mfr hal).trans (pos3_fieldCopyW_mfr _ _ _ _ _ _ _ hc)

theorem pos3_nckW_mfr {n : Nat} {m m' : Mem} {p fo fl : Word} {r : List Word} (h : nckW n m p fo fl = some (r, m')) :
    MFr [] [] m m' := by
  unfold nckW at h
  split at h; · cases h
  rename_i r1 m1 h1
  split at h; · cases h
  rename_i r2 m2 h2
  split at h; · cases h
  rename_i r3 m3 h3
  have f123 := ((pos3_memberNamesW_mfr h1).trans (pos3_lpsW_mfr h2)).trans (pos3_nIdxsW_mfr h3)
  cases h4 : plW n m3 (r2.headD 0) (r2.tail.headD 0) with
  | none => rw [h4] at h; simp [nckRec] at h
  | some x =>
    obtain ⟨r4, m4⟩ := x
    rw [h4] at h
    simp only [nckRec] at h
    cases h5 : formersW n m4 p with
    | none => rw [h5] at h; cases h
    | some y =>
      obtain ⟨r5, m5⟩ := y
      rw [h5] at h
      simp only at h
      have hm := partsNctx_eq m5 (r1.headD 0) (r1.tail.headD 0) (r2.headD 0) (r2.tail.headD 0)
        (rdW (m4.arr64 IW) (p + 4)) (r3.headD 0) (r3.tail.headD 0) fo fl (rdW (m4.arr64 IW) (p + 6)) (r4.headD 0)
        (r5.headD 0) (r5.tail.headD 0)
      cases ha : allocW m5 13 with
      | none => rw [ha] at h; cases h
      | some z =>
        obtain ⟨q, m6⟩ := z
        rw [ha] at h hm
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact ((f123.trans (pos3_plW_mfr h4)).trans (pos3_formersW_mfr h5)).trans (posRecW_mfr hm.symm)

theorem pos3_nhGoW_mfr : ∀ (k : Nat) (m m' : Mem) (ctx mm off l oo ol : Word) (r : List Word),
    nhGoW k m ctx mm off l oo ol = some (r, m') → MFr [] [] m m'
  | 0, _, _, _, _, _, _, _, _, _, h => by simp [nhGoW] at h
  | k + 1, m, m', ctx, mm, off, l, oo, ol, r, h => by
    by_cases hl : l = 0
    · rw [nhGoW.arm1 k m ctx mm off l oo ol hl] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]; exact MFr.refl _ _ _
    by_cases h12 : rdW (m.arr64 IW) (ctx + 12) ≤ mm
    · rw [nhGoW.arm2 k m ctx mm off l oo ol hl h12] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]; exact MFr.refl _ _ _
    rw [nhGoW.arm3 k m ctx mm off l oo ol hl h12] at h
    obtain ⟨⟨r2, m2⟩, h2, h⟩ := of_K h (nhGoW.k_inst_pis_with.none ..)
    have f2 := instW_mfr k _ _ _ _ _ _ h2
    by_cases h20 : r2.headD 0 = 0
    · rw [nhGoW.k_inst_pis_with.arm1 k ctx mm off l oo ol r2 m2 h20] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]; exact f2
    rw [nhGoW.k_inst_pis_with.arm2 k ctx mm off l oo ol r2 m2 h20] at h
    obtain ⟨⟨v, m3⟩, h3', h⟩ := of_K h (nhGoW.k_intern_fvar.none ..)
    have f3 := f2.trans (fvinternW_mfr h3')
    by_cases hv : 4294967296 ≤ v
    · rw [nhGoW.k_intern_fvar.abort1 k ctx mm off l oo ol v m3 hv] at h; cases h
    rw [nhGoW.k_intern_fvar.arm1 k ctx mm off l oo ol v m3 hv] at h
    obtain ⟨⟨r4, m4⟩, h4, h⟩ := of_K h (nhGoW.k_sl_snoc.none ..)
    rw [nhGoW.k_sl_snoc.arm1] at h
    obtain ⟨⟨r5, m5⟩, h5, h⟩ := of_K h nhGoW.k_nest_holes_go.none
    rw [nhGoW.k_nest_holes_go.arm1] at h
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact (f3.trans (snocW_mfr h4)).trans (pos3_nhGoW_mfr k _ _ _ _ _ _ _ _ _ h5)

/-! ## `check_abs_ctor_sorts_all` -/

end L.Ind
