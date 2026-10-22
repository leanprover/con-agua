import ConAgua.Arena.IndPosSpec5
import ConAgua.Arena.IndSumSpec5
import ConAgua.Arena.IndPos2SpecE

/-! # The positivity check's walk memos in the memory at hand (lane `indproofs2`, helper `posmemo`)

`PosMR m`: each per-call memo the positivity check's walks use is well formed in `m` (at some
twin map): `nest_occ` (`noMR`), `depth` (`dpMR`), `replace_apps` (`rpMR`), `has_loose_bvar_b`
(`hbMR`), and the banked `replace_fvars` memo has its invariant (`RfInv`). The walks clear their
memo on entry (the twin starts from `∅`), so a caller needs only *some* well-formed memo; a
relational lemma takes `PosMR m` for the memory it starts from and returns `PosMR m'` for the one
it leaves. It is carried across any writer outside the memo region (`MFr [] []`: stubs by
`stubM_memoFrame`, the stores' interns, `IW` records) by `PosMR.fr`, and across a walk by the
walk's own post (its memo) plus its frame (the others), `PosMR.setNo` etc.

This replaces helper `pos2`'s `PosMemo` (memos well formed in *every* stage state, which is false:
`StageR` does not constrain arrays 201‥208). -/

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem hbMR_mfr {S0 : List ArrId} {T0 : List Word} {m m' : Mem} (hf : MFr S0 T0 m m') (hS : HBM ∉ S0)
    (hT : (214 : Word) ∉ T0) {mp : Std.HashMap (EIdx × Nat) Bool} (h : hbMR m mp) : hbMR m' mp := by
  obtain ⟨A, C, f, hA, hC⟩ := hf.memo HBM 214 (by decide) (by decide) hS hT
  exact memoRV_frame hbSch hbSch_wf lfKey hbVR A C hA hC m m' f (fun _ _ h => h) mp h

/-- **The walk memos of the positivity check, well formed in `m`.** -/
structure PosMR (m : Mem) : Prop where
  no : ∃ mp, noMR m mp
  dp : ∃ mp, dpMR m mp
  rp : ∃ mp, rpMR m mp
  hb : ∃ mp, hbMR m mp
  rf : ∃ M G g, RfInv m M G g

/-- The five memos' arrays and stamp words. -/
abbrev PosAv (S : List ArrId) (T : List Word) : Prop :=
  (NOM ∉ S ∧ DPM ∉ S ∧ RAM ∉ S ∧ HBM ∉ S ∧ RFM ∉ S) ∧
  ((204 : Word) ∉ T ∧ (206 : Word) ∉ T ∧ (210 : Word) ∉ T ∧ (214 : Word) ∉ T ∧ (208 : Word) ∉ T ∧
    (218 : Word) ∉ T ∧ (219 : Word) ∉ T)

theorem PosMR.mfr {S : List ArrId} {T : List Word} {m m' : Mem} (h : PosMR m) (hf : MFr S T m m')
    (hv : PosAv S T) : PosMR m' := by
  obtain ⟨⟨h1, h2, h3, h4, h5⟩, ⟨t1, t2, t3, t4, t5, t6, t7⟩⟩ := hv
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩, ⟨M, G, g, hR⟩⟩ := h
  exact ⟨⟨a, noMR_mfr hf h1 t1 ha⟩, ⟨b, dpMR_mfr hf h2 t2 hb⟩, ⟨c, rpMR_mfr hf h3 t3 hc⟩,
    ⟨d, hbMR_mfr hf h4 t4 hd⟩, ⟨M, G, g, hR.mfr hf h5 ⟨t5, t6, t7⟩⟩⟩

/-- Across a writer outside the memo region. -/
theorem PosMR.fr {m m' : Mem} (h : PosMR m) (hf : MFr [] [] m m') : PosMR m' := h.mfr hf (by simp [PosAv])

/-- Across a `nest_occ` walk: its memo from the walk, the others by its frame. -/
theorem PosMR.setNo {m m' : Mem} (h : PosMR m) (hf : MFr [NOM] [204, 205] m m')
    (hn : ∃ mp, noMR m' mp) : PosMR m' := by
  obtain ⟨-, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩, ⟨M, G, g, hR⟩⟩ := h
  exact ⟨hn, ⟨b, dpMR_mfr hf (by decide) (by decide) hb⟩, ⟨c, rpMR_mfr hf (by decide) (by decide) hc⟩,
    ⟨d, hbMR_mfr hf (by decide) (by decide) hd⟩, ⟨M, G, g, hR.mfr hf (by decide) (by decide)⟩⟩

/-- Across a `depth` walk. -/
theorem PosMR.setDp {m m' : Mem} (h : PosMR m) (hf : MFr [DPM] [206, 207] m m')
    (hn : ∃ mp, dpMR m' mp) : PosMR m' := by
  obtain ⟨⟨a, ha⟩, -, ⟨c, hc⟩, ⟨d, hd⟩, ⟨M, G, g, hR⟩⟩ := h
  exact ⟨⟨a, noMR_mfr hf (by decide) (by decide) ha⟩, hn, ⟨c, rpMR_mfr hf (by decide) (by decide) hc⟩,
    ⟨d, hbMR_mfr hf (by decide) (by decide) hd⟩, ⟨M, G, g, hR.mfr hf (by decide) (by decide)⟩⟩

/-- Across a `replace_apps` walk. -/
theorem PosMR.setRp {m m' : Mem} (h : PosMR m) (hf : MFr [RAM] [210, 211] m m')
    (hn : ∃ mp, rpMR m' mp) : PosMR m' := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, -, ⟨d, hd⟩, ⟨M, G, g, hR⟩⟩ := h
  exact ⟨⟨a, noMR_mfr hf (by decide) (by decide) ha⟩, ⟨b, dpMR_mfr hf (by decide) (by decide) hb⟩, hn,
    ⟨d, hbMR_mfr hf (by decide) (by decide) hd⟩, ⟨M, G, g, hR.mfr hf (by decide) (by decide)⟩⟩

/-- Across a `has_loose_bvar_b` walk. -/
theorem PosMR.setHb {m m' : Mem} (h : PosMR m) (hf : MFr [HBM] [214, 215] m m')
    (hn : ∃ mp, hbMR m' mp) : PosMR m' := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, -, ⟨M, G, g, hR⟩⟩ := h
  exact ⟨⟨a, noMR_mfr hf (by decide) (by decide) ha⟩, ⟨b, dpMR_mfr hf (by decide) (by decide) hb⟩,
    ⟨c, rpMR_mfr hf (by decide) (by decide) hc⟩, hn, ⟨M, G, g, hR.mfr hf (by decide) (by decide)⟩⟩

/-- Across the banked `replace_fvars` walk. -/
theorem PosMR.setRf {m m' : Mem} (h : PosMR m) (hf : RxFr m m') (hn : ∃ M G g, RfInv m' M G g) :
    PosMR m' := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩, -⟩ := h
  exact ⟨⟨a, noMR_mfr hf (by decide) (by decide) ha⟩, ⟨b, dpMR_mfr hf (by decide) (by decide) hb⟩,
    ⟨c, rpMR_mfr hf (by decide) (by decide) hc⟩, ⟨d, hbMR_mfr hf (by decide) (by decide) hd⟩, hn⟩

/-- Across a stub. -/
theorem PosMR.stub {f : FnName} (hf : f ∈ stubNames) {m m' : Mem} {args r : List Word} (h : PosMR m)
    (hs : stubM f m args = some (r, m')) : PosMR m' := h.fr (MFr.stub hf hs)

theorem posmemo_erCopyW_iw : ∀ (n : Nat) (m m' : Mem) (d s l : Word), erCopyW n m d s l = some m' →
    MemFrame [IW] [200] m m'
  | 0, _, _, _, _, _, h => by simp [erCopyW] at h
  | n + 1, m, m', d, s, l, h => by
    by_cases hl : l = 0
    · rw [erCopyW_nil n m d s l hl] at h; cases h; exact MemFrame.refl _ _ _
    · rw [erCopyW_step n m d s l hl] at h
      exact (set64IW_frame _ _ _).trans (posmemo_erCopyW_iw n _ _ _ _ _ h)

theorem erToIwW_mfr {n : Nat} {m m' : Mem} {o l : Word} {r : List Word} (h : erToIwW n m o l = some (r, m')) :
    MFr [] [] m m' := by
  unfold erToIwW at h
  split at h; · simp at h
  rename_i q m1 hal
  split at h; · simp at h
  rename_i m2 hc
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  exact (allocW_mfr hal).trans (MFr.of_iw (posmemo_erCopyW_iw _ _ _ _ _ _ hc))

theorem consW_mfr {n : Nat} {m m' : Mem} {x o l : Word} {r : List Word} (h : consW n m x o l = some (r, m')) :
    MFr [] [] m m' := by
  unfold consW at h
  split at h; · simp at h
  split at h; · simp at h
  rename_i q m1 hal
  split at h; · simp at h
  rename_i m2 hc
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  exact ((allocW_mfr hal).trans (MFr.set_iw _ _ _)).trans (MFr.of_iw (posmemo_copyW_iw _ _ _ _ _ _ hc))

theorem piBW_mfr : ∀ (n : Nat) (m m' : Mem) (fuel h : Word) (r : List Word), piBW n m fuel h = some (r, m') →
    MFr [] [] m m'
  | 0, _, _, _, _, _, hh => by simp [piBW] at hh
  | n + 1, m, m', fuel, h, r, hh => by
    by_cases hf : fuel = 0
    · rw [piBW_fuel0 (hf := hf)] at hh; cases hh
    by_cases hg : h >>> 28 ≠ 6
    · rw [piBW_leaf (hf := hf) (hg := hg)] at hh
      simp only [Option.some.injEq, Prod.mk.injEq] at hh; rw [← hh.2]; exact MFr.refl _ _ _
    rw [piBW_node (hf := hf) (hg := hg)] at hh
    by_cases hr : eViewW m h = []
    · rw [hr, piBK1_nil] at hh; cases hh
    rw [piBK1_ne (hr := hr)] at hh
    cases h1 : piBW n m (fuel - 1) ((eViewW m h).getD 2 0) with
    | none => rw [h1] at hh; simp [piBK2] at hh
    | some p1 =>
    obtain ⟨rs, m1⟩ := p1
    rw [h1, piBK2_some] at hh
    cases h2 : consW n m1 ((eViewW m h).getD 1 0) (rs.headD 0) (rs.getD 1 0) with
    | none => rw [h2] at hh; simp [piBK3] at hh
    | some p2 =>
    obtain ⟨r2, m2⟩ := p2
    rw [h2, piBK3_some] at hh
    simp only [Option.some.injEq, Prod.mk.injEq] at hh
    obtain ⟨-, rfl⟩ := hh
    exact (piBW_mfr n _ _ _ _ _ h1).trans (consW_mfr h2)

end L.Ind
