import ConAgua.Arena.IndSumSpec.StructCtorResidOk
import ConAgua.Arena.IndInstallSpec.InstallRec2PSl

/-!
# `block_nest_ctx`'s pure parts keep the walk memos (lane `indstaget`)

`AFr` (`AbsOK m → AbsOK m'`) across `nckW` (the context record) and `nhW` (the holes): the
`AFr` twins of `IndInstallSpec/Pos3NhGoWMfr`'s `MFr` lemmas, so that `block_nest_ctx` under `StageC` returns
`AbsOK` (no `AbsKeep` premise).
-/


namespace L.Ind

open L.Arena

theorem nIdxsCopyW_afr : ∀ (n : Nat) (m m' : Mem) (d s l : Word), nIdxsCopyW n m d s l = some m' →
    AFr m m'
  | 0, _, _, _, _, _, h => by simp [nIdxsCopyW] at h
  | n + 1, m, m', d, s, l, h => by
    by_cases hl : l = 0
    · rw [nIdxsCopyW_nil n m d s l hl] at h; cases h; exact AFr.refl _
    · rw [nIdxsCopyW_step n m d s l hl] at h
      exact (AFr.set64 _ IW (by decide) (by decide) _ _).trans (nIdxsCopyW_afr n _ _ _ _ _ h)

theorem nIdxsW_afr {n : Nat} {m m' : Mem} {p : Word} {r : List Word}
    (h : nIdxsW n m p = some (r, m')) : AFr m m' := by
  unfold nIdxsW at h
  split at h; · cases h
  rename_i q m1 hal
  split at h; · cases h
  rename_i m2 hc
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  exact (allocW_afr hal).trans (nIdxsCopyW_afr _ _ _ _ _ _ hc)

theorem nckW_afr {n : Nat} {m m' : Mem} {p fo fl : Word} {r : List Word}
    (h : nckW n m p fo fl = some (r, m')) : AFr m m' := by
  unfold nckW at h
  split at h; · cases h
  rename_i r1 m1 h1
  split at h; · cases h
  rename_i r2 m2 h2
  split at h; · cases h
  rename_i r3 m3 h3
  have f123 := ((memberNamesW_afr h1).trans (lpsW_afr h2)).trans (nIdxsW_afr h3)
  cases h4 : plW n m3 (r2.headD 0) (r2.tail.headD 0) with
  | none => rw [h4] at h; simp [nckRec] at h
  | some x =>
    obtain ⟨r4, m4⟩ := x
    rw [h4] at h
    simp only [nckRec] at h
    have hm := partsNctx_eq m4 (r1.headD 0) (r1.tail.headD 0) (r2.headD 0) (r2.tail.headD 0)
      (rdW (m4.arr64 IW) (p + 4)) (r3.headD 0) (r3.tail.headD 0) fo fl (rdW (m4.arr64 IW) (p + 6)) (r4.headD 0)
    cases ha : allocW m4 11 with
    | none => rw [ha] at h; cases h
    | some y =>
      obtain ⟨q, m5⟩ := y
      rw [ha] at h hm
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact (f123.trans (plW_afr h4)).trans (posRecW_afr hm.symm)

theorem nhGoW_afr : ∀ (k : Nat) (m m' : Mem) (vis ctx mm off l oo ol : Word) (r : List Word),
    nhGoW k m vis ctx mm off l oo ol = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, _, _, _, _, h => by simp [nhGoW] at h
  | k + 1, m, m', vis, ctx, mm, off, l, oo, ol, r, h => by
    by_cases hl : l = 0
    · rw [nhGoW_nil k m vis ctx mm off l oo ol hl] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]; exact AFr.refl _
    rw [nhGoW_cons k m vis ctx mm off l oo ol hl] at h
    cases h1 : envFindW m (rdW (m.arr64 IW) off) vis with
    | none => rw [h1] at h; simp [nhK1] at h
    | some x1 =>
    obtain ⟨r1, m1⟩ := x1
    rw [h1] at h
    have f1 := envFindW_afr h1
    by_cases hm : r1.headD 0 = 0
    · rw [nhK1_miss k m1 vis ctx mm off l oo ol r1 hm] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]; exact f1
    by_cases h3 : rdW (m1.arr64 EREC) (r1.tail.headD 0) ≠ 3
    · rw [nhK1_noind k m1 vis ctx mm off l oo ol r1 hm h3] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]; exact f1
    rw [nhK1_ind k m1 vis ctx mm off l oo ol r1 hm h3] at h
    cases h2 : instW k m1 (rdW (m1.arr64 IW) (ctx + 7)) (rdW (m1.arr64 IW) (ctx + 8))
        (rdW (m1.arr64 EREC) (r1.tail.headD 0 + 4)) with
    | none => rw [h2] at h; simp [nhK2] at h
    | some x2 =>
    obtain ⟨r2, m2⟩ := x2
    rw [h2] at h
    have f2 := f1.trans (instW_afr k _ _ _ _ _ _ h2)
    by_cases h20 : r2.headD 0 = 0
    · rw [nhK2_none k m2 vis ctx mm off l oo ol r2 h20] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]; exact f2
    rw [nhK2_some k m2 vis ctx mm off l oo ol r2 h20] at h
    cases h3' : fvinternW m2 (rdW (m2.arr64 IW) (ctx + 4) + mm) (r2.tail.headD 0) with
    | none => rw [h3'] at h; simp [nhK3] at h
    | some x3 =>
    obtain ⟨v, m3⟩ := x3
    rw [h3'] at h
    have f3 := f2.trans (fvinternW_afr h3')
    by_cases hv : 4294967296 ≤ v
    · rw [nhK3_big k m3 vis ctx mm off l oo ol v hv] at h; cases h
    rw [nhK3_ok k m3 vis ctx mm off l oo ol v hv] at h
    cases h4 : snocW k m3 oo ol v with
    | none => rw [h4] at h; simp [nhK4] at h
    | some x4 =>
    obtain ⟨r4, m4⟩ := x4
    rw [h4, nhK4_some] at h
    exact (f3.trans (snocW_afr h4)).trans (nhGoW_afr k _ _ _ _ _ _ _ _ _ _ h)

theorem nhW_afr {k : Nat} {m m' : Mem} {vis ctx : Word} {r : List Word}
    (h : nhW k m vis ctx = some (r, m')) : AFr m m' :=
  nhGoW_afr k m m' vis ctx 0 _ _ 0 0 r h

end L.Ind
