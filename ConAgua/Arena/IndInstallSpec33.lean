import ConAgua.Arena.IndInstallSpec32

/-!
# Refinements of `IndInstall`, part 33 (lane `indproofs3`, helper `pos`): the walk memos across
`block_nest_ctx` and `check_abs_ctor_sorts_all`

`checkBlockPositivity` runs the positivity walk (`nest_uniform`, `nest_root`, later `nest_seeds`),
which needs the walk memos well formed in the memory at hand (`PosMR`). Between the walks it calls
`block_nest_ctx` and `check_abs_ctor_sorts_all`; here their word models are shown to leave the memo
region alone (`MFr [] []`), so `PosMR` crosses them (`PosMR.fr`). Stubs leave it alone by their
contract (`stubM_memoFrame`, `MFr.ofStub`); interns write the store tier (`LowFr`); the rest writes
`IW` and its top.
-/

set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Pieces -/

theorem pos3_callW_stub_mfr {p : Prog} {n : Nat} {f : FnName} {args r : List Word} {m m' : Mem}
    (hf : f ∈ stubNames) (h : callW p n f args m = some (r, m')) : MFr [] [] m m' := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (stubM_spec p f n _ args) h
  exact MFr.ofStub hW hf

theorem pos3_nameCopyW_mfr : ∀ (n : Nat) (m m' : Mem) (d s l : Word), nameCopyW n m d s l = some m' →
    MFr [] [] m m'
  | 0, _, _, _, _, _, h => by simp [nameCopyW] at h
  | n + 1, m, m', d, s, l, h => by
    by_cases hl : l = 0
    · rw [nameCopyW_nil n m d s l hl] at h; cases h; exact MFr.refl _ _ _
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
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  exact (allocW_mfr hal).trans (pos3_nameCopyW_mfr _ _ _ _ _ _ hc)

theorem pos3_nIdxsW_mfr {n : Nat} {m m' : Mem} {p : Word} {r : List Word}
    (h : nIdxsW n m p = some (r, m')) : MFr [] [] m m' := by
  unfold nIdxsW at h
  split at h; · cases h
  rename_i q m1 hal
  split at h; · cases h
  rename_i m2 hc
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
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
    by simp [paramSch, PREC, PSLOT], by simp [paramSch]⟩

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
        exact (pos3_plgW_mfr k _ _ _ _ _ hg).trans (MFr.of_frame (ilF_frame hs) (by simp [POOL, LSREC, LSSLOT, LSHP]) (by simp))

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
    have hm := partsNctx_eq m4 (r1.headD 0) (r1.tail.headD 0) (r2.headD 0) (r2.tail.headD 0)
      (rdW (m4.arr64 IW) (p + 4)) (r3.headD 0) (r3.tail.headD 0) fo fl (rdW (m4.arr64 IW) (p + 6)) (r4.headD 0)
    cases ha : allocW m4 11 with
    | none => rw [ha] at h; cases h
    | some y =>
      obtain ⟨q, m5⟩ := y
      rw [ha] at h hm
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact (f123.trans (pos3_plW_mfr h4)).trans (posRecW_mfr hm.symm)

theorem pos3_nhGoW_mfr : ∀ (k : Nat) (m m' : Mem) (vis ctx mm off l oo ol : Word) (r : List Word),
    nhGoW k m vis ctx mm off l oo ol = some (r, m') → MFr [] [] m m'
  | 0, _, _, _, _, _, _, _, _, _, _, h => by simp [nhGoW] at h
  | k + 1, m, m', vis, ctx, mm, off, l, oo, ol, r, h => by
    by_cases hl : l = 0
    · rw [nhGoW_nil k m vis ctx mm off l oo ol hl] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]; exact MFr.refl _ _ _
    rw [nhGoW_cons k m vis ctx mm off l oo ol hl] at h
    cases h1 : envFindW m (rdW (m.arr64 IW) off) vis with
    | none => rw [h1] at h; simp [nhK1] at h
    | some x1 =>
    obtain ⟨r1, m1⟩ := x1
    rw [h1] at h
    have f1 := envFindW_mfr h1
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
    have f2 := f1.trans (instW_mfr k _ _ _ _ _ _ h2)
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
    have f3 := f2.trans (fvinternW_mfr h3')
    by_cases hv : 4294967296 ≤ v
    · rw [nhK3_big k m3 vis ctx mm off l oo ol v hv] at h; cases h
    rw [nhK3_ok k m3 vis ctx mm off l oo ol v hv] at h
    cases h4 : snocW k m3 oo ol v with
    | none => rw [h4] at h; simp [nhK4] at h
    | some x4 =>
    obtain ⟨r4, m4⟩ := x4
    rw [h4, nhK4_some] at h
    exact (f3.trans (snocW_mfr h4)).trans (pos3_nhGoW_mfr k _ _ _ _ _ _ _ _ _ _ h)

/-- **`block_nest_ctx`'s model leaves the walk memos alone.** -/
theorem bncW_mfr {n : Nat} {m m' : Mem} {vis q cvO cvL : Word} {r : List Word}
    (h : bncW n m vis q cvO cvL = some (r, m')) : MFr [] [] m m' := by
  unfold bncW at h
  split at h; · cases h
  split at h; · cases h
  cases h1 : stubM "open_pis_at_fvars_f" m [rdW (m.arr64 IW) (q + 4),
      rdW (m.arr64 EREC) (rdW (m.arr64 IW) cvO + 3), 0] with
  | none => rw [h1] at h; simp [bncK1] at h
  | some x1 =>
  obtain ⟨r1, m1⟩ := x1
  rw [h1] at h
  have f1 := MFr.ofStub h1
  by_cases h0 : r1.headD 0 = 0
  · rw [bncK1_none n m1 vis q r1 h0] at h; cases h
  by_cases hov : r1.tail.tail.headD 0 + rdW (m1.arr64 IW) (q + 1) < r1.tail.tail.headD 0
  · rw [bncK1_ov n m1 vis q r1 h0 hov] at h; cases h
  rw [bncK1_some n m1 vis q r1 h0 hov] at h
  cases h2 : nckW n m1 q (r1.tail.headD 0) (r1.tail.tail.headD 0) with
  | none => rw [h2] at h; simp [bncK2] at h
  | some x2 =>
  obtain ⟨r2, m2⟩ := x2
  rw [h2, bncK2_some] at h
  have f2 := f1.trans (pos3_nckW_mfr h2)
  cases h3 : nhW n m2 vis (r2.headD 0) with
  | none => rw [h3] at h; simp [bncK3] at h
  | some x3 =>
  obtain ⟨r3, m3⟩ := x3
  rw [h3] at h
  by_cases h30 : r3.headD 0 = 0
  · rw [bncK3_none m3 (r2.headD 0) r3 h30] at h; cases h
  rw [bncK3_some m3 (r2.headD 0) r3 h30] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  rw [← h.2]
  exact f2.trans (pos3_nhGoW_mfr _ _ _ _ _ _ _ _ _ _ _ h3)

/-! ## `check_abs_ctor_sorts_all` -/

theorem pos3_cfbW_mfr {n : Nat} {m m' : Mem} {isProp large s io il fv u : Word} {r : List Word}
    (h : cfbW stubCall n m isProp large s io il fv u = some (r, m')) : MFr [] [] m m' := by
  cases n with
  | zero => simp [cfbW] at h
  | succ n =>
  by_cases hp : isProp = 0
  · rw [cfbW_leq stubCall n m isProp large s io il fv u hp] at h
    cases h1 : stubCall n "lv_leq_top" [u, s] m with
    | none => rw [h1] at h; simp [cfbK1] at h
    | some x =>
      obtain ⟨r1, m1⟩ := x
      rw [h1] at h
      simp only [cfbK1] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact MFr.ofStub h1
      · cases h
  by_cases hl : large = 0
  · rw [cfbW_none stubCall n m isProp large s io il fv u hp hl] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact MFr.refl _ _ _
  rw [cfbW_large stubCall n m isProp large s io il fv u hp hl] at h
  cases hz : pinWordV m 53 with
  | none => rw [hz] at h; simp [cfbK2] at h
  | some z =>
  rw [hz, cfbK2_some] at h
  cases he : eqTrueC stubCall n m u z with
  | none => rw [he] at h; simp [cfbK3] at h
  | some y =>
  obtain ⟨eq, m1⟩ := y
  rw [he, cfbK3_some] at h
  have f1 : MFr [] [] m m1 := by
    rcases n with _ | n
    · simp [eqTrueC] at he
    rw [eqTrueC_succ] at he
    cases hs : stubCall n "lvl_eq_c" [u, z] m with
    | none => rw [hs] at he; simp [eqTrueK] at he
    | some w =>
      obtain ⟨r2, m2⟩ := w
      rw [hs, eqTrueK_some] at he
      simp only [Option.some.injEq, Prod.mk.injEq] at he
      rw [← he.2]; exact MFr.ofStub hs
  cases hc : containsW n m1 io il fv with
  | none => rw [hc] at h; simp [cfbK4] at h
  | some ct =>
  rw [hc] at h
  simp only [cfbK4] at h
  split at h
  · cases h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact f1

theorem pos3_csfW_mfr : ∀ (n : Nat) (m m' : Mem) (vis isProp large s nP fo fl io il res j : Word) (r : List Word),
    csfW stubCall n m vis isProp large s nP fo fl io il res j = some (r, m') → MFr [] [] m m'
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h => by simp [csfW] at h
  | n + 1, m, m', vis, isProp, large, s, nP, fo, fl, io, il, res, j, r, h => by
    by_cases hj : j = 0
    · rw [csfW_zero stubCall n m vis isProp large s nP fo fl io il res j hj] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact MFr.refl _ _ _
    by_cases hf : fl ≤ j - 1
    · rw [csfW_oob stubCall n m vis isProp large s nP fo fl io il res j hj hf] at h; cases h
    rw [csfW_step stubCall n m vis isProp large s nP fo fl io il res j hj hf] at h
    cases h1 : ftdF m [rdW (m.arr64 IW) (fo + (j - 1))] with
    | none => rw [h1] at h; simp [csfK1] at h
    | some x1 =>
    obtain ⟨r1, m1⟩ := x1
    rw [h1, csfK1_some] at h
    cases h2 : stubCall n "infer_type_core" [vis, nP + (j - 1), r1.headD 0] m1 with
    | none => rw [h2] at h; simp [csfK2] at h
    | some x2 =>
    obtain ⟨r2, m2⟩ := x2
    rw [h2, csfK2_some] at h
    cases h3 : stubCall n "ensure_sort_core" [vis, nP + (j - 1), r2.headD 0] m2 with
    | none => rw [h3] at h; simp [csfK3] at h
    | some x3 =>
    obtain ⟨r3, m3⟩ := x3
    rw [h3, csfK3_some] at h
    cases h4 : cfbW stubCall n m3 isProp large s io il (rdW (m.arr64 IW) (fo + (j - 1))) (r3.headD 0) with
    | none => rw [h4] at h; simp [csfK4] at h
    | some x4 =>
    obtain ⟨r4, m4⟩ := x4
    rw [h4, csfK4_some] at h
    cases h5 : csfW stubCall n (m4.set64 IW (res + (j - 1)) (r3.headD 0)) vis isProp large s nP fo fl io il res (j - 1) with
    | none => rw [h5] at h; simp [csfK5] at h
    | some x5 =>
    obtain ⟨r5, m5⟩ := x5
    rw [h5, csfK5_some] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    exact ((((MFr.ofFtdF h1).trans (MFr.ofStub h2)).trans (MFr.ofStub h3)).trans (pos3_cfbW_mfr h4)).trans
      ((MFr.set_iw _ _ _).trans (pos3_csfW_mfr n _ _ _ _ _ _ _ _ _ _ _ _ _ _ h5))

theorem pos3_fsortsW_mfr {n : Nat} {m m' : Mem} {vis isProp large s nP fo fl io il nW : Word} {r : List Word}
    (h : fsortsW stubCall n m vis isProp large s nP fo fl io il nW = some (r, m')) : MFr [] [] m m' := by
  unfold fsortsW at h
  cases ha : allocW m nW with
  | none => rw [ha] at h; simp [fsortsK1] at h
  | some x =>
    obtain ⟨q, m1⟩ := x
    rw [ha, fsortsK1_some] at h
    cases hc : csfW stubCall n m1 vis isProp large s nP fo fl io il q nW with
    | none => rw [hc] at h; simp [fsortsK2] at h
    | some y =>
      obtain ⟨r2, m2⟩ := y
      rw [hc, fsortsK2_some] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]
      exact (allocW_mfr ha).trans (pos3_csfW_mfr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc)

theorem pos3_callW_fsorts_mfr {p : Prog} (hP : SumProg p) {n : Nat} {vis isP large s nP fo fl io il j : Word}
    {r : List Word} {m m' : Mem}
    (h : callW p n "check_struct_field_sorts_i" [vis, isP, large, s, nP, fo, fl, io, il, j] m = some (r, m')) :
    MFr [] [] m m' := by
  rcases n with _ | k
  · rw [callW_zero] at h; cases h
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (fsortsW_spec p hP.hg hP.hpw hP.het hP.hcn hP.hfsb hP.hcfg hP.ha hP.hcfs hP.ad.ftd stubCall (stubCall_spec p) k _ vis isP large s nP
      fo fl io il j) h
  exact pos3_fsortsW_mfr hW

theorem pos3_iaoW_mfr {p : Prog} (hP : SumProg p) {n : Nat} {m m' : Mem} {vis ctx isP nF tyN hi : Word}
    {r : List Word} (h : iaoW p n m vis ctx isP nF tyN hi = some (r, m')) : MFr [] [] m m' := by
  unfold iaoW at h
  split at h; · cases h
  cases h1 : callW p n "open_pis_at_fvars_f" [nF, tyN, hi] m with
  | none => rw [h1] at h; simp [iaoK1] at h
  | some x1 =>
  obtain ⟨r1, m1⟩ := x1
  rw [h1] at h
  by_cases h0 : r1.headD 0 = 0
  · rw [iaoK1_none p n m1 vis isP nF hi _ r1 h0] at h; cases h
  rw [iaoK1_some p n m1 vis isP nF hi _ r1 h0] at h
  cases h2 : callW p n "check_struct_field_sorts_i" [vis, isP, 0, rdW (m.arr64 IW) (ctx + 9), hi,
      r1.tail.headD 0, r1.tail.tail.headD 0, 0, 0, nF] m1 with
  | none => rw [h2] at h; simp [iaoK2] at h
  | some x2 =>
  obtain ⟨r2, m2⟩ := x2
  rw [h2, iaoK2_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  rw [← h.2]
  exact (pos3_callW_stub_mfr (by decide) h1).trans (pos3_callW_fsorts_mfr hP h2)

theorem pos3_iacW_mfr {p : Prog} (hP : AbsProg p) (n : Nat) : ∀ {m m' : Mem} {vis ctx isP co cl oo ol : Word}
    {r : List Word}, iacW p n m vis ctx isP co cl oo ol = some (r, m') → MFr [] [] m m' := by
  induction n with
  | zero => intro m m' vis ctx isP co cl oo ol r h; rw [iacW_zero] at h; cases h
  | succ n ih =>
  intro m m' vis ctx isP co cl oo ol r h
  by_cases hcl : cl = 0
  · rw [iacW_nil1 p n m vis ctx isP co cl oo ol hcl] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact MFr.refl _ _ _
  by_cases hol : ol = 0
  · rw [iacW_nil2 p n m vis ctx isP co cl oo ol hcl hol] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact MFr.refl _ _ _
  rw [iacW_cons p n m vis ctx isP co cl oo ol hcl hol] at h
  cases h1 : callW p n "all_level_params_defined" [rdW (m.arr64 IW) (ctx + 2), rdW (m.arr64 IW) (ctx + 3),
      rdW (m.arr64 IW) (rdW (m.arr64 IW) oo + 2)] m with
  | none => rw [h1] at h; simp [iacK1] at h
  | some x1 =>
  obtain ⟨r1, m1⟩ := x1
  rw [h1] at h
  by_cases h0 : r1.headD 0 = 0
  · rw [iacK1_none p n m1 vis ctx isP co cl oo ol _ _ r1 h0] at h; cases h
  rw [iacK1_some p n m1 vis ctx isP co cl oo ol _ _ r1 h0] at h
  cases h2 : callW p n "nest_ctx_hi_at" [ctx, 0] m1 with
  | none => rw [h2] at h; simp [iacK2] at h
  | some x2 =>
  obtain ⟨r2, m2⟩ := x2
  rw [h2, iacK2_some] at h
  have e2 : m2 = m1 := by
    obtain ⟨s', rfl, -, hm, -⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
      (nestCtxHiAt_specE p hP.hiAt n _ ctx 0) h2
    exact hm
  subst e2
  cases h3 : callW p n "check_abs_ctor_sorts_one" [vis, ctx, isP, rdW (m2.arr64 IW) (rdW (m.arr64 IW) co + 1),
      rdW (m2.arr64 IW) (rdW (m.arr64 IW) oo + 2), r2.headD 0] m2 with
  | none => rw [h3] at h; simp [iacK3] at h
  | some x3 =>
  obtain ⟨r3, m3⟩ := x3
  rw [h3, iacK3_some] at h
  have f3 : MFr [] [] m2 m3 := by
    rcases n with _ | k
    · rw [callW_zero] at h3; cases h3
    obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m2, Locals.init []⟩)
      (iao_spec p hP.one k _ _ _ _ _ _ _) h3
    exact pos3_iaoW_mfr hP.sum hW
  cases h4 : iacW p n m3 vis ctx isP (co + 1) (cl - 1) (oo + 1) (ol - 1) with
  | none => rw [h4] at h; simp [iacK4] at h
  | some x4 =>
  obtain ⟨r4, m4⟩ := x4
  rw [h4, iacK4_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  rw [← h.2]
  exact (((pos3_callW_stub_mfr (by decide) h1)).trans f3).trans (ih h4)

/-- **`check_abs_ctor_sorts_all`'s model leaves the walk memos alone.** -/
theorem iaaW_mfr {p : Prog} (hP : AbsProg p) (n : Nat) : ∀ {m m' : Mem} {vis ctx isP so sl oo ol : Word}
    {r : List Word}, iaaW p n m vis ctx isP so sl oo ol = some (r, m') → MFr [] [] m m' := by
  induction n with
  | zero => intro m m' vis ctx isP so sl oo ol r h; rw [iaaW_zero] at h; cases h
  | succ n ih =>
  intro m m' vis ctx isP so sl oo ol r h
  by_cases hsl : sl = 0
  · rw [iaaW_nil1 p n m vis ctx isP so sl oo ol hsl] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact MFr.refl _ _ _
  by_cases hol : ol = 0
  · rw [iaaW_nil2 p n m vis ctx isP so sl oo ol hsl hol] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact MFr.refl _ _ _
  rw [iaaW_cons p n m vis ctx isP so sl oo ol hsl hol] at h
  generalize hargs : [vis, ctx, isP, rdW (m.arr64 IW) (rdW (m.arr64 IW) so),
    rdW (m.arr64 IW) (rdW (m.arr64 IW) so + 1), rdW (m.arr64 IW) (rdW (m.arr64 IW) oo),
    rdW (m.arr64 IW) (rdW (m.arr64 IW) oo + 1)] = args at h
  cases h1 : callW p n "check_abs_ctor_sorts" args m with
  | none => rw [h1] at h; simp [iaaK1] at h
  | some x1 =>
  obtain ⟨r1, m1⟩ := x1
  rw [h1, iaaK1_some] at h
  cases h2 : iaaW p n m1 vis ctx isP (so + 1) (sl - 1) (oo + 1) (ol - 1) with
  | none => rw [h2] at h; simp [iaaK2] at h
  | some x2 =>
  obtain ⟨r2, m2⟩ := x2
  rw [h2, iaaK2_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  rw [← h.2]
  subst hargs
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (iac_spec p hP.abs n _ _ _ _ _ _ _ _) h1
  exact (pos3_iacW_mfr hP n hW).trans (ih h2)

end L.Ind
