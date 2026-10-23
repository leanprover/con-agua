import ConAgua.Arena.DeclValRef
import ConAgua.Arena.DeclCvgT

/-!
# The value checks under `StageT` (lane `loopt2`)

`DeclValRef.lean`'s relational lemmas run the value checks' models from the stage relation, the
core's entry points read through their stubs. Here they read the program's own calls
(`realCall p`) and run from `StageT`, as `check_value_group` does (`DeclCvgT.lean`). The value
checks end with `env_push`, which changes the environment; after it the stage relation holds at
the extended environment and the core's memos are still well formed (`CoreMemos`: `env_push`
writes the index rows, `ECON` and `CTL[128]` only), which is what the loop carries to the next
declaration (open end 4, `docs/design/loopt2.md`).
-/

open ConRon.Arena

namespace L.Arena

open L.Ind

local notation "V" => ConLeche.CheckMode.verified

/-- **`env_push` writes the index rows, `ECON` and its count** (`CTL[128]`). -/
theorem envPushW_frame {m m' : Mem} {vis q : Word} {r : List Word}
    (h : envPushW m vis q = some (r, m')) :
    MemFrame [132, 133, 134, ECON] [128] m m' := by
  simp only [envPushW] at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  rotate_left
  · cases h
  rename_i hc
  obtain ⟨ht, -⟩ := hc
  have hrow : rowArr (rdW (m.arr64 EREC) (q + 1)) ∈ [132, 133, 134, ECON] := by
    simp only [rowArr, List.mem_cons]
    have : rowTag (rdW (m.arr64 EREC) (q + 1)) = 0 ∨ rowTag (rdW (m.arr64 EREC) (q + 1)) = 1 ∨
        rowTag (rdW (m.arr64 EREC) (q + 1)) = 2 := by omega
    rcases this with h0 | h0 | h0 <;> simp [h0]
  have hf1 : MemFrame [132, 133, 134, ECON] [128] m (rowSet m (rdW (m.arr64 EREC) (q + 1)) (vis + 1) q) := by
    unfold rowSet
    exact ((MemFrame.set64 m _ (by simp only [rowArr, CTL, ArrId]; omega) _ _).mono
      (by intro b hb; simp at hb; subst hb; exact hrow) (by simp)).trans
      ((MemFrame.set64 _ _ (by simp only [rowArr, CTL, ArrId]; omega) _ _).mono
        (by intro b hb; simp at hb; subst hb; exact hrow) (by simp))
  simp only [envPushK] at h
  split at h
  · cases h
  split at h
  rotate_left
  · cases h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  exact (hf1.trans ((MemFrame.set64 _ ECON (by decide) _ _).mono (by simp) (by simp))).trans
    ((MemFrame.setCtl _ 128 _).mono (by simp) (by simp))

/-- **`lvl_eq_fueled` under `StageT`**: `lvl_eq_c` through `lvlEqC_simT`; an answer other than
`0` is the twin's `some true` (the callers abort on `0`). -/
theorem lfW_okT {p : Prog} (hq : KnotStageProg p) (hL : LvlCacheProg p)
    (hpc : p.lookup "lvl_eq_c" = some lvlEqCL) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {n : Nat} {m m' : Mem} {a : AState} {u v : Word} {r : List Word}
    (h : lfW (realCall p) n m u v = some (r, m')) (hS : StageT dn vis fe m a) (hu : H u) (hv : H v)
    (lu lv : ConLeche.Level) (hdu : denoteL a.store.ls (decI u) = some lu)
    (hdv : denoteL a.store.ls (decI v) = some lv) :
    ∃ x a', (lvlEq? (decI u) (decI v)).run a = .ok (x, a') ∧ StageT dn vis fe m' a' ∧
      IWGrow m m' ∧ (r.headD 0 ≠ 0 → x = some true) := by
  cases n with
  | zero => simp [lfW] at h
  | succ n =>
  simp only [lfW] at h
  cases hs : realCall p n "lvl_eq_c" [u, v] m with
  | none => simp [hs] at h
  | some rm1 =>
  obtain ⟨r1, m1⟩ := rm1
  simp only [hs] at h
  by_cases h0 : r1.headD 0 = 0
  · rw [if_pos h0] at h; exact absurd h (by simp)
  rw [if_neg h0] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨x, a1, hrun, hSt, hg, hdec, -⟩ :=
    lvlEqC_simT p hq.closed hL hpc n hS u v hu hv lu lv hdu hdv r1 m1 hs
  refine ⟨x, a1, hrun, hSt, hg, fun hne => ?_⟩
  have h2 : r1.headD 0 = 2 := Classical.byContradiction fun h2 => by
    simp only [List.headD_cons] at hne
    exact hne (if_neg h2)
  rw [← hdec, h2]; rfl

/-- **The value checks' common tail under `StageT`** (`dvK1_ok`'s): after the push, the stage
relation at the extended environment and the core's memos well formed. -/
theorem dvK1_okT {p : Prog} (hq : KnotStageProg p) (hRp : RecProg p)
    {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {n : Nat} (hn : n ≤ 2 ^ 62) {m1 m' : Mem} {c wv wt : Word} {r : List Word}
    {cv : IConstantVal} {ci : IConstantInfo} {a1 : AState} {r1 : List Word} (msg : String)
    (h : dvK1 p (realCall p) n vis c wv wt (some (r1, m1)) = some (r, m'))
    (hS1 : StageT dn vis fe m1 a1)
    (hci : decCI (erecP m1) dn c.toNat = some ci) (hcb : c.toNat + 5 < 2 ^ 64)
    (hwv : wv.toNat < 2 ^ 32) (hwt : wt.toNat < 2 ^ 32) (hty : cv.type = decI wt) :
    ∃ a', (do
        let vtype ← inferTypeCore V fe checkFuel 0 (decI wv)
        unless ← isDefEqCore V fe checkFuel 0 vtype cv.type do
          fail (.invalid msg)
        pure (fe.push ci) : AM IFEnv).run a1 = .ok (fe.push ci, a') ∧
      StageR dn (r.headD 0) (fe.push ci) m' a' ∧ CoreMemos m' ∧ IWGrow m1 m' := by
  rw [dvK1_some] at h
  cases h2 : realCall p n "infer_type_core" [vis, 0, wv] m1 with
  | none => rw [h2] at h; simp [dvK2] at h
  | some rm2 =>
  obtain ⟨r2, m2⟩ := rm2
  rw [h2, dvK2_some] at h
  obtain ⟨x2, a2, hrun2, hS2, hg2, hx2l, hx2⟩ := hq.inferTypeCore_sim n hn hS1 0 wv hwv r2 m2 h2
  cases h3 : realCall p n "is_def_eq_core" [vis, 0, r2.headD 0, wt] m2 with
  | none => rw [h3] at h; simp [dvK3] at h
  | some rm3 =>
  obtain ⟨r3, m3⟩ := rm3
  rw [h3, dvK3_some] at h
  obtain ⟨x3, a3, hrun3, hS3, hg3, hx3⟩ :=
    hq.isDefEqCore_sim n hn hS2 0 (r2.headD 0) wt hx2l hwt r3 m3 h3
  by_cases hb3 : r3.headD 0 = 0
  · rw [if_pos hb3] at h; simp at h
  rw [if_neg hb3] at h
  have ex3 : x3 = true := by rw [← hx3]; simpa [decBool] using hb3
  -- the push
  have hx13 : ArrExt (erecP m1) (erecP m3) := IWGrow.erecPExt (hg2.trans hg3)
  have hci3 := ArrExt.decCI hx13 hci
  obtain ⟨w, hw1, hwl, -⟩ := decCI_name hci3
  have hc1 : (c + 1).toNat = c.toNat + 1 := toNat_add_small c 1 (by omega)
  have hw : (rdW (m3.arr64 EREC) (c + 1)).toNat < 2 ^ 32 := by
    rw [rdW_of_get? hc1.symm (erecP_get hw1)]; exact hwl
  cases h4 : callW p n "env_push" [vis, c] m3 with
  | none => rw [h4] at h; simp [dvK4] at h
  | some rm4 =>
  obtain ⟨r4, m4⟩ := rm4
  rw [h4, dvK4_some] at h
  obtain ⟨s4, hs4, -, hW4⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
    (envPush_specW p hRp n ⟨m3, Locals.init []⟩ vis c hw) h4
  subst hs4
  obtain ⟨hS4, hg4⟩ := envPushW_ok hW4 hS3.stage hci3
  have hM4 : CoreMemos s4.mem := hS3.twin.memos.frame (envPushW_frame hW4)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have h00 : (0 : Word).toNat = 0 := rfl
  rw [h00] at hrun2
  rw [h00, hx2, ← hty] at hrun3
  refine ⟨a3, ?_, by simpa using hS4, hM4, hg2.trans (hg3.trans hg4)⟩
  simp only [StateT.run_bind, hrun2, exc_ok_bind', hrun3, ex3, if_true, StateT.run_pure]
  rfl

/-- **`check_defn_val`/`check_opaque_val` under `StageT`** (`dvW_ok`'s), `install_value_guards`
under `StageT` given (`IvgT`). -/
theorem dvW_okT {p : Prog} (hq : KnotStageProg p) (hRp : RecProg p) (hivg : IvgT)
    {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {a : AState} {n : Nat} (hn : n ≤ 2 ^ 62) {m m' : Mem} {c : Word} {r : List Word}
    {cv : IConstantVal} {v : EIdx} {ci : IConstantInfo} (msg : String)
    (h : dvW p (realCall p) n m vis c = some (r, m')) (hS : StageT dn vis fe m a)
    (hci : decCI (erecP m) dn c.toNat = some ci) (hcv : decCV (erecP m) (c.toNat + 1) = some cv)
    (hv : hd? (erecP m) (c.toNat + 5) = some v) :
    ∃ a', (dvT fe cv v ci msg).run a = .ok (fe.push ci, a') ∧
      StageR dn (r.headD 0) (fe.push ci) m' a' ∧ CoreMemos m' ∧ IWGrow m m' := by
  obtain ⟨wv, hwv, hwvl, rfl⟩ := hd?_some hv
  obtain ⟨wt, hwt, hwtl, hty⟩ := decCV_typeW hcv
  have hcb : c.toNat + 5 < 2 ^ 64 := erecP_bound hwv hS.stage.2
  have ev : rdW (m.arr64 EREC) (c + 5) = wv :=
    rdW_of_get? (toNat_add_small c 5 (by omega)).symm (erecP_get hwv)
  have et : rdW (m.arr64 EREC) (c + 4) = wt :=
    rdW_of_get? (toNat_add_small c 4 (by omega)).symm (erecP_get (by simpa [Nat.add_assoc] using hwt))
  cases n with
  | zero => simp [dvW] at h
  | succ n =>
  rw [dvW_step, ev, et] at h
  have hc1 : (c + 1).toNat = c.toNat + 1 := toNat_add_small c 1 (by omega)
  cases h1 : ivgW n m vis (c + 1) wv with
  | none => rw [h1] at h; simp [dvK1] at h
  | some rm1 =>
  obtain ⟨r1, m1⟩ := rm1
  rw [h1] at h
  obtain ⟨a1, hrun1, hS1, hg1⟩ :=
    hivg h1 hS (by rw [hc1]; exact ArrExt.decCV (erecP_ext m) hcv) (by rw [hc1]; omega) hwvl
  obtain ⟨a', hrun', hS', hM', hg'⟩ := dvK1_okT hq hRp (by omega) msg h hS1
    (ArrExt.decCI (IWGrow.erecPExt hg1) hci) hcb hwvl hwtl hty
  refine ⟨a', ?_, hS', hM', hg1.trans hg'⟩
  simp only [dvT, StateT.run_bind, hrun1, exc_ok_bind']
  simpa only [StateT.run_bind] using hrun'

/-- **`check_thm_val` under `StageT`** (`tvW_ok`'s). -/
theorem tvW_okT {p : Prog} (hq : KnotStageProg p) (hRp : RecProg p) (hL : LvlCacheProg p)
    (hpc : p.lookup "lvl_eq_c" = some lvlEqCL) (hivg : IvgT)
    {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {a : AState} {n : Nat} (hn : n ≤ 2 ^ 62) {m m' : Mem} {c : Word} {r : List Word}
    {cv : IConstantVal} {v : EIdx}
    (h : tvW p (realCall p) n m vis c = some (r, m')) (hS : StageT dn vis fe m a)
    (hci : decCI (erecP m) dn c.toNat = some (.thmInfo cv))
    (hcv : decCV (erecP m) (c.toNat + 1) = some cv)
    (hv : hd? (erecP m) (c.toNat + 5) = some v) :
    ∃ a', (checkThmVal V fe cv v).run a = .ok (fe.push (.thmInfo cv), a') ∧
      StageR dn (r.headD 0) (fe.push (.thmInfo cv)) m' a' ∧ CoreMemos m' ∧ IWGrow m m' := by
  obtain ⟨wv, hwv, hwvl, rfl⟩ := hd?_some hv
  obtain ⟨wt, hwt, hwtl, hty⟩ := decCV_typeW hcv
  have hcb : c.toNat + 5 < 2 ^ 64 := erecP_bound hwv hS.stage.2
  have ev : rdW (m.arr64 EREC) (c + 5) = wv :=
    rdW_of_get? (toNat_add_small c 5 (by omega)).symm (erecP_get hwv)
  have et : rdW (m.arr64 EREC) (c + 4) = wt :=
    rdW_of_get? (toNat_add_small c 4 (by omega)).symm (erecP_get (by simpa [Nat.add_assoc] using hwt))
  have hc1 : (c + 1).toNat = c.toNat + 1 := toNat_add_small c 1 (by omega)
  have h00 : (0 : Word).toNat = 0 := rfl
  cases n with
  | zero => simp [tvW] at h
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  rw [tvW_step, ev, et] at h
  -- the type's type and sort
  cases h1 : realCall p n "infer_type_core" [vis, 0, wt] m with
  | none => rw [h1] at h; simp [tvK1] at h
  | some rm1 =>
  obtain ⟨r1, m1⟩ := rm1
  rw [h1, tvK1_some] at h
  obtain ⟨x1, a1, hrun1, hS1, hg1, hx1l, hx1⟩ := hq.inferTypeCore_sim n hn' hS 0 wt hwtl r1 m1 h1
  cases h2 : realCall p n "ensure_sort_core" [vis, 0, r1.headD 0] m1 with
  | none => rw [h2] at h; simp [tvK2] at h
  | some rm2 =>
  obtain ⟨r2, m2⟩ := rm2
  rw [h2, tvK2_some] at h
  obtain ⟨x2, a2, hrun2, hS2, hg2, hx2l, hx2⟩ :=
    hq.ensureSortCore_sim n hn' hS1 0 (r1.headD 0) hx1l r2 m2 h2
  -- the zero level
  cases h3 : pinWordW m2 53 with
  | none => rw [h3] at h; simp [tvK3] at h
  | some rm3 =>
  obtain ⟨r3, m3⟩ := rm3
  rw [h3, tvK3_some] at h
  have hflag : pinW m2 0 ≠ 0 := hS2.flag
  simp only [pinWordW, hflag, if_false, Option.some.injEq, Prod.mk.injEq] at h3
  obtain ⟨rfl, rfl⟩ := h3
  have hF := hS2.stage.1.pins.full hflag
  have hz : rdW (m2.arr64 PINS) 53 = pinW m2 53 := by simp [rdW, pinW]
  simp only [List.headD_cons, hz] at h
  -- the two levels read back
  obtain ⟨xs, hxs⟩ := ensureSort_view (r := pureFnsA V fe checkFuel) (fe := fe)
    (d := (0 : Word).toNat) (e := decI (r1.headD 0)) hrun2
  obtain ⟨lu, hdu⟩ := hS2.twin.den.sort _ _ hxs
  rw [← hx2] at hdu
  obtain ⟨lz, hdz⟩ := hS2.twin.den.zero
  rw [hF.zeroLevel] at hdz
  -- the comparison
  cases h4 : lfW (realCall p) n m2 (r2.headD 0) (pinW m2 53) with
  | none => rw [h4] at h; simp [tvK4] at h
  | some rm4 =>
  obtain ⟨r4, m4⟩ := rm4
  rw [h4, tvK4_some] at h
  obtain ⟨x4, a4, hrun4, hS4, hg4, hr4⟩ :=
    lfW_okT hq hL hpc h4 hS2 hx2l hF.lv_lt.2.1 lu lz hdu hdz
  by_cases hb4 : r4.headD 0 = 0
  · rw [if_pos hb4] at h; simp at h
  rw [if_neg hb4] at h
  have ex4 := hr4 hb4
  -- the value's guards, then the common tail
  cases h5 : ivgW n m4 vis (c + 1) wv with
  | none => rw [h5] at h; simp [dvK1] at h
  | some rm5 =>
  obtain ⟨r5, m5⟩ := rm5
  rw [h5] at h
  have hg14 := hg1.trans (hg2.trans hg4)
  obtain ⟨a5, hrun5, hS5, hg5⟩ :=
    hivg h5 hS4 (by rw [hc1]; exact ArrExt.decCV (IWGrow.erecExt hg14) hcv)
      (by rw [hc1]; omega) hwvl
  obtain ⟨a', hrun', hS', hM', hg'⟩ := dvK1_okT hq hRp hn' "type mismatch in theorem" h hS5
    (ArrExt.decCI (IWGrow.erecPExt (hg14.trans hg5)) hci) hcb hwvl hwtl hty
  refine ⟨a', ?_, hS', hM', hg14.trans (hg5.trans hg')⟩
  rw [h00, ← hty] at hrun1
  rw [h00, hx1] at hrun2
  rw [hx2, ex4] at hrun4
  rw [checkThmVal_eq]
  simp only [StateT.run_bind, hrun1, exc_ok_bind', hrun2, zeroLevel, pinZeroLevel_run hF, hrun4,
    liftFueled, StateT.run_pure, if_true, pure_bind]
  simp only [dvT, StateT.run_bind, hrun5, exc_ok_bind']
  simpa only [StateT.run_bind] using hrun'

end L.Arena
