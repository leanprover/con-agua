import ConAgua.Arena.DeclValRef
import ConAgua.Arena.DeclCvgT
import ConAgua.Arena.IndT.WalkC
import ConAgua.Arena.DeclStepSpec
import ConAgua.Arena.DeclValSpec
import ConAgua.Verdict.LefRef

/-!
# The value checks under `StageT` (lane `loopt2`)

`DeclValRef.lean`'s relational lemmas run the value checks' models from the stage relation, the
core's entry points read through their stubs. Here they read the program's own calls
(`realCall p`) and run from `StageT`, as `check_value_group` does (`DeclCvgT.lean`). The value
checks end with `env_push`, which changes the environment; after it the stage relation holds at
the extended environment and the core's memos are still well formed (`CoreMemos`: `env_push`
writes the index rows, `ECON` and `CTL[128]` only), which is what the loop carries to the next
declaration.
-/

open ConRon.Arena

namespace L.Arena

open L.Ind

local notation "V" => ConLeche.CheckMode.verified

/-- **`env_push` writes the index rows, `ECON` and its count** (`CTL[128]`). -/
theorem envPushW_frame {m m' : Mem} {vis q : Word} {r : List Word}
    (h : envPushW m vis q = some (r, m')) :
    MemFrame [EIXA, EIXS, EIXN, ECON, EIXA1, EIXS1, EIXN1] [128] m m' := by
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
  have hrow : (rowArr (rdW (m.arr64 EREC) (q + 1)) : TieredArray) ∈
      ([EIXA, EIXS, EIXN, ECON, EIXA1, EIXS1, EIXN1] : List TieredArray) := by
    rcases rowArr_names (rdW (m.arr64 EREC) (q + 1)) with h | h | h | h | h | h <;> rw [h] <;> decide
  have hf1 : MemFrame [EIXA, EIXS, EIXN, ECON, EIXA1, EIXS1, EIXN1] [128] m
      (rowSet m (rdW (m.arr64 EREC) (q + 1)) (vis + 1) q) := by
    unfold rowSet
    exact ((MemFrame.set64 m _ (TieredArray.t0_ne (rowArr_ne _ (by decide))) _ _).mono
      (by intro b hb; simp at hb; subst hb; exact hrow) (by simp)).trans
      ((MemFrame.set64 _ _ (TieredArray.t0_ne (rowArr_ne _ (by decide))) _ _).mono
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
  · rw [ite_eq_left hb3] at h; simp at h
  rw [ite_eq_right hb3] at h
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
  simp only [StateT.run_bind, hrun2, exc_ok_bind', hrun3, ex3, ite_true, StateT.run_pure]
  rfl

/-- **`check_thm_val` under `StageT`** (`tvW_ok`'s). -/
theorem tvW_okT {p : Prog} (hq : KnotStageProg p) (hRp : RecProg p) (hL : LvlCacheProg p)
    (hlef : p.lookup "lvl_eq_fueled" = some lvlEqFueled) (hap : ApdF p) (hkp : CrKeep p)
    {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {a : AState} {n : Nat} (hn : n ≤ 2 ^ 62) {m m' : Mem} {c : Word} {r : List Word}
    {cv : IConstantVal} {v : EIdx}
    (h : tvW p (realCall p) n m vis c = some (r, m')) (hS : StageT dn vis fe m a)
    (hci : decCI (erecP m) dn c.toNat = some (.thmInfo cv))
    (hcv : decCV (erecP m) (c.toNat + 1) = some cv)
    (hv : hd? (erecP m) (c.toNat + 5) = some v)
    (hpre : ∃ env cP, ConLeche.EnvWF env ∧ ConRon.Bridge.CheckOK V env fe a ∧
      Frontend.denoteCV a.store cv = some cP ∧ ConLeche.Expr.WScoped 0 cP.type)
    (hCr : L.Stubs.CrOK m) :
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
  have hCr1 := hkp.call (im_mem _ rfl) h1 hCr
  obtain ⟨x1, a1, hrun1, hS1, hg1, hx1l, hx1⟩ := hq.inferTypeCore_sim n hn' hS 0 wt hwtl r1 m1 h1
  cases h2 : realCall p n "ensure_sort_core" [vis, 0, r1.headD 0] m1 with
  | none => rw [h2] at h; simp [tvK2] at h
  | some rm2 =>
  obtain ⟨r2, m2⟩ := rm2
  rw [h2, tvK2_some] at h
  have hCr2 := hkp.call (im_mem _ rfl) h2 hCr1
  obtain ⟨x2, a2, hrun2, hS2, hg2, hx2l, hx2⟩ :=
    hq.ensureSortCore_sim n hn' hS1 0 (r1.headD 0) hx1l r2 m2 h2
  -- the zero level
  cases h3 : pinWordW m2 53 with
  | none => rw [h3] at h; simp [tvK3] at h
  | some rm3 =>
  obtain ⟨r3, m3⟩ := rm3
  rw [h3, tvK3_some] at h
  have hflag : pinW m2 0 ≠ 0 := hS2.flag
  simp only [pinWordW, hflag, ite_false, Option.some.injEq, Prod.mk.injEq] at h3
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
  cases h4 : realCall p n "lvl_eq_fueled" [r2.headD 0, pinW m2 53] m2 with
  | none => rw [h4] at h; simp [tvK4] at h
  | some rm4 =>
  obtain ⟨r4, m4⟩ := rm4
  rw [h4, tvK4_some] at h
  have hCr4 := hkp.call (im_mem _ rfl) h4 hCr2
  obtain ⟨s4, hs4, -, b4, a4, -, ⟨hrun4, hr4, hS4, hg4, -, -⟩⟩ :=
    RefE.run_okW (lefE_spec p hlef n ⟨m2, Locals.init []⟩ _ _)
      (lef_ref hq.closed hL n hS2 hx2l hF.lv_lt.2.1 hdu hdz) h4
  rw [hs4] at hS4 hg4
  -- the parameters' names read back at the guards: the prefix extends the store
  have hlps4 : ∃ ks, cv.levelParams.mapM (denoteN a4.store.ns) = some ks := by
    obtain ⟨env, cP, henv, hck, hcvd, hws⟩ := hpre
    have hr1 := hrun1
    rw [h00, ← hty] at hr1
    have hr2 := hrun2
    rw [hx1] at hr2
    obtain ⟨hck2, hx02⟩ := thmPrefix_ext henv hck hcvd hws hr1 hr2
    obtain ⟨-, hst4, -⟩ := ConRon.Bridge.AM.of_run (P := fun t => t = a2) rfl hrun4
      (ConRon.Bridge.Core.lvlEq?_spec a2 _ _ hck2)
    rw [hst4]
    exact denoteCV_lps (ConRon.Bridge.denoteCV_ext hcvd hx02)
  by_cases hb4 : r4.headD 0 = 0
  · rw [ite_eq_left hb4] at h; simp at h
  rw [ite_eq_right hb4] at h
  have ex4 : b4 = true := by
    dsimp only at hr4
    cases b4
    · exact absurd hr4 (by simpa using hb4)
    · rfl
  -- the value's guards, then the common tail
  cases h5 : ivgW (realCall p) n m4 vis (c + 1) wv with
  | none => rw [h5] at h; simp [dvK1] at h
  | some rm5 =>
  obtain ⟨r5, m5⟩ := rm5
  rw [h5] at h
  have hg14 := hg1.trans (hg2.trans hg4)
  obtain ⟨a5, hrun5, hS5, hg5, -⟩ :=
    ivgW_okT hap hkp h5 hS4 (by rw [hc1]; exact ArrExt.decCV (IWGrow.erecExt hg14) hcv)
      (by rw [hc1]; omega) hwvl hlps4 hCr4
  obtain ⟨a', hrun', hS', hM', hg'⟩ := dvK1_okT hq hRp hn' "type mismatch in theorem" h hS5
    (ArrExt.decCI (IWGrow.erecPExt (hg14.trans hg5)) hci) hcb hwvl hwtl hty
  refine ⟨a', ?_, hS', hM', hg14.trans (hg5.trans hg')⟩
  rw [h00, ← hty] at hrun1
  rw [h00, hx1] at hrun2
  rw [hx2, ex4] at hrun4
  rw [checkThmVal_eq]
  simp only [StateT.run_bind, hrun1, exc_ok_bind', hrun2, zeroLevel, pinZeroLevel_run hF, hrun4,
    liftFueled, StateT.run_pure, ite_true, pure_bind]
  simp only [dvT, StateT.run_bind, hrun5, exc_ok_bind']
  simpa only [StateT.run_bind] using hrun'

end L.Arena
