import ConAgua.Arena.DeclCvg
import ConAgua.Arena.KnotEntry

/-!
# `check_value_group` under `StageT` (lane `loopt2`)

`DeclCvg.lean`'s relational lemma `cvgW_ok` runs the model from the stage relation, the core's
entry points read through their stubs (`stubCall`). Here the model reads the program's own calls
(`realCall p`) and runs from `StageT`: the knot's entry points under `StageT` (`KnotStageProg`,
lane `knotwire`), `lvl_eq_c` from lane `whnf`'s `lvlEqC_refines` (`lvlEqC_simT`), the pool writers
by their frames (`StageT.of_iw`). `StageT` holds after it: the twin's invariants survive the
group's check, so the loop can carry them (open end 4, `docs/design/loopt2.md`).
-/

open ConRon.Arena

namespace L.Arena

open L.Ind

local notation "V" => ConLeche.CheckMode.verified

/-- **`install_value_guards` under `StageT`** (what `cvgW_okT` needs of it; lane `indproofs3`'s
`StageT` contracts of the four walks give it, `ivgW_okT`). -/
def IvgT : Prop :=
  ∀ {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState} {n : Nat}
    {m m' : Mem} {q v : Word} {r : List Word} {cv : IConstantVal},
    ivgW n m vis q v = some (r, m') → StageT dn vis fe m a →
    decCV (erA m) q.toNat = some cv → q.toNat + 3 < 2 ^ 64 → v.toNat < 2 ^ 32 →
    ∃ a', (installValueGuards fe cv (decI v)).run a = .ok ((), a') ∧ StageT dn vis fe m' a' ∧
      IWGrow m m'

/-- The memory after `iw_reset` keeps `StageT`. -/
theorem iwReset_stageT {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem}
    {a : AState} (hT : StageT dn vis fe m a) : StageT dn vis fe (m.set64 CTL 200 0) a :=
  StageT.of_iw hT (iwReset_stage hT.stage).1
    (MemFrame.mono (MemFrame.setCtl m 200 0) (by simp) (by simp))

/-- **`check_value_group` refines `checkValueGroup .verified` under `StageT`**, at the model
level, from the memory after `iw_reset`: the program's own calls of the core (`realCall p`). -/
theorem cvgW_okT {p : Prog} (hq : KnotStageProg p) (hL : LvlCacheProg p)
    (hpc : p.lookup "lvl_eq_c" = some lvlEqCL) (hivg : IvgT)
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} (hn : n ≤ 2 ^ 62) {m m' : Mem} {g : Word} {r : List Word} {vg : ValueGroup}
    (h : cvgW (realCall p) n m vis g = some (r, m')) (hS : StageT dn vis fe m a)
    (hg : decVG (erecP m) g.toNat = some vg) :
    ∃ a', (checkValueGroup V fe vg).run a = .ok ((), a') ∧ StageT dn vis fe m' a' ∧
      IWGrow (m.set64 CTL 200 0) m' := by
  cases n with
  | zero => simp [cvgW] at h
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  rw [cvgW_step, show iwResetW m = some ([], m.set64 CTL 200 0) from rfl, cvgK0_some] at h
  generalize hm0 : m.set64 CTL 200 0 = m0 at h
  have hS0 := iwReset_stageT hS
  obtain ⟨-, -, hE0, -⟩ := iwReset_stage hS.stage
  rw [hm0] at hS0 hE0
  have hP0 : erecP m0 = erecP m := by rw [← hm0]; exact erecP_reset m
  rw [← hP0] at hg
  have hEs := hS0.stage.2.2.2.2.1
  obtain ⟨⟨wk, hwk, hvk⟩, hcv, wj, hwj, hwjl, hjv⟩ := decVG_words hg
  obtain ⟨wt, hwt, hwtl, hty⟩ := decCV_typeW hcv
  have hb5 : g.toNat + 5 < (m0.arr64 EREC).size := by
    have := (Array.getElem?_eq_some_iff.mp (erecP_get hwj)).1; exact this
  have et : rdW (m0.arr64 EREC) (g + 4) = wt :=
    rdW_of_get? (k := g.toNat + 4) (by rw [UInt64.toNat_add]; simp; omega)
      (erecP_get (by simpa [Nat.add_assoc] using hwt))
  have ev : rdW (m0.arr64 EREC) (g + 5) = wj :=
    rdW_of_get? (k := g.toNat + 5) (by rw [UInt64.toNat_add]; simp; omega) (erecP_get hwj)
  rw [et, ev] at h
  -- `infer_type_core(vis, 0, t)`
  cases h1 : realCall p n "infer_type_core" [vis, 0, wt] m0 with
  | none => rw [h1] at h; simp [cvgK1] at h
  | some rm1 =>
  obtain ⟨r1, m1⟩ := rm1
  rw [h1, cvgK1_some] at h
  obtain ⟨x1, a1, hrun1, hS1, hg1, hx1l, hx1⟩ := hq.inferTypeCore_sim n hn' hS0 0 wt hwtl r1 m1 h1
  -- `ensure_sort_core(vis, 0, st)`
  cases h2 : realCall p n "ensure_sort_core" [vis, 0, r1.headD 0] m1 with
  | none => rw [h2] at h; simp [cvgK2] at h
  | some rm2 =>
  obtain ⟨r2, m2⟩ := rm2
  rw [h2, cvgK2_some] at h
  obtain ⟨x2, a2, hrun2, hS2, hg2, hx2l, hx2⟩ :=
    hq.ensureSortCore_sim n hn' hS1 0 (r1.headD 0) hx1l r2 m2 h2
  have hext2 : ArrExt (erecP m0) (erA m2) := IWGrow.erecExt (hg1.trans hg2)
  have ek : rdW (m2.arr64 EREC) g = wk := rdW_of_get? rfl (hext2 _ _ hwk)
  rw [ek] at h
  have h00 : (0 : Word).toNat = 0 := rfl
  rw [h00] at hrun1 hrun2
  rw [← hty] at hrun1
  rw [hx1] at hrun2
  -- the tail: `infer_type_core(vis, 0, v)`, `is_def_eq_core(vis, 0, vt, t)`
  have tail : ∀ (m5 : Mem) (a5 : AState), StageT dn vis fe m5 a5 → IWGrow m0 m5 →
      cvgK6 (realCall p) n vis wt wj m5 = some (r, m') →
      ∃ a', (do
          let vtype ← inferTypeCore V fe checkFuel 0 vg.jv
          unless ← isDefEqCore V fe checkFuel 0 vtype vg.cv.type do
            fail (.invalid s!"type mismatch in {vg.kind.word}") : AM Unit).run a5 = .ok ((), a') ∧
        StageT dn vis fe m' a' ∧ IWGrow m0 m' := by
    intro m5 a5 hS5 hg5 h
    rw [cvgK6_eq] at h
    cases h7 : realCall p n "infer_type_core" [vis, 0, wj] m5 with
    | none => rw [h7] at h; simp [cvgK7] at h
    | some rm7 =>
    obtain ⟨r7, m7⟩ := rm7
    rw [h7, cvgK7_some] at h
    obtain ⟨x7, a7, hrun7, hS7, hg7, hx7l, hx7⟩ :=
      hq.inferTypeCore_sim n hn' hS5 0 wj hwjl r7 m7 h7
    cases h8 : realCall p n "is_def_eq_core" [vis, 0, r7.headD 0, wt] m7 with
    | none => rw [h8] at h; simp [cvgK8] at h
    | some rm8 =>
    obtain ⟨r8, m8⟩ := rm8
    rw [h8, cvgK8_some] at h
    obtain ⟨x8, a8, hrun8, hS8, hg8, hx8⟩ :=
      hq.isDefEqCore_sim n hn' hS7 0 (r7.headD 0) wt hx7l hwtl r8 m8 h8
    by_cases hb8 : r8.headD 0 = 0
    · rw [if_pos hb8] at h; simp at h
    rw [if_neg hb8] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    have ex8 : x8 = true := by rw [← hx8]; simpa [decBool] using hb8
    rw [h00, ← hjv] at hrun7
    rw [h00, hx7, ← hty] at hrun8
    refine ⟨a8, ?_, hS8, hg5.trans (hg7.trans hg8)⟩
    simp only [StateT.run_bind, hrun7, exc_ok_bind', hrun8, ex8, if_true, StateT.run_pure]
    rfl
  by_cases hk1 : wk = 1
  · -- a theorem: the proposition test and the value's guards
    rw [if_pos hk1] at h
    subst hk1
    have hkind : vg.kind = .thm := by simpa [decVK] using hvk.symm
    cases h3 : pinWordW m2 53 with
    | none => rw [h3] at h; simp [cvgK3] at h
    | some rm3 =>
    obtain ⟨r3, m3⟩ := rm3
    rw [h3, cvgK3_some] at h
    have hflag : pinW m2 0 ≠ 0 := hS2.flag
    simp only [pinWordW, hflag, if_false, Option.some.injEq, Prod.mk.injEq] at h3
    obtain ⟨rfl, rfl⟩ := h3
    have hF := hS2.stage.1.pins.full hflag
    have hz : rdW (m2.arr64 PINS) 53 = pinW m2 53 := by simp [rdW, pinW]
    simp only [List.headD_cons, hz] at h
    -- the two levels read back: the sort's level, the pinned zero
    obtain ⟨xs, hxs⟩ := ensureSort_view (r := pureFnsA V fe checkFuel) (fe := fe) (d := 0)
      (e := x1) hrun2
    obtain ⟨lu, hdu⟩ := hS2.twin.den.sort _ _ hxs
    rw [← hx2] at hdu
    obtain ⟨lz, hdz⟩ := hS2.twin.den.zero
    rw [hF.zeroLevel] at hdz
    cases h4 : realCall p n "lvl_eq_c" [r2.headD 0, pinW m2 53] m2 with
    | none => rw [h4] at h; simp [cvgK4] at h
    | some rm4 =>
    obtain ⟨r4, m4⟩ := rm4
    rw [h4, cvgK4_some] at h
    obtain ⟨x4, a4, hrun4, hS4, hg4, hx4, -⟩ :=
      lvlEqC_simT p hq.closed hL hpc n hS2 (r2.headD 0) (pinW m2 53) hx2l hF.lv_lt.2.1 lu lz hdu hdz r4 m4 h4
    by_cases hb4 : r4.headD 0 ≠ 2
    · rw [if_pos hb4] at h; simp at h
    rw [if_neg hb4] at h
    have ex4 : x4 = some true := by
      have : r4.headD 0 = 2 := by simpa using hb4
      rw [← hx4, this]; rfl
    cases h5 : ivgW n m4 vis (g + 1) wj with
    | none => rw [h5] at h; simp [cvgK5] at h
    | some rm5 =>
    obtain ⟨r5, m5⟩ := rm5
    rw [h5, cvgK5_some] at h
    have hg1' : (g + 1).toNat = g.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have hcv4 : decCV (erA m4) (g + 1).toNat = some vg.cv := by
      rw [hg1']
      exact ArrExt.decCV (IWGrow.erecExt (hg1.trans (hg2.trans hg4))) hcv
    obtain ⟨a5, hrun5, hS5, hg5⟩ := hivg h5 hS4 hcv4 (by rw [hg1']; omega) hwjl
    obtain ⟨a', hrun', hS', hg'⟩ :=
      tail m5 a5 hS5 (hg1.trans (hg2.trans (hg4.trans hg5))) h
    refine ⟨a', ?_, hS', hg'⟩
    rw [hx2] at hrun4
    rw [← hjv] at hrun5
    rw [ex4] at hrun4
    rw [hkind] at hrun'
    simp only [checkValueGroup, StateT.run_bind, hrun1, exc_ok_bind', hrun2, hkind,
      show (ValueKind.thm == ValueKind.thm) = true from rfl, if_true, zeroLevel,
      pinZeroLevel_run hF, hrun4, liftFueled, StateT.run_pure, hrun5]
    simp only [pure_bind, if_true, StateT.run_bind, hrun5, exc_ok_bind']
    exact hrun'
  · rw [if_neg hk1] at h
    have hkind : vg.kind ≠ .thm := by
      intro hk; rw [hk] at hvk
      have : wk.toNat = 1 := by
        unfold decVK at hvk; split at hvk <;> simp_all
      exact hk1 (UInt64.toNat_inj.mp (by simpa using this))
    obtain ⟨a', hrun', hS', hg'⟩ := tail m2 a2 hS2 (hg1.trans hg2) h
    refine ⟨a', ?_, hS', hg'⟩
    have hb : (vg.kind == ValueKind.thm) = false := by
      revert hkind; cases vg.kind <;> decide
    simp only [checkValueGroup, StateT.run_bind, hrun1, exc_ok_bind', hrun2, hb,
      Bool.false_eq_true, if_false]
    exact hrun'

end L.Arena
