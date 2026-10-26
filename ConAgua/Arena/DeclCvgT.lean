import ConAgua.Arena.DeclCvg
import ConAgua.Arena.IndRealWalkT
import ConAgua.Arena.KnotEntry
import ConAgua.Arena.StageTLift
import ConAgua.Arena.IndRealMemoCrT
import ConAgua.Arena.IndRealApdT
import ConAgua.Arena.CrOKFrame
import ConAgua.Final.Twin

/-!
# `check_value_group` under `StageT` (lane `loopt2`)

`DeclCvg.lean`'s relational lemma `cvgW_ok` runs the model from the stage relation, the core's
entry points read through their stubs (`stubCall`). Here the model reads the program's own calls
(`realCall p`) and runs from `StageT`: the knot's entry points under `StageT` (`KnotStageProg`,
lane `knotwire`), `lvl_eq_c` from lane `whnf`'s `lvlEqC_refines` (`lvlEqC_simT`), the pool writers
by their frames (`StageT.of_iw`), the value guards' walks by their real refinements (`apdF_okT`,
`crfF_okT`; helper `indproofs4-sw2`). `StageT` holds after it: the twin's invariants survive the
group's check, so the loop can carry them.
-/

noncomputable section

open ConRon.Arena

namespace L.Arena

open L.Ind

local notation "V" => ConLeche.CheckMode.verified

/-- `loose_bvars_bounded_fast`'s twin run keeps the store (it changes the per-call memos only). -/
theorem lbbF_store {f k : Nat} {e : EIdx} {a a' : AState} {x : Bool}
    (h : (looseBVarsBoundedFast f k e).run a = .ok (x, a')) : a'.store = a.store := by
  obtain ⟨X, rfl⟩ := memos_only_of_sp (Keeps.bind (keeps_bvarB_sp _ _) fun _ => Keeps.pure _) x a' h
  rfl

/-- `has_fvar_fast`'s twin run keeps the store. -/
theorem hffF_store {f : Nat} {e : EIdx} {a a' : AState} {x : Bool}
    (h : (hasFvarFast f e).run a = .ok (x, a')) : a'.store = a.store := by
  obtain ⟨X, rfl⟩ := memos_only_of_sp (Keeps.bind (keeps_fvarB_sp _ _) fun _ => Keeps.pure _) x a' h
  rfl

/-- **`install_value_guards` under `StageT`** (the statement `ivgW_okT` proves). -/
def IvgT (p : Prog) : Prop :=
  ∀ {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState} {n : Nat}
    {m m' : Mem} {q v : Word} {r : List Word} {cv : IConstantVal},
    ivgW (realCall p) n m vis q v = some (r, m') → StageT dn vis fe m a →
    decCV (erA m) q.toNat = some cv → q.toNat + 3 < 2 ^ 64 → v.toNat < 2 ^ 32 →
    (∃ ks, cv.levelParams.mapM (denoteN a.store.ns) = some ks) → L.Stubs.CrOK m →
    ∃ a', (installValueGuards fe cv (decI v)).run a = .ok ((), a') ∧ StageT dn vis fe m' a' ∧
      IWGrow m m' ∧ L.Stubs.CrOK m'

/-- **`install_value_guards` under `StageT`** (`ivgW_ok`'s): the copy by its frame
(`StageT.of_iw`), the four walks by their `StageT` refinements: `all_level_params_defined` by
`apdF_okT` (the parameters' names read back at the entry, the walks before it keeping the twin's
store), `consts_resolve_ffast` by `crfF_okT` (its memo `CrOK` carried across the copy and the walks
by their frames). -/
theorem ivgW_okT {p : Prog} (hap : ApdF p) (hkp : CrKeep p) : IvgT p := by
  intro dn vis fe a n m m' q v r cv h hS hq hqb hv hlps hCr
  obtain ⟨w1, w2, hw1, hw2, hsl⟩ := decCV_slice hq
  have e1 : rdW (m.arr64 EREC) (q + 1) = w1 :=
    rdW_of_get? (by rw [UInt64.toNat_add]; simp; omega) hw1
  have e2 : rdW (m.arr64 EREC) (q + 2) = w2 :=
    rdW_of_get? (by rw [UInt64.toNat_add]; simp; omega) hw2
  have hsrc : w2.toNat = 0 ∨ w1.toNat + w2.toNat ≤ (m.arr64 EREC).size := by
    rcases Nat.eq_zero_or_pos w2.toNat with h0 | h0
    · exact .inl h0
    · exact .inr (L.Ind.hslice?_bound _ _ _ _ hsl h0)
  cases n with
  | zero => simp [ivgW] at h
  | succ n =>
  cases n with
  | zero => simp [ivgW, cvLpsW, ivgK1] at h
  | succ n =>
  rw [ivgW_step, cvLpsW_step, e1, e2] at h
  cases h1 : erToIwW n m w1 w2 with
  | none => rw [h1] at h; simp [ivgK1] at h
  | some rm1 =>
  obtain ⟨r1, m1⟩ := rm1
  rw [h1, ivgK1_some] at h
  obtain ⟨-, hr1t, hdec1, hS1R, hg1, htop1⟩ := erToIwW_stage h1 hS.stage hsrc
  have hS1 := StageT.of_iw hS hS1R (erToIwW_frame h1 hS.stage hsrc)
  have hCr1 := CrOK.frame hCr (erToIwW_frame h1 hS.stage hsrc) (by decide) (by decide)
  cases h2 : lbbF m1 [4000000000, 0, v] with
  | none => rw [h2] at h; simp [ivgK2] at h
  | some rm2 =>
  obtain ⟨r2, m2⟩ := rm2
  rw [h2, ivgK2_some] at h
  have hCr2 := CrOK.frame hCr1 (lbbF_frame h2) (by decide) (by decide)
  obtain ⟨x2, a2, hrun2, hS2, hg2, hx2, -⟩ :=
    lbbF_okT dn vis fe 4000000000 0 v hv m1 m2 a r2 h2 hS1
  by_cases hb2 : r2.headD 0 = 0
  · rw [ite_eq_left hb2] at h; simp at h
  rw [ite_eq_right hb2] at h
  cases h3 : hffF m2 [4000000000, v] with
  | none => rw [h3] at h; simp [ivgK3] at h
  | some rm3 =>
  obtain ⟨r3, m3⟩ := rm3
  rw [h3, ivgK3_some] at h
  have hCr3 := CrOK.frame hCr2 (hffF_frame h3) (by decide) (by decide)
  obtain ⟨x3, a3, hrun3, hS3, hg3, hx3, -⟩ :=
    hffF_okT dn vis fe 4000000000 v hv m2 m3 a2 r3 h3 hS2
  by_cases hb3 : r3.headD 0 ≠ 0
  · rw [ite_eq_left hb3] at h; simp at h
  rw [ite_eq_right hb3] at h
  rw [hr1t] at h
  cases h4 : realCall p (n + 1) "all_level_params_defined" [r1.headD 0, w2, v] m3 with
  | none => rw [h4] at h; simp [ivgK4] at h
  | some rm4 =>
  obtain ⟨r4, m4⟩ := rm4
  rw [h4, ivgK4_some] at h
  have hdec3 : decHL m3 (r1.headD 0).toNat w2.toNat = some cv.levelParams := by
    rw [decHL_grow (hg2.trans hg3) (by omega), hdec1]; exact hsl
  have hst3 : a3.store = a.store := (hffF_store hrun3).trans (lbbF_store hrun2)
  have hCr4 := CrOK.frame hCr3 (apdF_frame (apdF_of_callW hap h4)) (by decide) (by decide)
  obtain ⟨x4, a4, hrun4, hS4, hg4, hx4, -⟩ :=
    apdF_okT dn vis fe (r1.headD 0) w2 v hv cv.levelParams m3 m4 a3 r4 (apdF_of_callW hap h4)
      ⟨hS3, hdec3, by rw [hst3]; exact hlps⟩
  by_cases hb4 : r4.headD 0 = 0
  · rw [ite_eq_left hb4] at h; simp at h
  rw [ite_eq_right hb4] at h
  cases h5 : realCall p (n + 1) "consts_resolve_ffast" [vis, v] m4 with
  | none => rw [h5] at h; simp [ivgK5] at h
  | some rm5 =>
  obtain ⟨r5, m5⟩ := rm5
  rw [h5, ivgK5_some] at h
  obtain ⟨x5, a5, hrun5, ⟨hS5, hg5, hx5, -⟩, hCr5⟩ :=
    crfF_okT dn vis fe v hv m4 m5 a4 r5 (crfF_of_callW hkp.crf h5) ⟨hS4, hCr4.crMemo⟩
  by_cases hb5 : r5.headD 0 = 0
  · rw [ite_eq_left hb5] at h; simp at h
  rw [ite_eq_right hb5] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  have ex2 : x2 = true := by rw [← hx2]; simpa using hb2
  have ex3 : x3 = false := by rw [← hx3]; simpa using hb3
  have ex4 : x4 = true := by rw [← hx4]; simpa using hb4
  have ex5 : x5 = true := by rw [← hx5]; simpa using hb5
  rw [fuelW] at hrun2 hrun3
  refine ⟨a5, ?_, hS5, hg1.trans (hg2.trans (hg3.trans (hg4.trans hg5))), hCr5.crOK⟩
  rw [show ((0 : Word).toNat) = 0 from rfl] at hrun2
  simp only [installValueGuards, StateT.run_bind, hrun2, exc_ok_bind', ex2, hrun3, ex3, hrun4,
    ex4, hrun5, ex5, ite_true, Bool.false_eq_true, ite_false, StateT.run_pure]
  rfl

/-- The memory after `iw_reset` keeps `StageT`. -/
theorem iwReset_stageT {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem}
    {a : AState} (hT : StageT dn vis fe m a) : StageT dn vis fe (m.set64 CTL 200 0) a :=
  StageT.of_iw hT (iwReset_stage hT.stage).1
    (MemFrame.mono (MemFrame.setCtl m 200 0) (by simp) (by simp))

/-- **The theorem test's prefix extends the twin's store** (con-ron's `KnotSpec.infer` and
`EnsureSortSpec`, as in `checkValueGroup_bridge`): from `CheckOK` and the constant's type denoting
in scope. -/
theorem thmPrefix_ext {env : ConLeche.Env} {fe : IFEnv} {a a1 a2 : AState} {cv : IConstantVal}
    {cP : ConLeche.ConstantVal} {x1 : EIdx} {x2 : LIdx} (henv : ConLeche.EnvWF env)
    (hck : ConRon.Bridge.CheckOK V env fe a) (hcv : Frontend.denoteCV a.store cv = some cP)
    (hws : ConLeche.Expr.WScoped 0 cP.type)
    (h1 : (inferTypeCore V fe checkFuel 0 cv.type).run a = .ok (x1, a1))
    (h2 : (ensureSortCore V fe checkFuel 0 x1).run a1 = .ok (x2, a2)) :
    ConRon.Bridge.CheckOK V env fe a2 ∧ Ext a.store a2.store := by
  obtain ⟨-, -, hty0⟩ := ConRon.Bridge.Core.denoteCV_inv hcv
  obtain ⟨hcka, hxa, -, sty, hsty, hwssty, -⟩ := ConRon.Bridge.AM.of_run (P := fun t => t = a) rfl h1
    (((ConRon.Bridge.CoreSpec.of_core rfl).knot env fe henv).infer a 0 cv.type cP.type hck hty0 hws)
  obtain ⟨hckb, hxb, -, -⟩ := ConRon.Bridge.AM.of_run (P := fun t => t = a1) rfl h2
    (((ConRon.Bridge.CoreSpec.of_core rfl).sort env fe henv) a1 0 x1 sty hcka hsty hwssty)
  exact ⟨hckb, hxa.trans hxb⟩

/-- **`check_value_group` refines `checkValueGroup .verified` under `StageT`**, at the model
level, from the memory after `iw_reset`: the program's own calls of the core (`realCall p`). -/
theorem cvgW_okT {p : Prog} (hq : KnotStageProg p) (hL : LvlCacheProg p)
    (hpc : p.lookup "lvl_eq_c" = some lvlEqCL) (hap : ApdF p) (hkp : CrKeep p)
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} (hn : n ≤ 2 ^ 62) {m m' : Mem} {g : Word} {r : List Word} {vg : ValueGroup}
    (h : cvgW (realCall p) n m vis g = some (r, m')) (hS : StageT dn vis fe m a)
    (hg : decVG (erecP m) g.toNat = some vg) (hCr : L.Stubs.CrOK m)
    (hthm : vg.kind = .thm → ∃ env cP, ConLeche.EnvWF env ∧ ConRon.Bridge.CheckOK V env fe a ∧
      Frontend.denoteCV a.store vg.cv = some cP ∧ ConLeche.Expr.WScoped 0 cP.type) :
    ∃ a', (checkValueGroup V fe vg).run a = .ok ((), a') ∧ StageT dn vis fe m' a' ∧
      IWGrow (m.set64 CTL 200 0) m' ∧ L.Stubs.CrOK m' := by
  cases n with
  | zero => simp [cvgW] at h
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  rw [cvgW_step, show iwResetW m = some ([], m.set64 CTL 200 0) from rfl, cvgK0_some] at h
  have hCr0 : L.Stubs.CrOK (m.set64 CTL 200 0) :=
    CrOK.frame hCr (MemFrame.setCtl m 200 0) (by simp) (by decide)
  generalize hm0 : m.set64 CTL 200 0 = m0 at h hCr0
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
  have hCr1 := hkp.call (im_mem _ rfl) h1 hCr0
  obtain ⟨x1, a1, hrun1, hS1, hg1, hx1l, hx1⟩ := hq.inferTypeCore_sim n hn' hS0 0 wt hwtl r1 m1 h1
  -- `ensure_sort_core(vis, 0, st)`
  cases h2 : realCall p n "ensure_sort_core" [vis, 0, r1.headD 0] m1 with
  | none => rw [h2] at h; simp [cvgK2] at h
  | some rm2 =>
  obtain ⟨r2, m2⟩ := rm2
  rw [h2, cvgK2_some] at h
  have hCr2 := hkp.call (im_mem _ rfl) h2 hCr1
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
      L.Stubs.CrOK m5 → cvgK6 (realCall p) n vis wt wj m5 = some (r, m') →
      ∃ a', (do
          let vtype ← inferTypeCore V fe checkFuel 0 vg.jv
          unless ← isDefEqCore V fe checkFuel 0 vtype vg.cv.type do
            fail (.invalid s!"type mismatch in {vg.kind.word}") : AM Unit).run a5 = .ok ((), a') ∧
        StageT dn vis fe m' a' ∧ IWGrow m0 m' ∧ L.Stubs.CrOK m' := by
    intro m5 a5 hS5 hg5 hCr5 h
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
    have hCr8 := hkp.call (im_mem _ rfl) h8 (hkp.call (im_mem _ rfl) h7 hCr5)
    obtain ⟨x8, a8, hrun8, hS8, hg8, hx8⟩ :=
      hq.isDefEqCore_sim n hn' hS7 0 (r7.headD 0) wt hx7l hwtl r8 m8 h8
    by_cases hb8 : r8.headD 0 = 0
    · rw [ite_eq_left hb8] at h; simp at h
    rw [ite_eq_right hb8] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    have ex8 : x8 = true := by rw [← hx8]; simpa [decBool] using hb8
    rw [h00, ← hjv] at hrun7
    rw [h00, hx7, ← hty] at hrun8
    refine ⟨a8, ?_, hS8, hg5.trans (hg7.trans hg8), hCr8⟩
    simp only [StateT.run_bind, hrun7, exc_ok_bind', hrun8, ex8, ite_true, StateT.run_pure]
    rfl
  by_cases hk1 : wk = 1
  · -- a theorem: the proposition test and the value's guards
    rw [ite_eq_left hk1] at h
    subst hk1
    have hkind : vg.kind = .thm := by simpa [decVK] using hvk.symm
    cases h3 : pinWordW m2 53 with
    | none => rw [h3] at h; simp [cvgK3] at h
    | some rm3 =>
    obtain ⟨r3, m3⟩ := rm3
    rw [h3, cvgK3_some] at h
    have hflag : pinW m2 0 ≠ 0 := hS2.flag
    simp only [pinWordW, hflag, ite_false, Option.some.injEq, Prod.mk.injEq] at h3
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
    have hCr4 := hkp.call (im_mem _ rfl) h4 hCr2
    obtain ⟨x4, a4, hrun4, hS4, hg4, hx4, -⟩ :=
      lvlEqC_simT p hq.closed hL hpc n hS2 (r2.headD 0) (pinW m2 53) hx2l hF.lv_lt.2.1 lu lz hdu hdz r4 m4 h4
    -- the parameters' names read back at the guards: the prefix extends the store
    have hlps4 : ∃ ks, vg.cv.levelParams.mapM (denoteN a4.store.ns) = some ks := by
      obtain ⟨env, cP, henv, hck, hcvd, hws⟩ := hthm hkind
      obtain ⟨hck2, hx02⟩ := thmPrefix_ext henv hck hcvd hws hrun1 hrun2
      obtain ⟨-, hst4, -⟩ := ConRon.Bridge.AM.of_run (P := fun t => t = a2) rfl hrun4
        (ConRon.Bridge.Core.lvlEq?_spec a2 _ _ hck2)
      rw [hst4]
      exact denoteCV_lps (ConRon.Bridge.denoteCV_ext hcvd hx02)
    by_cases hb4 : r4.headD 0 ≠ 2
    · rw [ite_eq_left hb4] at h; simp at h
    rw [ite_eq_right hb4] at h
    have ex4 : x4 = some true := by
      have : r4.headD 0 = 2 := by simpa using hb4
      rw [← hx4, this]; rfl
    cases h5 : ivgW (realCall p) n m4 vis (g + 1) wj with
    | none => rw [h5] at h; simp [cvgK5] at h
    | some rm5 =>
    obtain ⟨r5, m5⟩ := rm5
    rw [h5, cvgK5_some] at h
    have hg1' : (g + 1).toNat = g.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have hcv4 : decCV (erA m4) (g + 1).toNat = some vg.cv := by
      rw [hg1']
      exact ArrExt.decCV (IWGrow.erecExt (hg1.trans (hg2.trans hg4))) hcv
    obtain ⟨a5, hrun5, hS5, hg5, hCr5⟩ :=
      ivgW_okT hap hkp h5 hS4 hcv4 (by rw [hg1']; omega) hwjl hlps4 hCr4
    obtain ⟨a', hrun', hS', hg', hCr'⟩ :=
      tail m5 a5 hS5 (hg1.trans (hg2.trans (hg4.trans hg5))) hCr5 h
    refine ⟨a', ?_, hS', hg', hCr'⟩
    rw [hx2] at hrun4
    rw [← hjv] at hrun5
    rw [ex4] at hrun4
    rw [hkind] at hrun'
    simp only [checkValueGroup, StateT.run_bind, hrun1, exc_ok_bind', hrun2, hkind,
      show (ValueKind.thm == ValueKind.thm) = true from rfl, ite_true, zeroLevel,
      pinZeroLevel_run hF, hrun4, liftFueled, StateT.run_pure]
    simp only [pure_bind, ite_true, StateT.run_bind, hrun5, exc_ok_bind']
    exact hrun'
  · rw [ite_eq_right hk1] at h
    have hkind : vg.kind ≠ .thm := by
      intro hk; rw [hk] at hvk
      have : wk.toNat = 1 := by
        unfold decVK at hvk; split at hvk <;> simp_all
      exact hk1 (UInt64.toNat_inj.mp (by simpa using this))
    obtain ⟨a', hrun', hS', hg', hCr'⟩ := tail m2 a2 hS2 (hg1.trans hg2) hCr2 h
    refine ⟨a', ?_, hS', hg', hCr'⟩
    have hb : (vg.kind == ValueKind.thm) = false := by
      revert hkind; cases vg.kind <;> decide
    simp only [checkValueGroup, StateT.run_bind, hrun1, exc_ok_bind', hrun2, hb,
      Bool.false_eq_true, ite_false]
    exact hrun'

end L.Arena
