import ConAgua.Arena.DeclNatSub
import ConAgua.Arena.DeclDivModSpec.SubstConst0List

/-!
# The structural-`Nat` gate: constant substitution under binders (lane `decls4`, helper `decls4-sca`)

`subst_const_all` refines `substConstAll`, after `DeclNatSub`'s `subst_const0`: the model `scaW` of
one call, then the refinement by induction on the twin's fuel. The binary arms (`app`, `lam`,
`forallE`) share `sca_bin`; `letE` and `proj` have their own.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem scaGetD3 (r : List Word) : r.getD 3 0 = r.tail.tail.tail.headD 0 := by
  rcases r with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩ <;> rfl

section suball
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}

structure NatSubAllProg (p : Prog) : Prop extends NatSubProg p where
  lSubstConstAll : p.lookup "subst_const_all" = some substConstAllL

/-- **`subst_const_all` is its model `scaW`** (generated). -/
l_model sca_specW (p : Prog) (hp : p.lookup "subst_const_all" = some substConstAllL)
  fns [hp ↦ scaW list]
  specs [callW_spec p n "e_view", callW_spec p n "pin_word", callW_spec p n "subst_const_all", callW_spec p n "mk_app", callW_spec p n "mk_lam", callW_spec p n "mk_forall", callW_spec p n "mk_let", callW_spec p n "mk_proj"]
  grind [arena_grind] finish [ntBW] gen 20 bind ntBW instances 10000

/-- The induction hypothesis of `sca_ref`: every returning call at a fuel word of value `f`. -/
def ScaIH (p : Prog) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (nm r : Word)
    (f : Nat) : Prop :=
  ∀ (fuel : Word), fuel.toNat = f → ∀ (h : Word) (k : Nat) (m : Mem) (a : AState)
    (res : List Word) (m' : Mem), StageR dn vis fe m a → H nm → H r → H h →
    callW p k "subst_const_all" [nm, r, fuel, h] m = some (res, m') →
    ∃ x a', (substConstAll (decI nm) (decE r) f (decE h)).run a = .ok (x, a') ∧
      KeepPost dn vis fe decW0E m m' a' res x

/-- A binary arm: both children, then the interner `mk` (refining `I`). -/
theorem sca_bin {nm r : Word} {f : Nat} (ih : ScaIH p dn vis fe nm r f) (mk : FnName)
    (I : EIdx → EIdx → AM EIdx)
    (hmk : ∀ t b, CallRef p mk [t, b] (StageR dn vis fe) (I (decE t) (decE b))
      (KeepPost dn vis fe decW0E))
    {fuel x y : Word} (hf : (fuel - 1).toNat = f) {k : Nat} {m1 : Mem} {a1 : AState}
    {res : List Word} {m' : Mem} (hS1 : StageR dn vis fe m1 a1) (hn : H nm) (hr : H r)
    (hx : H x) (hy : H y)
    (hw : (ntBW (callW p k "subst_const_all" [nm, r, fuel - 1, x] m1) fun r1 m2 =>
      ntBW (callW p k "subst_const_all" [nm, r, fuel - 1, y] m2) fun r2 m3 =>
      ntBW (callW p k mk [r1.headD 0, r2.headD 0] m3) fun r3 m4 => some ([r3.headD 0], m4)) =
      some (res, m')) :
    ∃ e a', (do
        let f' ← substConstAll (decI nm) (decE r) f (decE x)
        let a' ← substConstAll (decI nm) (decE r) f (decE y)
        I f' a').run a1 = .ok (e, a') ∧ KeepPost dn vis fe decW0E m1 m' a' res e := by
  cases h2 : callW p k "subst_const_all" [nm, r, fuel - 1, x] m1 with
  | none => rw [h2] at hw; simp [ntBW] at hw
  | some q2 =>
  obtain ⟨r1, m2⟩ := q2
  rw [h2, bW_some] at hw
  obtain ⟨x2, a2, hrun2, hS2, hg2, hl2, hx2⟩ := ih (fuel - 1) hf x k m1 a1 r1 m2 hS1 hn hr hx h2
  cases h3 : callW p k "subst_const_all" [nm, r, fuel - 1, y] m2 with
  | none => rw [h3] at hw; simp [ntBW] at hw
  | some q3 =>
  obtain ⟨r2, m3⟩ := q3
  rw [h3, bW_some] at hw
  obtain ⟨x3, a3, hrun3, hS3, hg3, hl3, hx3⟩ := ih (fuel - 1) hf y k m2 a2 r2 m3 hS2 hn hr hy h3
  cases h4 : callW p k mk [r1.headD 0, r2.headD 0] m3 with
  | none => rw [h4] at hw; simp [ntBW] at hw
  | some q4 =>
  obtain ⟨r3, m4⟩ := q4
  rw [h4, bW_some] at hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  obtain ⟨x4, a4, hrun4, hS4, hg4, hl4, hx4⟩ := hmk (r1.headD 0) (r2.headD 0) k m3 a3 r3 m4 hS3 h4
  refine ⟨x4, a4, ?_, hS4, hg2.trans (hg3.trans hg4), hl4, hx4⟩
  simp only [StateT.run_bind, hrun2, hrun3, exc_ok_bind', ← hx2, ← hx3]
  exact hrun4

/-- The `letE` arm. -/
theorem sca_let (hM : MasterProg p) {nm r : Word} {f : Nat} (ih : ScaIH p dn vis fe nm r f)
    {fuel x y z : Word} (hf : (fuel - 1).toNat = f) {k : Nat} {m1 : Mem} {a1 : AState}
    {res : List Word} {m' : Mem} (hS1 : StageR dn vis fe m1 a1) (hn : H nm) (hr : H r)
    (hx : H x) (hy : H y) (hz : H z)
    (hw : (ntBW (callW p k "subst_const_all" [nm, r, fuel - 1, x] m1) fun r1 m2 =>
      ntBW (callW p k "subst_const_all" [nm, r, fuel - 1, y] m2) fun r2 m3 =>
      ntBW (callW p k "subst_const_all" [nm, r, fuel - 1, z] m3) fun r3 m4 =>
      ntBW (callW p k "mk_let" [r1.headD 0, r2.headD 0, r3.headD 0] m4) fun r5 m5 =>
      some ([r5.headD 0], m5)) = some (res, m')) :
    ∃ e a', (do
        let t' ← substConstAll (decI nm) (decE r) f (decE x)
        let v' ← substConstAll (decI nm) (decE r) f (decE y)
        let b' ← substConstAll (decI nm) (decE r) f (decE z)
        internE (.letE t' v' b')).run a1 = .ok (e, a') ∧ KeepPost dn vis fe decW0E m1 m' a' res e := by
  cases h2 : callW p k "subst_const_all" [nm, r, fuel - 1, x] m1 with
  | none => rw [h2] at hw; simp [ntBW] at hw
  | some q2 =>
  obtain ⟨r1, m2⟩ := q2
  rw [h2, bW_some] at hw
  obtain ⟨x2, a2, hrun2, hS2, hg2, hl2, hx2⟩ := ih (fuel - 1) hf x k m1 a1 r1 m2 hS1 hn hr hx h2
  cases h3 : callW p k "subst_const_all" [nm, r, fuel - 1, y] m2 with
  | none => rw [h3] at hw; simp [ntBW] at hw
  | some q3 =>
  obtain ⟨r2, m3⟩ := q3
  rw [h3, bW_some] at hw
  obtain ⟨x3, a3, hrun3, hS3, hg3, hl3, hx3⟩ := ih (fuel - 1) hf y k m2 a2 r2 m3 hS2 hn hr hy h3
  cases h4 : callW p k "subst_const_all" [nm, r, fuel - 1, z] m3 with
  | none => rw [h4] at hw; simp [ntBW] at hw
  | some q4 =>
  obtain ⟨r3, m4⟩ := q4
  rw [h4, bW_some] at hw
  obtain ⟨x4, a4, hrun4, hS4, hg4, hl4, hx4⟩ := ih (fuel - 1) hf z k m3 a3 r3 m4 hS3 hn hr hz h4
  cases h5 : callW p k "mk_let" [r1.headD 0, r2.headD 0, r3.headD 0] m4 with
  | none => rw [h5] at hw; simp [ntBW] at hw
  | some q5 =>
  obtain ⟨r5, m5⟩ := q5
  rw [h5, bW_some] at hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  obtain ⟨x5, a5, hrun5, hS5, hg5, hl5, hx5⟩ := mkLet_ref (dn := dn) (vis := vis) (fe := fe) hM
    (r1.headD 0) (r2.headD 0) (r3.headD 0) k m4 a4 r5 m5 hS4 h5
  refine ⟨x5, a5, ?_, hS5, hg2.trans (hg3.trans (hg4.trans hg5)), hl5, hx5⟩
  simp only [StateT.run_bind, hrun2, hrun3, hrun4, exc_ok_bind', ← hx2, ← hx3, ← hx4]
  exact hrun5

/-- The `proj` arm. -/
theorem sca_proj (hM : MasterProg p) {nm r : Word} {f : Nat} (ih : ScaIH p dn vis fe nm r f)
    {fuel x y z : Word} (hf : (fuel - 1).toNat = f) {k : Nat} {m1 : Mem} {a1 : AState}
    {res : List Word} {m' : Mem} (hS1 : StageR dn vis fe m1 a1) (hn : H nm) (hr : H r) (hz : H z)
    (hw : (ntBW (callW p k "subst_const_all" [nm, r, fuel - 1, z] m1) fun r1 m2 =>
      ntBW (callW p k "mk_proj" [x, y, r1.headD 0] m2) fun r3 m3 => some ([r3.headD 0], m3)) =
      some (res, m')) :
    ∃ e a', (do
        let e' ← substConstAll (decI nm) (decE r) f (decE z)
        internE (.proj (decI x) y.toNat e')).run a1 = .ok (e, a') ∧
      KeepPost dn vis fe decW0E m1 m' a' res e := by
  cases h2 : callW p k "subst_const_all" [nm, r, fuel - 1, z] m1 with
  | none => rw [h2] at hw; simp [ntBW] at hw
  | some q2 =>
  obtain ⟨r1, m2⟩ := q2
  rw [h2, bW_some] at hw
  obtain ⟨x2, a2, hrun2, hS2, hg2, hl2, hx2⟩ := ih (fuel - 1) hf z k m1 a1 r1 m2 hS1 hn hr hz h2
  cases h3 : callW p k "mk_proj" [x, y, r1.headD 0] m2 with
  | none => rw [h3] at hw; simp [ntBW] at hw
  | some q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [h3, bW_some] at hw
  simp only [Option.some.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  obtain ⟨x3, a3, hrun3, hS3, hg3, hl3, hx3⟩ := mkProj_ref (dn := dn) (vis := vis) (fe := fe) hM
    x y (r1.headD 0) k m2 a2 r3 m3 hS2 h3
  refine ⟨x3, a3, ?_, hS3, hg2.trans hg3, hl3, hx3⟩
  simp only [StateT.run_bind, hrun2, exc_ok_bind', ← hx2]
  exact hrun3

theorem sca_ref (hN : NatSubAllProg p) (nm r : Word) : ∀ f, ScaIH p dn vis fe nm r f := by
  intro f
  induction f with
  | zero =>
    intro fuel hf h k m a res m' hS hn hr hh hc
    cases k with
    | zero => rw [callW_zero] at hc; cases hc
    | succ k =>
    have hw := callW_model (M := fun mm => scaW p (k + 1) mm nm r fuel h) (sca_specW p hN.lSubstConstAll (k + 1) · nm r fuel h) hc
    have hz : fuel = 0 := UInt64.toNat_inj.mp (by simpa using hf)
    simp [scaW.eq_2, hz] at hw
  | succ f ih =>
    intro fuel hf h k m a res m' hS hn hr hh hc
    cases k with
    | zero => rw [callW_zero] at hc; cases hc
    | succ k =>
    have hw := callW_model (M := fun mm => scaW p (k + 1) mm nm r fuel h) (sca_specW p hN.lSubstConstAll (k + 1) · nm r fuel h) hc
    have hnz : fuel ≠ 0 := fun e => by simp [e] at hf
    rw [scaW.eq_2] at hw
    rw [ite_eq_right hnz] at hw
    cases h1 : callW p k "e_view" [h] m with
    | none => rw [h1] at hw; simp [ntBW] at hw
    | some q1 =>
    obtain ⟨rv, m1⟩ := q1
    rw [h1, bW_some] at hw
    obtain ⟨vv, a1, hrun1, hS1, hg1, hvr⟩ := eView_ref (dn := dn) (vis := vis) (fe := fe) (p := p) h hN.lEView k m a rv m1 hS h1
    have hrun1' : (view (decE h)).run a = .ok (vv, a1) := hrun1
    have hfuel1 : (fuel - 1).toNat = f := by
      have : 0 < fuel.toNat := Nat.pos_of_ne_zero (fun e => hnz (UInt64.toNat_inj.mp (by simpa using e)))
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp; omega
    have ihs : ScaIH p dn vis fe nm r f := ih
    -- the arms that return `h`
    have hret : rv.headD 0 ≠ 3 → rv.headD 0 ≠ 4 → rv.headD 0 ≠ 5 → rv.headD 0 ≠ 6 →
        rv.headD 0 ≠ 7 → rv.headD 0 ≠ 9 →
        ((substConstAll (decI nm) (decE r) (f + 1) (decE h)).run a = .ok (decE h, a1)) →
        ∃ x a', (substConstAll (decI nm) (decE r) (f + 1) (decE h)).run a = .ok (x, a') ∧
          KeepPost dn vis fe decW0E m m' a' res x := by
      intro n3 n4 n5 n6 n7 n9 hrun
      rw [ite_eq_right n3, ite_eq_right n4, ite_eq_right n5, ite_eq_right n6, ite_eq_right n7, ite_eq_right n9] at hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      exact ⟨decE h, a1, hrun, hS1, hg1, by simpa using hh, rfl⟩
    cases vv with
    | const c us =>
      simp only [ViewR, ntGetD1, getD2] at hvr
      obtain ⟨h3, hc0, hcd, hu0, hud⟩ := hvr
      rw [ite_eq_left h3] at hw
      cases h2 : callW p k "pin_word" [52] m1 with
      | none => rw [h2] at hw; simp [ntBW] at hw
      | some q2 =>
      obtain ⟨re, m2⟩ := q2
      rw [h2, bW_some] at hw
      obtain ⟨x2, a2, hrun2, hS2, hg2, hx2l, hx2⟩ := pinWord52_ref (dn := dn) (vis := vis) (fe := fe) p
        hN.lPinWord k m1 a1 re m2 hS1 h2
      subst hcd hud
      have hbeq : ((decI (rv.tail.headD 0) : NIdx) == decI nm && (decI (rv.tail.tail.headD 0) : LsIdx) == x2) =
          decide (rv.tail.headD 0 = nm ∧ rv.tail.tail.headD 0 = re.headD 0) := by
        rw [← hx2, decI_beq_word hc0 hn, decI_beq_word hu0 hx2l]; simp
      by_cases hcond : rv.tail.headD 0 = nm ∧ rv.tail.tail.headD 0 = re.headD 0
      · rw [ite_eq_left hcond] at hw
        simp only [Option.some.injEq, Prod.mk.injEq] at hw
        obtain ⟨rfl, rfl⟩ := hw
        refine ⟨decE r, a2, ?_, hS2, hg1.trans hg2, by simpa using hr, rfl⟩
        simp only [substConstAll, StateT.run_bind, hrun1', exc_ok_bind', emptyLevels, hrun2, hbeq,
          decide_eq_true hcond, ite_true]
        rfl
      · rw [ite_eq_right hcond] at hw
        simp only [Option.some.injEq, Prod.mk.injEq] at hw
        obtain ⟨rfl, rfl⟩ := hw
        refine ⟨decE h, a2, ?_, hS2, hg1.trans hg2, by simpa using hh, rfl⟩
        simp only [substConstAll, StateT.run_bind, hrun1', exc_ok_bind', emptyLevels, hrun2, hbeq,
          decide_eq_false hcond, Bool.false_eq_true, ite_false]
        rfl
    | app fa aa =>
      simp only [ViewR, ntGetD1, getD2] at hvr
      obtain ⟨hT, hf0, hfd, ha0, had⟩ := hvr
      simp (config := { decide := true }) only [hT, ↓reduceIte] at hw
      subst hfd had
      obtain ⟨e, a', hrun, hK⟩ := sca_bin ihs "mk_app" (fun t b => internE (.app t b))
        (fun t b => mkApp_ref hN.toMasterProg t b) hfuel1 hS1 hn hr hf0 ha0 hw
      refine ⟨e, a', ?_, hK.1, hg1.trans hK.2.1, hK.2.2⟩
      simp only [substConstAll, StateT.run_bind, hrun1', exc_ok_bind']
      exact hrun
    | lam ty b =>
      simp only [ViewR, ntGetD1, getD2] at hvr
      obtain ⟨hT, hf0, hfd, ha0, had⟩ := hvr
      simp (config := { decide := true }) only [hT, ↓reduceIte] at hw
      subst hfd had
      obtain ⟨e, a', hrun, hK⟩ := sca_bin ihs "mk_lam" (fun t b => internE (.lam t b))
        (fun t b => mkLam_ref hN.toMasterProg t b) hfuel1 hS1 hn hr hf0 ha0 hw
      refine ⟨e, a', ?_, hK.1, hg1.trans hK.2.1, hK.2.2⟩
      simp only [substConstAll, StateT.run_bind, hrun1', exc_ok_bind']
      exact hrun
    | forallE ty b =>
      simp only [ViewR, ntGetD1, getD2] at hvr
      obtain ⟨hT, hf0, hfd, ha0, had⟩ := hvr
      simp (config := { decide := true }) only [hT, ↓reduceIte] at hw
      subst hfd had
      obtain ⟨e, a', hrun, hK⟩ := sca_bin ihs "mk_forall" (fun t b => internE (.forallE t b))
        (fun t b => mkForall_ref hN.toMasterProg t b) hfuel1 hS1 hn hr hf0 ha0 hw
      refine ⟨e, a', ?_, hK.1, hg1.trans hK.2.1, hK.2.2⟩
      simp only [substConstAll, StateT.run_bind, hrun1', exc_ok_bind']
      exact hrun
    | letE t v b =>
      simp only [ViewR, ntGetD1, getD2, scaGetD3] at hvr
      obtain ⟨hT, ht0, htd, hv0, hvd, hb0, hbd⟩ := hvr
      simp (config := { decide := true }) only [hT, ↓reduceIte] at hw
      subst htd hvd hbd
      obtain ⟨e, a', hrun, hK⟩ := sca_let hN.toMasterProg ihs hfuel1 hS1 hn hr ht0 hv0 hb0 hw
      refine ⟨e, a', ?_, hK.1, hg1.trans hK.2.1, hK.2.2⟩
      simp only [substConstAll, StateT.run_bind, hrun1', exc_ok_bind']
      exact hrun
    | proj s i e0 =>
      simp only [ViewR, ntGetD1, getD2, scaGetD3] at hvr
      obtain ⟨hT, hs0, hsd, hid, he0, hed⟩ := hvr
      simp (config := { decide := true }) only [hT, ↓reduceIte] at hw
      subst hsd hid hed
      obtain ⟨e, a', hrun, hK⟩ := sca_proj hN.toMasterProg ihs hfuel1 hS1 hn hr he0 hw
      refine ⟨e, a', ?_, hK.1, hg1.trans hK.2.1, hK.2.2⟩
      simp only [substConstAll, StateT.run_bind, hrun1', exc_ok_bind']
      exact hrun
    | bvar i =>
      simp only [ViewR] at hvr
      exact hret (by rw [hvr.1]; decide) (by rw [hvr.1]; decide) (by rw [hvr.1]; decide)
        (by rw [hvr.1]; decide) (by rw [hvr.1]; decide) (by rw [hvr.1]; decide)
        (by simp only [substConstAll, StateT.run_bind, hrun1', exc_ok_bind']; rfl)
    | fvar i ty =>
      simp only [ViewR] at hvr
      exact hret (by rw [hvr.1]; decide) (by rw [hvr.1]; decide) (by rw [hvr.1]; decide)
        (by rw [hvr.1]; decide) (by rw [hvr.1]; decide) (by rw [hvr.1]; decide)
        (by simp only [substConstAll, StateT.run_bind, hrun1', exc_ok_bind']; rfl)
    | sort u =>
      simp only [ViewR] at hvr
      exact hret (by rw [hvr.1]; decide) (by rw [hvr.1]; decide) (by rw [hvr.1]; decide)
        (by rw [hvr.1]; decide) (by rw [hvr.1]; decide) (by rw [hvr.1]; decide)
        (by simp only [substConstAll, StateT.run_bind, hrun1', exc_ok_bind']; rfl)
    | lit l =>
      simp only [ViewR] at hvr
      exact hret (by rw [hvr]; decide) (by rw [hvr]; decide) (by rw [hvr]; decide)
        (by rw [hvr]; decide) (by rw [hvr]; decide) (by rw [hvr]; decide)
        (by simp only [substConstAll, StateT.run_bind, hrun1', exc_ok_bind']; rfl)

@[refines ConRon.Arena.substConstAll]
theorem substConstAll_refines (hN : NatSubAllProg p) (nm r fuel h : Word) :
    RefAM p "subst_const_all" [nm, r, fuel, h]
      (fun m a => StageR dn vis fe m a ∧ H nm ∧ H r ∧ H h)
      (substConstAll (decI nm) (decE r) fuel.toNat (decE h)) (KeepPost dn vis fe decW0E) :=
  CallRef.refAM (fun k m a res m' ⟨hS, hn, hr, hh⟩ hc =>
    sca_ref hN nm r fuel.toNat fuel rfl h k m a res m' hS hn hr hh hc)

/-- **`subst_const_all` at the walk fuel**: `DeclDivModSpec/SubstConst0List`'s `SubstCAll`. -/
theorem substCAll_of (hN : NatSubAllProg p) : ∀ dn vis fe, SubstCAll p dn vis fe :=
  fun _ _ _ nm r h hn hr hh k m a res m' hS hc =>
    sca_ref hN nm r coreWalkFuel 4000000000 rfl h k m a res m' hS hn hr hh hc

end suball

end L.Ind
