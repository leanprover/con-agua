import ConAgua.Arena.DeclNatSub
import ConAgua.Arena.DeclDivMod5

/-!
# The structural-`Nat` gate: constant substitution under binders (lane `decls4`, helper `decls4-sca`)

`subst_const_all` refines `substConstAll`, after `DeclNatSub`'s `subst_const0`: the model `scaW` of
one call, then the refinement by induction on the twin's fuel. The binary arms (`app`, `lam`,
`forallE`) share `sca_bin`; `letE` and `proj` have their own.
-/

set_option experimental.vcgen true
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

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

section scamodel
variable (p : Prog) (n : Nat)

/-- The second recursive call of a binary arm, then the interner `mk`. -/
def scaB2 (mk : FnName) (r1 : List Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m) => sc0K4 (callW p n mk [r1.headD 0, r2.headD 0] m)

def scaB1 (mk : FnName) (nm r fuel y : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m) => scaB2 p n mk r1 (callW p n "subst_const_all" [nm, r, fuel - 1, y] m)

def scaL3 (r1 r2 : List Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m) => sc0K4 (callW p n "mk_let" [r1.headD 0, r2.headD 0, r3.headD 0] m)

def scaL2 (nm r fuel z : Word) (r1 : List Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m) => scaL3 p n r1 r2 (callW p n "subst_const_all" [nm, r, fuel - 1, z] m)

def scaL1 (nm r fuel y z : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m) => scaL2 p n nm r fuel z r1 (callW p n "subst_const_all" [nm, r, fuel - 1, y] m)

def scaP1 (x y : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m) => sc0K4 (callW p n "mk_proj" [x, y, r1.headD 0] m)

/-- The arms after `e_view`, dispatched on the view's tag. -/
def scaK1 (nm r fuel h : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rv, m) =>
    if rv.headD 0 = 3 then sc0K5 nm r h rv (callW p n "pin_word" [52] m)
    else if rv.headD 0 = 4 then
      scaB1 p n "mk_app" nm r fuel (rv.tail.tail.headD 0)
        (callW p n "subst_const_all" [nm, r, fuel - 1, rv.tail.headD 0] m)
    else if rv.headD 0 = 5 then
      scaB1 p n "mk_lam" nm r fuel (rv.tail.tail.headD 0)
        (callW p n "subst_const_all" [nm, r, fuel - 1, rv.tail.headD 0] m)
    else if rv.headD 0 = 6 then
      scaB1 p n "mk_forall" nm r fuel (rv.tail.tail.headD 0)
        (callW p n "subst_const_all" [nm, r, fuel - 1, rv.tail.headD 0] m)
    else if rv.headD 0 = 7 then
      scaL1 p n nm r fuel (rv.tail.tail.headD 0) (rv.tail.tail.tail.headD 0)
        (callW p n "subst_const_all" [nm, r, fuel - 1, rv.tail.headD 0] m)
    else if rv.headD 0 = 9 then
      scaP1 p n (rv.tail.headD 0) (rv.tail.tail.headD 0)
        (callW p n "subst_const_all" [nm, r, fuel - 1, rv.tail.tail.tail.headD 0] m)
    else some ([h], m)

end scamodel

/-- The model of one call of `subst_const_all`. -/
def scaW (p : Prog) (n : Nat) (m : Mem) (nm r fuel h : Word) : Option (List Word × Mem) :=
  if fuel = 0 then none else scaK1 p n nm r fuel h (callW p n "e_view" [h] m)

section scaarms
variable (p : Prog) (n : Nat) (mk : FnName) (nm r fuel h x y z : Word) (rv r1 r2 : List Word) (m : Mem)
theorem scaB2_some : scaB2 p n mk r1 (some (r2, m)) = sc0K4 (callW p n mk [r1.headD 0, r2.headD 0] m) := rfl
theorem scaB1_some : scaB1 p n mk nm r fuel y (some (r1, m)) =
    scaB2 p n mk r1 (callW p n "subst_const_all" [nm, r, fuel - 1, y] m) := rfl
theorem scaL3_some (r3 : List Word) : scaL3 p n r1 r2 (some (r3, m)) =
    sc0K4 (callW p n "mk_let" [r1.headD 0, r2.headD 0, r3.headD 0] m) := rfl
theorem scaL2_some : scaL2 p n nm r fuel z r1 (some (r2, m)) =
    scaL3 p n r1 r2 (callW p n "subst_const_all" [nm, r, fuel - 1, z] m) := rfl
theorem scaL1_some : scaL1 p n nm r fuel y z (some (r1, m)) =
    scaL2 p n nm r fuel z r1 (callW p n "subst_const_all" [nm, r, fuel - 1, y] m) := rfl
theorem scaP1_some : scaP1 p n x y (some (r1, m)) = sc0K4 (callW p n "mk_proj" [x, y, r1.headD 0] m) := rfl
theorem scaK1_some : scaK1 p n nm r fuel h (some (rv, m)) =
    if rv.headD 0 = 3 then sc0K5 nm r h rv (callW p n "pin_word" [52] m)
    else if rv.headD 0 = 4 then
      scaB1 p n "mk_app" nm r fuel (rv.tail.tail.headD 0)
        (callW p n "subst_const_all" [nm, r, fuel - 1, rv.tail.headD 0] m)
    else if rv.headD 0 = 5 then
      scaB1 p n "mk_lam" nm r fuel (rv.tail.tail.headD 0)
        (callW p n "subst_const_all" [nm, r, fuel - 1, rv.tail.headD 0] m)
    else if rv.headD 0 = 6 then
      scaB1 p n "mk_forall" nm r fuel (rv.tail.tail.headD 0)
        (callW p n "subst_const_all" [nm, r, fuel - 1, rv.tail.headD 0] m)
    else if rv.headD 0 = 7 then
      scaL1 p n nm r fuel (rv.tail.tail.headD 0) (rv.tail.tail.tail.headD 0)
        (callW p n "subst_const_all" [nm, r, fuel - 1, rv.tail.headD 0] m)
    else if rv.headD 0 = 9 then
      scaP1 p n (rv.tail.headD 0) (rv.tail.tail.headD 0)
        (callW p n "subst_const_all" [nm, r, fuel - 1, rv.tail.tail.tail.headD 0] m)
    else some ([h], m) := rfl
end scaarms

grind_pattern [ind_grind] scaB2_some => scaB2 p n mk r1 (some (r2, m))
grind_pattern [ind_grind] scaB1_some => scaB1 p n mk nm r fuel y (some (r1, m))
grind_pattern [ind_grind] scaL3_some => scaL3 p n r1 r2 (some (r3, m))
grind_pattern [ind_grind] scaL2_some => scaL2 p n nm r fuel z r1 (some (r2, m))
grind_pattern [ind_grind] scaL1_some => scaL1 p n nm r fuel y z (some (r1, m))
grind_pattern [ind_grind] scaP1_some => scaP1 p n x y (some (r1, m))
grind_pattern [ind_grind] scaK1_some => scaK1 p n nm r fuel h (some (rv, m))

theorem sca_specW (p : Prog) (hp : p.lookup "subst_const_all" = some substConstAllL) (n : Nat)
    (s₀ : St) (nm r fuel h : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "subst_const_all" [nm, r, fuel, h]
    ⦃fun res s' => LocEq s' s₀ ∧ scaW p n s₀.mem nm r fuel h = some (res, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, substConstAllL]
  vcgen [exec, step, evalE, L.evalC_spec, evalArgs, setLoc, setLocs, ld64,
    callW_spec p n "e_view", callW_spec p n "pin_word", callW_spec p n "subst_const_all",
    callW_spec p n "mk_app", callW_spec p n "mk_lam", callW_spec p n "mk_forall",
    callW_spec p n "mk_let", callW_spec p n "mk_proj"]
  all_goals (try simp only [Cond.pval, Expr.pval, Cmp.eval, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, rd64_eq_rdW] at *)
  all_goals grind (gen := 20) (instances := 10000) [lang_grind, arena_grind, ind_grind, scaW]

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
    (hw : scaB1 p k mk nm r fuel y (callW p k "subst_const_all" [nm, r, fuel - 1, x] m1) =
      some (res, m')) :
    ∃ e a', (do
        let f' ← substConstAll (decI nm) (decE r) f (decE x)
        let a' ← substConstAll (decI nm) (decE r) f (decE y)
        I f' a').run a1 = .ok (e, a') ∧ KeepPost dn vis fe decW0E m1 m' a' res e := by
  cases h2 : callW p k "subst_const_all" [nm, r, fuel - 1, x] m1 with
  | none => rw [h2] at hw; simp [scaB1] at hw
  | some q2 =>
  obtain ⟨r1, m2⟩ := q2
  rw [h2, scaB1_some] at hw
  obtain ⟨x2, a2, hrun2, hS2, hg2, hl2, hx2⟩ := ih (fuel - 1) hf x k m1 a1 r1 m2 hS1 hn hr hx h2
  cases h3 : callW p k "subst_const_all" [nm, r, fuel - 1, y] m2 with
  | none => rw [h3] at hw; simp [scaB2] at hw
  | some q3 =>
  obtain ⟨r2, m3⟩ := q3
  rw [h3, scaB2_some] at hw
  obtain ⟨x3, a3, hrun3, hS3, hg3, hl3, hx3⟩ := ih (fuel - 1) hf y k m2 a2 r2 m3 hS2 hn hr hy h3
  cases h4 : callW p k mk [r1.headD 0, r2.headD 0] m3 with
  | none => rw [h4] at hw; simp [sc0K4] at hw
  | some q4 =>
  obtain ⟨r3, m4⟩ := q4
  rw [h4, sc0K4_some] at hw
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
    (hw : scaL1 p k nm r fuel y z (callW p k "subst_const_all" [nm, r, fuel - 1, x] m1) =
      some (res, m')) :
    ∃ e a', (do
        let t' ← substConstAll (decI nm) (decE r) f (decE x)
        let v' ← substConstAll (decI nm) (decE r) f (decE y)
        let b' ← substConstAll (decI nm) (decE r) f (decE z)
        internE (.letE t' v' b')).run a1 = .ok (e, a') ∧ KeepPost dn vis fe decW0E m1 m' a' res e := by
  cases h2 : callW p k "subst_const_all" [nm, r, fuel - 1, x] m1 with
  | none => rw [h2] at hw; simp [scaL1] at hw
  | some q2 =>
  obtain ⟨r1, m2⟩ := q2
  rw [h2, scaL1_some] at hw
  obtain ⟨x2, a2, hrun2, hS2, hg2, hl2, hx2⟩ := ih (fuel - 1) hf x k m1 a1 r1 m2 hS1 hn hr hx h2
  cases h3 : callW p k "subst_const_all" [nm, r, fuel - 1, y] m2 with
  | none => rw [h3] at hw; simp [scaL2] at hw
  | some q3 =>
  obtain ⟨r2, m3⟩ := q3
  rw [h3, scaL2_some] at hw
  obtain ⟨x3, a3, hrun3, hS3, hg3, hl3, hx3⟩ := ih (fuel - 1) hf y k m2 a2 r2 m3 hS2 hn hr hy h3
  cases h4 : callW p k "subst_const_all" [nm, r, fuel - 1, z] m3 with
  | none => rw [h4] at hw; simp [scaL3] at hw
  | some q4 =>
  obtain ⟨r3, m4⟩ := q4
  rw [h4, scaL3_some] at hw
  obtain ⟨x4, a4, hrun4, hS4, hg4, hl4, hx4⟩ := ih (fuel - 1) hf z k m3 a3 r3 m4 hS3 hn hr hz h4
  cases h5 : callW p k "mk_let" [r1.headD 0, r2.headD 0, r3.headD 0] m4 with
  | none => rw [h5] at hw; simp [sc0K4] at hw
  | some q5 =>
  obtain ⟨r5, m5⟩ := q5
  rw [h5, sc0K4_some] at hw
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
    (hw : scaP1 p k x y (callW p k "subst_const_all" [nm, r, fuel - 1, z] m1) = some (res, m')) :
    ∃ e a', (do
        let e' ← substConstAll (decI nm) (decE r) f (decE z)
        internE (.proj (decI x) y.toNat e')).run a1 = .ok (e, a') ∧
      KeepPost dn vis fe decW0E m1 m' a' res e := by
  cases h2 : callW p k "subst_const_all" [nm, r, fuel - 1, z] m1 with
  | none => rw [h2] at hw; simp [scaP1] at hw
  | some q2 =>
  obtain ⟨r1, m2⟩ := q2
  rw [h2, scaP1_some] at hw
  obtain ⟨x2, a2, hrun2, hS2, hg2, hl2, hx2⟩ := ih (fuel - 1) hf z k m1 a1 r1 m2 hS1 hn hr hz h2
  cases h3 : callW p k "mk_proj" [x, y, r1.headD 0] m2 with
  | none => rw [h3] at hw; simp [sc0K4] at hw
  | some q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [h3, sc0K4_some] at hw
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
    have hw := callW_model (M := fun mm => scaW p k mm nm r fuel h) (sca_specW p hN.lSubstConstAll k · nm r fuel h) hc
    have hz : fuel = 0 := UInt64.toNat_inj.mp (by simpa using hf)
    simp [scaW, hz] at hw
  | succ f ih =>
    intro fuel hf h k m a res m' hS hn hr hh hc
    cases k with
    | zero => rw [callW_zero] at hc; cases hc
    | succ k =>
    have hw := callW_model (M := fun mm => scaW p k mm nm r fuel h) (sca_specW p hN.lSubstConstAll k · nm r fuel h) hc
    have hnz : fuel ≠ 0 := fun e => by simp [e] at hf
    unfold scaW at hw
    rw [if_neg hnz] at hw
    cases h1 : callW p k "e_view" [h] m with
    | none => rw [h1] at hw; simp [scaK1] at hw
    | some q1 =>
    obtain ⟨rv, m1⟩ := q1
    rw [h1, scaK1_some] at hw
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
      rw [if_neg n3, if_neg n4, if_neg n5, if_neg n6, if_neg n7, if_neg n9] at hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      exact ⟨decE h, a1, hrun, hS1, hg1, by simpa using hh, rfl⟩
    cases vv with
    | const c us =>
      simp only [ViewR, ntGetD1, getD2] at hvr
      obtain ⟨h3, hc0, hcd, hu0, hud⟩ := hvr
      rw [if_pos h3] at hw
      cases h2 : callW p k "pin_word" [52] m1 with
      | none => rw [h2] at hw; simp [sc0K5] at hw
      | some q2 =>
      obtain ⟨re, m2⟩ := q2
      rw [h2, sc0K5_some] at hw
      obtain ⟨x2, a2, hrun2, hS2, hg2, hx2l, hx2⟩ := pinWord52_ref (dn := dn) (vis := vis) (fe := fe) p
        hN.lPinWord k m1 a1 re m2 hS1 h2
      subst hcd hud
      have hbeq : ((decI (rv.tail.headD 0) : NIdx) == decI nm && (decI (rv.tail.tail.headD 0) : LsIdx) == x2) =
          decide (rv.tail.headD 0 = nm ∧ rv.tail.tail.headD 0 = re.headD 0) := by
        rw [← hx2, decI_beq_word hc0 hn, decI_beq_word hu0 hx2l]; simp
      by_cases hcond : rv.tail.headD 0 = nm ∧ rv.tail.tail.headD 0 = re.headD 0
      · rw [if_pos hcond] at hw
        simp only [Option.some.injEq, Prod.mk.injEq] at hw
        obtain ⟨rfl, rfl⟩ := hw
        refine ⟨decE r, a2, ?_, hS2, hg1.trans hg2, by simpa using hr, rfl⟩
        simp only [substConstAll, StateT.run_bind, hrun1', exc_ok_bind', emptyLevels, hrun2, hbeq,
          decide_eq_true hcond, if_true]
        rfl
      · rw [if_neg hcond] at hw
        simp only [Option.some.injEq, Prod.mk.injEq] at hw
        obtain ⟨rfl, rfl⟩ := hw
        refine ⟨decE h, a2, ?_, hS2, hg1.trans hg2, by simpa using hh, rfl⟩
        simp only [substConstAll, StateT.run_bind, hrun1', exc_ok_bind', emptyLevels, hrun2, hbeq,
          decide_eq_false hcond, Bool.false_eq_true, if_false]
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

/-- **`subst_const_all` at the walk fuel**: `DeclDivMod5`'s `SubstCAll`. -/
theorem substCAll_of (hN : NatSubAllProg p) : ∀ dn vis fe, SubstCAll p dn vis fe :=
  fun _ _ _ nm r h hn hr hh k m a res m' hS hc =>
    sca_ref hN nm r coreWalkFuel 4000000000 rfl h k m a res m' hS hn hr hh hc

end suball

end L.Ind
