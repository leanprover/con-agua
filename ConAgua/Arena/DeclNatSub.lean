import ConAgua.Arena.DeclNatEq

/-!
# The structural-`Nat` gate: constant substitution (lane `decls3`, helper `decls3-nat`)

`subst_const0`, `subst_const0_pairs`.
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

theorem viewR_shape {rv : List Word} {v : ENodeView} (h : ViewR rv v) :
    (rv.headD 0 = 3 ∧ ∃ c us, v = .const c us ∧ H (rv.tail.headD 0) ∧ decI (rv.tail.headD 0) = c ∧
      H (rv.tail.tail.headD 0) ∧ decI (rv.tail.tail.headD 0) = us) ∨
    (rv.headD 0 = 4 ∧ ∃ f a, v = .app f a ∧ H (rv.tail.headD 0) ∧ decE (rv.tail.headD 0) = f ∧
      H (rv.tail.tail.headD 0) ∧ decE (rv.tail.tail.headD 0) = a) ∨
    (rv.headD 0 ≠ 3 ∧ rv.headD 0 ≠ 4 ∧ (∀ c us, v ≠ .const c us) ∧ ∀ f a, v ≠ .app f a) := by
  cases v <;> simp only [ViewR] at h
  case const c us =>
    left
    obtain ⟨h0, h1, h2, h3, h4⟩ := h
    refine ⟨h0, _, _, rfl, ?_, ?_, ?_, ?_⟩ <;> simp_all [getD1, getD2, H]
  case app f a =>
    right; left
    obtain ⟨h0, h1, h2, h3, h4⟩ := h
    refine ⟨h0, _, _, rfl, ?_, ?_, ?_, ?_⟩ <;> simp_all [getD1, getD2, H]
  all_goals
    right; right
    refine ⟨?_, ?_, fun _ _ => by simp, fun _ _ => by simp⟩ <;> simp_all

section sub
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}

structure NatSubProg (p : Prog) : Prop extends NatEqProg p where
  lSubstConst0 : p.lookup "subst_const0" = some substConst0L
  lSubstConst0Pairs : p.lookup "subst_const0_pairs" = some substConst0PairsL

section scmodel
variable (p : Prog) (n : Nat)

def sc0K4 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)

def sc0K3 (r1 : List Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m) => sc0K4 (callW p n "mk_app" [r1.headD 0, r2.headD 0] m)

def sc0K2 (nm r fuel : Word) (r1 : List Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1', m) => sc0K3 p n r1' (callW p n "subst_const0" [nm, r, fuel - 1, r1.tail.tail.headD 0] m)

def sc0K5 (nm r h : Word) (rv : List Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (re, m2) =>
    if rv.tail.headD 0 = nm ∧ rv.tail.tail.headD 0 = re.headD 0 then some ([r], m2)
    else some ([h], m2)

def sc0K1 (nm r fuel h : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rv, m) =>
    if rv.headD 0 = 3 then sc0K5 nm r h rv (callW p n "pin_word" [52] m)
    else if rv.headD 0 = 4 then
      sc0K2 p n nm r fuel rv (callW p n "subst_const0" [nm, r, fuel - 1, rv.tail.headD 0] m)
    else some ([h], m)

end scmodel

def sc0W (p : Prog) (n : Nat) (m : Mem) (nm r fuel h : Word) : Option (List Word × Mem) :=
  if fuel = 0 then none else sc0K1 p n nm r fuel h (callW p n "e_view" [h] m)


section scarms
variable (p : Prog) (n : Nat) (nm r fuel h : Word) (rv r1 r2 re : List Word) (m : Mem)
theorem sc0K4_some : sc0K4 (some (r2, m)) = some ([r2.headD 0], m) := rfl
theorem sc0K3_some : sc0K3 p n r1 (some (r2, m)) =
    sc0K4 (callW p n "mk_app" [r1.headD 0, r2.headD 0] m) := rfl
theorem sc0K2_some : sc0K2 p n nm r fuel rv (some (r1, m)) =
    sc0K3 p n r1 (callW p n "subst_const0" [nm, r, fuel - 1, rv.tail.tail.headD 0] m) := rfl
theorem sc0K5_some : sc0K5 nm r h rv (some (re, m)) =
    if rv.tail.headD 0 = nm ∧ rv.tail.tail.headD 0 = re.headD 0 then some ([r], m)
    else some ([h], m) := rfl
theorem sc0K1_some : sc0K1 p n nm r fuel h (some (rv, m)) =
    if rv.headD 0 = 3 then sc0K5 nm r h rv (callW p n "pin_word" [52] m)
    else if rv.headD 0 = 4 then
      sc0K2 p n nm r fuel rv (callW p n "subst_const0" [nm, r, fuel - 1, rv.tail.headD 0] m)
    else some ([h], m) := rfl
end scarms

grind_pattern [ind_grind] sc0K4_some => sc0K4 (some (r2, m))
grind_pattern [ind_grind] sc0K3_some => sc0K3 p n r1 (some (r2, m))
grind_pattern [ind_grind] sc0K2_some => sc0K2 p n nm r fuel rv (some (r1, m))
grind_pattern [ind_grind] sc0K5_some => sc0K5 nm r h rv (some (re, m))
grind_pattern [ind_grind] sc0K1_some => sc0K1 p n nm r fuel h (some (rv, m))

theorem sc0_specW (p : Prog) (hp : p.lookup "subst_const0" = some substConst0L) (n : Nat)
    (s₀ : St) (nm r fuel h : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "subst_const0" [nm, r, fuel, h]
    ⦃fun res s' => LocEq s' s₀ ∧ sc0W p n s₀.mem nm r fuel h = some (res, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, substConst0L]
  vcgen [exec, step, evalE, L.evalC_spec, evalArgs, setLoc, setLocs, ld64,
    callW_spec p n "e_view", callW_spec p n "pin_word", callW_spec p n "subst_const0",
    callW_spec p n "mk_app"]
  all_goals (try simp only [Cond.pval, Expr.pval, Cmp.eval, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, rd64_eq_rdW] at *)
  all_goals grind (gen := 20) (instances := 10000) [lang_grind, arena_grind, ind_grind, sc0W]


theorem sc0_ref (hN : NatSubProg p) (nm r : Word) :
    ∀ (f : Nat) (fuel : Word), fuel.toNat = f → ∀ (h : Word) (k : Nat) (m : Mem) (a : AState)
      (res : List Word) (m' : Mem), StageR dn vis fe m a → H nm → H r → H h →
      callW p k "subst_const0" [nm, r, fuel, h] m = some (res, m') →
      ∃ x a', (substConst0 (decI nm) (decE r) f (decE h)).run a = .ok (x, a') ∧
        KeepPost dn vis fe decW0E m m' a' res x := by
  intro f
  induction f with
  | zero =>
    intro fuel hf h k m a res m' hS hn hr hh hc
    cases k with
    | zero => rw [callW_zero] at hc; cases hc
    | succ k =>
    have hw := callW_model (M := fun mm => sc0W p k mm nm r fuel h) (sc0_specW p hN.lSubstConst0 k · nm r fuel h) hc
    have hz : fuel = 0 := UInt64.toNat_inj.mp (by simpa using hf)
    simp [sc0W, hz] at hw
  | succ f ih =>
    intro fuel hf h k m a res m' hS hn hr hh hc
    cases k with
    | zero => rw [callW_zero] at hc; cases hc
    | succ k =>
    have hw := callW_model (M := fun mm => sc0W p k mm nm r fuel h) (sc0_specW p hN.lSubstConst0 k · nm r fuel h) hc
    have hnz : fuel ≠ 0 := fun e => by simp [e] at hf
    unfold sc0W at hw
    rw [if_neg hnz] at hw
    cases h1 : callW p k "e_view" [h] m with
    | none => rw [h1] at hw; simp [sc0K1] at hw
    | some q1 =>
    obtain ⟨rv, m1⟩ := q1
    rw [h1, sc0K1_some] at hw
    obtain ⟨vv, a1, hrun1, hS1, hg1, hvr⟩ := eView_ref (dn := dn) (vis := vis) (fe := fe) (p := p) h hN.lEView k m a rv m1 hS h1
    have hrun1' : (view (decE h)).run a = .ok (vv, a1) := hrun1
    have hfuel1 : (fuel - 1).toNat = f := by
      have : 0 < fuel.toNat := Nat.pos_of_ne_zero (fun e => hnz (UInt64.toNat_inj.mp (by simpa using e)))
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp; omega
    rcases viewR_shape hvr with ⟨h3, c, us, hvv, hc0, hcd, hu0, hud⟩ | ⟨h4, fa, aa, hvv, hf0, hfd, ha0, had⟩ | ⟨hn3, hn4, hnc, hna⟩
    · -- a constant
      rw [if_pos h3] at hw
      cases h2 : callW p k "pin_word" [52] m1 with
      | none => rw [h2] at hw; simp [sc0K5] at hw
      | some q2 =>
      obtain ⟨re, m2⟩ := q2
      rw [h2, sc0K5_some] at hw
      obtain ⟨x2, a2, hrun2, hS2, hg2, hx2l, hx2⟩ := pinWord52_ref (dn := dn) (vis := vis) (fe := fe) p
        hN.lPinWord k m1 a1 re m2 hS1 h2
      subst hvv hcd hud
      have hbeq : ((decI (rv.tail.headD 0) : NIdx) == decI nm && (decI (rv.tail.tail.headD 0) : LsIdx) == x2) =
          decide (rv.tail.headD 0 = nm ∧ rv.tail.tail.headD 0 = re.headD 0) := by
        rw [← hx2, decI_beq_word hc0 hn, decI_beq_word hu0 hx2l]; simp
      by_cases hcond : rv.tail.headD 0 = nm ∧ rv.tail.tail.headD 0 = re.headD 0
      · rw [if_pos hcond] at hw
        simp only [Option.some.injEq, Prod.mk.injEq] at hw
        obtain ⟨rfl, rfl⟩ := hw
        refine ⟨decE r, a2, ?_, hS2, hg1.trans hg2, by simpa using hr, rfl⟩
        simp only [substConst0, StateT.run_bind, hrun1', exc_ok_bind', emptyLevels, hrun2, hbeq,
          decide_eq_true hcond, if_true]
        rfl
      · rw [if_neg hcond] at hw
        simp only [Option.some.injEq, Prod.mk.injEq] at hw
        obtain ⟨rfl, rfl⟩ := hw
        refine ⟨decE h, a2, ?_, hS2, hg1.trans hg2, by simpa using hh, rfl⟩
        simp only [substConst0, StateT.run_bind, hrun1', exc_ok_bind', emptyLevels, hrun2, hbeq,
          decide_eq_false hcond, Bool.false_eq_true, if_false]
        rfl
    · -- an application
      rw [if_neg (by rw [h4]; decide), if_pos h4] at hw
      subst hvv hfd had
      cases h2 : callW p k "subst_const0" [nm, r, fuel - 1, rv.tail.headD 0] m1 with
      | none => rw [h2] at hw; simp [sc0K2] at hw
      | some q2 =>
      obtain ⟨r1, m2⟩ := q2
      rw [h2, sc0K2_some] at hw
      obtain ⟨x2, a2, hrun2, hK2⟩ := ih (fuel - 1) hfuel1 (rv.tail.headD 0) k m1 a1 r1 m2 hS1 hn hr hf0 h2
      obtain ⟨hS2, hg2, hl2, hx2⟩ := hK2
      cases h3 : callW p k "subst_const0" [nm, r, fuel - 1, rv.tail.tail.headD 0] m2 with
      | none => rw [h3] at hw; simp [sc0K3] at hw
      | some q3 =>
      obtain ⟨r2, m3⟩ := q3
      rw [h3, sc0K3_some] at hw
      obtain ⟨x3, a3, hrun3, hK3⟩ := ih (fuel - 1) hfuel1 (rv.tail.tail.headD 0) k m2 a2 r2 m3 hS2 hn hr ha0 h3
      obtain ⟨hS3, hg3, hl3, hx3⟩ := hK3
      cases h4' : callW p k "mk_app" [r1.headD 0, r2.headD 0] m3 with
      | none => rw [h4'] at hw; simp [sc0K4] at hw
      | some q4 =>
      obtain ⟨r3, m4⟩ := q4
      rw [h4', sc0K4_some] at hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      obtain ⟨x4, a4, hrun4, hS4, hg4, hl4, hx4⟩ := mkApp_ref (dn := dn) (vis := vis) (fe := fe) hN.toMasterProg
        (r1.headD 0) (r2.headD 0) k m3 a3 r3 m4 hS3 h4'
      refine ⟨x4, a4, ?_, hS4, hg1.trans (hg2.trans (hg3.trans hg4)), hl4, hx4⟩
      simp only [substConst0, StateT.run_bind, hrun1', exc_ok_bind', hrun2, hrun3, ← hx2, ← hx3,
        ENodeView.app.injEq]
      exact hrun4
    · rw [if_neg (fun e => hn3 e), if_neg (fun e => hn4 e)] at hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      refine ⟨decE h, a1, ?_, hS1, hg1, by simpa using hh, rfl⟩
      simp only [substConst0, StateT.run_bind, hrun1', exc_ok_bind']
      cases vv <;> first | rfl | (exfalso; exact hnc _ _ rfl) | (exfalso; exact hna _ _ rfl)


@[refines ConRon.Arena.substConst0]
theorem substConst0_refines (hN : NatSubProg p) (nm r fuel h : Word) :
    RefAM p "subst_const0" [nm, r, fuel, h]
      (fun m a => StageR dn vis fe m a ∧ H nm ∧ H r ∧ H h)
      (substConst0 (decI nm) (decE r) fuel.toNat (decE h)) (KeepPost dn vis fe decW0E) :=
  CallRef.refAM (fun k m a res m' ⟨hS, hn, hr, hh⟩ hc =>
    sc0_ref hN nm r fuel.toNat fuel rfl h k m a res m' hS hn hr hh hc)

end sub

end L.Ind
