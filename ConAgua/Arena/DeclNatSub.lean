import ConAgua.Arena.DeclNatEq
import ConAgua.Arena.RecClassSpec

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
    refine ⟨h0, _, _, rfl, ?_, ?_, ?_, ?_⟩ <;> simp_all [ntGetD1, getD2, H]
  case app f a =>
    right; left
    obtain ⟨h0, h1, h2, h3, h4⟩ := h
    refine ⟨h0, _, _, rfl, ?_, ?_, ?_, ?_⟩ <;> simp_all [ntGetD1, getD2, H]
  all_goals
    right; right
    refine ⟨?_, ?_, fun _ _ => by simp, fun _ _ => by simp⟩ <;> simp_all

theorem decNL_getW : ∀ (m : Mem) (l o : Nat) (xs : List Nat), decNL m o l = some xs →
    xs.length = l ∧ ∀ (j : Nat) (hj : j < xs.length), ∃ w : Word, (iwA m)[o + j]? = some w ∧
      w.toNat = xs[j]
  | m, 0, o, xs, h => by simp [decNL] at h; subst h; simp
  | m, l + 1, o, xs, h => by
    rw [decNL_succ] at h
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨x, hx, xs', hxs, rfl⟩ := h
    obtain ⟨hl, hg⟩ := decNL_getW m l (o + 1) xs' hxs
    refine ⟨by simp [hl], fun j hj => ?_⟩
    cases j with
    | zero =>
      simp only [iwN, nat?, Option.map_eq_some_iff] at hx
      obtain ⟨w, hw, rfl⟩ := hx
      exact ⟨w, by simpa using hw, by simp⟩
    | succ j =>
      obtain ⟨w, hw, hwx⟩ := hg j (by simpa using hj)
      exact ⟨w, by simpa [Nat.add_assoc, Nat.add_comm 1 j] using hw, by simpa using hwx⟩

theorem EqL.decNL {m : Mem} {o l : Nat} {ps : List (EIdx × EIdx)} (h : EqL m o l ps) :
    ∃ xs, decNL m o l = some xs := by
  obtain ⟨h1, h2, h3⟩ := h
  have hget : ∀ j (hj : j < ps.length), ∃ p : Word, (iwA m)[o + j]? = some p := fun j hj => by
    obtain ⟨p, a, b, hp, -⟩ := h3 j hj
    exact ⟨p, hp⟩
  refine ⟨(List.range ps.length).map (fun j => ((iwN m (o + j)).getD 0)), ?_⟩
  have := decNL_of_get m ((List.range ps.length).map (fun j => ((iwN m (o + j)).getD 0))) o (fun j hj => by
    simp only [List.length_map, List.length_range] at hj
    obtain ⟨p, hp⟩ := hget j hj
    simp [iwN, nat?, hp])
  simpa [h2] using this

theorem eqL_cons {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState} {n : Nat}
    {m m' : Mem} {x o l : Word} {r : List Word} {es : List (EIdx × EIdx)} {ea eb : Word}
    (h : consW n m x o l = some (r, m')) (hS : StageR dn vis fe m a)
    (hE : EqL m o.toNat l.toNat es) (hx : RecAt m x ea eb) (hea : H ea) (heb : H eb) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧
      EqL m' (r.headD 0).toNat (r.tail.headD 0).toNat ((decE ea, decE eb) :: es) := by
  obtain ⟨xs, hxs⟩ := hE.decNL
  obtain ⟨hS', hg, hd, ht⟩ := consW_stageN h hS hE.1 hxs
  obtain ⟨hlen, hget⟩ := decNL_getW m l.toNat o.toNat xs hxs
  obtain ⟨hlen', hget'⟩ := decNL_getW m' _ _ _ hd
  simp only [List.length_cons] at hlen'
  have hel := hE.2.1
  refine ⟨hS', hg, ?_, ?_, ?_⟩
  · omega
  · simp only [List.length_cons]; omega
  · intro j hj
    cases j with
    | zero =>
      obtain ⟨w, hw, hwx⟩ := hget' 0 (by simp)
      have : w = x := UInt64.toNat_inj.mp (by simpa using hwx)
      subst this
      exact ⟨w, ea, eb, by simpa using hw, hx.grow hg, hea, heb, by simp⟩
    | succ j =>
      have hj' : j < es.length := by simpa using hj
      obtain ⟨w, hw, hwx⟩ := hget' (j + 1) (by simp only [List.length_cons]; omega)
      obtain ⟨p, pa, pb, hp, hr, hpa, hpb, hpe⟩ := hE.2.2 j hj'
      obtain ⟨w0, hw0, hwx0⟩ := hget j (by omega)
      have hpw : w0 = p := by
        have := hp; rw [hw0] at this; exact Option.some.inj this
      have : w = p := UInt64.toNat_inj.mp (by
        simp only [List.getElem_cons_succ] at hwx
        rw [hwx, ← hwx0, hpw])
      subst this
      refine ⟨w, pa, pb, ?_, hr.grow hg, hpa, hpb, by simpa using hpe⟩
      simpa [Nat.add_assoc, Nat.add_comm 1 j] using hw

section sub
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}

structure NatSubProg (p : Prog) : Prop extends NatEqProg p where
  lSubstConst0 : p.lookup "subst_const0" = some substConst0L
  lSlCons : p.lookup "sl_cons" = some slCons
  lIwCopy : p.lookup "iw_copy" = some iwCopy
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

/-! ### `subst_const0_pairs` -/

def pairsW (p : Prog) (n : Nat) (m : Mem) (nm r o l : Word) : Option (List Word × Mem) :=
  if l = 0 then some ([0, 0], m) else
  ntBW (callW p n "subst_const0" [nm, r, 4000000000, rdW (m.arr64 IW) (rdW (m.arr64 IW) o)] m) fun r1 m1 =>
  ntBW (callW p n "subst_const0" [nm, r, 4000000000, rdW (m1.arr64 IW) (rdW (m.arr64 IW) o + 1)] m1) fun r2 m2 =>
  ntBW (callW p n "subst_const0_pairs" [nm, r, o + 1, l - 1] m2) fun r3 m3 =>
  ntBW (callW p n "rec2" [r1.headD 0, r2.headD 0] m3) fun r4 m4 =>
  ntBW (callW p n "sl_cons" [r4.headD 0, r3.headD 0, r3.tail.headD 0] m4) fun r5 m5 =>
  some ([r5.headD 0, r5.tail.headD 0], m5)

theorem pairs_specW (p : Prog) (hp : p.lookup "subst_const0_pairs" = some substConst0PairsL) (n : Nat)
    (s₀ : St) (nm r o l : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "subst_const0_pairs" [nm, r, o, l]
    ⦃fun res s' => LocEq s' s₀ ∧ pairsW p n s₀.mem nm r o l = some (res, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, substConst0PairsL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "subst_const0", callW_spec p n "subst_const0_pairs", callW_spec p n "rec2",
      callW_spec p n "sl_cons"] <;>
    finish (gen := 20) (instances := 10000) [pairsW, ntBW]

theorem pairs_ref (hN : NatSubProg p) (nm r : Word) (hn : H nm) (hr : H r) :
    ∀ (ps : List (EIdx × EIdx)) (o l : Word) (k : Nat) (m : Mem) (a : AState) (res : List Word)
      (m' : Mem), StageR dn vis fe m a → EqL m o.toNat l.toNat ps → o.toNat + l.toNat < 2 ^ 64 →
      callW p k "subst_const0_pairs" [nm, r, o, l] m = some (res, m') →
      ∃ x a', (substConst0Pairs (decI nm) (decE r) ps).run a = .ok (x, a') ∧
        KeepPost dn vis fe decEqRL m m' a' res x := by
  intro ps
  induction ps with
  | nil =>
    intro o l k m a res m' hS hE hb hc
    have hl0 : l = 0 := UInt64.toNat_inj.mp (by have := hE.2.1; simpa using this)
    cases k with
    | zero => rw [callW_zero] at hc; cases hc
    | succ k =>
    have hw := callW_model (M := fun mm => pairsW p k mm nm r o l) (pairs_specW p hN.lSubstConst0Pairs k · nm r o l) hc
    simp only [pairsW, hl0, if_true, Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    exact ⟨[], a, rfl, hS, IWGrow.refl _, by
      refine ⟨by simp, by simp, fun j hj => by simp at hj⟩⟩
  | cons e es ih =>
    intro o l k m a res m' hS hE hb hc
    cases k with
    | zero => rw [callW_zero] at hc; cases hc
    | succ k =>
    obtain ⟨pp, ea, eb, hl0, hpp, hrec, hea, heb, he, hrest⟩ := hE.cons
    have hw := callW_model (M := fun mm => pairsW p k mm nm r o l) (pairs_specW p hN.lSubstConst0Pairs k · nm r o l) hc
    unfold pairsW at hw
    rw [if_neg (fun h => hl0 (by simp [h]))] at hw
    have hpp' : rdW (m.arr64 IW) o = pp := by
      simp only [iwA] at hpp; simp [rdW, hpp]
    have hea' : rdW (m.arr64 IW) pp = ea := by
      obtain ⟨-, h2, -⟩ := hrec; simp only [iwA] at h2; simp [rdW, h2]
    have hpb : (pp + 1).toNat = pp.toNat + 1 := by
      obtain ⟨h1, -, -⟩ := hrec
      have e1 := hS.2.1; have e2 := hS.2.2.2.1; have e3 : pp.toNat + 1 < 2 ^ 64 := by omega
      rw [UInt64.toNat_add]; simp only [UInt64.toNat_one]; exact Nat.mod_eq_of_lt e3
    have heb' : ∀ m1, IWGrow m m1 → rdW (m1.arr64 IW) (pp + 1) = eb := by
      intro m1 hg
      obtain ⟨h1, -, h3⟩ := hrec
      simp only [iwA] at h3; simp only [rdW, hpb]; rw [hg.2.2.1 _ (by omega)]; simp [h3]
    rw [hpp', hea'] at hw
    cases h1 : callW p k "subst_const0" [nm, r, 4000000000, ea] m with
    | none => rw [h1] at hw; simp at hw
    | some q1 =>
    obtain ⟨r1, m1⟩ := q1
    rw [h1, bW_some] at hw
    obtain ⟨x1, a1, hrun1, hK1⟩ := sc0_ref hN nm r _ 4000000000 fuelW ea k m a r1 m1 hS hn hr hea h1
    obtain ⟨hS1, hg1, hl1, hx1⟩ := hK1
    rw [heb' m1 hg1] at hw
    cases h2 : callW p k "subst_const0" [nm, r, 4000000000, eb] m1 with
    | none => rw [h2] at hw; simp at hw
    | some q2 =>
    obtain ⟨r2, m2⟩ := q2
    rw [h2, bW_some] at hw
    obtain ⟨x2, a2, hrun2, hK2⟩ := sc0_ref hN nm r _ 4000000000 fuelW eb k m1 a1 r2 m2 hS1 hn hr heb h2
    obtain ⟨hS2, hg2, hl2, hx2⟩ := hK2
    cases h3 : callW p k "subst_const0_pairs" [nm, r, o + 1, l - 1] m2 with
    | none => rw [h3] at hw; simp at hw
    | some q3 =>
    obtain ⟨r3, m3⟩ := q3
    rw [h3, bW_some] at hw
    have ho1 : (o + 1).toNat = o.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have hl1' : (l - 1).toNat = l.toNat - 1 := by
      have : 0 < l.toNat := Nat.pos_of_ne_zero hl0
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
    have hrest2 : EqL m2 (o + 1).toNat (l - 1).toNat es := by
      rw [ho1, hl1']; exact hrest.grow (hg1.trans hg2)
    obtain ⟨x3, a3, hrun3, hK3⟩ := ih (o + 1) (l - 1) k m2 a2 r3 m3 hS2 hrest2 (by omega) h3
    obtain ⟨hS3, hg3, hd3⟩ := hK3
    cases h4 : callW p k "rec2" [r1.headD 0, r2.headD 0] m3 with
    | none => rw [h4] at hw; simp at hw
    | some q4 =>
    obtain ⟨r4, m4⟩ := q4
    rw [h4, bW_some] at hw
    have hR4 := rec2_fref p hN.lIwAlloc hN.lRec2 (r1.headD 0) (r2.headD 0) k m3 r4 m4 hS3.2 h4
    have hK4 := hR4.2.1
    have hS4 := hK4.stage hS3
    have rec4 := recAt_of_post hR4 hS3.2
    cases h5 : callW p k "sl_cons" [r4.headD 0, r3.headD 0, r3.tail.headD 0] m4 with
    | none => rw [h5] at hw; simp at hw
    | some q5 =>
    obtain ⟨r5, m5⟩ := q5
    rw [h5, bW_some] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨hr5, rfl⟩ := hw
    obtain ⟨s', hs', -, hcons⟩ := triple_of_callW (s₀ := ⟨m4, Locals.init []⟩)
      (slCons_specW p hN.lIwAlloc hN.lIwCopy hN.lSlCons k _ (r4.headD 0) (r3.headD 0) (r3.tail.headD 0)) h5
    have hE3 : EqL m4 (r3.headD 0).toNat (r3.tail.headD 0).toNat x3 := by
      have := hd3; simp only [decEqRL, ntGetD0, ntGetD1] at this; exact this.grow hK4.1
    have hcons' : consW k m4 (r4.headD 0) (r3.headD 0) (r3.tail.headD 0) = some (r5, m5) := by
      rw [← hs']; exact hcons
    obtain ⟨hS5, hg5, hE5⟩ := eqL_cons hcons' hS4 hE3 rec4 hl1 hl2
    subst hr5 he
    refine ⟨(decE (r1.headD 0), decE (r2.headD 0)) :: x3, a3, ?_, hS5, hg1.trans (hg2.trans (hg3.trans (hK4.1.trans hg5))), ?_⟩
    · simp only [substConst0Pairs, StateT.run_bind, hrun1, hrun2, hrun3, exc_ok_bind', StateT.run_pure,
        ← hx1, ← hx2]
      rfl
    · simp only [decEqRL, ntGetD0, ntGetD1, List.headD_cons, List.tail_cons]
      exact hE5

@[refines ConRon.Arena.substConst0Pairs]
theorem substConst0Pairs_refines (hN : NatSubProg p) (nm r o l : Word) (ps : List (EIdx × EIdx)) :
    RefAM p "subst_const0_pairs" [nm, r, o, l]
      (fun m a => StageR dn vis fe m a ∧ H nm ∧ H r ∧ EqL m o.toNat l.toNat ps ∧
        o.toNat + l.toNat < 2 ^ 64)
      (substConst0Pairs (decI nm) (decE r) ps) (KeepPost dn vis fe decEqRL) :=
  CallRef.refAM (fun k m a res m' ⟨hS, hn, hr, hE, hb⟩ hc =>
    pairs_ref hN nm r hn hr ps o l k m a res m' hS hE hb hc)

end sub

end L.Ind
