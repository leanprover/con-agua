import ConAgua.Arena.IndT.Sum3
import ConAgua.Arena.IndT.PosCensus
import ConAgua.Arena.KnotE
import ConAgua.Checker.NoVerdictClosed

/-!
# Error refinements of `check_field_sort_bound`, `nest_cont_key` (lane `verdicts-b`, helper `c6`)
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Ind

open L.Arena

l_model cfbE_spec (p : Prog) (hf : p.lookup "check_field_sort_bound" = some checkFieldSortBoundL)
  fns [hf ↦ cfbE] grind [arena_grind] fold [tierW, idxW]
  extra [evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] finish [tierW, idxW] errors

/-- **`check_field_sort_bound`'s error refinement**: a failing run (the model `cfbE`, the real
calls) of class `1` or `2` claims that the twin's universe bound `sfbT` fails with that class.
The callees (`lv_leq_top`, `pin_word`, `lvl_eq_true`, `sl_contains`) are outside the verdict
closure. -/
theorem cfbE_claim {p : Prog} (hcl : CoreStageClosed p) (hLC : LvlCacheProg p)
    (hLT : p.lookup "lv_leq_top" = some lvLeqTop) (hnv : closedNV p L.Checker.nvFns = true)
    {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {env : ConLeche.Env} (n : Nat) (m : Mem)
    (a : AState) (isProp large s io il fv u : Word) (idxArgs : List EIdx)
    (hC : StageC dn vis fe env m a) (hA : AbsOK m)
    (hpw : p.lookup "pin_word" = some pinWordL) (het : p.lookup "lvl_eq_true" = some lvlEqTrue)
    (hc : p.lookup "sl_contains" = some slContains)
    (hu : H u) (hs : H s) (hfv : H fv) (hidx : decHL m io.toNat il.toNat = some idxArgs)
    (hib : io.toNat + il.toNat ≤ iwTop m) {lu sP : ConLeche.Level}
    (hdu : denoteL a.store.ls (decI u) = some lu) (hsP : denoteL a.store.ls (decI s) = some sP)
    (e : Err) (he : cfbE p n m isProp large s io il fv u = .error e) :
    ErrClaim (sfbT (isProp != 0) (large != 0) (decI s) idxArgs (decI fv) (decI u)) a e := by
  cases n with
  | zero => rw [cfbE] at he; cases he; exact ErrClaim.of_cls0 Err.cls_outOfFuel
  | succ n =>
  by_cases hp : isProp = 0
  · rw [cfbE.arm1 p n m isProp large s io il fv u hp] at he
    simp only [sfbT, hp, bne_self_eq_false, Bool.not_false, ite_true]
    rw [sfb_leq_eq]
    cases h1 : callE p n "lv_leq_top" [u, s] m with
    | error e1 =>
      rw [h1, cfbE.k_lv_leq_top.none] at he
      cases he
      exact ErrClaim.of_callE_nv hnv (by decide +kernel) h1
    | ok q =>
      obtain ⟨r, m1⟩ := q
      rw [h1] at he
      obtain ⟨x, a', hrun, -, -, hx, -⟩ :=
        lvLeqTop_simC p hLC.lev hLT n hC hA u s hu hs lu sP hdu hsP r m1 (callW_of_callE h1)
      refine ErrClaim.bind_right hrun ?_
      simp only [decLvlEq] at hx
      by_cases h0 : r.headD 0 = 0
      · rw [cfbE.k_lv_leq_top.abort1 p r m1 h0] at he
        cases he
        cases x with
        | none => exact ErrClaim.bind_left (ErrClaim.fail _ _ (by decide))
        | some b => cases b <;> (rw [h0] at hx; exact absurd hx (by simp))
      by_cases h2 : r.headD 0 = 2
      · rw [cfbE.k_lv_leq_top.arm1 p r m1 h0 h2, cfbE.j1.arm1] at he
        cases he
      · rw [cfbE.k_lv_leq_top.abort2 p r m1 h0 h2] at he
        cases he
        cases x with
        | none => exact absurd hx h0
        | some b =>
          cases b with
          | true => exact absurd hx h2
          | false =>
            exact ErrClaim.congr (T' := ConRon.Arena.fail (.invalid "direct sum: field universe too large"))
              rfl (ErrClaim.fail _ _ (by decide))
  have hp' : (isProp != 0) = true := by simpa using hp
  by_cases hl : large = 0
  · rw [cfbE.arm3 p n m isProp large s io il fv u hp hl, cfbE.j1.arm1] at he
    cases he
  have hl' : (large != 0) = true := by simpa using hl
  rw [cfbE.arm2 p n m isProp large s io il fv u hp hl] at he
  simp only [sfbT, hp', hl', Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
  have hS := hC.stage
  cases h1 : callE p n "pin_word" [53] m with
  | error e1 =>
    rw [h1, cfbE.k_pin_word.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h1
  | ok q =>
  obtain ⟨rz, m1⟩ := q
  obtain ⟨s', hs', -, hmm, hz'⟩ := triple_of_callW (pinWord_specV p hpw n ⟨m, Locals.init []⟩ 53)
    (callW_of_callE h1)
  simp only at hmm
  subst hs'
  rw [h1, cfbE.k_pin_word.eq_2, hmm] at he
  simp only at hz'
  have hpne : rdW (m.arr64 PINS) 0 ≠ 0 := by
    intro h0; simp [pinWordV, h0] at hz'
  obtain ⟨hrun0, hz⟩ := pinZero_stage hS hz'
  have hzp : rz.headD 0 = pinW m 53 := by
    simp only [pinWordV, hpne, ite_false, Option.some.injEq] at hz'
    rw [← hz']; rfl
  have hF := hS.1.pins.full hpne
  obtain ⟨lz, hdz⟩ := hC.stageT.twin.den.zero
  rw [hF.zeroLevel, ← hzp] at hdz
  refine ErrClaim.bind_right hrun0 ?_
  cases h2 : callE p n "lvl_eq_true" [u, rz.headD 0] m with
  | error e2 =>
    rw [h2, cfbE.k_lvl_eq_true.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h2
  | ok q2 =>
  obtain ⟨rq, mq⟩ := q2
  rw [h2, cfbE.k_lvl_eq_true.eq_2] at he
  obtain ⟨s2, hs2, -, hW2⟩ := triple_of_callW (eqTrue_specC p het (realCall p) (realCall_spec p) n
    ⟨m, Locals.init []⟩ u (rz.headD 0)) (callW_of_callE h2)
  simp only at hW2
  cases n with
  | zero => simp [eqTrueC] at hW2
  | succ n' =>
  rw [eqTrueC_succ] at hW2
  rcases he' : realCall p n' "lvl_eq_c" [u, rz.headD 0] m with _ | ⟨r1, m1⟩
  · rw [he'] at hW2; simp [eqTrueK] at hW2
  rw [he', eqTrueK_some] at hW2
  simp only [Option.some.injEq, Prod.mk.injEq] at hW2
  obtain ⟨hreq, hm2⟩ := hW2
  obtain ⟨x, a1, hrun1, hC1, hg1, hx, hA1, -⟩ :=
    lvlEqC_simC p hcl hLC n' hC hA u (rz.headD 0) hu hz lu lz hdu hdz r1 m1 he'
  refine ErrClaim.bind_right hrun1 ?_
  have hmq : mq = m1 := by rw [← hs2, ← hm2]
  subst hmq
  have hS1 := hC1.stage
  have hidx1 : decHL mq io.toNat il.toNat = some idxArgs := by
    rw [decHL_grow hg1 hib]; exact hidx
  cases h3 : callE p (n' + 1) "sl_contains" [io, il, fv] mq with
  | error e3 =>
    rw [h3, cfbE.k_sl_contains.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h3
  | ok q3 =>
  obtain ⟨r3, m3⟩ := q3
  by_cases hg : (rq.headD 0) = 0 ∧ r3.headD 0 = 0
  · rw [h3, cfbE.k_sl_contains.abort1 p _ r3 m3 hg] at he
    cases he
    obtain ⟨s3, -, -, -, hW3⟩ := triple_of_callW (slContains_spec p hc (n' + 1) ⟨mq, Locals.init []⟩ io il fv)
      (callW_of_callE h3)
    simp only at hW3
    obtain ⟨ws, hws, hwsd, hwlt⟩ := slR_of_decHL mq _ _ idxArgs hidx1 (hS1.lt64 (by have := hg1.1; omega))
    simp only [UInt64.ofNat_toNat] at hws
    have hct := containsW_ok (n' + 1) _ _ _ _ _ _ hws hW3
    have hr1 : r1.headD 0 ≠ 2 := by
      intro h2; rw [ite_eq_left h2] at hreq; rw [hg.1] at hreq; exact absurd hreq (by decide)
    have hxn : x ≠ some true := by
      intro hxt; subst hxt; simp only [decLvlEq] at hx; exact hr1 hx
    have hnin : ws.contains fv = false := by
      cases hcw : ws.contains fv
      · rfl
      · rw [hcw, hg.2] at hct; exact absurd hct (by decide)
    have hcond : (x == some true || idxArgs.contains (decI fv)) = false := by
      rw [hwsd, sumContains_decI fv hfv ws hwlt, hnin]
      cases x with
      | none => rfl
      | some b => cases b <;> simp_all
    refine ErrClaim.congr (T' := ConRon.Arena.fail (.invalid "direct sum: large eliminator with a non-propositional \
        field outside the indices")) ?_ (ErrClaim.fail _ _ (by decide))
    simp only [hcond]; rfl
  · rw [h3, cfbE.k_sl_contains.arm1 p _ r3 m3 hg, cfbE.j1.arm1] at he
    cases he

end L.Ind
