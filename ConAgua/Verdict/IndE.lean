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
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] finish [tierW, idxW] errors

/-- **`check_field_sort_bound`'s error refinement**: a failing run (the model `cfbE`, the real
calls) of class `1` or `2` claims that the twin's universe bound `sfbT` fails with that class.
The callees (`lv_leq_top`, `pin_word`, `lvl_eq_true`, `sl_contains`) are outside the verdict
closure. -/
theorem cfbE_claim {p : Prog} (hcl : CoreStageClosed p) (hLC : LvlCacheProg p)
    (hLT : p.lookup "lv_leq_top" = some lvLeqTop) (hnv : closedNV p _root_.L.Checker.nvFns = true)
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

l_model nckE_spec (p : Prog) (hf : p.lookup "nest_cont_key" = some nestContKeyL)
  fns [hf ↦ nckE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW, pos2_getElem_getD] errors

open ConRon.Bridge.Inductives (dCtx dProg dState dCtx_ext dProg_ext dState_ext)

local notation "V" => ConLeche.CheckMode.verified

section stmts
variable (p : Prog) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)

/-- **`nest_cont_new`'s error claim** at L fuel `n` (a callee's error claim, the shape of
`NewOKC`'s hypotheses; discharged bottom-up). -/
def NewOKE (n : Nat) : Prop :=
  ∀ (m : Mem) (a : AState) (ctx fu po pl kb nn us dO dL nPc cty ns : Word) (c : NestCtx)
    (prog : List NestHole) (ds : List EIdx) (NS : NestState)
    (ctxP : ConLeche.NestCtx) (progP : List ConLeche.NestHole) (nP : ConLeche.Name)
    (usP : List ConLeche.Level) (dsP : List ConLeche.Expr) (ctyP : ConLeche.Expr)
    (nsP : ConLeche.NestState),
    StageC dn vis fe env m a →
    WCtx dn vis fe m ctx po pl c prog → H nn → H us →
    DecB (fun m => (decHL m dO.toNat dL.toNat : Option (List EIdx))) m ds → dO.toNat + dL.toNat ≤ iwTop m →
    H cty → NSB m ns NS → PosMR m → AbsOK m →
    ConLeche.NestCtxOk ctxP → dCtx a.store env.find? c = some ctxP → dProg a.store prog = some progP →
    denoteN a.store.ns (decI nn) = some nP → denoteLs a.store.lss (decI us) = some usP →
    Frontend.denoteEList a.store ds = some dsP → denoteE a.store (decI cty) = some ctyP →
    dState a.store NS = some nsP →
    (∀ d ∈ dsP, ConLeche.Expr.WScoped (ctxP.hiAt progP.length) d) →
    (∀ d, (∀ y ∈ dsP, ConLeche.Expr.WScoped d y) → ConLeche.Expr.WScoped d ctyP) →
    ∀ e, callE p n "nest_cont_new" [vis, ctx, fu, po, pl, kb, nn, us, dO, dL, nPc, cty, ns] m = .error e →
      ErrClaim (nestContNew V fe c fu.toNat prog kb.toNat (decI nn) (decI us) ds nPc.toNat (decI cty) NS) a e

/-- **`nest_cont_key`'s error claim** at L fuel `n`. -/
def KeyOKE (n : Nat) : Prop :=
  ∀ (m : Mem) (a : AState) (ctx fu po pl kb nn us dO dL nPc cty ns : Word) (c : NestCtx)
    (prog : List NestHole) (ds : List EIdx) (NS : NestState)
    (ctxP : ConLeche.NestCtx) (progP : List ConLeche.NestHole) (nP : ConLeche.Name)
    (usP : List ConLeche.Level) (dsP : List ConLeche.Expr) (ctyP : ConLeche.Expr)
    (nsP : ConLeche.NestState),
    StageC dn vis fe env m a →
    WCtx dn vis fe m ctx po pl c prog → H nn → H us →
    DecB (fun m => (decHL m dO.toNat dL.toNat : Option (List EIdx))) m ds → dO.toNat + dL.toNat ≤ iwTop m →
    H cty → NSB m ns NS → PosMR m → AbsOK m →
    ConLeche.NestCtxOk ctxP → dCtx a.store env.find? c = some ctxP → dProg a.store prog = some progP →
    denoteN a.store.ns (decI nn) = some nP → denoteLs a.store.lss (decI us) = some usP →
    Frontend.denoteEList a.store ds = some dsP → denoteE a.store (decI cty) = some ctyP →
    dState a.store NS = some nsP →
    (∀ d ∈ dsP, ConLeche.Expr.WScoped (ctxP.hiAt progP.length) d) →
    (∀ d, (∀ y ∈ dsP, ConLeche.Expr.WScoped d y) → ConLeche.Expr.WScoped d ctyP) →
    ∀ e, nckE p n m vis ctx fu po pl kb nn us dO dL nPc cty ns = .error e →
      ErrClaim (nestContKey V fe c fu.toNat prog kb.toNat (decI nn) (decI us) ds nPc.toNat (decI cty) NS) a e

end stmts

/-- At fuel `0` the model is `outOfFuel`, class `0`. -/
theorem keyOKE_zero (p : Prog) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (env : ConLeche.Env) : KeyOKE p dn vis fe env 0 := by
  intro m a ctx fu po pl kb nn us dO dL nPc cty ns c prog ds NS ctxP progP nP usP dsP ctyP nsP hC hW hnn hus
    hds hdsb hcty hns hP hA hc hctx hprog hnP husP hdsP hctyP hnsP hwds hni e he
  rw [nckE.eq_1] at he
  cases he
  exact ErrClaim.of_cls0 Err.cls_outOfFuel

section steps
variable {p : Prog} (L : NbLook p) (hnv : closedNV p _root_.L.Checker.nvFns = true)
  (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) {env : ConLeche.Env}

include L hnv in
/-- **`nest_cont_key`'s error claim at L fuel `n`**, from `nest_cont_new`'s at the same fuel
(`keyOKC_step`'s proof, on the model `nckE`). -/
theorem keyOKE_step (n : Nat) (hNewE : NewOKE p dn vis fe env n) : KeyOKE p dn vis fe env (n + 1) := by
  intro m a ctx fu po pl kb nn us dO dL nPc cty ns c prog ds NS ctxP progP nP usP dsP ctyP nsP hC hW hnn hus
    hds hdsb hcty hns hP hA hc hctx hprog hnP husP hdsP hctyP hnsP hwds hni e he
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have R := L.ct.cr.rx
  have hS := hC.stage
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  rw [nckE.arm1] at he
  cases h1 : callE p n "rec4" [nn, us, dO, dL] m with
  | error e1 =>
    rw [h1, nckE.k_rec4.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h1
  | ok q =>
  obtain ⟨rk, m1⟩ := q
  obtain ⟨s1, hs1, -, hk⟩ := triple_of_callW (posRec4_specW p R.ha R.h4 n ⟨m, Locals.init []⟩ nn us dO dL)
    (callW_of_callE h1)
  simp only at hk
  rw [hs1] at hk
  rw [h1, nckE.k_rec4.eq_2] at he
  obtain ⟨hS1, hg1, hkq, ht1, hget1⟩ := posRecW_stage hk hS (by simp)
  simp only [List.length_cons, List.length_nil] at ht1
  have hK : DecB (fun m => decNK m (rk.headD 0).toNat) m1 ⟨decI nn, decI us, ds⟩ :=
    pos2_key_rec hnn hus (by omega) hget1 (hds.grow (OMono.decHL _ _) hg1)
  have htop1 : iwTop m1 < 2 ^ 64 := Nat.lt_of_le_of_lt hS1.2.1 hS1.2.2.2.1
  obtain ⟨hp6, hk0', ha0, -⟩ := nsb_words hns htop
  cases h2 : callE p n "nest_keys_contains" [rdW (m1.arr64 IW) (ns + 2), rdW (m1.arr64 IW) (ns + 3), rk.headD 0] m1 with
  | error e2 =>
    rw [h2, nckE.k_nest_keys_contains.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h2
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  obtain ⟨s2, hs2, -, hm2, hW2⟩ := triple_of_callW (nestKeysContains_spec p L.nag.hq L.nag.he L.nag.hkc n
    ⟨m1, Locals.init []⟩ _ _ _) (callW_of_callE h2)
  simp only at hm2 hW2
  rw [hs2] at hm2
  rw [pos2_ns_rd hg1 hp6 htop 2 (by decide), pos2_ns_rd hg1 hp6 htop 3 (by decide)] at hW2
  have hb1 := nkcW_ok (rk.headD 0) _ n m1 _ _ _ NS.active hW2 (ha0.grow hg1) hK htop1
  by_cases hb1n : r2.headD 0 ≠ 0
  · rw [h2, nckE.k_nest_keys_contains.abort1 p n vis ctx fu po pl kb nn us dO dL nPc cty ns (rk.headD 0) r2 m2 hb1n] at he
    cases he
    have hact : NS.active.contains ⟨decI nn, decI us, ds⟩ = true := by
      cases e : NS.active.contains ⟨decI nn, decI us, ds⟩ with
      | true => rfl
      | false => rw [e] at hb1; exact absurd (by simpa using hb1) hb1n
    simp only [nestContKey.eq_def, hact, ite_true]
    exact ErrClaim.fail _ _ (by decide)
  obtain rfl := hm2.symm
  rw [h2, nckE.k_nest_keys_contains.arm1 p n vis ctx fu po pl kb nn us dO dL nPc cty ns (rk.headD 0) r2 m1
    (by simpa using hb1n)] at he
  have hact : NS.active.contains ⟨decI nn, decI us, ds⟩ = false := by
    cases e : NS.active.contains ⟨decI nn, decI us, ds⟩ with
    | false => rfl
    | true =>
      have h0 : r2.headD 0 = 0 := by simpa using hb1n
      rw [e, h0] at hb1; exact absurd hb1 (by decide)
  cases h3 : callE p n "nest_ds_closed" [ctx, dO, dL] m1 with
  | error e3 =>
    rw [h3, nckE.k_nest_ds_closed.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h3
  | ok q3 =>
  obtain ⟨r3, m3⟩ := q3
  obtain ⟨s3, hs3, -, hW3⟩ := triple_of_callW (dc_spec' p L.dc.hf L.dc.hh L.dc.hg L.dc.hp n
    ⟨m1, Locals.init []⟩ ctx dO dL) (callW_of_callE h3)
  simp only at hW3
  rw [hs3] at hW3
  rw [h3] at he
  cases n with
  | zero => simp [dcWf] at hW3
  | succ n' =>
  have hhi0 : c.hiAt 0 < 2 ^ 64 := by have := hW.hb; simp only [NestCtx.hiAt] at this ⊢; omega
  obtain ⟨bc, a2, hrun2, hS2, hg2, hr2⟩ := dcWf_ok dn fe vis (n' + 1) m1 m3 a ctx dO dL c ds [r3.headD 0] hW3 hS1
    (hW.grow hg1).u.dec (hW.grow hg1).u.inn hhi0 ((hds.grow (OMono.decHL _ _) hg1).get (OMono.decHL _ _))
    (fun j hj => by have := hg1.1; omega)
  have hg12 := hg1.trans hg2
  have hP2 : PosMR m3 := (hP.fr (posRecW_mfr hk)).fr (dcWf_mfr hW3)
  have hA2 : AbsOK m3 := dcWf_afr hW3 (posRecW_afr hk hA)
  have hrun2' : (ds.allM fun x => do
      let b ← fvarB coreWalkFuel x
      pure (decide (b ≤ c.hiAt 0))).run a = .ok (bc, a2) := hrun2
  obtain ⟨p2, -⟩ := ConRon.Bridge.Inductives.closedAll_spec (c.hiAt 0) ds dsP a a2 bc hC.check.state hdsP hrun2'
  have hC2 : StageC dn vis fe env m3 a2 := hC.of_pstep hS2 hA2 p2
  have hnew : ∀ e', callE p (n' + 1) "nest_cont_new" [vis, ctx, fu, po, pl, kb, nn, us, dO, dL, nPc, cty, ns] m3 =
      .error e' → ErrClaim (nestContNew V fe c fu.toNat prog kb.toNat (decI nn) (decI us) ds nPc.toNat (decI cty) NS)
        a2 e' := fun e' h =>
    hNewE m3 a2 ctx fu po pl kb nn us dO dL nPc cty ns c prog ds NS ctxP progP nP usP dsP ctyP nsP hC2
      (hW.grow hg12) hnn hus (hds.grow (OMono.decHL _ _) hg12) (by have := hg12.1; omega) hcty
      (hns.grow hg12 htop) hP2 hA2 hc (dCtx_ext _ p2.ext _ _ hctx) (dProg_ext p2.ext _ _ hprog)
      (ConRon.Bridge.denoteN_ext hnP p2.ext) (ConRon.Bridge.denoteLs_ext husP p2.ext)
      (ConRon.Bridge.denoteEList_ext p2.ext _ _ hdsP) (ConRon.Bridge.denote_ext hctyP p2.ext)
      (dState_ext p2.ext _ _ hnsP) hwds hni e' h
  simp only [nestContKey.eq_def, hact, Bool.false_eq_true, ite_false]
  refine ErrClaim.bind_right hrun2' ?_
  have hnewR : ∀ e', nckE.j1 p (n' + 1) vis ctx fu po pl kb nn us dO dL nPc cty ns m3 = .error e' →
      ErrClaim (nestContNew V fe c fu.toNat prog kb.toNat (decI nn) (decI us) ds nPc.toNat (decI cty) NS)
        a2 e' := fun e' h => by
    simp only [nckE.j1] at h
    cases h5 : callE p (n' + 1) "nest_cont_new" [vis, ctx, fu, po, pl, kb, nn, us, dO, dL, nPc, cty, ns] m3 with
    | error e5 => rw [h5, nckE.k_nest_cont_new.none] at h; cases h; exact hnew _ h5
    | ok q5 => obtain ⟨r5, m5⟩ := q5; rw [h5, nckE.k_nest_cont_new.arm1] at h; cases h
  by_cases hr3 : r3.headD 0 ≠ 0
  · rw [nckE.k_nest_ds_closed.arm1 p (n' + 1) vis ctx fu po pl kb nn us dO dL nPc cty ns (rk.headD 0) r3 m3 hr3] at he
    have hbc : bc = true := by cases bc <;> simp_all
    subst hbc
    cases h4 : callE p (n' + 1) "nest_keys_contains"
        [rdW (m3.arr64 IW) ns, rdW (m3.arr64 IW) (ns + 1), rk.headD 0] m3 with
    | error e4 =>
      rw [h4, nckE.k_nest_keys_contains_2.none] at he
      cases he
      exact ErrClaim.of_callE_nv hnv (by decide +kernel) h4
    | ok q4 =>
    obtain ⟨r4, m4⟩ := q4
    obtain ⟨s4, hs4, -, hm4, hW4⟩ := triple_of_callW (nestKeysContains_spec p L.nag.hq L.nag.he L.nag.hkc (n' + 1)
      ⟨m3, Locals.init []⟩ _ _ _) (callW_of_callE h4)
    simp only at hm4 hW4
    rw [hs4] at hm4
    obtain rfl := hm4.symm
    rw [h4] at he
    rw [pos2_rd_grow hg12 (by omega), pos2_ns_rd hg12 hp6 htop 1 (by decide)] at hW4
    have hb2 := nkcW_ok (rk.headD 0) _ (n' + 1) m3 _ _ _ NS.keys.toList hW4 (hk0'.grow hg12)
      (hK.grow (decNK_mono _) hg2) (Nat.lt_of_le_of_lt hS2.2.1 hS2.2.2.2.1)
    by_cases hb2n : r4.headD 0 ≠ 0
    · rw [nckE.k_nest_keys_contains_2.arm1 p (n' + 1) vis ctx fu po pl kb nn us dO dL nPc cty ns r4 m3 hb2n] at he
      cases he
    · have h0 : r4.headD 0 = 0 := by simpa using hb2n
      rw [nckE.k_nest_keys_contains_2.arm2 p (n' + 1) vis ctx fu po pl kb nn us dO dL nPc cty ns r4 m3 h0] at he
      have hout : NS.keys.contains ⟨decI nn, decI us, ds⟩ = false := by
        rw [← Array.contains_toList]
        cases e : NS.keys.toList.contains ⟨decI nn, decI us, ds⟩ with
        | false => rfl
        | true => rw [e, h0] at hb2; exact absurd hb2 (by decide)
      exact ErrClaim.ite_neg (by simp [hout]) (hnewR e he)
  · have h0 : r3.headD 0 = 0 := by simpa using hr3
    rw [nckE.k_nest_ds_closed.arm2 p (n' + 1) vis ctx fu po pl kb nn us dO dL nPc cty ns (rk.headD 0) r3 m3 h0] at he
    have hbc : bc = false := by cases bc <;> simp_all
    subst hbc
    exact ErrClaim.ite_neg (by simp) (hnewR e he)

end steps

end L.Ind
