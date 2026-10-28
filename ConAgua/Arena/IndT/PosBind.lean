import ConAgua.Arena.IndT.PosFields
import ConAgua.Arena.IndPosSpec.NestCrest
import ConAgua.Arena.IndRealAbsPos

/-!
# `nest_pos_bind` under `StageC` (lane `indstaget`, helper `indstaget-pos`)

`bindRef_step`: `nest_pos_bind` refines `posBindT` (con-ron's `nestPos_succ`, its `Π` case), both
outcomes (`npbE`, unified): the domain's occurrence check (no state change), its variable (`internFVarE_run`), the body
opened (`instantiate1Fast_run`), walked (the block's `PosRef` at `n`, `nestPos_spec` on the run
for the walked body's denotation), abstracted (`abstract1Fast_spec`) and rebuilt
(`internForallEE_run`).
-/


open ConRon.Arena
open ConRon.Bridge.Inductives (PStep dCtx dProg dState dCtx_ext dProg_ext dState_ext kindOf)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section steps
variable (p : Prog) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) {env : ConLeche.Env}
  (henv : ConLeche.EnvWF env)

include henv in
theorem bindRef_step (L : NbLook p) (n : Nat) (ih : NbRef p dn vis fe env n) : BindRef p dn vis fe env (n + 1) := by
  intro m a ctx fu po pl dep kb w ns c prog NS ctxP progP wP nsP hC hW hw h6 hns hP hA hc hctx hprog hwP hnsP hww
  have R := L.ct.cr.rx
  have hS := hC.stage
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  rw [npbE.arm1]
  -- `nest_ctx_hi_at`
  cases h1 : callE p n "nest_ctx_hi_at" [ctx, pl] m with
  | error e1 =>
    rw [npbE.k_nest_ctx_hi_at.eq_1]
    exact fun hG => ErrClaim.of_callE_nv hG.nv (_root_.L.Checker.nv_mem (by decide +kernel)) h1
  | ok q1 =>
  obtain ⟨rh, m1⟩ := q1
  obtain ⟨s1, hs1, -, hm1, hrh⟩ := triple_of_callW (nestCtxHiAt_specE p R.hi n ⟨m, Locals.init []⟩ ctx pl)
    (callW_of_callE h1)
  dsimp only at hm1 hrh
  rw [hs1] at hm1
  rw [npbE.k_nest_ctx_hi_at.arm1, hrh, hm1]
  -- `e_view`
  cases h2 : callE p n "e_view" [w] m with
  | error e2 =>
    rw [npbE.k_e_view.eq_1]
    exact fun hG => ErrClaim.of_callE_nv hG.nv (_root_.L.Checker.nv_mem (by decide +kernel)) h2
  | ok q2 =>
  obtain ⟨rv, m2⟩ := q2
  obtain ⟨s2, hs2, hm2, hev, hrv⟩ := triple_of_callW (eView_spec p R.hl.hv n ⟨m, Locals.init []⟩ w)
    (callW_of_callE h2)
  have hm2' : m2 = m := by rw [← hs2, hm2]
  dsimp only at hrv
  rw [npbE.k_e_view.arm1, hm2', hrv]
  rw [hrv] at hev
  obtain ⟨d, b, hv, hd, hb, hvb, htag⟩ := pos2_forall_view hS hw h6 hev
  simp only [hv, List.tail_cons, List.headD_cons]
  obtain ⟨-, hvbS⟩ := ConRon.Bridge.Inductives.viewBind_run hvb
  obtain ⟨dP, bP, rfl, hdP, hbP⟩ := ConRon.Bridge.denote_forallE_inv hC.check.state.wf
    (ConRon.Bridge.view_forallE_of_viewBind (by simp [htag]) hvbS.symm) hwP
  simp only [ConLeche.Expr.WScoped] at hww
  unfold posBindT
  refine RefE.bind_right hvb ?_
  dsimp only
  obtain ⟨hn0, hnb0, -, -, hnP, -⟩ := ctx_fields hW.u.dec hW.u.inn htop
  have hne0 := ctx_names_end hW.u.dec hW.u.inn hW.u.sl htop
  have hhi := hW.hi htop
  -- the domain mentions no member and no hole
  cases h3 : callE p n "nest_occ" [rdW (m.arr64 IW) ctx, rdW (m.arr64 IW) (ctx + 1), rdW (m.arr64 IW) (ctx + 4),
      nhiW m ctx pl, d] m with
  | error e3 =>
    rw [npbE.k_nest_occ.eq_1]
    exact fun hG => ErrClaim.of_callE_nv hG.nv (_root_.L.Checker.nv_mem (by decide +kernel)) h3
  | ok q3 =>
  obtain ⟨ro, m3⟩ := q3
  obtain ⟨s3, hs3, -, hno⟩ := triple_of_callW (nestOcc_spec' p L.nit.no n ⟨m, Locals.init []⟩ _ _ _ _ d)
    (callW_of_callE h3)
  dsimp only at hno
  rw [hs3] at hno
  obtain ⟨mp, hmp⟩ := hP.no
  obtain ⟨bo, hrun1, hbo, hM1, hS1, hg1, hf1⟩ := noConstWf_ok n dn fe vis m m3 a _ _ _ _ d _ c.names mp hno hS hd hn0
    (by omega) hmp
  rw [hnP, hhi, decE_eq] at hrun1
  refine RefE.bind_right hrun1 ?_
  by_cases ho : ro.headD 0 ≠ 0
  · rw [npbE.k_nest_occ.abort1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ ho]
    have hbo' : bo = true := by rw [← hbo]; simpa using ho
    subst hbo'
    exact RefE.ite_pos rfl fun _ => ErrClaim.fail _ _ (by decide)
  have hbo' : bo = false := by rw [← hbo]; simpa using ho
  subst hbo'
  refine RefE.ite_neg (by simp) ?_
  rw [npbE.k_nest_occ.eq_2, ite_eq_right ho]
  by_cases hd1 : dep + 1 = 0
  · rw [ite_eq_left hd1]; exact RefE.of_cls0 rfl
  rw [ite_eq_right hd1]
  by_cases hk1 : kb + 1 = 0
  · rw [ite_eq_left hk1]; exact RefE.of_cls0 rfl
  rw [ite_eq_right hk1]
  -- the variable, the body opened
  cases h4 : callE p n "intern_fvar" [dep, d] m3 with
  | error e4 =>
    rw [npbE.k_intern_fvar.eq_1]
    exact fun hG => ErrClaim.of_callE_nv hG.nv (_root_.L.Checker.nv_mem (by decide +kernel)) h4
  | ok q4 =>
  obtain ⟨rf, m4⟩ := q4
  obtain ⟨s4, hs4, -, hfv⟩ := triple_of_callW (internFVar_spec p R.hl.hff R.hl.hfp R.hl.hif n ⟨m3, Locals.init []⟩ dep d)
    (callW_of_callE h4)
  dsimp only at hfv
  rw [hs4] at hfv
  by_cases hfvb : 4294967296 ≤ rf.headD 0
  · rw [npbE.k_intern_fvar.abort1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ hfvb]; exact RefE.of_cls0 rfl
  rw [npbE.k_intern_fvar.arm1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ hfvb]
  have hfvH : H (rf.headD 0) := by
    have : ¬ (4294967296 : Word).toNat ≤ (rf.headD 0).toNat := fun e => hfvb (UInt64.le_iff_toNat_le.mpr e)
    simp only [H]; simpa using this
  obtain ⟨a2, hrun2, hS2, hg2⟩ := internFVar_stage hS1 dep d hd hfv
  have e2 : (internFVarE dep.toNat (decI d)).run a = .ok (decI (rf.headD 0), a2) := by
    simpa [internFVarE, decE_eq] using hrun2
  obtain ⟨p2, hfvP⟩ := ConRon.Bridge.Inductives.internFVarE_run hC.check.state hdP e2
  refine RefE.bind_right e2 ?_
  cases h5 : callE p n "instantiate1_fast" [CWF, b, rf.headD 0, 0] m4 with
  | error e5 =>
    rw [npbE.k_instantiate1_fast.eq_1]
    exact fun hG => ErrClaim.of_callE_nv hG.nv (_root_.L.Checker.nv_mem (by decide +kernel)) h5
  | ok q5 =>
  obtain ⟨rb, m5⟩ := q5
  obtain ⟨s5, hs5, -, hin⟩ := triple_of_callW (i1F_spec p L.hi1 n ⟨m4, Locals.init []⟩ _) (callW_of_callE h5)
  dsimp only at hin
  rw [hs5] at hin
  rw [npbE.k_instantiate1_fast.arm1]
  obtain ⟨b2, a3, hrun3, hS3, hg3, hb2H, hb2d⟩ := i1F_ok dn vis fe b (rf.headD 0) 0 hb m4 m5 a2 rb hin hS2
  rw [CWF_eq] at hrun3
  have e3 : (instantiate1Fast coreWalkFuel (decI b) (decI (rf.headD 0)) 0).run a2 = .ok (b2, a3) := by
    simpa using hrun3
  refine RefE.bind_right e3 ?_
  have hbP2 : denoteE a2.store (decI b) = some bP := ConRon.Bridge.denote_ext hbP p2.ext
  obtain ⟨q1, q2, q4, q5, -, q7⟩ := ConRon.Bridge.ExprOps.instantiate1Fast_run p2.ok hfvP
    (by rw [hbP2]; rfl) e3
  have p3 : PStep a2 a3 := PStep.of_caches q1 q2 q4 q5
  have hb2P : denoteE a3.store b2 = some (bP.instantiate1 (.fvar dep.toNat dP) 0) := q7 _ hbP2
  have hg13 := (hg1.trans hg2).trans hg3
  have hA3 : AbsOK m5 := i1F_afr hin (fvinternW_afr hfv (noConstWf_afr hno hA))
  have p23 := p2.trans p3
  have hC3 : StageC dn vis fe env m5 a3 := hC.of_pstep hS3 hA3 p23
  have hx03 := p23.ext
  have hdep1 : (dep + 1).toNat = dep.toNat + 1 := pos2_word_succ hd1
  have hwb : ConLeche.Expr.WScoped (dep + 1).toNat (bP.instantiate1 (.fvar dep.toNat dP) 0) := by
    rw [hdep1]; exact ConLeche.Expr.WScoped.instantiate1 hww.1 0 hww.2
  have hb2P' : denoteE a3.store (decI (rb.headD 0)) = some (bP.instantiate1 (.fvar dep.toNat dP) 0) := by
    rw [show (decI (rb.headD 0) : EIdx) = b2 by simpa [decE_eq] using hb2d]; exact hb2P
  -- the codomain walked
  have hR := ih.pos m5 a3 ctx fu po pl (dep + 1) (kb + 1) (rb.headD 0) ns c prog NS ctxP progP _ nsP hC3
    (hW.grow hg13) (by simpa using hb2H) (hns.grow hg13 htop)
    (((hP.setNo hf1 ⟨∅, hM1⟩).fr (fvinternW_mfr hfv)).fr (MFr.ofI1F hin)) hA3
    hc (dCtx_ext _ hx03 _ _ hctx) (dProg_ext hx03 _ _ hprog) hb2P' (dState_ext hx03 _ _ hnsP) hwb
  have hs := npE_spec p L.ppos n ⟨m5, Locals.init []⟩ vis ctx fu po pl (dep + 1) (kb + 1) (rb.headD 0) ns
  cases h6c : callE p n "nest_pos" [vis, ctx, fu, po, pl, dep + 1, kb + 1, rb.headD 0, ns] m5 with
  | error e6 =>
    rw [npbE.k_nest_pos.eq_1]
    refine RefE.bind_left fun hG => ?_
    have := RefE.run_err hs True.intro hG hR h6c
    rw [pos2_word_succ hd1, pos2_word_succ hk1, hb2d] at this
    exact this
  | ok q6 =>
  obtain ⟨rp, m6⟩ := q6
  rw [npbE.k_nest_pos.arm1]
  obtain ⟨s6, hs6, -, x, a4, hrun4, hQ4⟩ := RefE.run_ok hs hR h6c
  rw [hs6] at hQ4
  obtain ⟨hC4, hg4, hk4, hnbH, hnbd, hns4, hP4, hA4, c4⟩ := hQ4
  have hS4 := hC4.stage
  obtain ⟨-, v1, ⟨-, hnbP, -, -⟩, -⟩ := ConRon.Bridge.Inductives.nestPos_spec coreSpecV henv hc
    fu.toNat prog progP (dep + 1).toNat (kb + 1).toNat (decI (rb.headD 0)) _ NS nsP hwb
    a3 a4 x hC3.check ⟨dCtx_ext _ hx03 _ _ hctx, dProg_ext hx03 _ _ hprog, hb2P', dState_ext hx03 _ _ hnsP⟩ hrun4
  rw [pos2_word_succ hd1, pos2_word_succ hk1, hb2d] at hrun4
  refine RefE.bind_right hrun4 ?_
  -- the rest: abstracted, rebuilt
  cases h7 : callE p n "abstract1_fast" [CWF, rp.tail.headD 0, dep, 0] m6 with
  | error e7 =>
    rw [npbE.k_abstract1_fast.eq_1]
    exact fun hG => ErrClaim.of_callE_nv hG.nv (_root_.L.Checker.nv_mem (by decide +kernel)) h7
  | ok q7 =>
  obtain ⟨ra, m7⟩ := q7
  obtain ⟨s7, hs7, -, hab⟩ := triple_of_callW (abF_spec p L.ab n ⟨m6, Locals.init []⟩ _) (callW_of_callE h7)
  dsimp only at hab
  rw [hs7] at hab
  rw [npbE.k_abstract1_fast.arm1]
  obtain ⟨nb2, a5, hrun5, ⟨hS5, hg5, hnb2H, hnb2d⟩, hA5⟩ := abF_ok dn vis fe _ dep 0 hnbH m6 m7 a4 ra hab ⟨hS4, hA4⟩
  simp only [CWF_eq, hnbd] at hrun5
  have e5 : (abstract1Fast coreWalkFuel x.2.1 dep.toNat 0).run a4 = .ok (nb2, a5) := by simpa using hrun5
  obtain ⟨r1, r2, r3, r4, -, r7⟩ := ConRon.Bridge.AM.of_run (P := fun t => t = a4) rfl e5
    (ConRon.Bridge.ExprOps.abstract1Fast_spec ConRon.Bridge.Core.fvarBSpec coreWalkFuel a4 x.2.1 dep.toNat 0
      hC4.check.state (by rw [hnbP]; rfl))
  have p5 : PStep a4 a5 := PStep.of_caches r1 r2 r3 r4
  cases h8 : callE p n "mk_forall" [d, ra.headD 0] m7 with
  | error e8 =>
    rw [npbE.k_mk_forall.eq_1]
    exact fun hG => ErrClaim.of_callE_nv hG.nv (_root_.L.Checker.nv_mem (by decide +kernel)) h8
  | ok q8 =>
  obtain ⟨rz, m8⟩ := q8
  obtain ⟨s8, hs8, -, hmf⟩ := triple_of_callW
    (mkForall_spec p R.hk.hd R.hk.forF R.hk.forP R.hk.forI R.hk.forM n ⟨m7, Locals.init []⟩ d (ra.headD 0))
    (callW_of_callE h8)
  dsimp only at hmf
  rw [hs8] at hmf
  rw [npbE.k_mk_forall.eq_2]
  by_cases hzb : 4294967296 ≤ rz.headD 0
  · rw [ite_eq_left hzb]; exact RefE.of_cls0 rfl
  rw [ite_eq_right hzb]
  obtain ⟨a6, hrun6, hS6, hg6⟩ := mkForall_stage hS5 d (ra.headD 0) hmf
  have hzH : H (rz.headD 0) := by
    have : ¬ (4294967296 : Word).toNat ≤ (rz.headD 0).toNat := fun e => hzb (UInt64.le_iff_toNat_le.mpr e)
    simp only [H]; simpa using this
  have e6 : (internForallEE (decI d) nb2).run a5 = .ok (decI (rz.headD 0), a6) := by
    rw [← hnb2d]; exact hrun6
  obtain ⟨p6, -⟩ := ConRon.Bridge.Inductives.internForallEE_run p5.ok
    (ConRon.Bridge.denote_ext hdP (hx03.trans (c4.ext.trans p5.ext))) (r7 _ hnbP) e6
  have htop4 : iwTop m6 < 2 ^ 64 := Nat.lt_of_le_of_lt hS4.2.1 hS4.2.2.2.1
  have hA6 : AbsOK m8 := mkForallW_afr hmf hA5
  refine RefE.ret (y := (x.1, decI (rz.headD 0), x.2.2)) (a' := a6) ?_
    ⟨hC4.of_pstep hS6 hA6 (p5.trans p6), ((hg13.trans hg4).trans hg5).trans hg6, by simpa using hk4,
      by simpa using hzH, by simp, by simpa using (hns4.grow (hg5.trans hg6) htop4),
      (hP4.fr (MFr.ofAbF hab)).fr (mkForallW_mfr hmf), hA6,
      ((p23.toCore hC.check).trans c4).trans ((p5.trans p6).toCore hC4.check)⟩
  simp only [StateT.run_bind, e5, except_ok_bind, e6]
  rfl

end steps

end L.Ind
