import ConAgua.Verdict.PosE1L

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dCtx dProg dState dCtx_ext dProg_ext dState_ext kindOf)
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace L.Ind
open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- `nest_cont_key`'s claim in `callE` form, from the model form. -/
theorem keyOKEc_of {p : Prog} (L : NbLook p) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {env : ConLeche.Env} {n : Nat} (h : KeyOKE p dn vis fe env n) : KeyOKEc p dn vis fe env n := by
  intro m a ctx fu po pl kb nn us dO dL nPc cty ns c prog ds NS ctxP progP nP usP dsP ctyP nsP hC hW hnn hus
    hds hdsb hcty hns hP hA hc hctx hprog hnP husP hdsP hctyP hnsP hwds hni e he
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have he' := triple_of_callE_err (nckE_spec p L.pkey n ⟨m, Locals.init []⟩ vis ctx fu po pl kb nn us dO dL nPc cty ns)
    he (Err.code_ne_of_cls hk0)
  exact h m a ctx fu po pl kb nn us dO dL nPc cty ns c prog ds NS ctxP progP nP usP dsP ctyP nsP hC hW hnn hus
    hds hdsb hcty hns hP hA hc hctx hprog hnP husP hdsP hctyP hnsP hwds hni e he'

theorem bindOKE_step {p : Prog} (L : NbLook p) (hnv : closedNV p _root_.L.Checker.nvFns = true)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) {env : ConLeche.Env}
    (n : Nat) (ihE : NbOKE p dn vis fe env n) : BindOKE p dn vis fe env (n + 1) := by
  obtain ⟨hPosE, -, -, -, -, -, -, -, -, -, -⟩ := ihE
  intro m a ctx fu po pl dep kb w ns c prog NS ctxP progP wP nsP hC hW hw h6 hns hP hA hc hctx hprog hwP
    hnsP hww er he
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have R := L.ct.cr.rx
  replace he := triple_of_callE_err (npbE_spec p L.pbind (n + 1) ⟨m, Locals.init []⟩ vis ctx fu po pl dep kb w ns)
    he (Err.code_ne_of_cls hk0)
  dsimp only at he
  rw [npbE.arm1] at he
  have hS := hC.stage
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  -- `nest_ctx_hi_at`
  cases h1 : callE p n "nest_ctx_hi_at" [ctx, pl] m with
  | error e1 =>
    rw [h1, npbE.k_nest_ctx_hi_at.eq_1] at he; cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h1
  | ok q1 =>
  obtain ⟨rh, m1⟩ := q1
  obtain ⟨s1, hs1, -, hm1, hrh⟩ := triple_of_callW (nestCtxHiAt_specE p R.hi n ⟨m, Locals.init []⟩ ctx pl)
    (callW_of_callE h1)
  dsimp only at hm1 hrh
  rw [hs1] at hm1
  rw [h1, npbE.k_nest_ctx_hi_at.arm1, hrh, hm1] at he
  -- `e_view`
  cases h2 : callE p n "e_view" [w] m with
  | error e2 =>
    rw [h2, npbE.k_e_view.eq_1] at he; cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h2
  | ok q2 =>
  obtain ⟨rv, m2⟩ := q2
  obtain ⟨s2, hs2, hm2, hev, hrv⟩ := triple_of_callW (eView_spec p R.hl.hv n ⟨m, Locals.init []⟩ w)
    (callW_of_callE h2)
  have hm2' : m2 = m := by rw [← hs2, hm2]
  dsimp only at hrv
  rw [h2, npbE.k_e_view.arm1, hm2', hrv] at he
  rw [hrv] at hev
  obtain ⟨d, b, hv, hd, hb, hvb, htag⟩ := pos2_forall_view hS hw h6 hev
  rw [hv] at he
  simp only [List.tail_cons, List.headD_cons] at he
  obtain ⟨-, hvbS⟩ := ConRon.Bridge.Inductives.viewBind_run hvb
  obtain ⟨dP, bP, rfl, hdP, hbP⟩ := ConRon.Bridge.denote_forallE_inv hC.check.state.wf
    (ConRon.Bridge.view_forallE_of_viewBind (by simp [htag]) hvbS.symm) hwP
  simp only [ConLeche.Expr.WScoped] at hww
  unfold posBindT
  refine ErrClaim.bind_right hvb ?_
  dsimp only
  obtain ⟨hn0, hnb0, -, -, hnP, -⟩ := ctx_fields hW.u.dec hW.u.inn htop
  have hne0 := ctx_names_end hW.u.dec hW.u.inn hW.u.sl htop
  have hhi := hW.hi htop
  -- `nest_occ` of the domain
  cases h3 : callE p n "nest_occ" [rdW (m.arr64 IW) ctx, rdW (m.arr64 IW) (ctx + 1), rdW (m.arr64 IW) (ctx + 4),
      nhiW m ctx pl, d] m with
  | error e3 =>
    rw [h3, npbE.k_nest_occ.eq_1] at he; cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h3
  | ok q3 =>
  obtain ⟨ro, m3⟩ := q3
  obtain ⟨s3, hs3, -, hno⟩ := triple_of_callW (nestOcc_spec' p L.nit.no n ⟨m, Locals.init []⟩ _ _ _ _ d)
    (callW_of_callE h3)
  dsimp only at hno
  rw [hs3] at hno
  rw [h3] at he
  obtain ⟨mp, hmp⟩ := hP.no
  obtain ⟨bo, hrun1, hbo, hM1, hS1, hg1, hf1⟩ := noConstWf_ok n dn fe vis m m3 a _ _ _ _ d _ c.names mp hno hS hd hn0
    (by omega) hmp
  rw [hnP, hhi, decE_eq] at hrun1
  refine ErrClaim.bind_right hrun1 ?_
  by_cases ho : ro.headD 0 ≠ 0
  · rw [npbE.k_nest_occ.abort1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ ho] at he; cases he
    have hbo' : bo = true := by rw [← hbo]; simpa using ho
    subst hbo'
    exact ErrClaim.ite_pos rfl (ErrClaim.fail _ _ (by decide))
  have hbo' : bo = false := by rw [← hbo]; simpa using ho
  subst hbo'
  refine ErrClaim.ite_neg (by simp) ?_
  rw [npbE.k_nest_occ.eq_2, if_neg ho] at he
  by_cases hd1 : dep + 1 = 0
  · rw [if_pos hd1] at he; cases he; exact absurd rfl hk0
  rw [if_neg hd1] at he
  by_cases hk1 : kb + 1 = 0
  · rw [if_pos hk1] at he; cases he; exact absurd rfl hk0
  rw [if_neg hk1] at he
  -- the variable, the body opened
  cases h4 : callE p n "intern_fvar" [dep, d] m3 with
  | error e4 =>
    rw [h4, npbE.k_intern_fvar.eq_1] at he; cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h4
  | ok q4 =>
  obtain ⟨rf, m4⟩ := q4
  obtain ⟨s4, hs4, -, hfv⟩ := triple_of_callW (internFVar_spec p R.hl.hff R.hl.hfp R.hl.hif n ⟨m3, Locals.init []⟩ dep d)
    (callW_of_callE h4)
  dsimp only at hfv
  rw [hs4] at hfv
  rw [h4] at he
  by_cases hfvb : 4294967296 ≤ rf.headD 0
  · rw [npbE.k_intern_fvar.abort1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ hfvb] at he; cases he; exact absurd rfl hk0
  rw [npbE.k_intern_fvar.arm1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ hfvb] at he
  have hfvH : H (rf.headD 0) := by
    have : ¬ (4294967296 : Word).toNat ≤ (rf.headD 0).toNat := fun e => hfvb (UInt64.le_iff_toNat_le.mpr e)
    simp only [H]; simpa using this
  obtain ⟨a2, hrun2, hS2, hg2⟩ := internFVar_stage hS1 dep d hd hfv
  have e2 : (internFVarE dep.toNat (decI d)).run a = .ok (decI (rf.headD 0), a2) := by
    simpa [internFVarE, decE_eq] using hrun2
  obtain ⟨p2, hfvP⟩ := ConRon.Bridge.Inductives.internFVarE_run hC.check.state hdP e2
  refine ErrClaim.bind_right e2 ?_
  cases h5 : callE p n "instantiate1_fast" [CWF, b, rf.headD 0, 0] m4 with
  | error e5 =>
    rw [h5, npbE.k_instantiate1_fast.eq_1] at he; cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h5
  | ok q5 =>
  obtain ⟨rb, m5⟩ := q5
  obtain ⟨s5, hs5, -, hin⟩ := triple_of_callW (i1F_spec p L.hi1 n ⟨m4, Locals.init []⟩ _) (callW_of_callE h5)
  dsimp only at hin
  rw [hs5] at hin
  rw [h5, npbE.k_instantiate1_fast.arm1] at he
  obtain ⟨b2, a3, hrun3, hS3, hg3, hb2H, hb2d⟩ := i1F_ok dn vis fe b (rf.headD 0) 0 hb m4 m5 a2 rb hin hS2
  rw [CWF_eq] at hrun3
  have e3 : (instantiate1Fast coreWalkFuel (decI b) (decI (rf.headD 0)) 0).run a2 = .ok (b2, a3) := by
    simpa using hrun3
  refine ErrClaim.bind_right e3 ?_
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
  cases h6c : callE p n "nest_pos" [vis, ctx, fu, po, pl, dep + 1, kb + 1, rb.headD 0, ns] m5 with
  | error e6 =>
    rw [h6c, npbE.k_nest_pos.eq_1] at he; cases he
    have := hPosE m5 a3 ctx fu po pl (dep + 1) (kb + 1) (rb.headD 0) ns c prog NS ctxP progP _ nsP hC3
      (hW.grow hg13) (by simpa using hb2H) (hns.grow hg13 htop)
      (((hP.setNo hf1 ⟨∅, hM1⟩).fr (fvinternW_mfr hfv)).fr (MFr.ofI1F hin)) hA3
      hc (dCtx_ext _ hx03 _ _ hctx) (dProg_ext hx03 _ _ hprog) hb2P' (dState_ext hx03 _ _ hnsP) hwb _ h6c
    rw [pos2_word_succ hd1, pos2_word_succ hk1, hb2d] at this
    exact ErrClaim.bind_left this
  | ok q6 =>
  obtain ⟨rp, m6⟩ := q6
  rw [h6c, npbE.k_nest_pos.arm1] at he
  -- the rest claims nothing
  cases h7 : callE p n "abstract1_fast" [CWF, rp.tail.headD 0, dep, 0] m6 with
  | error e7 =>
    rw [h7, npbE.k_abstract1_fast.eq_1] at he; cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h7
  | ok q7 =>
  obtain ⟨ra, m7⟩ := q7
  rw [h7, npbE.k_abstract1_fast.arm1] at he
  cases h8 : callE p n "mk_forall" [d, ra.headD 0] m7 with
  | error e8 =>
    rw [h8, npbE.k_mk_forall.eq_1] at he; cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h8
  | ok q8 =>
  obtain ⟨rz, m8⟩ := q8
  rw [h8, npbE.k_mk_forall.eq_2] at he
  split at he <;> cases he
  exact absurd rfl hk0

theorem posOKE_step {p : Prog} (L : NbLook p) (hq : KnotStageProg p)
    (hnv : closedNV p _root_.L.Checker.nvFns = true) (hW : WhnfTopE p)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) {env : ConLeche.Env}
    (henv : ConLeche.EnvWF env) (n : Nat) (hn : n ≤ 2 ^ 62) (ihE : NbOKE p dn vis fe env n) :
    PosOKE p dn vis fe env (n + 1) := by
  obtain ⟨-, hBindE, hAppE, -, -, -, -, -, -, -, -⟩ := ihE
  intro m a ctx fu po pl dep kb e ns c prog NS ctxP progP eP nsP hC hWc he hns hP hA hc hctx hprog heP hnsP
    hwe er hce
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have R := L.ct.cr.rx
  replace hce := triple_of_callE_err (npE_spec p L.ppos (n + 1) ⟨m, Locals.init []⟩ vis ctx fu po pl dep kb e ns)
    hce (Err.code_ne_of_cls hk0)
  dsimp only at hce
  have hS := hC.stage
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  by_cases hf0 : fu = 0
  · rw [npE.abort1 _ _ _ _ _ _ _ _ _ _ _ _ hf0] at hce; cases hce
    subst hf0
    rw [show (0 : Word).toNat = 0 from rfl, ConRon.Arena.nestPos]
    exact ErrClaim.fail _ _ (by decide)
  rw [npE.arm1 _ _ _ _ _ _ _ _ _ _ _ _ hf0] at hce
  have hfu : fu.toNat = (fu - 1).toNat + 1 := by
    have : fu.toNat ≠ 0 := fun e' => hf0 (UInt64.toNat_inj.mp (by simpa using e'))
    rw [pos2_word_pred hf0]; omega
  rw [hfu, nestPos_succ]
  have hhi := hWc.hi htop
  -- `nest_ctx_hi_at`
  cases h1 : callE p n "nest_ctx_hi_at" [ctx, pl] m with
  | error e1 =>
    rw [h1, npE.k_nest_ctx_hi_at.eq_1] at hce; cases hce
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h1
  | ok q1 =>
  obtain ⟨rh, m1⟩ := q1
  obtain ⟨s1, hs1, -, hm1, hrh⟩ := triple_of_callW (nestCtxHiAt_specE p R.hi n ⟨m, Locals.init []⟩ ctx pl)
    (callW_of_callE h1)
  dsimp only at hm1 hrh
  rw [hs1] at hm1
  rw [h1, npE.k_nest_ctx_hi_at.arm1, hrh, hm1] at hce
  -- the reduct
  cases h2 : callE p n "whnf_top" [vis, dep, e] m with
  | error e2 =>
    rw [h2, npE.k_whnf_top.eq_1] at hce; cases hce
    exact ErrClaim.bind_left (hW n hn hC.stageT dep e he _ h2)
  | ok q2 =>
  obtain ⟨rw, m1⟩ := q2
  rw [h2, npE.k_whnf_top.arm1] at hce
  obtain ⟨w, a1, hrun1, hC1, hg1, ⟨hwH, hwd⟩, hA1, c1, wP, hwP, hww⟩ :=
    whnfC_rsim hq henv n hn hC hA dep e he heP hwe _ (callW_of_callE h2)
  dsimp only at hC1 hg1 hwH hwd hA1
  have hrun1' : (whnf V fe checkFuel dep.toNat (decI e)).run a = .ok (w, a1) := hrun1
  refine ErrClaim.bind_right hrun1' ?_
  have hS1 := hC1.stage
  have htop1 : iwTop m1 < 2 ^ 64 := Nat.lt_of_le_of_lt hS1.2.1 hS1.2.2.2.1
  have hW1 := hWc.grow hg1
  obtain ⟨hn1, -, -, -, hnP1, -⟩ := ctx_fields hW1.u.dec hW1.u.inn htop1
  have hne1 := ctx_names_end hW1.u.dec hW1.u.inn hW1.u.sl htop1
  have hhi1 : (nhiW m ctx pl).toNat = c.hiAt prog.length := hhi
  cases h3 : callE p n "nest_occ" [rdW (m1.arr64 IW) ctx, rdW (m1.arr64 IW) (ctx + 1), rdW (m1.arr64 IW) (ctx + 4),
      nhiW m ctx pl, rw.headD 0] m1 with
  | error e3 =>
    rw [h3, npE.k_nest_occ.eq_1] at hce; cases hce
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h3
  | ok q3 =>
  obtain ⟨ro, m2⟩ := q3
  obtain ⟨s3, hs3, -, hno⟩ := triple_of_callW (nestOcc_spec' p L.nit.no n ⟨m1, Locals.init []⟩ _ _ _ _ _)
    (callW_of_callE h3)
  dsimp only at hno
  rw [hs3] at hno
  rw [h3] at hce
  have hP1 : PosMR m1 := hP.fr (coreF_mfr hq (by decide) (callW_of_callE h2))
  obtain ⟨mp, hmp⟩ := hP1.no
  obtain ⟨bo, hrun2, hbo, hM2, hS2, hg2, hf2⟩ := noConstWf_ok n dn fe vis m1 m2 a1 _ _ _ _ _ _ c.names mp hno hS1 hwH hn1
    (by omega) hmp
  rw [hnP1, hhi1, decE_eq, hwd] at hrun2
  refine ErrClaim.bind_right hrun2 ?_
  by_cases ho : ro.headD 0 = 0
  · -- no occurrence: the rest claims nothing
    rw [npE.k_nest_occ.eq_2, if_pos ho] at hce
    cases h4 : callE p n "nest_occ" [rdW (m2.arr64 IW) ctx, rdW (m2.arr64 IW) (ctx + 1), rdW (m2.arr64 IW) (ctx + 4),
        nhiW m ctx pl, e] m2 with
    | error e4 =>
      rw [h4, npE.k_nest_occ_2.eq_1] at hce; cases hce
      exact ErrClaim.of_callE_nv hnv (by decide +kernel) h4
    | ok q4 =>
      obtain ⟨r4, m4⟩ := q4
      rw [h4, npE.k_nest_occ_2.eq_2] at hce
      split at hce <;> cases hce
  rw [npE.k_nest_occ.eq_2, if_neg ho] at hce
  have hbo' : bo = true := by rw [← hbo]; simpa using ho
  subst hbo'
  have hg12 := hg1.trans hg2
  have htop2 : iwTop m2 < 2 ^ 64 := Nat.lt_of_le_of_lt hS2.2.1 hS2.2.2.2.1
  have hW2 := hWc.grow hg12
  have hns2 := hns.grow hg12 htop
  have hP2 : PosMR m2 := hP1.setNo hf2 ⟨∅, hM2⟩
  have hA2 : AbsOK m2 := noConstWf_afr hno hA1
  have hC2 : StageC dn vis fe env m2 a1 := hC1.of_pstep hS2 hA2 (PStep.refl hC1.check.state)
  have hx01 := c1.ext
  have hwP' : denoteE a1.store (decI (rw.headD 0)) = some wP := by rw [hwd]; exact hwP
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  by_cases h6 : rw.headD 0 >>> 28 = 6
  · rw [if_pos h6] at hce
    have htag : w.tag = ETag.forallE := by rw [← hwd]; exact (decE_tag_forall _ hwH).mpr h6
    rw [if_pos (by simpa using htag)]
    cases h5 : callE p n "nest_pos_bind" [vis, ctx, fu - 1, po, pl, dep, kb, rw.headD 0, ns] m2 with
    | error e5 =>
      rw [h5, npE.k_nest_pos_bind.eq_1] at hce; cases hce
      have := hBindE m2 a1 ctx (fu - 1) po pl dep kb (rw.headD 0) ns c prog NS ctxP progP wP nsP hC2 hW2 hwH h6 hns2
        hP2 hA2 hc (dCtx_ext _ hx01 _ _ hctx) (dProg_ext hx01 _ _ hprog) hwP' (dState_ext hx01 _ _ hnsP) hww _ h5
      rw [hwd] at this
      exact this
    | ok q5 =>
      obtain ⟨r5, m5⟩ := q5
      rw [h5, npE.k_nest_pos_bind.eq_2] at hce; cases hce
  · rw [if_neg h6] at hce
    have htag : ¬ w.tag = ETag.forallE := by rw [← hwd]; exact fun e' => h6 ((decE_tag_forall _ hwH).mp e')
    rw [if_neg (by simpa using htag)]
    cases h5 : callE p n "nest_pos_app" [vis, ctx, fu - 1, po, pl, kb, nhiW m ctx pl, rw.headD 0, ns] m2 with
    | error e5 =>
      rw [h5, npE.k_nest_pos_app.eq_1] at hce; cases hce
      have := hAppE m2 a1 ctx (fu - 1) po pl kb (nhiW m ctx pl) (rw.headD 0) ns c prog NS ctxP progP wP nsP dep.toNat
        hC2 hW2 hhi1 hwH hns2 hP2 hA2 hc (dCtx_ext _ hx01 _ _ hctx) (dProg_ext hx01 _ _ hprog) hwP'
        (dState_ext hx01 _ _ hnsP) hww _ h5
      rw [hwd, hhi1] at this
      exact this
    | ok q5 =>
      obtain ⟨r5, m5⟩ := q5
      rw [h5, npE.k_nest_pos_app.eq_2] at hce; cases hce

theorem appOKE_step {p : Prog} (L : NbLook p) (hnv : closedNV p _root_.L.Checker.nvFns = true)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) {env : ConLeche.Env}
    (n : Nat) (ihE : NbOKE p dn vis fe env n) : AppOKE p dn vis fe env (n + 1) := by
  obtain ⟨-, -, -, hContE, -, -, -, -, -, -, -⟩ := ihE
  intro m a ctx fu po pl kb hi w ns c prog NS ctxP progP wP nsP dep hC hW hhi hw hns hP hA hc hctx hprog
    hwP hnsP hww er hce
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  replace hce := triple_of_callE_err (npaE_spec p L.papp (n + 1) ⟨m, Locals.init []⟩ vis ctx fu po pl kb hi w ns)
    hce (Err.code_ne_of_cls hk0)
  dsimp only at hce
  rw [npaE.arm1] at hce
  have hS := hC.stage
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  -- the arguments
  cases h1 : callE p n "get_app_args_f" [CWF, w] m with
  | error e1 =>
    rw [h1, npaE.k_get_app_args_f.eq_1] at hce; cases hce
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h1
  | ok q1 =>
  obtain ⟨ra, m1⟩ := q1
  obtain ⟨s1, hs1, -, hga⟩ := triple_of_callW (gaaF_spec p L.nt.ad n ⟨m, Locals.init []⟩ _) (callW_of_callE h1)
  dsimp only at hga
  rw [hs1] at hga
  rw [h1, npaE.k_get_app_args_f.arm1] at hce
  obtain ⟨args, a1, hrun1, hS1, hg1, hargs, hargsb⟩ := gaaF_ok dn vis fe CWF w hw m m1 a ra hga hS
  rw [CWF_eq] at hrun1
  obtain ⟨ha1, hargsP⟩ := ConRon.Bridge.Inductives.getAppArgs_run hC.check.state hwP hrun1
  subst ha1
  have e0 : ra.getD 0 0 = ra.headD 0 := by cases ra <;> rfl
  rw [e0, getD1_eq] at hargs hargsb
  unfold posAppT
  refine ErrClaim.bind_right hrun1 ?_
  -- the head
  cases h2 : callE p n "get_app_fn_f" [CWF, w] m1 with
  | error e2 =>
    rw [h2, npaE.k_get_app_fn_f.eq_1] at hce; cases hce
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h2
  | ok q2 =>
  obtain ⟨rh, m2⟩ := q2
  obtain ⟨s2, hs2, -, hgf⟩ := triple_of_callW (gafF_spec p L.nt.ad n ⟨m1, Locals.init []⟩ _) (callW_of_callE h2)
  dsimp only at hgf
  rw [hs2] at hgf
  rw [h2, npaE.k_get_app_fn_f.arm1] at hce
  obtain ⟨hd, a2, hrun2, hS2, hg2, hhdH, hhdd⟩ := gafF_ok dn vis fe CWF w hw m1 m2 a1 rh hgf hS1
  rw [CWF_eq] at hrun2
  obtain ⟨ha2, hhdP⟩ := ConRon.Bridge.Inductives.getAppFn_run hC.check.state hwP hrun2
  subst ha2
  refine ErrClaim.bind_right hrun2 ?_
  have hg12 := hg1.trans hg2
  have hP2 : PosMR m2 := (hP.fr (MFr.ofGaaF hga)).fr (MFr.ofGafF hgf)
  have hA2 : AbsOK m2 := gafF_afr hgf (gaaF_afr hga hA)
  have hC2 : StageC dn vis fe env m2 a2 := hC.of_pstep hS2 hA2 (PStep.refl hC.check.state)
  -- the view
  cases h3 : callE p n "e_view" [rh.headD 0] m2 with
  | error e3 =>
    rw [h3, npaE.k_e_view.eq_1] at hce; cases hce
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h3
  | ok q3 =>
  obtain ⟨rv, m3⟩ := q3
  obtain ⟨s3, hs3, hm3, hev, hrv⟩ := triple_of_callW (eView_spec p L.ct.cr.rx.hl.hv n ⟨m2, Locals.init []⟩ _)
    (callW_of_callE h3)
  have hm3' : m3 = m2 := by rw [← hs3, hm3]
  dsimp only at hrv
  rw [h3, npaE.k_e_view.eq_2, hm3', hrv] at hce
  rw [hrv] at hev
  obtain ⟨v, hview, hvr⟩ := eViewW_ok m2 a2 hS2.1.arena.1 (rh.headD 0) hev
  have hvrun : (view hd).run a2 = .ok (v, a2) := by rw [← hhdd, ← decE_eq]; exact view_run _ _ _ hview
  refine ErrClaim.bind_right hvrun ?_
  have hargs2 : decHL m2 (ra.headD 0).toNat (ra.tail.headD 0).toNat = some args := by
    rw [decHL_agree (RdS.of_grow hg2) (fun j hj => by omega)]; exact hargs
  by_cases h1v : (eViewW m2 (rh.headD 0)).headD 0 = 1
  · rw [if_pos h1v] at hce
    obtain ⟨i, ty, rfl⟩ : ∃ i ty, v = .fvar i ty := by
      cases v <;> simp only [ViewR] at hvr <;> (try (rw [h1v] at hvr; simp at hvr)) <;> exact ⟨_, _, rfl⟩
    obtain ⟨-, hi1, -, -⟩ := hvr
    rw [getD1_eq] at hi1
    cases h4 : callE p n "nest_pos_fvar" [vis, ctx, po, pl, kb, hi, (eViewW m2 (rh.headD 0)).tail.headD 0,
        ra.headD 0, ra.tail.headD 0] m2 with
    | error e4 =>
      rw [h4, npaE.k_nest_pos_fvar.eq_1] at hce; cases hce
      have h4' := triple_of_callE_err (pfvE_spec p L.pf.hp n ⟨m2, Locals.init []⟩ vis ctx po pl kb hi _ _ _) h4
        (Err.code_ne_of_cls hk0)
      dsimp only at h4'
      have := pfvE_claim L.pf hnv dn vis fe h4' hS2 (hW.grow hg12).u (hW.grow hg12).hs hargs2
        (by have := hg2.1; omega) hP2 (fun k => (pure (k, (decI w : EIdx), NS) : AM (NestFieldKind × EIdx × NestState)))
      rw [hi1] at this
      exact this
    | ok q4 =>
      obtain ⟨r4, m4⟩ := q4
      rw [h4, npaE.k_nest_pos_fvar.eq_2] at hce; cases hce
  rw [if_neg h1v] at hce
  by_cases h3v : (eViewW m2 (rh.headD 0)).headD 0 = 3
  · rw [if_pos h3v] at hce
    obtain ⟨nn, us, rfl⟩ : ∃ nn us, v = .const nn us := by
      cases v <;> simp only [ViewR] at hvr <;> (try (rw [h3v] at hvr; simp at hvr)) <;> exact ⟨_, _, rfl⟩
    obtain ⟨-, hnH, hnd, husH, husd⟩ := hvr
    rw [getD1_eq] at hnH hnd
    rw [pos2_getD2] at husH husd
    obtain ⟨nm, ls, -, hnmP, hlsP⟩ := ConRon.Bridge.denote_const_inv hC.check.state.wf
      (by rw [← hhdd, ← decE_eq]; exact hview) hhdP
    have htop2 : iwTop m2 < 2 ^ 64 := Nat.lt_of_le_of_lt hS2.2.1 hS2.2.2.2.1
    obtain ⟨hn2, hnb2, -, -, -, -⟩ := ctx_fields (hW.grow hg12).u.dec (hW.grow hg12).u.inn htop2
    have hne2 := ctx_names_end (hW.grow hg12).u.dec (hW.grow hg12).u.inn (hW.grow hg12).u.sl htop2
    obtain ⟨ws, hws, hwsd, hwsH⟩ := slR_of_decHL m2 _ _ _ hn2 (by omega)
    simp only [UInt64.ofNat_toNat] at hws
    cases h4 : callE p n "sl_contains" [rdW (m2.arr64 IW) ctx, rdW (m2.arr64 IW) (ctx + 1),
        (eViewW m2 (rh.headD 0)).tail.headD 0] m2 with
    | error e4 =>
      rw [h4, npaE.k_sl_contains.eq_1] at hce; cases hce
      exact ErrClaim.of_callE_nv hnv (by decide +kernel) h4
    | ok q4 =>
    obtain ⟨ro, m4⟩ := q4
    obtain ⟨s4, hs4, -, hm4, hco⟩ := triple_of_callW (slContains_spec p L.nit.no.hc n ⟨m2, Locals.init []⟩ _ _ _)
      (callW_of_callE h4)
    dsimp only at hm4 hco
    have hm4' : m4 = m2 := by rw [← hs4, hm4]
    rw [h4, hm4'] at hce
    have ho := containsW_ok n m2 _ _ _ _ ws hws hco
    dsimp only
    by_cases hon : ro.headD 0 ≠ 0
    · rw [npaE.k_sl_contains.abort1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hon] at hce; cases hce
      have hin : c.names.contains nn = true := by
        rw [hwsd, ← hnd, pos2_contains_map ws hwsH _ hnH]
        cases e : ws.contains ((eViewW m2 (rh.headD 0)).tail.headD 0) with
        | true => rfl
        | false => rw [e] at ho; simp only [Bool.false_eq_true, ite_false] at ho; exact absurd ho hon
      exact ErrClaim.ite_pos hin (ErrClaim.fail _ _ (by decide))
    have hnotin : c.names.contains nn = false := by
      rw [hwsd, ← hnd, pos2_contains_map ws hwsH _ hnH]
      cases e : ws.contains ((eViewW m2 (rh.headD 0)).tail.headD 0) with
      | false => rfl
      | true =>
        rw [e] at ho; simp only [ite_true] at ho
        have := Decidable.of_not_not hon; rw [ho] at this; exact absurd this (by decide)
    rw [npaE.k_sl_contains.arm1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by simpa using hon)] at hce
    refine ErrClaim.ite_neg (by rw [hnotin]; simp) ?_
    cases h5 : callE p n "nest_cont" [vis, ctx, fu, po, pl, kb, (eViewW m2 (rh.headD 0)).tail.headD 0,
        (eViewW m2 (rh.headD 0)).tail.tail.headD 0, ra.headD 0, ra.tail.headD 0, ns] m2 with
    | error e5 =>
      rw [h5, npaE.k_nest_cont.eq_1] at hce; cases hce
      have := hContE m2 a2 ctx fu po pl kb _ _ _ _ ns c prog args NS ctxP progP nm ls wP.getAppArgs nsP dep hC2
        (hW.grow hg12) hnH husH hargs2 (by have := hg2.1; omega) (hns.grow hg12 htop) hP2 hA2 hc hctx hprog
        (by rw [hnd]; exact hnmP) (by rw [husd]; exact hlsP) hargsP hnsP
        (ConLeche.Expr.WScoped.getAppArgs hww) _ h5
      rw [hnd, husd] at this
      exact ErrClaim.bind_left this
    | ok q5 =>
      obtain ⟨r5, m5⟩ := q5
      rw [h5, npaE.k_nest_cont.eq_2] at hce; cases hce
  · rw [if_neg h3v] at hce; cases hce
    cases v with
    | fvar i ty => exact absurd hvr.1 h1v
    | const nn us => exact absurd hvr.1 h3v
    | _ => exact ErrClaim.fail _ _ (by decide)

end L.Ind
