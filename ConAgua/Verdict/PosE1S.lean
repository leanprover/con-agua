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

end L.Ind
