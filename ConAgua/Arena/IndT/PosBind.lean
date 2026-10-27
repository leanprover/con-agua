import ConAgua.Arena.IndT.PosFields
import ConAgua.Arena.IndPosSpec.NestCrest
import ConAgua.Arena.IndRealAbsPos

/-!
# `nest_pos_bind` under `StageC` (lane `indstaget`, helper `indstaget-pos`)

`bindOK_step`'s proof (`IndPosSpec/Pos2DecHLSplit`) with the twin side of con-ron's `nestPos_succ` (its `Π`
case): the domain's occurrence check (no state change), its variable (`internFVarE_run`), the body
opened (`instantiate1Fast_run`), walked (the block's `PosOKC` at `n`, `nestPos_spec` on the run
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
theorem bindOKC_step (n : Nat) (ih : NbOKC p dn vis fe env n) : BindOKC p dn vis fe env (n + 1) := by
  obtain ⟨hPos, -, -, -, -, -, -, -, -, -, -⟩ := ih
  intro m m' a ctx fu po pl dep kb w ns c prog NS r ctxP progP wP nsP h hC hW hw h6 hns hP hA hc hctx hprog hwP
    hnsP hww
  have hS := hC.stage
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  rw [nbBindW_succ] at h
  by_cases hev : eViewW m w = []
  · rw [ite_eq_left hev] at h; cases h
  rw [ite_eq_right hev] at h
  obtain ⟨d, b, hv, hd, hb, hvb, htag⟩ := pos2_forall_view hS hw h6 hev
  simp only [hv, List.tail_cons, List.headD_cons] at h
  -- the twin's view of the `Π`
  obtain ⟨-, hvbS⟩ := ConRon.Bridge.Inductives.viewBind_run hvb
  obtain ⟨dP, bP, rfl, hdP, hbP⟩ := ConRon.Bridge.denote_forallE_inv hC.check.state.wf
    (ConRon.Bridge.view_forallE_of_viewBind (by simp [htag]) hvbS.symm) hwP
  simp only [ConLeche.Expr.WScoped] at hww
  -- the domain mentions no member and no hole
  obtain ⟨hn0, hnb0, -, -, hnP, -⟩ := ctx_fields hW.u.dec hW.u.inn htop
  have hne0 := ctx_names_end hW.u.dec hW.u.inn hW.u.sl htop
  have hhi := hW.hi htop
  rcases hno : noConstWf n m (rdW (m.arr64 IW) ctx) (rdW (m.arr64 IW) (ctx + 1)) (rdW (m.arr64 IW) (ctx + 4))
      (nhiW m ctx pl) d with _ | ⟨o, m1⟩; · rw [hno] at h; simp [nbBindK1] at h
  rw [hno, nbBindK1_some] at h
  obtain ⟨mp, hmp⟩ := hP.no
  obtain ⟨bo, hrun1, hbo, hM1, hS1, hg1, hf1⟩ := noConstWf_ok n dn fe vis m m1 a _ _ _ _ d o c.names mp hno hS hd hn0
    (by omega) hmp
  rw [hnP, hhi, decE_eq] at hrun1
  by_cases ho : o ≠ 0
  · rw [ite_eq_left ho] at h; cases h
  rw [ite_eq_right ho] at h
  have hbo' : bo = false := by rw [← hbo]; simpa using ho
  subst hbo'
  by_cases hd1 : dep + 1 = 0
  · rw [ite_eq_left hd1] at h; cases h
  rw [ite_eq_right hd1] at h
  by_cases hk1 : kb + 1 = 0
  · rw [ite_eq_left hk1] at h; cases h
  simp only [ite_eq_right hk1, List.tail_cons, List.headD_cons] at h
  -- the variable, the body opened
  rcases hfv : fvinternW m1 dep d with _ | ⟨fv, m2⟩ <;> rw [hfv] at h; · simp [nbBindK2] at h
  rw [nbBindK2_some] at h
  by_cases hfvb : 4294967296 ≤ fv
  · rw [ite_eq_left hfvb] at h; cases h
  simp only [ite_eq_right hfvb, List.tail_cons, List.headD_cons] at h
  have hfvH : H fv := by
    have : ¬ (4294967296 : Word).toNat ≤ fv.toNat := fun e => hfvb (UInt64.le_iff_toNat_le.mpr e)
    simp only [H]; simpa using this
  obtain ⟨a2, hrun2, hS2, hg2⟩ := internFVar_stage hS1 dep d hd hfv
  have e2 : (internFVarE dep.toNat (decI d)).run a = .ok (decI fv, a2) := by simpa [internFVarE, decE_eq] using hrun2
  obtain ⟨p2, hfvP⟩ := ConRon.Bridge.Inductives.internFVarE_run hC.check.state hdP e2
  rcases hin : i1F m2 [CWF, b, fv, 0] with _ | ⟨rb, m3⟩ <;> rw [hin] at h; · simp [nbBindK3] at h
  simp only [nbBindK3_some, List.tail_cons, List.headD_cons] at h
  obtain ⟨b2, a3, hrun3, hS3, hg3, hb2H, hb2d⟩ := i1F_ok dn vis fe b fv 0 hb m2 m3 a2 rb hin hS2
  rw [CWF_eq] at hrun3
  have e3 : (instantiate1Fast coreWalkFuel (decI b) (decI fv) 0).run a2 = .ok (b2, a3) := by simpa using hrun3
  have hbP2 : denoteE a2.store (decI b) = some bP := ConRon.Bridge.denote_ext hbP p2.ext
  obtain ⟨q1, q2, q4, q5, -, q7⟩ := ConRon.Bridge.ExprOps.instantiate1Fast_run p2.ok hfvP
    (by rw [hbP2]; rfl) e3
  have p3 : PStep a2 a3 := PStep.of_caches q1 q2 q4 q5
  have hb2P : denoteE a3.store b2 = some (bP.instantiate1 (.fvar dep.toNat dP) 0) := q7 _ hbP2
  have hg13 := (hg1.trans hg2).trans hg3
  have hA3 : AbsOK m3 := i1F_afr hin (fvinternW_afr hfv (noConstWf_afr hno hA))
  have p23 := p2.trans p3
  have hC3 : StageC dn vis fe env m3 a3 := hC.of_pstep hS3 hA3 p23
  have hx03 := p23.ext
  have hdep1 : (dep + 1).toNat = dep.toNat + 1 := pos2_word_succ hd1
  -- the codomain walked
  rcases hp : nbPosW (realCall p) n m3 vis ctx fu po pl (dep + 1) (kb + 1) (rb.headD 0) ns with _ | ⟨rp, m4⟩ <;> rw [hp] at h; · simp [nbBindK4] at h
  rw [nbBindK4_some] at h
  have hwb : ConLeche.Expr.WScoped (dep + 1).toNat (bP.instantiate1 (.fvar dep.toNat dP) 0) := by
    rw [hdep1]; exact ConLeche.Expr.WScoped.instantiate1 hww.1 0 hww.2
  have hb2P' : denoteE a3.store (decI (rb.headD 0)) = some (bP.instantiate1 (.fvar dep.toNat dP) 0) := by
    rw [show (decI (rb.headD 0) : EIdx) = b2 by simpa [decE_eq] using hb2d]; exact hb2P
  obtain ⟨x, a4, hrun4, hC4, hg4, hk4, hnbH, hnbd, hns4, hP4, hA4, c4⟩ := hPos m3 m4 a3 ctx fu po pl (dep + 1)
    (kb + 1) (rb.headD 0) ns c prog NS rp ctxP progP _ nsP hp hC3 (hW.grow hg13) (by simpa using hb2H)
    (hns.grow hg13 htop) (((hP.setNo hf1 ⟨∅, hM1⟩).fr (fvinternW_mfr hfv)).fr (MFr.ofI1F hin)) hA3
    hc (dCtx_ext _ hx03 _ _ hctx) (dProg_ext hx03 _ _ hprog) hb2P' (dState_ext hx03 _ _ hnsP) hwb
  have hS4 := hC4.stage
  obtain ⟨-, v1, ⟨-, hnbP, -, -⟩, -⟩ := ConRon.Bridge.Inductives.nestPos_spec coreSpecV henv hc
    fu.toNat prog progP (dep + 1).toNat (kb + 1).toNat (decI (rb.headD 0)) _ NS nsP hwb
    a3 a4 x hC3.check ⟨dCtx_ext _ hx03 _ _ hctx, dProg_ext hx03 _ _ hprog, hb2P', dState_ext hx03 _ _ hnsP⟩ hrun4
  rcases hab : abF m4 [CWF, rp.tail.headD 0, dep, 0] with _ | ⟨ra, m5⟩ <;> rw [hab] at h; · simp [nbBindK5] at h
  rw [nbBindK5_some] at h
  obtain ⟨nb2, a5, hrun5, ⟨hS5, hg5, hnb2H, hnb2d⟩, hA5⟩ := abF_ok dn vis fe _ dep 0 hnbH m4 m5 a4 ra hab ⟨hS4, hA4⟩
  simp only [CWF_eq, hnbd] at hrun5
  have e5 : (abstract1Fast coreWalkFuel x.2.1 dep.toNat 0).run a4 = .ok (nb2, a5) := by simpa using hrun5
  obtain ⟨r1, r2, r3, r4, -, r7⟩ := ConRon.Bridge.AM.of_run (P := fun t => t = a4) rfl e5
    (ConRon.Bridge.ExprOps.abstract1Fast_spec ConRon.Bridge.Core.fvarBSpec coreWalkFuel a4 x.2.1 dep.toNat 0
      hC4.check.state (by rw [hnbP]; rfl))
  have p5 : PStep a4 a5 := PStep.of_caches r1 r2 r3 r4
  rcases hmf : mkForallW m5 d (ra.headD 0) with _ | ⟨z, m6⟩ <;> rw [hmf] at h; · simp [nbBindK6] at h
  rw [nbBindK6_some] at h
  by_cases hzb : 4294967296 ≤ z
  · rw [ite_eq_left hzb] at h; cases h
  rw [ite_eq_right hzb] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨a6, hrun6, hS6, hg6⟩ := mkForall_stage hS5 d (ra.headD 0) hmf
  have hzH : H z := by
    have : ¬ (4294967296 : Word).toNat ≤ z.toNat := fun e => hzb (UInt64.le_iff_toNat_le.mpr e)
    simp only [H]; simpa using this
  have e6 : (internForallEE (decI d) nb2).run a5 = .ok (decI z, a6) := by
    rw [← hnb2d]; exact hrun6
  obtain ⟨p6, -⟩ := ConRon.Bridge.Inductives.internForallEE_run p5.ok
    (ConRon.Bridge.denote_ext hdP (hx03.trans (c4.ext.trans p5.ext))) (r7 _ hnbP) e6
  have htop4 : iwTop m4 < 2 ^ 64 := Nat.lt_of_le_of_lt hS4.2.1 hS4.2.2.2.1
  have hA6 : AbsOK m6 := mkForallW_afr hmf hA5
  refine ⟨(x.1, decI z, x.2.2), a6, ?_, hC4.of_pstep hS6 hA6 (p5.trans p6), ((hg13.trans hg4).trans hg5).trans hg6,
    by simpa using hk4, by simpa using hzH, by simp, by simpa using (hns4.grow (hg5.trans hg6) htop4),
    (hP4.fr (MFr.ofAbF hab)).fr (mkForallW_mfr hmf), hA6,
    ((p23.toCore hC.check).trans c4).trans ((p5.trans p6).toCore hC4.check)⟩
  rw [pos2_word_succ hd1, pos2_word_succ hk1, hb2d] at hrun4
  simp only [posBindT, StateT.run_bind, hvb, except_ok_bind, hrun1, Bool.false_eq_true, ite_false, e2, e3, hrun4,
    e5, e6]
  rfl

end steps

end L.Ind
