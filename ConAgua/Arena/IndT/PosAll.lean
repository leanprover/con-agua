import ConAgua.Arena.IndT.PosBind
import ConAgua.Arena.IndT.PosApp
import ConAgua.Arena.IndT.PosCont
import ConAgua.Arena.IndT.PosCtors
import ConAgua.Arena.IndT.PosFrame
import ConAgua.Arena.IndT.PosKey
import ConAgua.Arena.IndT.PosNew
import ConAgua.Arena.IndT.PosOne
import ConAgua.Arena.IndT.PosWalk

/-!
# `nest_pos` and the whole walk under `StageC` (lane `indstaget`, helper `indstaget-pos`)

`posRef_step`: `nest_pos` refines con-ron's `nestPos_succ`, both outcomes (`npE`, unified): the
reduct (`whnfC_rsim`; its error by `WhnfTopE`), its occurrence checks (no state change), then
hole-free, a binder (the block's `BindRef` at `n`) or a head (`AppRef` at `n`). Then the block's `StageC` facts at every
exec fuel up to the core walk's (`nbOKC_all`).
-/


open ConRon.Arena
open ConRon.Bridge.Inductives (PStep dCtx dProg dState dCtx_ext dProg_ext dState_ext kindOf)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section steps
variable {p : Prog} (hq : KnotStageProg p) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
  {env : ConLeche.Env} (henv : ConLeche.EnvWF env)

include hq henv in
theorem posRef_step (L : NbLook p) (n : Nat) (hn : n ≤ 2 ^ 62) (ih : NbRef p dn vis fe env n) :
    PosRef p dn vis fe env (n + 1) := by
  intro m a ctx fu po pl dep kb e ns c prog NS ctxP progP eP nsP hC hW he hns hP hA hc hctx hprog heP hnsP hwe
  have R := L.ct.cr.rx
  have hS := hC.stage
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  by_cases hf0 : fu = 0
  · rw [npE.abort1 _ _ _ _ _ _ _ _ _ _ _ _ hf0]
    subst hf0
    rw [show (0 : Word).toNat = 0 from rfl, ConRon.Arena.nestPos]
    exact fun _ => ErrClaim.fail _ _ (by decide)
  rw [npE.arm1 _ _ _ _ _ _ _ _ _ _ _ _ hf0]
  have hfu : fu.toNat = (fu - 1).toNat + 1 := by
    have : fu.toNat ≠ 0 := fun e' => hf0 (UInt64.toNat_inj.mp (by simpa using e'))
    rw [pos2_word_pred hf0]; omega
  rw [hfu, nestPos_succ]
  have hhi := hW.hi htop
  -- `nest_ctx_hi_at`
  cases h1 : callE p n "nest_ctx_hi_at" [ctx, pl] m with
  | error e1 =>
    rw [npE.k_nest_ctx_hi_at.eq_1]
    exact fun hG => ErrClaim.of_callE_nv hG.nv (_root_.L.Checker.nv_mem (by decide +kernel)) h1
  | ok q1 =>
  obtain ⟨rh, m1⟩ := q1
  obtain ⟨s1, hs1, -, hm1, hrh⟩ := triple_of_callW (nestCtxHiAt_specE p R.hi n ⟨m, Locals.init []⟩ ctx pl)
    (callW_of_callE h1)
  dsimp only at hm1 hrh
  rw [hs1] at hm1
  rw [npE.k_nest_ctx_hi_at.arm1, hrh, hm1]
  -- the reduct
  cases h2 : callE p n "whnf_top" [vis, dep, e] m with
  | error e2 =>
    rw [npE.k_whnf_top.eq_1]
    exact RefE.bind_left fun hG => hG.whnf n hn hC.stageT dep e he _ h2
  | ok q2 =>
  obtain ⟨rw, m1⟩ := q2
  rw [npE.k_whnf_top.arm1]
  obtain ⟨w, a1, hrun1, hC1, hg1, ⟨hwH, hwd⟩, hA1, c1, wP, hwP, hww⟩ :=
    whnfC_rsim hq henv n hn hC hA dep e he heP hwe _ (callW_of_callE h2)
  dsimp only at hC1 hg1 hwH hwd hA1
  have hrun1' : (whnf V fe checkFuel dep.toNat (decI e)).run a = .ok (w, a1) := hrun1
  refine RefE.bind_right hrun1' ?_
  have hS1 := hC1.stage
  have htop1 : iwTop m1 < 2 ^ 64 := Nat.lt_of_le_of_lt hS1.2.1 hS1.2.2.2.1
  have hW1 := hW.grow hg1
  obtain ⟨hn1, -, -, -, hnP1, -⟩ := ctx_fields hW1.u.dec hW1.u.inn htop1
  have hne1 := ctx_names_end hW1.u.dec hW1.u.inn hW1.u.sl htop1
  have hhi1 : (nhiW m ctx pl).toNat = c.hiAt prog.length := hhi
  -- the reduct's occurrences
  cases h3 : callE p n "nest_occ" [rdW (m1.arr64 IW) ctx, rdW (m1.arr64 IW) (ctx + 1), rdW (m1.arr64 IW) (ctx + 4),
      nhiW m ctx pl, rw.headD 0] m1 with
  | error e3 =>
    rw [npE.k_nest_occ.eq_1]
    exact fun hG => ErrClaim.of_callE_nv hG.nv (_root_.L.Checker.nv_mem (by decide +kernel)) h3
  | ok q3 =>
  obtain ⟨ro, m2⟩ := q3
  obtain ⟨s3, hs3, -, hno⟩ := triple_of_callW (nestOcc_spec' p L.nit.no n ⟨m1, Locals.init []⟩ _ _ _ _ _)
    (callW_of_callE h3)
  dsimp only at hno
  rw [hs3] at hno
  have hP1 : PosMR m1 := hP.fr (coreF_mfr hq (by decide) (callW_of_callE h2))
  obtain ⟨mp, hmp⟩ := hP1.no
  obtain ⟨bo, hrun2, hbo, hM2, hS2, hg2, hf2⟩ := noConstWf_ok n dn fe vis m1 m2 a1 _ _ _ _ _ _ c.names mp hno hS1 hwH hn1
    (by omega) hmp
  rw [hnP1, hhi1, decE_eq, hwd] at hrun2
  refine RefE.bind_right hrun2 ?_
  have hg12 := hg1.trans hg2
  have htop2 : iwTop m2 < 2 ^ 64 := Nat.lt_of_le_of_lt hS2.2.1 hS2.2.2.2.1
  have hW2 := hW.grow hg12
  have hns2 := hns.grow hg12 htop
  have hP2 : PosMR m2 := hP1.setNo hf2 ⟨∅, hM2⟩
  have hA2 : AbsOK m2 := noConstWf_afr hno hA1
  have hC2 : StageC dn vis fe env m2 a1 := hC1.of_pstep hS2 hA2 (PStep.refl hC1.check.state)
  have hx01 := c1.ext
  rw [npE.k_nest_occ.eq_2]
  by_cases ho : ro.headD 0 = 0
  · -- no occurrence in the reduct: the original, or the reduct
    rw [ite_eq_left ho]
    have hbo' : bo = false := by rw [← hbo, ho]; rfl
    subst hbo'
    obtain ⟨hn2, -, -, -, hnP2, -⟩ := ctx_fields hW2.u.dec hW2.u.inn htop2
    have hne2 := ctx_names_end hW2.u.dec hW2.u.inn hW2.u.sl htop2
    cases h4 : callE p n "nest_occ" [rdW (m2.arr64 IW) ctx, rdW (m2.arr64 IW) (ctx + 1), rdW (m2.arr64 IW) (ctx + 4),
        nhiW m ctx pl, e] m2 with
    | error e4 =>
      rw [npE.k_nest_occ_2.eq_1]
      exact fun hG => ErrClaim.of_callE_nv hG.nv (_root_.L.Checker.nv_mem (by decide +kernel)) h4
    | ok q4 =>
    obtain ⟨o2, m3⟩ := q4
    obtain ⟨s4, hs4, -, hno2⟩ := triple_of_callW (nestOcc_spec' p L.nit.no n ⟨m2, Locals.init []⟩ _ _ _ _ _)
      (callW_of_callE h4)
    dsimp only at hno2
    rw [hs4] at hno2
    rw [npE.k_nest_occ_2.eq_2]
    obtain ⟨mp2, hmp2⟩ := hP2.no
    obtain ⟨bo2, hrun3, hbo2, hM3, hS3, hg3, hf3⟩ := noConstWf_ok n dn fe vis m2 m3 a1 _ _ _ _ _ _ c.names mp2 hno2 hS2
      he hn2 (by omega) hmp2
    rw [hnP2, hhi1, decE_eq] at hrun3
    have hns3 := hns2.grow hg3 htop2
    have hP3 : PosMR m3 := hP2.setNo hf3 ⟨∅, hM3⟩
    have hA3 : AbsOK m3 := noConstWf_afr hno2 hA2
    have hC3 : StageC dn vis fe env m3 a1 := hC2.of_pstep hS3 hA3 (PStep.refl hC1.check.state)
    simp only [Bool.not_false, ite_true]
    refine RefE.bind_right hrun3 ?_
    by_cases ho2 : o2.headD 0 ≠ 0
    · rw [ite_eq_left ho2]
      have hbo2' : bo2 = true := by rw [← hbo2]; simpa using ho2
      subst hbo2'
      exact RefE.ret (y := (.ordinary, w, NS)) (a' := a1) rfl ⟨hC3, hg12.trans hg3, by simp [decNFK],
        by simpa using hwH, by simpa using hwd, by simpa using hns3, hP3, hA3, c1⟩
    · rw [ite_eq_right ho2]
      have hbo2' : bo2 = false := by rw [← hbo2]; simpa using ho2
      subst hbo2'
      exact RefE.ret (y := (.ordinary, decI e, NS)) (a' := a1) rfl ⟨hC3, hg12.trans hg3, by simp [decNFK],
        by simpa using he, by simp, by simpa using hns3, hP3, hA3, c1⟩
  rw [ite_eq_right ho]
  have hbo' : bo = true := by rw [← hbo]; simpa using ho
  subst hbo'
  have hwP' : denoteE a1.store (decI (rw.headD 0)) = some wP := by rw [hwd]; exact hwP
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  by_cases h6 : rw.headD 0 >>> 28 = 6
  · -- a binder
    rw [ite_eq_left h6]
    have htag : w.tag = ETag.forallE := by rw [← hwd]; exact (decE_tag_forallE _ hwH).mpr h6
    rw [ite_eq_left (by simpa using htag)]
    have hs := npbE_spec p L.pbind n ⟨m2, Locals.init []⟩ vis ctx (fu - 1) po pl dep kb (rw.headD 0) ns
    have hR := ih.bind m2 a1 ctx (fu - 1) po pl dep kb (rw.headD 0) ns c prog NS ctxP progP wP nsP hC2 hW2 hwH h6
      hns2 hP2 hA2 hc (dCtx_ext _ hx01 _ _ hctx) (dProg_ext hx01 _ _ hprog) hwP' (dState_ext hx01 _ _ hnsP) hww
    rw [hwd] at hR
    cases h5 : callE p n "nest_pos_bind" [vis, ctx, fu - 1, po, pl, dep, kb, rw.headD 0, ns] m2 with
    | error e5 =>
      rw [npE.k_nest_pos_bind.eq_1]
      exact fun hG => RefE.run_err hs True.intro hG hR h5
    | ok q5 =>
    obtain ⟨r5, m5⟩ := q5
    rw [npE.k_nest_pos_bind.eq_2]
    obtain ⟨s5, hs5, -, x, a4, hrun4, hQ4⟩ := RefE.run_ok hs hR h5
    rw [hs5] at hQ4
    obtain ⟨hC4, hg4, hk4, hxH, hxd, hns4, hP4, hA4, c4⟩ := hQ4
    exact RefE.ret hrun4 ⟨hC4, hg12.trans hg4, by simpa using hk4, by simpa using hxH, by simpa using hxd,
      by simpa using hns4, hP4, hA4, c1.trans c4⟩
  · -- an application
    rw [ite_eq_right h6]
    have htag : ¬ w.tag = ETag.forallE := by rw [← hwd]; exact fun e' => h6 ((decE_tag_forallE _ hwH).mp e')
    rw [ite_eq_right (by simpa using htag)]
    have hs := npaE_spec p L.papp n ⟨m2, Locals.init []⟩ vis ctx (fu - 1) po pl kb (nhiW m ctx pl) (rw.headD 0) ns
    have hR := ih.app m2 a1 ctx (fu - 1) po pl kb (nhiW m ctx pl) (rw.headD 0) ns c prog NS ctxP progP wP nsP
      dep.toNat hC2 hW2 hhi1 hwH hns2 hP2 hA2 hc (dCtx_ext _ hx01 _ _ hctx) (dProg_ext hx01 _ _ hprog) hwP'
      (dState_ext hx01 _ _ hnsP) hww
    rw [hwd, hhi1] at hR
    cases h5 : callE p n "nest_pos_app" [vis, ctx, fu - 1, po, pl, kb, nhiW m ctx pl, rw.headD 0, ns] m2 with
    | error e5 =>
      rw [npE.k_nest_pos_app.eq_1]
      exact fun hG => RefE.run_err hs True.intro hG hR h5
    | ok q5 =>
    obtain ⟨r5, m5⟩ := q5
    rw [npE.k_nest_pos_app.eq_2]
    obtain ⟨s5, hs5, -, x, a4, hrun4, hQ4⟩ := RefE.run_ok hs hR h5
    rw [hs5] at hQ4
    obtain ⟨hC4, hg4, hk4, hx1, hns4, hP4, hA4, c4⟩ := hQ4
    exact RefE.ret hrun4 ⟨hC4, hg12.trans hg4, by simpa using hk4, by simpa using hwH,
      by simpa [hwd] using hx1.symm, by simpa using hns4, hP4, hA4, c1.trans c4⟩

end steps

section all
variable {p : Prog} (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)

theorem nbOKC_zero : NbOKC p dn vis fe env 0 := by
  simp only [NbOKC, PosOKC, BindOKC, AppOKC, ContOKC, KeyOKC, NewOKC, FrameOKC, CtorsOKC, OneOKC, WalkOKC,
    FieldsOKC]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;>
    simp_all [nbPosW, nbBindW, nbAppW, nbContW, nbKeyW, nbNewW, nbFrameW, nbCtorsW, nbOneW, nbWalkW, nbFieldsW]

variable {dn vis fe env} in
/-- **The block's `StageC` facts** at every exec fuel below `2^62` (the knot's sims'). -/
theorem nbOKC_all (L : NbLook p) (hq : KnotStageProg p) (hIlpf : IlpfF p) (hLC : LvlCacheProg p) (henv : ConLeche.EnvWF env) :
    ∀ n, n ≤ 2 ^ 62 → NbOKC p dn vis fe env n
  | 0, _ => nbOKC_zero dn vis fe env
  | n + 1, hn => by
    have ih := nbOKC_all L hq hIlpf hLC henv n (by omega)
    exact ⟨posOKC_step hq dn vis fe henv n (by omega) ih, bindOKC_step p dn vis fe henv n ih,
      appOKC_step p dn vis fe L.pf n ih, contOKC_step p dn vis fe L hIlpf hq.closed hLC n ih, keyOKC_step p dn vis fe n ih,
      newOKC_step p dn vis fe hIlpf hq.closed hLC L.nit.ty n ih, frameOKC_step hq dn vis fe henv L n hn ih, ctorsOKC_step p dn vis fe env n ih,
      oneOKC_step hq hIlpf dn vis fe henv L.ct n hn ih, walkOKC_step p dn vis fe henv n ih,
      fieldsOKC_step p dn vis fe henv n ih⟩

end all

end L.Ind
