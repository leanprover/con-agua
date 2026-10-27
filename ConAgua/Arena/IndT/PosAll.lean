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

`posOK_step`'s proof (`IndPosSpec/Pos2DecHLSplit`) at `realCall p`, its twin side con-ron's `nestPos_succ`'s:
the reduct (`whnfC_rsim`), its occurrence checks (no state change), then hole-free, a binder (the
block's `BindOKC` at `n`) or a head (`AppOKC` at `n`). Then the block's `StageC` facts at every
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
theorem posOKC_step (n : Nat) (hn : n ≤ 2 ^ 62) (ih : NbOKC p dn vis fe env n) :
    PosOKC p dn vis fe env (n + 1) := by
  obtain ⟨-, hBind, hApp, -, -, -, -, -, -, -, -⟩ := ih
  intro m m' a ctx fu po pl dep kb e ns c prog NS r ctxP progP eP nsP h hC hW he hns hP hA hc hctx hprog heP hnsP
    hwe
  have hS := hC.stage
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  rw [nbPosW_succ] at h
  by_cases hf0 : fu = 0
  · rw [ite_eq_left hf0] at h; cases h
  rw [ite_eq_right hf0] at h
  have hfu : fu.toNat = (fu - 1).toNat + 1 := by
    have : fu.toNat ≠ 0 := fun e' => hf0 (UInt64.toNat_inj.mp (by simpa using e'))
    rw [pos2_word_pred hf0]; omega
  have hhi := hW.hi htop
  -- the reduct
  rcases hwt : realCall p n "whnf_top" [vis, dep, e] m with _ | ⟨rw, m1⟩ <;> rw [hwt] at h; · simp [nbPosK1] at h
  rw [nbPosK1_some] at h
  obtain ⟨w, a1, hrun1, hC1, hg1, ⟨hwH, hwd⟩, hA1, c1, wP, hwP, hww⟩ :=
    whnfC_rsim hq henv n hn hC hA dep e he heP hwe _ hwt
  dsimp only at hC1 hg1 hwH hwd hA1
  have hS1 := hC1.stage
  have htop1 : iwTop m1 < 2 ^ 64 := Nat.lt_of_le_of_lt hS1.2.1 hS1.2.2.2.1
  have hW1 := hW.grow hg1
  obtain ⟨hn1, -, -, -, hnP1, -⟩ := ctx_fields hW1.u.dec hW1.u.inn htop1
  have hne1 := ctx_names_end hW1.u.dec hW1.u.inn hW1.u.sl htop1
  have hhi1 : (nhiW m ctx pl).toNat = c.hiAt prog.length := hhi
  rcases hno : noConstWf n m1 (rdW (m1.arr64 IW) ctx) (rdW (m1.arr64 IW) (ctx + 1)) (rdW (m1.arr64 IW) (ctx + 4))
      (nhiW m ctx pl) (rw.headD 0) with _ | ⟨o, m2⟩; · rw [hno] at h; simp [nbPosK2] at h
  rw [hno, nbPosK2_some] at h
  have hP1 : PosMR m1 := hP.fr (coreF_mfr hq (by decide) hwt)
  obtain ⟨mp, hmp⟩ := hP1.no
  obtain ⟨bo, hrun2, hbo, hM2, hS2, hg2, hf2⟩ := noConstWf_ok n dn fe vis m1 m2 a1 _ _ _ _ _ o c.names mp hno hS1 hwH hn1
    (by omega) hmp
  rw [hnP1, hhi1, decE_eq, hwd] at hrun2
  have hg12 := hg1.trans hg2
  have htop2 : iwTop m2 < 2 ^ 64 := Nat.lt_of_le_of_lt hS2.2.1 hS2.2.2.2.1
  have hW2 := hW.grow hg12
  have hns2 := hns.grow hg12 htop
  have hP2 : PosMR m2 := hP1.setNo hf2 ⟨∅, hM2⟩
  have hA2 : AbsOK m2 := noConstWf_afr hno hA1
  have hC2 : StageC dn vis fe env m2 a1 := hC1.of_pstep hS2 hA2 (PStep.refl hC1.check.state)
  have hrun1' : (whnf V fe checkFuel dep.toNat (decI e)).run a = .ok (w, a1) := hrun1
  have hx01 := c1.ext
  by_cases ho : o = 0
  · -- no occurrence in the reduct: the original, or the reduct
    rw [ite_eq_left ho] at h
    have hbo' : bo = false := by rw [← hbo]; simp [ho]
    subst hbo'
    obtain ⟨hn2, -, -, -, hnP2, -⟩ := ctx_fields hW2.u.dec hW2.u.inn htop2
    have hne2 := ctx_names_end hW2.u.dec hW2.u.inn hW2.u.sl htop2
    rcases hno2 : noConstWf n m2 (rdW (m2.arr64 IW) ctx) (rdW (m2.arr64 IW) (ctx + 1)) (rdW (m2.arr64 IW) (ctx + 4))
        (nhiW m ctx pl) e with _ | ⟨o2, m3⟩; · rw [hno2] at h; simp [nbPosK3] at h
    rw [hno2] at h
    obtain ⟨mp2, hmp2⟩ := hP2.no
    obtain ⟨bo2, hrun3, hbo2, hM3, hS3, hg3, hf3⟩ := noConstWf_ok n dn fe vis m2 m3 a1 _ _ _ _ _ o2 c.names mp2 hno2 hS2
      he hn2 (by omega) hmp2
    rw [hnP2, hhi1, decE_eq] at hrun3
    have hns3 := hns2.grow hg3 htop2
    have hP3 : PosMR m3 := hP2.setNo hf3 ⟨∅, hM3⟩
    have hA3 : AbsOK m3 := noConstWf_afr hno2 hA2
    have hC3 : StageC dn vis fe env m3 a1 := hC2.of_pstep hS3 hA3 (PStep.refl hC1.check.state)
    simp only [nbPosK3] at h
    by_cases ho2 : o2 ≠ 0
    · rw [ite_eq_left ho2] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have hbo2' : bo2 = true := by rw [← hbo2]; simpa using ho2
      subst hbo2'
      refine ⟨(.ordinary, w, NS), a1, ?_, hC3, hg12.trans hg3, by simp [decNFK], by simpa using hwH,
        by simpa using hwd, by simpa using hns3, hP3, hA3, c1⟩
      simp only [hfu, nestPos_succ, StateT.run_bind, hrun1', except_ok_bind, hrun2, Bool.not_false, ite_true, hrun3]
      rfl
    · rw [ite_eq_right ho2] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have hbo2' : bo2 = false := by rw [← hbo2]; simpa using ho2
      subst hbo2'
      refine ⟨(.ordinary, decI e, NS), a1, ?_, hC3, hg12.trans hg3, by simp [decNFK], by simpa using he,
        by simp, by simpa using hns3, hP3, hA3, c1⟩
      simp only [hfu, nestPos_succ, StateT.run_bind, hrun1', except_ok_bind, hrun2, Bool.not_false, ite_true, hrun3]
      rfl
  rw [ite_eq_right ho] at h
  have hbo' : bo = true := by rw [← hbo]; simpa using ho
  subst hbo'
  have hwP' : denoteE a1.store (decI (rw.headD 0)) = some wP := by rw [hwd]; exact hwP
  by_cases h6 : rw.headD 0 >>> 28 = 6
  · -- a binder
    rw [ite_eq_left h6] at h
    rcases hb : nbBindW (realCall p) n m2 vis ctx (fu - 1) po pl dep kb (rw.headD 0) ns with _ | ⟨rb, m4⟩ <;> rw [hb] at h; · simp [nbPosK4] at h
    simp only [nbPosK4, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨x, a4, hrun4, hC4, hg4, hk4, hxH, hxd, hns4, hP4, hA4, c4⟩ :=
      hBind m2 m4 a1 ctx (fu - 1) po pl dep kb (rw.headD 0) ns c prog NS rb ctxP progP wP nsP hb hC2 hW2 hwH h6 hns2 hP2
        hA2 hc (dCtx_ext _ hx01 _ _ hctx) (dProg_ext hx01 _ _ hprog) hwP' (dState_ext hx01 _ _ hnsP) hww
    refine ⟨x, a4, ?_, hC4, hg12.trans hg4, by simpa using hk4, by simpa using hxH, by simpa using hxd,
      by simpa using hns4, hP4, hA4, c1.trans c4⟩
    have htag : w.tag = ETag.forallE := by rw [← hwd]; exact (decE_tag_forall _ hwH).mpr h6
    rw [hwd] at hrun4
    simp only [hfu, nestPos_succ, StateT.run_bind, hrun1', except_ok_bind, hrun2, Bool.not_true, htag, beq_iff_eq]
    simpa using hrun4
  · -- an application
    rw [ite_eq_right h6] at h
    rcases hp : nbAppW (realCall p) n m2 vis ctx (fu - 1) po pl kb (nhiW m ctx pl) (rw.headD 0) ns with _ | ⟨rp, m4⟩ <;> rw [hp] at h; · simp [nbPosK5] at h
    simp only [nbPosK5, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨x, a4, hrun4, hC4, hg4, hk4, hx1, hns4, hP4, hA4, c4⟩ :=
      hApp m2 m4 a1 ctx (fu - 1) po pl kb (nhiW m ctx pl) (rw.headD 0) ns c prog NS rp ctxP progP wP nsP dep.toNat hp
        hC2 hW2 hhi1 hwH hns2 hP2 hA2 hc (dCtx_ext _ hx01 _ _ hctx) (dProg_ext hx01 _ _ hprog) hwP'
        (dState_ext hx01 _ _ hnsP) hww
    refine ⟨x, a4, ?_, hC4, hg12.trans hg4, by simpa using hk4, by simpa using hwH,
      by simpa [hwd] using hx1.symm, by simpa using hns4, hP4, hA4, c1.trans c4⟩
    have htag : ¬ w.tag = ETag.forallE := by rw [← hwd]; exact fun e' => h6 ((decE_tag_forall _ hwH).mp e')
    rw [hwd, hhi1] at hrun4
    simp only [hfu, nestPos_succ, StateT.run_bind, hrun1', except_ok_bind, hrun2, Bool.not_true, htag, beq_iff_eq]
    simpa using hrun4

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
theorem nbOKC_all (hq : KnotStageProg p) (hIlpf : IlpfF p) (hLC : LvlCacheProg p) (henv : ConLeche.EnvWF env) :
    ∀ n, n ≤ 2 ^ 62 → NbOKC p dn vis fe env n
  | 0, _ => nbOKC_zero dn vis fe env
  | n + 1, hn => by
    have ih := nbOKC_all hq hIlpf hLC henv n (by omega)
    exact ⟨posOKC_step hq dn vis fe henv n (by omega) ih, bindOKC_step p dn vis fe henv n ih,
      appOKC_step p dn vis fe n ih, contOKC_step p dn vis fe hIlpf hq.closed hLC n ih, keyOKC_step p dn vis fe n ih,
      newOKC_step p dn vis fe hIlpf hq.closed hLC n ih, frameOKC_step hq dn vis fe henv n hn ih, ctorsOKC_step p dn vis fe env n ih,
      oneOKC_step hq hIlpf dn vis fe henv n hn ih, walkOKC_step p dn vis fe henv n ih,
      fieldsOKC_step p dn vis fe henv n ih⟩

end all

end L.Ind
