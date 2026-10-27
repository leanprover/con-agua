import ConAgua.Arena.IndT.PosCrest
import ConAgua.Arena.IndPosSpec.Pos2DecHLSplit
import ConAgua.Arena.IndPosSpec.Snoc

/-!
# `nest_frame` under `StageC` (lane `indstaget`, helper `indstaget-pos`)

`frameOK_step`'s proof (`IndPosSpec/Pos2DecHLSplit`) at `realCall p`, its twin side con-ron's
`nestFrame_spec`'s: the group's head name (`internNNode_run`), the instantiation (`internConstE_run`,
`mkAppN_run`) typed (`inferC_rsim`), the group's constructors (`nestGroupCtors_spec`), the frame's
holes (`frameHoles_run`), the constructors walked (the block's `CtorsOKC` at `n`).
-/


open ConRon.Arena
open ConRon.Bridge.Inductives (PStep dCtx dProg dState dCtx_ext dProg_ext dState_ext dOut dCtors dGrp kindOf)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section steps
variable {p : Prog} (hq : KnotStageProg p) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
  {env : ConLeche.Env} (henv : ConLeche.EnvWF env)

include hq henv in
theorem frameOKC_step (n : Nat) (hn : n + 1 ≤ 2 ^ 62) (ih : NbOKC p dn vis fe env n) :
    FrameOKC p dn vis fe env (n + 1) := by
  obtain ⟨-, -, -, -, -, -, -, hCtors, -, -, -⟩ := ih
  intro m m' a ctx fu po pl hi us dO dL nPc gO gL ns c prog ds grp NS r ctxP progP usP dsP grpP nsP h hC hW hhi hus
    hds hdsb hgl hgb hgrp hns hP hA hc hctx hprog husP hdsP hgrpP hnsP hwds hwg
  have hS := hC.stage
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  obtain ⟨-, -, hfind, -, -, -⟩ := ConRon.Bridge.Inductives.dCtx_fields hctx
  rw [nbFrameW_succ] at h
  -- the group's head name
  have hhn : (if gL = 0 then naF m [] else some ([rdW (m.arr64 IW) (rdW (m.arr64 IW) gO)], m)) =
        none ∨ ∃ (rn : List Word) (m1 : Mem) (a1 : AState),
      (if gL = 0 then naF m [] else some ([rdW (m.arr64 IW) (rdW (m.arr64 IW) gO)], m)) =
        some (rn, m1) ∧ StageR dn vis fe m1 a1 ∧ IWGrow m m1 ∧ MFr [] [] m m1 ∧ AFr m m1 ∧ H (rn.headD 0) ∧
      (match grp with
        | [] => internNNode .anonymous
        | (c, _) :: _ => pure c : AM NIdx).run a = .ok (decI (rn.headD 0), a1) := by
    by_cases h0 : gL = 0
    · rw [ite_eq_left h0]
      have : grp = [] := List.eq_nil_of_length_eq_zero (by rw [← hgl, h0]; rfl)
      subst this
      rcases hst : naF m [] with _ | ⟨rn, m1⟩; · exact Or.inl rfl
      obtain ⟨x, a1, hrun, hS1, hg1, hxH, hxd⟩ := naF_ok dn vis fe m m1 a rn hst hS
      exact Or.inr ⟨rn, m1, a1, rfl, hS1, hg1, MFr.of_frame (naF_frame hst) (by simp [tier1, tierOff, NAREC, NASLOT]) (by simp),
        naF_afr hst, hxH, by rw [hxd]; exact hrun⟩
    · rw [ite_eq_right h0]
      obtain ⟨⟨cg, tg⟩, grp', rfl⟩ : ∃ x grp', grp = x :: grp' := by
        cases grp with
        | nil => exact absurd (UInt64.toNat_inj.mp (by simpa using hgl)) h0
        | cons x grp' => exact ⟨x, grp', rfl⟩
      simp only [List.length_cons] at hgb
      obtain ⟨w, cw, tw, hrw, hw1, hrc, hcH, hcd, -, -, -⟩ := hgrp.head (by omega) htop
      rw [UInt64.ofNat_toNat] at hrw
      rw [hrw, hrc]
      exact Or.inr ⟨[cw], m, a, rfl, hS, IWGrow.refl _, MFr.refl _ _ _, AFr.refl _, hcH,
        by simp only [List.headD_cons]; rw [hcd]; rfl⟩
  rcases hhn with hnone | ⟨rn, m1, a1, hrn, hS1, hg1, hf1, hfa1, hrnH, hrun1⟩
  · rw [hnone] at h; simp [nbFrameK1] at h
  rw [hrn, nbFrameK1_some] at h
  -- its twin side: a pure step, the name denoting the group's head
  have hhnP : PStep a a1 ∧ denoteN a1.store.ns (decI (rn.headD 0)) = some (grpP.headD default).1 := by
    cases grp with
    | nil =>
      simp only [dGrp, List.mapM_nil, Option.pure_def, Option.some.injEq] at hgrpP
      subst hgrpP
      simp only at hrun1
      obtain ⟨p, hd⟩ := ConRon.Bridge.Inductives.internNNode_run hC.check.state
        (by intro c hc; simp [NNodeView.children] at hc) hrun1
      exact ⟨p, by rw [hd]; rfl⟩
    | cons x grp' =>
      simp only at hrun1
      obtain ⟨hr, hs⟩ := ConRon.Bridge.AM.pure_ok hrun1
      rw [hs, hr]
      simp only [dGrp, List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at hgrpP
      rcases hx : ConRon.Bridge.Inductives.dGE a.store x with _ | y; · rw [hx] at hgrpP; simp at hgrpP
      rcases hxs : grp'.mapM (ConRon.Bridge.Inductives.dGE a.store) with _ | ys; · rw [hx, hxs] at hgrpP; simp at hgrpP
      simp only [hx, hxs, Option.bind_some, Option.some.injEq] at hgrpP
      subst hgrpP
      simp only [ConRon.Bridge.Inductives.dGE, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hx
      obtain ⟨cP, hcP, tyP, htyP, rfl⟩ := hx
      exact ⟨PStep.refl hC.check.state, hcP⟩
  obtain ⟨p1, hhn'⟩ := hhnP
  have hA1 : AbsOK m1 := hfa1 hA
  have hrnb : ¬ 4294967296 ≤ rn.headD 0 := by
    have : ¬ (4294967296 : Word).toNat ≤ (rn.headD 0).toNat := by simpa using hrnH
    exact fun e => this (UInt64.le_iff_toNat_le.mp e)
  rw [ite_eq_right hrnb] at h
  -- the instantiation `hn.{us} ds`, typed
  rcases hic : ceinternW m1 (rn.headD 0) us with _ | ⟨hc', m2⟩ <;> rw [hic] at h; · simp [nbFrameK2] at h
  rw [nbFrameK2_some] at h
  by_cases hcb : 4294967296 ≤ hc'
  · rw [ite_eq_left hcb] at h; cases h
  rw [ite_eq_right hcb] at h
  have hcH : H hc' := by
    have : ¬ (4294967296 : Word).toNat ≤ hc'.toNat := fun e => hcb (UInt64.le_iff_toNat_le.mpr e)
    simp only [H]; simpa using this
  obtain ⟨a2, hrun2, hS2, hg2⟩ := internConst_stage hS1 (rn.headD 0) us hrnH hus hic
  have e2 : (internConstE (decI (rn.headD 0)) (decI us)).run a1 = .ok (decI hc', a2) := hrun2
  obtain ⟨p2, hc2⟩ := ConRon.Bridge.Inductives.internConstE_run p1.ok hhn'
    (ConRon.Bridge.denoteLs_ext husP p1.ext) e2
  have hA2 : AbsOK m2 := ceinternW_afr hic hA1
  have hg12 := hg1.trans hg2
  rcases hma : mknF m2 [hc', dO, dL] with _ | ⟨ra, m3⟩ <;> rw [hma] at h; · simp [nbFrameK3] at h
  rw [nbFrameK3_some] at h
  obtain ⟨app, a3, hrun3, hS3, hg3, happH, happd⟩ := mknF_ok dn vis fe hc' dO dL hcH ds m2 m3 a2 ra hma
    ⟨hS2, (hds.grow (OMono.decHL _ _) hg12).get (OMono.decHL _ _)⟩
  obtain ⟨p3, happ⟩ := ConRon.Bridge.Inductives.mkAppN_run ds dsP p2.ok hc2
    (ConRon.Bridge.denoteEList_ext (p1.ext.trans p2.ext) _ _ hdsP) hrun3
  have hA3 : AbsOK m3 := mknF_afr hma hA2
  have p13 := p1.trans (p2.trans p3)
  have hC3 : StageC dn vis fe env m3 a3 := hC.of_pstep hS3 hA3 p13
  have hwapp : ConLeche.Expr.WScoped hi.toNat
      (ConLeche.Expr.mkAppN (.const (grpP.headD default).1 usP) dsP) :=
    ConLeche.Expr.WScoped.mkAppN (by simp [ConLeche.Expr.WScoped]) hwds
  rcases hit : realCall p n "infer_type_core" [vis, hi, ra.headD 0] m3 with _ | ⟨rt, m4⟩ <;> rw [hit] at h; · simp [nbFrameK4] at h
  rw [nbFrameK4_some] at h
  obtain ⟨ty, a4, hrun4, hC4, hg4, -, hA4, c4, -⟩ :=
    inferC_rsim hq henv n (by omega) hC3 hA3 hi (ra.headD 0) happH (by rw [happd]; exact happ) hwapp _ hit
  dsimp only at hC4 hg4 hA4
  have hS4 := hC4.stage
  have hg14 := (hg12.trans hg3).trans hg4
  have c3 := p13.toCore hC.check
  -- the stack grown and the names
  rcases hfg : fgW n m4 hi us dO dL gO gL po pl 0 0 with _ | ⟨rp, m5⟩ <;> rw [hfg] at h; · simp [nbFrameK5] at h
  rw [nbFrameK5_some] at h
  obtain ⟨hS5, hg5, hP5, hN5, hNb5⟩ := fgW_ok dn vis fe hi us dO dL ds hus n m4 m5 a4 gO gL po pl 0 0 grp prog [] rp
    hfg hS4 (hds.grow (OMono.decHL _ _) hg14) hgl (by have := hg14.1; omega) (hgrp.grow hgb hg14)
    (hW.hs.grow hg14) (by simp [decHL, hslice?]) (by simp)
  simp only [List.nil_append] at hP5 hN5
  -- the group's constructors
  rcases hgc : gcW n m5 vis nPc (rp.tail.tail.headD 0) (rp.tail.tail.tail.headD 0) 0 0 with _ | ⟨rc, m6⟩ <;> rw [hgc] at h; · simp [nbFrameK6] at h
  rw [nbFrameK6_some] at h
  obtain ⟨ctors, a6, hrun6, hS6, hg6, hcl6, hcb6, hcs6⟩ := gcW_ok dn fe vis nPc n m5 m6 a4 _ _ 0 0 (grp.map (·.1)) []
    rc hgc hS5 hN5 (fun j hj => by omega) (by simp) (by simp) (fun i hi => by simp at hi)
  have hx04 := c3.ext.trans c4.ext
  have hgrp4 := ConRon.Bridge.Inductives.dGrp_ext hx04 _ _ hgrpP
  obtain ⟨p5, vc, hvc, -, hvcl⟩ := ConRon.Bridge.Inductives.nestGroupCtors_spec ctxP hfind hc nPc.toNat _ _ [] []
    a4 a6 ctors hC4.check.state ⟨hC4.check.ienv.toS, ConRon.Bridge.Inductives.dGrp_names hgrp4, rfl⟩ hrun6
  simp only [List.nil_append] at hvc
  -- the holes
  have hg46 := hg5.trans hg6
  rcases hfh : fhW n m6 hi gO gL 0 0 with _ | ⟨rh, m7⟩ <;> rw [hfh] at h; · simp [nbFrameK7] at h
  rw [nbFrameK7_some] at h
  obtain ⟨holes, a7, hrun7, hS7, hg7, hH7, hHb7⟩ := fhW_ok dn vis fe n m6 m7 a6 hi gO gL 0 0 grp [] rh hfh hS6 hgl
    (by have := (hg14.trans hg46).1; omega) (hgrp.grow hgb (hg14.trans hg46)) (by simp [decHL, hslice?]) (by simp)
  simp only [List.nil_append] at hH7
  have hz : (grp.zipIdx.mapM fun ((_, ty), i) => internFVarE (hi.toNat + i) ty) = pos2FhT hi.toNat grp := by
    simpa using pos2_zipIdx_holes hi.toNat grp 0
  have hrun7' := hrun7
  rw [← hz] at hrun7'
  obtain ⟨p6, hholesP⟩ := ConRon.Bridge.Inductives.frameHoles_run hi.toNat (fun c ty i => rfl) grp grpP 0 a6 a7
    holes p5.ok (ConRon.Bridge.Inductives.dGrp_ext p5.ext _ _ hgrp4) hrun7'
  have hholesEq : ((grpP.zipIdx 0).map fun p => ConLeche.Expr.fvar (hi.toNat + p.2) p.1.2) =
      ConLeche.Cached.frameHoles hi.toNat grpP := by
    rw [ConLeche.Cached.frameHoles, List.mapIdx_eq_zipIdx_map]
  rw [hholesEq] at hholesP
  by_cases hov : hi + gL < hi
  · rw [ite_eq_left hov] at h; cases h
  rw [ite_eq_right hov] at h
  by_cases hov2 : dL + gL < dL
  · rw [ite_eq_left hov2] at h; cases h
  rw [ite_eq_right hov2] at h
  have hhg : (hi + gL).toNat = hi.toNat + gL.toNat := pos2_word_add hov
  have hdg : (dL + gL).toNat = dL.toNat + gL.toNat := pos2_word_add hov2
  have hg47 := (hg5.trans hg6).trans hg7
  have hg17 := (hg14.trans hg47)
  have htop7 : iwTop m7 < 2 ^ 64 := Nat.lt_of_le_of_lt hS7.2.1 hS7.2.2.2.1
  have hA7 : AbsOK m7 := fhW_afr _ _ _ _ _ _ _ _ _ hfh (gcW_afr _ _ _ _ _ _ _ _ _ _ hgc
    (fgW_afr _ _ _ _ _ _ _ _ _ _ _ _ _ _ hfg hA4))
  have p57 := p5.trans p6
  have hC7 : StageC dn vis fe env m7 a7 := hC4.of_pstep hS7 hA7 p57
  have hx07 := hx04.trans p57.ext
  have hlenG : grp.length = grpP.length := (ConLeche.option_mapM_length hgrpP).symm
  rcases hct : nbCtorsW (realCall p) n m7 vis ctx 0 fu (rp.headD 0) (rp.tail.headD 0) (hi + gL) us dO dL
      (rp.tail.tail.headD 0) (rp.tail.tail.tail.headD 0) (rh.headD 0) (rh.tail.headD 0) (rc.headD 0) (rc.tail.headD 0)
      ns 0 0 with _ | ⟨r8, m8⟩; · rw [hct] at h; simp [nbFrameK8] at h
  rw [hct, nbFrameK8_some] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  have hP7 := hP5.grow (hg6.trans hg7)
  have hpl2 : (rp.tail.headD 0).toNat = pl.toNat + gL.toNat := by rw [← hP7.1, List.length_append, hW.len]; simp [hgl]
  have hprog2 : dProg a7.store (prog ++ grp.map fun (x : NIdx × EIdx) =>
      ({ key := ⟨x.1, decI us, ds⟩, base := hi.toNat } : NestHole)) =
      some ((grpP.mapIdx fun _ (x : ConLeche.Name × ConLeche.Expr) =>
        ({ key := ⟨x.1, usP, dsP⟩, base := hi.toNat } : ConLeche.NestHole)).reverse ++ progP) := by
    rw [ConRon.Bridge.Inductives.mapIdx_blind (fun (x : ConLeche.Name × ConLeche.Expr) =>
      ({ key := ⟨x.1, usP, dsP⟩, base := hi.toNat } : ConLeche.NestHole))]
    exact ConRon.Bridge.Inductives.dProg_append (dProg_ext hx07 _ _ hprog)
      (ConRon.Bridge.Inductives.dHoles_grp (ConRon.Bridge.denoteLs_ext husP hx07)
        (ConRon.Bridge.denoteEList_ext hx07 _ _ hdsP) hi.toNat
        (ConRon.Bridge.Inductives.dGrp_ext hx07 _ _ hgrpP))
  have hpre : CtorsPre a7.store (decI us) ds (grp.map (·.1)) holes (hi + gL).toNat usP dsP (grpP.map (·.1))
      (ConLeche.Cached.frameHoles hi.toNat grpP) :=
    ⟨ConRon.Bridge.denoteLs_ext husP hx07, ConRon.Bridge.denoteEList_ext hx07 _ _ hdsP,
      ConRon.Bridge.Inductives.dGrp_names (ConRon.Bridge.Inductives.dGrp_ext p57.ext _ _ hgrp4), hholesP,
      fun d hd => ConLeche.Expr.WScoped.mono (by omega) (hwds d hd),
      by rw [hhg, hgl, hlenG]; exact ConLeche.Cached.frameHoles_wscoped hwg,
      by simp [ConLeche.Cached.frameHoles]⟩
  obtain ⟨x, a8, hrun8, hC8, hg8, -, -, hns8, hPm8, hA8, c8⟩ := hCtors m7 m8 a7 ctx 0 fu _ _ (hi + gL) us dO dL _ _ _ _
    _ _ ns 0 0 c (prog ++ grp.map fun x => (⟨⟨x.1, decI us, ds⟩, hi.toNat⟩ : NestHole)) ds (grp.map (·.1)) holes ctors
    NS [] r8 ctxP _ usP dsP (grpP.map (·.1)) (ConLeche.Cached.frameHoles hi.toNat grpP) vc nsP []
    hct hC7 ⟨hW.u.grow hg17, hP7, by
      have := hW.hb; rw [hW.len] at hhi; simp only [NestCtx.hiAt] at this hhi ⊢; rw [hpl2]
      have := (hi + gL).toNat_lt; omega⟩
    ⟨hus, hds.grow (OMono.decHL _ _) hg17, by have := hg17.1; omega,
      by rw [decHL_agree (RdS.of_grow (hg6.trans hg7)) (fun j hj => by omega)]; exact hN5,
      by have := (hg6.trans hg7).1; omega, by simp only [List.length_map]; rw [← hgl, ← hdg]; exact (dL + gL).toNat_lt,
      hH7, hHb7⟩
    hcl6 (by have := hg7.1; omega) (hcs6.grow hcb6 hg7) (hns.grow hg17 htop) (OutsB.nil _ _) (by simp)
    ((((((hP.fr hf1).fr (ceinternW_mfr hic)).fr (MFr.ofMknF hma)).fr (coreF_mfr hq (by decide) hit)).fr
      (fgW_mfr _ _ _ _ _ _ _ _ _ _ _ _ _ _ hfg)).fr (gcW_mfr _ _ _ _ _ _ _ _ _ _ hgc) |>.fr
      (fhW_mfr _ _ _ _ _ _ _ _ _ hfh)) hA7
    hc (dCtx_ext _ hx07 _ _ hctx) hprog2 hpre (ConRon.Bridge.Inductives.dCtors_ext p6.ext _ _ hvc) hvcl
    (dState_ext hx07 _ _ hnsP) rfl
  refine ⟨x.2, a8, ?_, hC8, hg17.trans hg8, by simpa using hns8, hPm8, hA8,
    (c3.trans c4).trans ((p57.toCore hC4.check).trans c8)⟩
  rw [ConRon.Arena.nestFrame.eq_def]
  rw [happd] at hrun4
  have e8 : (ConRon.Arena.nestCtors V fe c false fu.toNat
      (prog ++ grp.map fun (c, _) => { key := ⟨c, decI us, ds⟩, base := hi.toNat }) (hi.toNat + grp.length)
      (decI us) ds (grp.map (·.1)) holes ctors NS []).run a7 = .ok (x, a8) := by
    rw [hhg, hgl] at hrun8; simpa using hrun8
  cases grp with
  | nil =>
    simp only at hrun1
    simp only [StateT.run_bind, hrun1, except_ok_bind, e2, hrun3, hrun4, hrun6, hz, hrun7, e8]
    rfl
  | cons xg grp' =>
    obtain ⟨cg, tg⟩ := xg
    simp only at hrun1
    simp only [StateT.run_bind, hrun1, except_ok_bind, e2, hrun3, hrun4, hrun6, hz, hrun7, e8]
    rfl

end steps

end L.Ind
