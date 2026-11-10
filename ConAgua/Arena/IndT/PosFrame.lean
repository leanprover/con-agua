module

public import ConAgua.Arena.IndT.PosFkc
import ConAgua.Arena.IndPosSpec.FgW
public import ConAgua.Verdict.PosE
import ConAgua.Verdict.PosNgc
import ConAgua.Arena.IndPosSpec.Pos2DecHLSplit
import ConAgua.Arena.IndPosSpec.Snoc
import all ConRon.Bridge.Inductives.Positivity
import ConAgua.Arena.IndPosSpec.GgW2
import ConAgua.Arena.IndPosSpec.Grow
import ConAgua.Arena.IndRealAbsPos
import ConAgua.Arena.IndRealAbsSim
import ConAgua.Checker.NoVerdictTree

@[expose] public section

/-!
# `nest_frame` refines `nestFrame`, both outcomes (lane `indstaget`, helper `indstaget-pos`)

`frameRef_step`, on the unified model `nfrE`, its twin side con-ron's `nestFrame_spec`'s: the group's
head name (`internNNode_run`), the instantiation (`internConstE_run`, `mkAppN_run`) typed
(`inferC_rsim`; its error from `CoreStubsE`), the group's constructors (`ngc_ref`), the frame's holes
(`frameHoles_run`), the constructors walked (the block's `CtorsRef` at `n`).
-/


open ConRon.Arena
open ConRon.Bridge.Inductives (PStep dCtx dProg dState dCtx_ext dProg_ext dState_ext dOut dCtors dGrp kindOf)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- The head of `nestFrame`'s group (its first step). -/
def nestHeadT (grp : List (NIdx × EIdx)) : AM NIdx :=
  match grp with
  | [] => internNNode .anonymous
  | (c, _) :: _ => pure c

section steps
variable {p : Prog} (hq : KnotStageProg p) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
  {env : ConLeche.Env} (henv : ConLeche.EnvWF env)

include hq henv in
/-- **`nest_frame` refines `nestFrame`, both outcomes**, at L fuel `n + 1`: the group's head name, the
family at the key typed (`fkc_ref`), the frame's stack entries (`fgW_ok`), the group's constructors
(`ngc_ref`), the holes, the constructors walked (the block's `CtorsRef` at `n`). -/
theorem frameRef_step (L : NbLook p) (hFk : FkcProg p) (hIlpf : IlpfF p) (n : Nat) (hn : n ≤ 2 ^ 62)
    (ih : NbRef p dn vis fe env n) : FrameRef p dn vis fe env (n + 1) := by
  have R := L.ct.cr.rx
  intro m a ctx fu po pl hi us dO dL nPc gO gL ns c prog ds grp NS ctxP progP usP dsP grpP nsP hC hW hhi hus
    hds hdsb hgl hgb hgrp hns hP hA hc hctx hprog husP hdsP hgrpP hnsP hwds hwg
  have hS := hC.stage
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.iw.iw hS.iw.iwSize
  obtain ⟨-, -, hfind, -, -, -⟩ := ConRon.Bridge.Inductives.dCtx_fields hctx
  -- the group's head name
  suffices hJ : ∀ rn m1, (if gL = 0 then naF m [] else some ([rdW (m.arr64 IW) (rdW (m.arr64 IW) gO)], m)) =
      some (rn, m1) → RefE (NbG p) (nfrE.j1 p n vis ctx fu po pl hi us dO dL nPc gO gL ns (rn.headD 0) m1)
        (nestFrame V fe c fu.toNat prog hi.toNat (decI us) ds nPc.toNat grp NS) a
        (fun v x a' => FramePost dn vis fe env a m v.1 v.2 x a') by
    by_cases h0 : gL = 0
    · rw [nfrE.arm1 p n m vis ctx fu po pl hi us dO dL nPc gO gL ns h0]
      cases h1 : callE p n "intern_nanon" [] m with
      | error e1 =>
        rw [nfrE.k_intern_nanon.none]
        exact fun hG => ErrClaim.of_callE_nv hG.nv (_root_.L.Checker.nv_mem (by decide +kernel)) h1
      | ok q1 =>
      obtain ⟨rn, m1⟩ := q1
      obtain ⟨s1, hs1, -, hna⟩ := triple_of_callW (naF_spec p L.na n ⟨m, Locals.init []⟩ []) (callW_of_callE h1)
      simp only at hna
      rw [hs1] at hna
      rw [nfrE.k_intern_nanon.arm1]
      exact hJ rn m1 (by rw [ite_eq_left h0]; exact hna)
    · rw [nfrE.arm2 p n m vis ctx fu po pl hi us dO dL nPc gO gL ns h0]
      exact hJ _ _ (by rw [ite_eq_right h0])
  intro rn m1 hX
  have hhn : (if gL = 0 then naF m [] else some ([rdW (m.arr64 IW) (rdW (m.arr64 IW) gO)], m)) =
        none ∨ ∃ (rn : List Word) (m1 : Mem) (a1 : AState),
      (if gL = 0 then naF m [] else some ([rdW (m.arr64 IW) (rdW (m.arr64 IW) gO)], m)) =
        some (rn, m1) ∧ StageR vis fe m1 a1 ∧ IWGrow m m1 ∧ MFr [] [] m m1 ∧ AFr m m1 ∧ H (rn.headD 0) ∧
      (nestHeadT grp).run a = .ok (decI (rn.headD 0), a1) := by
    by_cases h0 : gL = 0
    · rw [ite_eq_left h0]
      have : grp = [] := List.eq_nil_of_length_eq_zero (by rw [← hgl, h0]; rfl)
      subst this
      rcases hst : naF m [] with _ | ⟨rn, m1⟩; · exact Or.inl rfl
      obtain ⟨x, a1, hrun, hS1, hg1, hxH, hxd⟩ := naF_ok dn vis fe m m1 a rn hst hS
      exact Or.inr ⟨rn, m1, a1, rfl, hS1, hg1, MFr.of_frame (naF_frame hst) (by simp [tier1, NAREC, NASLOT]) (by simp),
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
  rcases hhn with hnone | ⟨rn', m1', a1, hrn, hS1, hg1, hf1, hfa1, hrnH, hrun1⟩
  · rw [hnone] at hX; cases hX
  rw [hX] at hrn
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hrn)
  -- its twin side: a pure step, the name denoting the group's head
  have hhnP : PStep a a1 ∧ denoteN a1.store.ns (decI (rn.headD 0)) = some (grpP.headD default).1 := by
    cases grp with
    | nil =>
      simp only [dGrp, List.mapM_nil, Option.pure_def, Option.some.injEq] at hgrpP
      subst hgrpP
      simp only [nestHeadT] at hrun1
      obtain ⟨p, hd⟩ := ConRon.Bridge.Inductives.internNNode_run hC.check.state
        (by intro c hc; simp [NNodeView.children] at hc) hrun1
      exact ⟨p, by rw [hd]; rfl⟩
    | cons x grp' =>
      simp only [nestHeadT] at hrun1
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
  rw [nfrE.j1.arm1 p n vis ctx fu po pl hi us dO dL nPc gO gL ns _ m1 hrnb]
  rw [ConRon.Bridge.Inductives.nestFrame_eq]
  refine RefE.bind_right (x := nestHeadT grp) hrun1 ?_
  have hC1 : StageC dn vis fe env m1 a1 := hC.of_pstep hS1 hA1 p1
  have c1 := p1.toCore hC.check
  -- the family at the key, typed
  have hdsD1 : decHL m1 dO.toNat dL.toNat = some ds := (hds.grow (OMono.decHL _ _) hg1).get (OMono.decHL _ _)
  have hR2 := fkc_ref hq henv (G := NbG p) hFk hIlpf (fun hG => hG.nv) (fun hG => hG.core) (fun hG => hG.whnf)
    hi n hn hC1 hA1 hrnH hus hdsD1 (.inr (by have := hg1.iw; omega)) hhn' (ConRon.Bridge.denoteLs_ext husP p1.ext)
    (ConRon.Bridge.denoteEList_ext p1.ext _ _ hdsP) hwds
  have hsp2 := fkcE_spec p hFk n ⟨m1, Locals.init []⟩ vis hi (rn.headD 0) us dO dL
  cases h2 : callE p n "family_key_check" [vis, hi, rn.headD 0, us, dO, dL] m1 with
  | error e2 =>
    rw [nfrE.k_family_key_check.none]
    exact RefE.bind_left fun hG => RefE.run_err hsp2 hG.nv hG hR2 h2
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [nfrE.k_family_key_check.arm1]
  obtain ⟨s2, hs2, -, u2, a2, hrun2, k2, hP2⟩ := RefE.run_ok hsp2 hR2 h2
  dsimp only at k2 hP2
  rw [hs2] at k2 hP2
  refine RefE.bind_right hrun2 ?_
  have hS2 := k2.stage.stage
  have hA2 := k2.abs
  have hg12 := hg1.trans k2.grow
  have hx02 := p1.ext.trans k2.core.ext
  -- the stack grown and the names
  cases h5 : callE p n "nest_frame_grp" [hi, us, dO, dL, gO, gL, po, pl, 0, 0] m2 with
  | error e5 =>
    rw [nfrE.k_nest_frame_grp.none]
    exact fun hG => ErrClaim.of_callE_nv hG.nv (_root_.L.Checker.nv_mem (by decide +kernel)) h5
  | ok q5 =>
  obtain ⟨r5, m5⟩ := q5
  obtain ⟨s5, hs5, -, hfg⟩ := triple_of_callW (nestFrameGrp_spec p R.ha L.nit.hc2 L.h3 R.h4 L.nag.hsn
    L.pf.na.hv L.pf.na.hs L.pf.na.hpb L.hfg n ⟨m2, Locals.init []⟩ hi us dO dL gO gL po pl 0 0) (callW_of_callE h5)
  simp only at hfg
  rw [hs5] at hfg
  rw [nfrE.k_nest_frame_grp.arm1]
  generalize hrp : [r5.headD 0, r5.tail.headD 0, r5.tail.tail.headD 0, r5.tail.tail.tail.headD 0] = rp at hfg
  have e0 : r5.headD 0 = rp.headD 0 := by rw [← hrp]; rfl
  have e1 : r5.tail.headD 0 = rp.tail.headD 0 := by rw [← hrp]; rfl
  have e2' : r5.tail.tail.headD 0 = rp.tail.tail.headD 0 := by rw [← hrp]; rfl
  have e3 : r5.tail.tail.tail.headD 0 = rp.tail.tail.tail.headD 0 := by rw [← hrp]; rfl
  rw [e0, e1, e2', e3]
  obtain ⟨fr, hrunF, hS5, hg5, hP5, hN5, hNb5⟩ := fgW_ok dn vis fe hi us dO dL ds hus n m2 m5 a2 gO gL po pl 0 0 grp
    prog [] rp hfg hS2 (hds.grow (OMono.decHL _ _) hg12) hgl (by have := hg12.iw; omega) (hgrp.grow hgb hg12)
    (hW.hs.grow hg12) (by simp [decHL, hslice?]) (by simp)
  simp only [List.nil_append] at hN5
  obtain ⟨-, hfrP⟩ := ConRon.Bridge.Inductives.frameEntries_run hi.toNat (fun c ty => rfl) grp grpP a2 a2 fr
    k2.stage.check.state (ConRon.Bridge.denoteLs_ext husP hx02) (ConRon.Bridge.denoteEList_ext hx02 _ _ hdsP)
    (ConRon.Bridge.Inductives.dGrp_ext hx02 _ _ hgrpP) hrunF
  refine RefE.bind_right (x := grp.mapM (frEntryT (decI us) ds hi.toNat)) hrunF ?_
  have hgrp4 := ConRon.Bridge.Inductives.dGrp_ext hx02 _ _ hgrpP
  -- the group's constructors
  have hsp6 := ngcE_spec p L.nt L.nit.hc2 L.hap L.hgc n ⟨m5, Locals.init []⟩ vis nPc
    (rp.tail.tail.headD 0) (rp.tail.tail.tail.headD 0) 0 0
  have hR6 := ngc_ref (p := p) dn fe vis nPc n m5 a2 _ _ 0 0 (grp.map (·.1)) [] hS5 hN5 (fun j hj => by omega)
    (by simp) (by simp) (fun i hi => by simp at hi)
  cases h6 : callE p n "nest_group_ctors" [vis, nPc, rp.tail.tail.headD 0, rp.tail.tail.tail.headD 0, 0, 0] m5 with
  | error e6 =>
    rw [nfrE.k_nest_group_ctors.none]
    exact RefE.bind_left fun hG => RefE.run_err hsp6 hG.nv hG.nv hR6 h6
  | ok q6 =>
  obtain ⟨rc, m6⟩ := q6
  rw [nfrE.k_nest_group_ctors.arm1]
  obtain ⟨s6, hs6, -, ctors, a6, hrun6, ⟨hS6, hg6, hcl6, hcb6, hcs6, hA6, hM6⟩⟩ := RefE.run_ok hsp6 hR6 h6
  dsimp only at hS6 hg6 hcl6 hcb6 hcs6 hA6 hM6
  rw [hs6] at hS6 hg6 hcb6 hcs6 hA6 hM6
  obtain ⟨p5, vc, hvc, -, hvcl⟩ := ConRon.Bridge.Inductives.nestGroupCtors_spec ctxP hfind hc nPc.toNat _ _ [] []
    a2 a6 ctors k2.stage.check.state ⟨k2.stage.check.ienv.toS, ConRon.Bridge.Inductives.dGrp_names hgrp4, rfl⟩ hrun6
  simp only [List.nil_append] at hvc
  refine RefE.bind_right hrun6 ?_
  -- the holes
  have hg46 := hg5.trans hg6
  cases h7 : callE p n "nest_frame_holes" [hi, gO, gL, 0, 0] m6 with
  | error e7 =>
    rw [nfrE.k_nest_frame_holes.none]
    exact fun hG => ErrClaim.of_callE_nv hG.nv (_root_.L.Checker.nv_mem (by decide +kernel)) h7
  | ok q7 =>
  obtain ⟨r7, m7⟩ := q7
  obtain ⟨s7, hs7, -, hfh⟩ := triple_of_callW (nestFrameHoles_spec p R.ha L.nit.hc2 L.nag.hsn R.hl.hff R.hl.hfp
    R.hl.hif L.hfh n ⟨m6, Locals.init []⟩ hi gO gL 0 0) (callW_of_callE h7)
  simp only at hfh
  rw [hs7] at hfh
  generalize hrh : [r7.headD 0, r7.tail.headD 0] = rh at hfh
  have g0 : r7.headD 0 = rh.headD 0 := by rw [← hrh]; rfl
  have g1 : r7.tail.headD 0 = rh.tail.headD 0 := by rw [← hrh]; rfl
  obtain ⟨holes, a7, hrun7, hS7, hg7, hH7, hHb7⟩ := fhW_ok dn vis fe n m6 m7 a6 hi gO gL 0 0 grp [] rh hfh hS6 hgl
    (by have := (hg12.trans hg46).iw; omega) (hgrp.grow hgb (hg12.trans hg46)) (by simp [decHL, hslice?]) (by simp)
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
  refine RefE.bind_right hrun7' ?_
  by_cases hov : hi + gL < hi
  · rw [nfrE.k_nest_frame_holes.abort1 p n vis ctx fu hi us dO dL gL ns _ _ _ _ _ _ r7 m7 hov]
    exact RefE.of_cls0 rfl
  by_cases hov2 : dL + gL < dL
  · rw [nfrE.k_nest_frame_holes.abort2 p n vis ctx fu hi us dO dL gL ns _ _ _ _ _ _ r7 m7 hov hov2]
    exact RefE.of_cls0 rfl
  rw [nfrE.k_nest_frame_holes.arm1 p n vis ctx fu hi us dO dL gL ns _ _ _ _ _ _ r7 m7 hov hov2, g0, g1]
  have hhg : (hi + gL).toNat = hi.toNat + gL.toNat := pos2_word_add hov
  have hdg : (dL + gL).toNat = dL.toNat + gL.toNat := pos2_word_add hov2
  have hg47 := (hg5.trans hg6).trans hg7
  have hg17 := (hg12.trans hg47)
  have htop7 : iwTop m7 < 2 ^ 64 := Nat.lt_of_le_of_lt hS7.iw.iw hS7.iw.iwSize
  have hA7 : AbsOK m7 := fhW_afr _ _ _ _ _ _ _ _ _ hfh (hA6
    (fgW_afr _ _ _ _ _ _ _ _ _ _ _ _ _ _ hfg hA2))
  have p57 := p5.trans p6
  have hC7 : StageC dn vis fe env m7 a7 := k2.stage.of_pstep hS7 hA7 p57
  have hx07 := hx02.trans p57.ext
  have hlenG : grp.length = grpP.length := (ConLeche.option_mapM_length hgrpP).symm
  have hP7 := hP5.grow (hg6.trans hg7)
  have hfrl : fr.length = grp.length := by
    have := ConLeche.option_mapM_length hfrP
    simp only [List.length_map] at this; omega
  have hpl2 : (rp.tail.headD 0).toNat = pl.toNat + gL.toNat := by
    rw [← hP7.1, List.length_append, hW.len]; simp [hgl, hfrl]
  obtain ⟨progP2, hprog2⟩ : ∃ q, dProg a7.store (prog ++ fr) = some q :=
    ⟨_, ConRon.Bridge.Inductives.dProg_append (dProg_ext hx07 _ _ hprog)
      (ConRon.Bridge.Inductives.dHole_ext.list p57.ext _ _ hfrP)⟩
  have hpre : CtorsPre a7.store (decI us) ds (grp.map (·.1)) holes (hi + gL).toNat usP dsP (grpP.map (·.1))
      (ConLeche.Cached.frameHoles hi.toNat grpP) :=
    ⟨ConRon.Bridge.denoteLs_ext husP hx07, ConRon.Bridge.denoteEList_ext hx07 _ _ hdsP,
      ConRon.Bridge.Inductives.dGrp_names (ConRon.Bridge.Inductives.dGrp_ext p57.ext _ _ hgrp4), hholesP,
      fun d hd => ConLeche.Expr.WScoped.mono (by omega) (hwds d hd),
      by rw [hhg, hgl, hlenG]; exact ConLeche.Cached.frameHoles_wscoped hwg,
      by simp [ConLeche.Cached.frameHoles]⟩
  -- the constructors walked
  have hR8 := ih.ctors m7 a7 ctx 0 fu (rp.headD 0) (rp.tail.headD 0) (hi + gL) us dO dL (rp.tail.tail.headD 0)
    (rp.tail.tail.tail.headD 0) (rh.headD 0) (rh.tail.headD 0) (rc.headD 0) (rc.tail.headD 0) ns 0 0 c
    (prog ++ fr) ds (grp.map (·.1)) holes ctors
    NS [] ctxP _ usP dsP (grpP.map (·.1)) (ConLeche.Cached.frameHoles hi.toNat grpP) vc nsP []
    hC7 ⟨hW.u.grow hg17, hP7, by
      have := hW.hb; rw [hW.len] at hhi; simp only [NestCtx.hiAt] at this hhi ⊢; rw [hpl2]
      have := (hi + gL).toNat_lt; omega⟩
    ⟨hus, hds.grow (OMono.decHL _ _) hg17, by have := hg17.iw; omega,
      by rw [decHL_agree (RdS.of_grow (hg6.trans hg7)) (fun j hj => by omega)]; exact hN5,
      by have := (hg6.trans hg7).iw; omega, by simp only [List.length_map]; rw [← hgl, ← hdg]; exact (dL + gL).toNat_lt,
      hH7, hHb7⟩
    hcl6 (by have := hg7.iw; omega) (hcs6.grow hcb6 hg7) (hns.grow hg17 htop) (OutsB.nil _ _) (by simp)
    (((hP2 (hP.fr hf1)).fr
      (fgW_mfr _ _ _ _ _ _ _ _ _ _ _ _ _ _ hfg)).fr hM6 |>.fr
      (fhW_mfr _ _ _ _ _ _ _ _ _ hfh)) hA7
    hc (dCtx_ext _ hx07 _ _ hctx) hprog2 hpre (ConRon.Bridge.Inductives.dCtors_ext p6.ext _ _ hvc) hvcl
    (dState_ext hx07 _ _ hnsP) rfl
  rw [hhg, hgl] at hR8
  have hsp8 := nctE_spec p L.pctors n ⟨m7, Locals.init []⟩ vis ctx 0 fu (rp.headD 0) (rp.tail.headD 0) (hi + gL) us
    dO dL (rp.tail.tail.headD 0) (rp.tail.tail.tail.headD 0) (rh.headD 0) (rh.tail.headD 0) (rc.headD 0)
    (rc.tail.headD 0) ns 0 0
  cases h8 : callE p n "nest_ctors" [vis, ctx, 0, fu, rp.headD 0, rp.tail.headD 0, hi + gL, us, dO, dL,
      rp.tail.tail.headD 0, rp.tail.tail.tail.headD 0, rh.headD 0, rh.tail.headD 0, rc.headD 0, rc.tail.headD 0,
      ns, 0, 0] m7 with
  | error e8 =>
    rw [nfrE.k_nest_ctors.none]
    exact RefE.bind_left fun hG => by simpa using RefE.run_err hsp8 True.intro hG hR8 h8
  | ok q8 =>
  obtain ⟨r8, m8⟩ := q8
  rw [nfrE.k_nest_ctors.arm1]
  obtain ⟨s8, hs8, -, x, a8, hrun8, hpost⟩ := RefE.run_ok hsp8 hR8 h8
  dsimp only at hpost
  rw [hs8] at hpost
  have e8 : (ConRon.Arena.nestCtors V fe c false fu.toNat
      (prog ++ fr) (hi.toNat + grp.length)
      (decI us) ds (grp.map (·.1)) holes ctors NS []).run a7 = .ok (x, a8) := by simpa using hrun8
  refine RefE.bind_right e8 (RefE.ret rfl ⟨hpost.stage, hg17.trans hpost.grow, by simpa using hpost.ns, hpost.pos,
    hpost.abs, (c1.trans k2.core).trans ((p57.toCore k2.stage.check).trans hpost.core)⟩)

end steps

end L.Ind
