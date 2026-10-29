import ConAgua.Arena.IndT.PosCrest
import ConAgua.Verdict.PosE
import ConAgua.Verdict.PosNgc
import ConAgua.Arena.IndPosSpec.Pos2DecHLSplit
import ConAgua.Arena.IndPosSpec.Snoc

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

/-- The tail of `nestFrame` after the group's head name (its `do` join point). -/
def nestFrameRest (mode : ConLeche.CheckMode) (fe : IFEnv) (ctx : NestCtx) (fuel : Nat)
    (prog : List NestHole) (hi : Nat) (us : LsIdx) (ds : List EIdx) (nPc : Nat)
    (grp : List (NIdx × EIdx)) (ns : NestState) (hn : NIdx) : AM NestState := do
  let hc ← internConstE hn us
  let app ← mkAppN hc ds
  let _ ← inferTypeCore mode fe checkFuel hi app
  let prog2 := prog ++ grp.map fun (c, _) => { key := ⟨c, us, ds⟩, base := hi }
  let names := grp.map (·.1)
  let ctors ← nestGroupCtors fe nPc names []
  let holes ← grp.zipIdx.mapM fun ((_, ty), i) => internFVarE (hi + i) ty
  let (_, ns2) ← nestCtors mode fe ctx false fuel prog2 (hi + grp.length) us ds names
    holes ctors ns []
  pure ns2

theorem nestFrame_run {mode : ConLeche.CheckMode} {fe : IFEnv} {ctx : NestCtx} {fuel : Nat}
    {prog : List NestHole} {hi : Nat} {us : LsIdx} {ds : List EIdx} {nPc : Nat}
    {grp : List (NIdx × EIdx)} {ns : NestState} {hn : NIdx} {a a1 : AState}
    (h : (nestHeadT grp).run a = .ok (hn, a1)) :
    (ConRon.Arena.nestFrame mode fe ctx fuel prog hi us ds nPc grp ns).run a =
      (nestFrameRest mode fe ctx fuel prog hi us ds nPc grp ns hn).run a1 := by
  rw [ConRon.Arena.nestFrame.eq_def]
  cases grp with
  | nil =>
    simp only [nestHeadT] at h
    simp only [StateT.run_bind, h, except_ok_bind]
    rfl
  | cons x g =>
    obtain ⟨c, ty⟩ := x
    simp only [nestHeadT] at h
    obtain ⟨rfl, rfl⟩ := ConRon.Bridge.AM.pure_ok h
    rfl

section steps
variable {p : Prog} (hq : KnotStageProg p) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
  {env : ConLeche.Env} (henv : ConLeche.EnvWF env)

include hq henv in
/-- **`nest_frame` refines `nestFrame`, both outcomes**, at L fuel `n + 1`: the group's head name, the
instantiation typed (`inferC_rsim`; `infer_type_core`'s claim from `CoreStubsE`), the group's
constructors (`ngc_ref`), the holes, the constructors walked (the block's `CtorsRef` at `n`). -/
theorem frameRef_step (L : NbLook p) (n : Nat) (hn : n ≤ 2 ^ 62) (ih : NbRef p dn vis fe env n) :
    FrameRef p dn vis fe env (n + 1) := by
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
        some (rn, m1) ∧ StageR dn vis fe m1 a1 ∧ IWGrow m m1 ∧ MFr [] [] m m1 ∧ AFr m m1 ∧ H (rn.headD 0) ∧
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
  refine RefE.of_run_eq (nestFrame_run hrun1) ?_
  unfold nestFrameRest
  -- the instantiation `hn.{us} ds`, typed
  cases h2 : callE p n "intern_const" [rn.headD 0, us] m1 with
  | error e2 =>
    rw [nfrE.k_intern_const.none]
    exact fun hG => ErrClaim.of_callE_nv hG.nv (_root_.L.Checker.nv_mem (by decide +kernel)) h2
  | ok q2 =>
  obtain ⟨rc2, m2⟩ := q2
  obtain ⟨s2, hs2, -, hic⟩ := triple_of_callW (internConst_spec p R.cf R.cp R.ci n ⟨m1, Locals.init []⟩ _ _)
    (callW_of_callE h2)
  simp only at hic
  rw [hs2] at hic
  by_cases hcb : 4294967296 ≤ rc2.headD 0
  · rw [nfrE.k_intern_const.abort1 p n vis ctx fu po pl hi us dO dL nPc gO gL ns rc2 m2 hcb]
    exact RefE.of_cls0 rfl
  rw [nfrE.k_intern_const.arm1 p n vis ctx fu po pl hi us dO dL nPc gO gL ns rc2 m2 hcb]
  generalize hhc : rc2.headD 0 = hc' at hic hcb ⊢
  have hcH : H hc' := by
    have : ¬ (4294967296 : Word).toNat ≤ hc'.toNat := fun e => hcb (UInt64.le_iff_toNat_le.mpr e)
    simp only [H]; simpa using this
  obtain ⟨a2, hrun2, hS2, hg2⟩ := internConst_stage hS1 (rn.headD 0) us hrnH hus hic
  have e2 : (internConstE (decI (rn.headD 0)) (decI us)).run a1 = .ok (decI hc', a2) := hrun2
  obtain ⟨p2, hc2⟩ := ConRon.Bridge.Inductives.internConstE_run p1.ok hhn'
    (ConRon.Bridge.denoteLs_ext husP p1.ext) e2
  have hA2 : AbsOK m2 := ceinternW_afr hic hA1
  have hg12 := hg1.trans hg2
  refine RefE.bind_right e2 ?_
  cases h3 : callE p n "mk_app_n_f" [hc', dO, dL] m2 with
  | error e3 =>
    rw [nfrE.k_mk_app_n_f.none]
    exact fun hG => ErrClaim.of_callE_nv hG.nv (_root_.L.Checker.nv_mem (by decide +kernel)) h3
  | ok q3 =>
  obtain ⟨ra, m3⟩ := q3
  obtain ⟨s3, hs3, -, hma⟩ := triple_of_callW (mknF_spec p L.nt.ad n ⟨m2, Locals.init []⟩ _) (callW_of_callE h3)
  simp only at hma
  rw [hs3] at hma
  rw [nfrE.k_mk_app_n_f.arm1]
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
  refine RefE.bind_right hrun3 ?_
  cases h4 : callE p n "infer_type_core" [vis, hi, ra.headD 0] m3 with
  | error e4 =>
    rw [nfrE.k_infer_type_core.none]
    refine RefE.bind_left fun hG => ?_
    rw [← happd]
    exact hG.core.inferTypeCore n hn hC3.stageT hi (ra.headD 0) happH _ h4
  | ok q4 =>
  obtain ⟨rt, m4⟩ := q4
  have hit : realCall p n "infer_type_core" [vis, hi, ra.headD 0] m3 = some (rt, m4) := callW_of_callE h4
  rw [nfrE.k_infer_type_core.arm1]
  obtain ⟨ty, a4, hrun4, hC4, hg4, -, hA4, c4, -⟩ :=
    inferC_rsim hq henv n hn hC3 hA3 hi (ra.headD 0) happH (by rw [happd]; exact happ) hwapp _ hit
  dsimp only at hC4 hg4 hA4
  have hS4 := hC4.stage
  have hg14 := (hg12.trans hg3).trans hg4
  have c3 := p13.toCore hC.check
  rw [happd] at hrun4
  refine RefE.bind_right hrun4 ?_
  -- the stack grown and the names
  cases h5 : callE p n "nest_frame_grp" [hi, us, dO, dL, gO, gL, po, pl, 0, 0] m4 with
  | error e5 =>
    rw [nfrE.k_nest_frame_grp.none]
    exact fun hG => ErrClaim.of_callE_nv hG.nv (_root_.L.Checker.nv_mem (by decide +kernel)) h5
  | ok q5 =>
  obtain ⟨r5, m5⟩ := q5
  obtain ⟨s5, hs5, -, hfg⟩ := triple_of_callW (nestFrameGrp_spec p R.ha L.nit.hc2 R.h2 R.h4 L.nag.hsn L.hfg n
    ⟨m4, Locals.init []⟩ hi us dO dL gO gL po pl 0 0) (callW_of_callE h5)
  simp only at hfg
  rw [hs5] at hfg
  rw [nfrE.k_nest_frame_grp.arm1]
  generalize hrp : [r5.headD 0, r5.tail.headD 0, r5.tail.tail.headD 0, r5.tail.tail.tail.headD 0] = rp at hfg
  have e0 : r5.headD 0 = rp.headD 0 := by rw [← hrp]; rfl
  have e1 : r5.tail.headD 0 = rp.tail.headD 0 := by rw [← hrp]; rfl
  have e2' : r5.tail.tail.headD 0 = rp.tail.tail.headD 0 := by rw [← hrp]; rfl
  have e3 : r5.tail.tail.tail.headD 0 = rp.tail.tail.tail.headD 0 := by rw [← hrp]; rfl
  rw [e0, e1, e2', e3]
  obtain ⟨hS5, hg5, hP5, hN5, hNb5⟩ := fgW_ok dn vis fe hi us dO dL ds hus n m4 m5 a4 gO gL po pl 0 0 grp prog [] rp
    hfg hS4 (hds.grow (OMono.decHL _ _) hg14) hgl (by have := hg14.1; omega) (hgrp.grow hgb hg14)
    (hW.hs.grow hg14) (by simp [decHL, hslice?]) (by simp)
  simp only [List.nil_append] at hP5 hN5
  have hx04 := c3.ext.trans c4.ext
  have hgrp4 := ConRon.Bridge.Inductives.dGrp_ext hx04 _ _ hgrpP
  -- the group's constructors
  have hsp6 := ngcE_spec p L.nt L.nit.hc2 L.hap L.hgc n ⟨m5, Locals.init []⟩ vis nPc
    (rp.tail.tail.headD 0) (rp.tail.tail.tail.headD 0) 0 0
  have hR6 := ngc_ref (p := p) dn fe vis nPc n m5 a4 _ _ 0 0 (grp.map (·.1)) [] hS5 hN5 (fun j hj => by omega)
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
    a4 a6 ctors hC4.check.state ⟨hC4.check.ienv.toS, ConRon.Bridge.Inductives.dGrp_names hgrp4, rfl⟩ hrun6
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
    (by have := (hg14.trans hg46).iw; omega) (hgrp.grow hgb (hg14.trans hg46)) (by simp [decHL, hslice?]) (by simp)
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
  have hg17 := (hg14.trans hg47)
  have htop7 : iwTop m7 < 2 ^ 64 := Nat.lt_of_le_of_lt hS7.iw.iw hS7.iw.iwSize
  have hA7 : AbsOK m7 := fhW_afr _ _ _ _ _ _ _ _ _ hfh (hA6
    (fgW_afr _ _ _ _ _ _ _ _ _ _ _ _ _ _ hfg hA4))
  have p57 := p5.trans p6
  have hC7 : StageC dn vis fe env m7 a7 := hC4.of_pstep hS7 hA7 p57
  have hx07 := hx04.trans p57.ext
  have hlenG : grp.length = grpP.length := (ConLeche.option_mapM_length hgrpP).symm
  have hP7 := hP5.grow (hg6.trans hg7)
  have hpl2 : (rp.tail.headD 0).toNat = pl.toNat + gL.toNat := by
    rw [← hP7.1, List.length_append, hW.len]; simp [hgl]
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
  -- the constructors walked
  have hR8 := ih.ctors m7 a7 ctx 0 fu (rp.headD 0) (rp.tail.headD 0) (hi + gL) us dO dL (rp.tail.tail.headD 0)
    (rp.tail.tail.tail.headD 0) (rh.headD 0) (rh.tail.headD 0) (rc.headD 0) (rc.tail.headD 0) ns 0 0 c
    (prog ++ grp.map fun x => (⟨⟨x.1, decI us, ds⟩, hi.toNat⟩ : NestHole)) ds (grp.map (·.1)) holes ctors
    NS [] ctxP _ usP dsP (grpP.map (·.1)) (ConLeche.Cached.frameHoles hi.toNat grpP) vc nsP []
    hC7 ⟨hW.u.grow hg17, hP7, by
      have := hW.hb; rw [hW.len] at hhi; simp only [NestCtx.hiAt] at this hhi ⊢; rw [hpl2]
      have := (hi + gL).toNat_lt; omega⟩
    ⟨hus, hds.grow (OMono.decHL _ _) hg17, by have := hg17.1; omega,
      by rw [decHL_agree (RdS.of_grow (hg6.trans hg7)) (fun j hj => by omega)]; exact hN5,
      by have := (hg6.trans hg7).iw; omega, by simp only [List.length_map]; rw [← hgl, ← hdg]; exact (dL + gL).toNat_lt,
      hH7, hHb7⟩
    hcl6 (by have := hg7.1; omega) (hcs6.grow hcb6 hg7) (hns.grow hg17 htop) (OutsB.nil _ _) (by simp)
    ((((((hP.fr hf1).fr (ceinternW_mfr hic)).fr (MFr.ofMknF hma)).fr (coreF_mfr hq (by decide) hit)).fr
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
      (prog ++ grp.map fun (c, _) => { key := ⟨c, decI us, ds⟩, base := hi.toNat }) (hi.toNat + grp.length)
      (decI us) ds (grp.map (·.1)) holes ctors NS []).run a7 = .ok (x, a8) := by simpa using hrun8
  refine RefE.bind_right e8 (RefE.ret rfl ⟨hpost.stage, hg17.trans hpost.grow, by simpa using hpost.ns, hpost.pos,
    hpost.abs, (c3.trans c4).trans ((p57.toCore hC4.check).trans hpost.core)⟩)

end steps

end L.Ind
