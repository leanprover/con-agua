module

public import ConAgua.Arena.IndT.PosFkc
import ConAgua.Arena.IndPosSpec.FgW
import ConAgua.Arena.IndPosSpec.CfW
public import ConAgua.Verdict.PosE
import ConAgua.Verdict.PosNgc
import ConAgua.Arena.IndPosSpec.Snoc
import all ConRon.Bridge.Inductives.Positivity
import ConAgua.Arena.IndPosSpec.Grow
import ConAgua.Arena.IndRealAbsPos
import ConAgua.Arena.IndRealAbsSim
import ConAgua.Checker.NoVerdictTree
import ConAgua.L.WordOff
import ConAgua.Arena.RefWalk

@[expose] public section

/-!
# `nest_frame` refines `nestFrame`, both outcomes (lane `indstaget`, helper `indstaget-pos`)

`fkcs_ref`: `family_key_checks` refines `familyKeyChecks` (every group mate's family at the key,
typed). `frameRef_step`, on the unified model `nfrE`, its twin side con-ron's `nestFrame_spec`'s: the
group mates' families at the key (`fkcs_ref`), the group's constructors (`ngc_ref`), the frame's holes
(`frameHoles_run`), the constructors walked (the block's `CtorsRef` at `n`).
-/


open ConRon.Arena
open ConRon.Bridge.Inductives (PStep dCtx dProg dState dCtx_ext dProg_ext dState_ext dOut dCtors dGrp kindOf)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section fkcs
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env) {G : Prop}

include hq henv in
/-- **`family_key_checks` refines `familyKeyChecks .verified`, both outcomes** (twin side: con-ron's
`familyKeyChecks_specF`'s proof): each group mate's name read off its record (`GrpAt.head`), its
family at the key (`fkc_ref`), the rest of the group; induction on the fuel. -/
@[refines ConRon.Arena.familyKeyChecks]
theorem fkcs_ref (hP : FkcProg p) (hIlpf : IlpfF p) (hGnv : G → closedNV p _root_.L.Checker.nvFns = true)
    (hGc : G → CoreStubsE p) (hGw : G → WhnfTopE p) (d us dO dL : Word) (ds : List EIdx)
    (usP : List ConLeche.Level) (dsP : List ConLeche.Expr) (hlH : H us)
    (hwds : ∀ x ∈ dsP, ConLeche.Expr.WScoped d.toNat x) (k : Nat) (hk62 : k ≤ 2 ^ 62) :
    ∀ (m : Mem) (a : AState) (gO gL : Word) (grp : List (NIdx × EIdx))
      (grpP : List (ConLeche.Name × ConLeche.Expr)),
    StageC dn vis fe env m a → AbsOK m →
    decHL m dO.toNat dL.toNat = some ds → dO.toNat + dL.toNat ≤ iwTop m →
    gL.toNat = grp.length → gO.toNat + grp.length ≤ iwTop m → GrpAt m gO.toNat grp →
    ConRon.Bridge.Inductives.dGrp a.store grp = some grpP →
    denoteLs a.store.lss (decI us) = some usP → Frontend.denoteEList a.store ds = some dsP →
    RefE G (fkcsE p k m vis d us dO dL gO gL)
      (ConRon.Arena.familyKeyChecks V fe d.toNat (decI us) ds (grp.map (·.1))) a
      (fun v _ a' => InsAt dn vis fe env m a v.2 a' ∧ (PosMR m → PosMR v.2)) := by
  induction k with
  | zero => intros; rw [fkcsE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  | succ k ih =>
  intro m a gO gL grp grpP hC hA hds hdsb hgl hgb hgrp hgrpP husP hdsP
  have hS := hC.stage
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.iw.iw hS.iw.iwSize
  cases grp with
  | nil =>
    have hl0 : gL = 0 := UInt64.toNat_inj.mp (by simpa using hgl)
    rw [fkcsE.arm1 p k m vis d us dO dL gO gL hl0]
    exact RefE.ret rfl ⟨InsAt.refl hC hA, id⟩
  | cons x grp =>
  have hl0 : gL ≠ 0 := fun h => by subst h; simp at hgl
  simp only [List.length_cons] at hgl hgb
  rw [fkcsE.arm2 p k m vis d us dO dL gO gL hl0]
  obtain ⟨w, cw, tw, hrw, -, hrc, hcH, hcd, -, -, -⟩ := hgrp.head (by omega) htop
  rw [UInt64.ofNat_toNat] at hrw
  rw [hrw, hrc]
  -- the head's denotation, the rest's
  simp only [ConRon.Bridge.Inductives.dGrp, List.mapM_cons, Option.bind_eq_bind, Option.pure_def] at hgrpP
  rcases hx : ConRon.Bridge.Inductives.dGE a.store x with _ | y; · rw [hx] at hgrpP; simp at hgrpP
  rcases hxs : grp.mapM (ConRon.Bridge.Inductives.dGE a.store) with _ | ys; · rw [hx, hxs] at hgrpP; simp at hgrpP
  simp only [ConRon.Bridge.Inductives.dGE, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hx
  obtain ⟨cP, hcP, -⟩ := hx
  simp only [List.map_cons, ConRon.Arena.familyKeyChecks]
  -- the head's family at the key
  have hR1 := fkc_ref hq henv hP hIlpf hGnv hGc hGw d k (by omega) hC hA hcH hlH hds (.inr hdsb)
    (by rw [hcd]; exact hcP) husP hdsP hwds
  rw [hcd] at hR1
  refine RefE.bindRun (s₀ := ⟨m, Locals.init []⟩) (fun _ => fkcsE.k_family_key_check.none ..)
    (fkcE_spec p hP k _ vis d cw us dO dL) hGnv id hR1 fun r1 s1 _ a1 _ _ _ ⟨k1, hP1⟩ => ?_
  rw [fkcsE.k_family_key_check.arm1]
  dsimp only at k1 hP1
  -- the rest of the group
  have e1 : (gO + 1).toNat = gO.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have e2 : (gL - 1).toNat = grp.length := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
  have hR2 := ih (by omega) s1.mem a1 (gO + 1) (gL - 1) grp ys k1.stage k1.abs (k1.decHL hds hdsb)
    (k1.top hdsb) e2 (by rw [e1]; exact k1.top (by omega))
    (by rw [e1]; exact hgrp.tail.grow (by omega) k1.grow)
    (ConRon.Bridge.Inductives.dGrp_ext k1.core.ext _ _ hxs)
    (ConRon.Bridge.denoteLs_ext husP k1.core.ext) (ConRon.Bridge.denoteEList_ext k1.core.ext _ _ hdsP)
  exact RefE.lastE (K := fkcsE.k_family_key_checks p) (f := fun v => (0, v.2)) (fun _ => rfl) (fun _ => rfl) id hR2
    fun v _ a2 _ ⟨k2, hP2⟩ => ⟨k1.trans k2, fun hPm => hP2 (hP1 hPm)⟩

end fkcs

section steps
variable {p : Prog} (hq : KnotStageProg p) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
  {env : ConLeche.Env} (henv : ConLeche.EnvWF env)

include hq henv in
/-- **`nest_frame` refines `nestFrame`, both outcomes**, at L fuel `n + 1`: every group mate's family
at the key typed (`fkcs_ref`), the frame's stack entries (`fgW_ok`), the group's constructors
(`ngc_ref`), the holes, the constructors walked (the block's `CtorsRef` at `n`). -/
theorem frameRef_step (L : NbLook p) (hFk : FkcProg p) (hIlpf : IlpfF p) (n : Nat) (hn : n ≤ 2 ^ 62)
    (ih : NbRef p dn vis fe env n) : FrameRef p dn vis fe env (n + 1) := by
  have R := L.ct.cr.rx
  intro m a ctx fu po pl hi us dO dL nPc gO gL ns c prog ds grp NS ctxP progP usP dsP grpP nsP hC hW hhi hus
    hds hdsb hgl hgb hgrp hns hP hA hc hctx hprog husP hdsP hgrpP hnsP hwds hwg
  have hS := hC.stage
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.iw.iw hS.iw.iwSize
  obtain ⟨-, -, hfind, -, -, -⟩ := ConRon.Bridge.Inductives.dCtx_fields hctx
  rw [nfrE.arm1, ConRon.Bridge.Inductives.nestFrame_eq]
  -- every group mate's family at the key, typed
  have hR2 := fkcs_ref hq henv (G := NbG p) hFk hIlpf (fun hG => hG.nv) (fun hG => hG.core) (fun hG => hG.whnf)
    hi us dO dL ds usP dsP hus hwds n hn m a gO gL grp grpP hC hA (hds.get (OMono.decHL _ _)) hdsb hgl hgb hgrp
    hgrpP husP hdsP
  refine RefE.bindRun (s₀ := ⟨m, Locals.init []⟩) (fun _ => rfl) (fkcsE_spec p hFk n _ vis hi us dO dL gO gL)
    (fun hG => hG.nv) id hR2 fun r2 s2 u2 a2 _ _ hrun2 ⟨k2, hP2⟩ => ?_
  dsimp only [nfrE.k_family_key_checks]
  generalize s2.mem = m2 at k2 hP2 ⊢
  have hS2 := k2.stage.stage
  have hA2 := k2.abs
  have hg12 := k2.grow
  have hx02 := k2.core.ext
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
  obtain ⟨fr, hrunF, hS5, hg5, hP5, hN5, hNb5⟩ := fgW_ok dn vis fe hi us dO dL ds hus n m2 m5 a2 gO gL po pl 0 0 grp
    prog [] r5 hfg hS2 (hds.grow (OMono.decHL _ _) hg12) hgl (k2.top hgb) (hgrp.grow hgb hg12)
    (hW.hs.grow hg12) (by simp [decHL, hslice?]) (by simp)
  simp only [List.nil_append] at hN5
  obtain ⟨-, hfrP⟩ := ConRon.Bridge.Inductives.frameEntries_run hi.toNat (fun c ty => rfl) grp grpP a2 a2 fr
    k2.stage.check.state (ConRon.Bridge.denoteLs_ext husP hx02) (ConRon.Bridge.denoteEList_ext hx02 _ _ hdsP)
    (ConRon.Bridge.Inductives.dGrp_ext hx02 _ _ hgrpP) hrunF
  refine RefE.bind_right (x := grp.mapM (frEntryT (decI us) ds hi.toNat)) hrunF ?_
  have hgrp4 := ConRon.Bridge.Inductives.dGrp_ext hx02 _ _ hgrpP
  -- the group's constructors
  have hsp6 := ngcE_spec p L.nt L.nit.hc2 L.hap L.hgc n ⟨m5, Locals.init []⟩ vis nPc
    (r5.tail.tail.headD 0) (r5.tail.tail.tail.headD 0) 0 0
  have hR6 := ngc_ref (p := p) dn fe vis nPc n m5 a2 _ _ 0 0 (grp.map (·.1)) [] hS5 hN5 (fun j hj => by omega)
    (by simp) (by simp) (fun i hi => by simp at hi)
  cases h6 : callE p n "nest_group_ctors" [vis, nPc, r5.tail.tail.headD 0, r5.tail.tail.tail.headD 0, 0, 0] m5 with
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
  obtain ⟨holes, a7, hrun7, hS7, hg7, hH7, hHb7⟩ := fhW_ok dn vis fe n m6 m7 a6 hi gO gL 0 0 grp [] r7 hfh hS6 hgl
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
  rw [nfrE.k_nest_frame_holes.arm1 p n vis ctx fu hi us dO dL gL ns _ _ _ _ _ _ r7 m7 hov hov2]
  have hhg : (hi + gL).toNat = hi.toNat + gL.toNat := _root_.L.toNat_add_of_not_lt hov
  have hdg : (dL + gL).toNat = dL.toNat + gL.toNat := _root_.L.toNat_add_of_not_lt hov2
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
  have hpl2 : (r5.tail.headD 0).toNat = pl.toNat + gL.toNat := by
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
  have hR8 := ih.ctors m7 a7 ctx 0 fu (r5.headD 0) (r5.tail.headD 0) (hi + gL) us dO dL (r5.tail.tail.headD 0)
    (r5.tail.tail.tail.headD 0) (r7.headD 0) (r7.tail.headD 0) (rc.headD 0) (rc.tail.headD 0) ns 0 0 c
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
    (((hP2 hP).fr
      (fgW_mfr _ _ _ _ _ _ _ _ _ _ _ _ _ _ hfg)).fr hM6 |>.fr
      (fhW_mfr _ _ _ _ _ _ _ _ _ hfh)) hA7
    hc (dCtx_ext _ hx07 _ _ hctx) hprog2 hpre (ConRon.Bridge.Inductives.dCtors_ext p6.ext _ _ hvc) hvcl
    (dState_ext hx07 _ _ hnsP) rfl
  rw [hhg, hgl] at hR8
  have hsp8 := nctE_spec p L.pctors n ⟨m7, Locals.init []⟩ vis ctx 0 fu (r5.headD 0) (r5.tail.headD 0) (hi + gL) us
    dO dL (r5.tail.tail.headD 0) (r5.tail.tail.tail.headD 0) (r7.headD 0) (r7.tail.headD 0) (rc.headD 0)
    (rc.tail.headD 0) ns 0 0
  cases h8 : callE p n "nest_ctors" [vis, ctx, 0, fu, r5.headD 0, r5.tail.headD 0, hi + gL, us, dO, dL,
      r5.tail.tail.headD 0, r5.tail.tail.tail.headD 0, r7.headD 0, r7.tail.headD 0, rc.headD 0, rc.tail.headD 0,
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
    hpost.abs, k2.core.trans ((p57.toCore k2.stage.check).trans hpost.core)⟩)

end steps

end L.Ind
