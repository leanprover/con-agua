module

public import ConAgua.Verdict.PosE
import ConAgua.Verdict.PosE2
import ConAgua.Arena.IndPosSpec.Pos2DecHLSplit
import ConAgua.Arena.IndPosSpec.Snoc
import all ConRon.Bridge.Inductives.Positivity
import ConAgua.Arena.IndPosSpec.GgW2
import ConAgua.Arena.IndPosSpec.Grow
import ConAgua.Arena.IndPosSpec.NestAcceptGroup
import ConAgua.Arena.IndPosSpec.NestContParamsClosed
import ConAgua.Arena.IndPosSpec.NestCrest
import ConAgua.Arena.IndPosSpec.Pos2RdGrow
import ConAgua.Arena.IndRealAbsPos
import ConAgua.Arena.IndT.RecGen19
import ConAgua.Checker.NoVerdictTree
public import ConAgua.Arena.IndPosSpec.NbPosW
public import ConAgua.Arena.IndRealIlpL

@[expose] public section

/-!
# `nest_cont_new` refines `nestContNew`, both outcomes (lane `indstaget`, helper `indstaget-pos`)

`newRef_step`, on the model `nnewE`, with the twin side of con-ron's `nestContNew_spec`: the walk
stack (`nestWalkStack_spec`), the group grown (`ngg_ref`), the
frame (the block's `FrameRef` at `n`), the cache (`closedAll_spec`).
-/


open ConRon.Arena
open ConRon.Bridge.Inductives (PStep dCtx dProg dState dCtx_ext dProg_ext dState_ext dGrp kindOf)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- The cache check closing a new frame (`cfT`) is a pure step. -/
theorem cfT_pstep {c : NestCtx} {us : LsIdx} {ds : List EIdx} {grp : List (NIdx × EIdx)} {ns2 : NestState}
    {act : List NestKey} {kb : Nat} {x : NestFieldKind × NestState} {a a' : AState} {dsP : List ConLeche.Expr}
    (h : (cfT c us ds grp ns2 act kb).run a = .ok (x, a')) (hok : ConRon.Bridge.StateOK a)
    (hds : Frontend.denoteEList a.store ds = some dsP) : PStep a a' := by
  have h' : (cfT c us ds grp ns2 act kb) a = .ok (x, a') := h
  simp only [cfT] at h'
  obtain ⟨b, s1, h1, h2⟩ := ConRon.Bridge.AM.bind_ok h'
  obtain ⟨p1, -⟩ := ConRon.Bridge.Inductives.closedAll_spec (c.hiAt 0) ds dsP a s1 b hok hds h1
  obtain ⟨-, rfl⟩ := ConRon.Bridge.AM.pure_ok h2
  exact p1

section steps
variable {p : Prog} (hq : KnotStageProg p) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) {env : ConLeche.Env}

include hq in
/-- **`nest_cont_new` refines `nestContNew`, both outcomes**, at L fuel `n + 1`: the walk stack, the
group grown (`ngg_ref`), the frame (the block's `FrameRef` at `n`), the
cache (`cfW_ok`). -/
theorem newRef_step (L : NbLook p) (hIlpf : IlpfF p) (hLC : LvlCacheProg p) (n : Nat)
    (ih : NbRef p dn vis fe env n) : NewRef p dn vis fe env (n + 1) := by
  have hcl : CoreStageClosed p := hq.closed
  have R := L.ct.cr.rx
  intro m a ctx fu po pl kb nn us dO dL nPc cty ns c prog ds NS ctxP progP nP usP dsP ctyP nsP hC hW hnn hus
    hds hdsb hcty hns hP hA hc hctx hprog hnP husP hdsP hctyP hnsP hwds hni
  have hS := hC.stage
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.iw.iw hS.iw.iwSize
  have hdsD := hds.get (OMono.decHL _ _)
  have hhi0 : c.hiAt 0 < 2 ^ 64 := by have := hW.hb; simp only [NestCtx.hiAt] at this ⊢; omega
  obtain ⟨-, -, hfind, -, -, -⟩ := ConRon.Bridge.Inductives.dCtx_fields hctx
  rw [nnewE.arm1]
  -- the walk stack
  cases h1 : callE p n "nest_walk_stack" [ctx, dO, dL, po, pl] m with
  | error e1 =>
    rw [nnewE.k_nest_walk_stack.none]
    exact fun hG => ErrClaim.of_callE_nv hG.nv (_root_.L.Checker.nv_mem (by decide +kernel)) h1
  | ok q1 =>
  obtain ⟨rw, m1⟩ := q1
  obtain ⟨s1, hs1, -, hws⟩ := triple_of_callW (nestWalkStack_spec' p L n ⟨m, Locals.init []⟩ ctx dO dL po pl)
    (callW_of_callE h1)
  simp only at hws
  rw [hs1] at hws
  rw [nnewE.k_nest_walk_stack.arm1]
  cases n with
  | zero => simp [nwsWf] at hws
  | succ n' =>
  simp only [nwsWf] at hws
  obtain ⟨wp, a1, hrun1, hS1, hg1, hwp⟩ := nwsW_ok dn fe vis n' m m1 a ctx dO dL po pl c ds prog rw hws hS
    hW.u.dec hW.u.inn hhi0 hdsD (fun j hj => by omega)
  have hWp : WCtx dn vis fe m1 ctx (rw.headD 0) (rw.tail.headD 0) c wp := by
    rcases hwp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hW.u.grow hg1, ⟨rfl, by simp, fun i hi => by simp at hi⟩, by simpa using hhi0⟩
    · exact hW.grow hg1
  obtain ⟨p1, hwpE⟩ := ConRon.Bridge.Inductives.nestWalkStack_spec c prog ds dsP a a1 wp hC.check.state hdsP hrun1
  simp only [ConRon.Bridge.Inductives.RV, ConRon.Bridge.Inductives.hiAt_eq hctx] at hwpE
  have hwpP : dProg a.store wp = some (ConLeche.nestWalkStack ctxP progP dsP) := by
    rw [hwpE]; simp only [ConLeche.nestWalkStack]
    split
    · rfl
    · exact hprog
  have hwpl : wp.length = (ConLeche.nestWalkStack ctxP progP dsP).length :=
    ConRon.Bridge.Inductives.dProg_length hwpP
  have hdsw : ∀ d ∈ dsP,
      ConLeche.Expr.WScoped (ctxP.hiAt (ConLeche.nestWalkStack ctxP progP dsP).length) d := by
    unfold ConLeche.nestWalkStack; split
    · rename_i hfree
      intro x hx
      exact ConLeche.WScoped.of_fvarsBelow (hwds x hx)
        (ConLeche.Expr.fvarB_le (by simpa using List.all_eq_true.mp hfree x hx))
    · exact hwds
  have c1 := p1.toCore hC.check
  rw [ConRon.Arena.nestContNew.eq_def]
  refine RefE.bind_right hrun1 ?_
  -- the mates
  cases h2 : callE p (n' + 1) "nest_frame_mates" [vis, nn] m1 with
  | error e2 =>
    rw [nnewE.k_nest_frame_mates.none]
    exact fun hG => ErrClaim.of_callE_nv hG.nv (_root_.L.Checker.nv_mem (by decide +kernel)) h2
  | ok q2 =>
  obtain ⟨rm, m2⟩ := q2
  obtain ⟨s2, hs2, -, hfm⟩ := triple_of_callW (nestFrameMates_specW p L.fm (n' + 1) ⟨m1, Locals.init []⟩ vis nn)
    (callW_of_callE h2)
  simp only at hfm
  rw [hs2] at hfm
  rw [nnewE.k_nest_frame_mates.arm1]
  obtain ⟨hS2, hg2, hmd, hmb⟩ := nfmW_ok hfm hS1 hnn
  have htop2 : iwTop m2 < 2 ^ 64 := Nat.lt_of_le_of_lt hS2.iw.iw hS2.iw.iwSize
  have hWp2 := hWp.grow hg2
  have hhw : (nhiW m2 ctx (rw.tail.headD 0)).toNat = c.hiAt wp.length := hWp2.hi htop2
  -- the frame's first free index
  cases h2b : callE p (n' + 1) "nest_ctx_hi_at" [ctx, rw.tail.headD 0] m2 with
  | error e2 =>
    rw [nnewE.k_nest_ctx_hi_at.none]
    exact fun hG => ErrClaim.of_callE_nv hG.nv (_root_.L.Checker.nv_mem (by decide +kernel)) h2b
  | ok q2b =>
  obtain ⟨rh, m2b⟩ := q2b
  obtain ⟨s2b, hs2b, -, hm2b, hrh⟩ := triple_of_callW (nestCtxHiAt_specE p R.hi (n' + 1) ⟨m2, Locals.init []⟩ ctx
    (rw.tail.headD 0)) (callW_of_callE h2b)
  simp only at hm2b hrh
  rw [hs2b] at hm2b
  subst hm2b
  rw [nnewE.k_nest_ctx_hi_at.arm1, hrh]
  -- the group, from the instantiation met
  cases h3 : callE p (n' + 1) "rec2" [nn, cty] m2b with
  | error e3 =>
    rw [nnewE.k_rec2.none]
    exact fun hG => ErrClaim.of_callE_nv hG.nv (_root_.L.Checker.nv_mem (by decide +kernel)) h3
  | ok q3 =>
  obtain ⟨rp3, m3⟩ := q3
  obtain ⟨s3, hs3, -, hpr⟩ := triple_of_callW (posRec2_specW p R.ha R.h2 (n' + 1) ⟨m2b, Locals.init []⟩ nn cty)
    (callW_of_callE h3)
  simp only at hpr
  rw [hs3] at hpr
  rw [nnewE.k_rec2.arm1]
  generalize hpw : rp3.headD 0 = pw at hpr ⊢
  obtain ⟨hS3, hg3, hpq, ht3, hget3⟩ := posRecW_stage hpr hS2 (by simp)
  simp only [List.length_cons, List.length_nil] at ht3
  cases h4 : callE p (n' + 1) "sl_new1" [pw] m3 with
  | error e4 =>
    rw [nnewE.k_sl_new1.none]
    exact fun hG => ErrClaim.of_callE_nv hG.nv (_root_.L.Checker.nv_mem (by decide +kernel)) h4
  | ok q4 =>
  obtain ⟨g0, m4⟩ := q4
  obtain ⟨s4, hs4, -, hn1⟩ := triple_of_callW (slNew1_specW p R.ha L.hn1 (n' + 1) ⟨m3, Locals.init []⟩ pw)
    (callW_of_callE h4)
  simp only at hn1
  rw [hs4] at hn1
  rw [nnewE.k_sl_new1.arm1]
  obtain ⟨hn1r, hg0⟩ := new1W_rec hn1
  obtain ⟨hS4, hg4, hg0q, ht4, hget4⟩ := posRecW_stage hn1r hS3 (by simp)
  simp only [List.length_cons, List.length_nil] at ht4
  have hgrp0 : GrpAt m4 (g0.headD 0).toNat [(decI nn, decI cty)] := by
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    have hi0 : i = 0 := by omega
    subst hi0
    have e0 := hget3 0 (by simp); have e1 := hget3 1 (by simp)
    simp only [Nat.add_zero, List.getElem?_cons_zero, List.getElem?_cons_succ] at e0 e1
    refine ⟨pw, nn, cty, by simpa using hget4 0 (by simp), by omega,
      by rw [hg4.iwGet _ (by omega)]; exact e0, hnn, rfl, by rw [hg4.iwGet _ (by omega)]; exact e1, hcty, rfl⟩
  have hg1t : g0.tail.headD 0 = 1 := by rw [hg0]; rfl
  rw [hg1t]
  have hg24 := hg3.trans hg4
  have hmates := ConRon.Bridge.Inductives.nestFrameMates_rel c1.ok.state c1.ok.ienv ctxP hfind
    (ConRon.Bridge.denoteN_ext hnP p1.ext)
  have hA4 : AbsOK m4 := new1W_afr hn1 (posRecW_afr hpr (nfmW_afr hfm (nwsW_afr hws hA)))
  have hC4 : StageC dn vis fe env m4 a1 := hC.of_pstep hS4 hA4 p1
  have hg14 := hg1.trans (hg2.trans hg24)
  have hP4 : PosMR m4 := ((((hP.fr (nwsW_mfr hws)).fr (nfmW_mfr hfm)).fr (posRecW_mfr hpr)).fr (new1W_mfr hn1))
  have hctx1 : dCtx a1.store env.find? c = some ctxP := dCtx_ext _ p1.ext _ _ hctx
  have hmdD : decHL m4 (rm.headD 0).toNat (rm.tail.headD 0).toNat = some (nestFrameMates fe (decI nn)) := by
    rw [decHL_agree (RdS.of_grow hg24) (fun j hj => by omega)]; exact hmd
  have hdsD4 : decHL m4 dO.toNat dL.toNat = some ds := by
    rw [decHL_agree (RdS.of_grow hg14) (fun j hj => by omega)]; exact hdsD
  have hR5 := ngg_ref L hIlpf hcl hLC dn vis fe ctx _ us dO dL (c.hiAt wp.length) hhw c ds hus a1
    (nestFrameMates fe (decI nn)) hc hctx1 (ConRon.Bridge.denoteLs_ext husP p1.ext)
    (ConRon.Bridge.denoteEList_ext p1.ext _ _ hdsP) hmates (n' + 1) m4 a1 _ _ _ 1
    (nestFrameMates fe (decI nn)) [(decI nn, decI cty)] hC4 hA4 (ConRon.Arena.Ext.refl _) (fun _ h => h)
    (hW.u.grow hg14) hdsD4 (by have := hg14.iw; omega) hmdD (fun j hj => by have := hg24.iw; omega) (by simp)
    (by simp only [List.length_cons, List.length_nil]; omega) hgrp0 hP4
  have hsg := nggE_spec p L.nit R.h2 R.h4 L.nag.hsn L.hgg (n' + 1) ⟨m4, Locals.init []⟩ vis ctx
    (nhiW m2b ctx (rw.tail.headD 0)) us dO dL (rm.headD 0) (rm.tail.headD 0) (g0.headD 0) 1
  cases h5 : callE p (n' + 1) "nest_grow_group" [vis, ctx, nhiW m2b ctx (rw.tail.headD 0), us, dO, dL, rm.headD 0,
      rm.tail.headD 0, g0.headD 0, 1] m4 with
  | error e5 =>
    rw [nnewE.k_nest_grow_group.none]
    exact RefE.bind_left fun hG => RefE.run_err hsg hG.nv hG.nv hR5 h5
  | ok q5 =>
  obtain ⟨rg, m5⟩ := q5
  rw [nnewE.k_nest_grow_group.arm1]
  obtain ⟨s5, hm5, -, grp, a5, hrun5, hR⟩ := RefE.run_ok hsg hR5 h5
  dsimp only at hR; rw [hm5] at hR
  obtain ⟨hC5, hg5, hgl5, hgb5, hgrp5, hP5, hA5, -⟩ := hR
  have hS5 := hC5.stage
  obtain ⟨c2, grpV, ⟨hgrp, hgs⟩, -⟩ := ConRon.Bridge.Inductives.nestGrowGroup_spec hc c (c.hiAt wp.length) (decI us)
    usP ds dsP _ _ [(decI nn, decI cty)] [(nP, ctyP)]
    (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact hni)
    a1 a5 grp c1.ok ⟨dCtx_ext _ p1.ext _ _ hctx, ConRon.Bridge.denoteLs_ext husP p1.ext,
      ConRon.Bridge.denoteEList_ext p1.ext _ _ hdsP, hmates,
      by simp [dGrp, ConRon.Bridge.Inductives.dGE, ConRon.Bridge.denoteN_ext hnP p1.ext,
        ConRon.Bridge.denote_ext hctyP p1.ext]⟩ hrun5
  have hx05 := p1.ext.trans c2.ext
  have c12 := c1.trans c2
  obtain ⟨hk1, hk2, hk3⟩ := ConRon.Bridge.Inductives.dState_inv (dState_ext hx05 _ _ hnsP)
  have hg15 := hg14.trans hg5
  have htop5 : iwTop m5 < 2 ^ 64 := Nat.lt_of_le_of_lt hS5.iw.iw hS5.iw.iwSize
  refine RefE.bind_right hrun5 ?_
  -- its keys, then the active list
  cases h6 : callE p (n' + 1) "nest_cont_new_active" [us, dO, dL, rg.headD 0, rg.tail.headD 0, 0, 0] m5 with
  | error e6 =>
    rw [nnewE.k_nest_cont_new_active.none]
    exact fun hG => ErrClaim.of_callE_nv hG.nv (_root_.L.Checker.nv_mem (by decide +kernel)) h6
  | ok q6 =>
  obtain ⟨ra6, m6⟩ := q6
  obtain ⟨s6, hs6, -, hca⟩ := triple_of_callW (nestContNewActive_spec p R.ha L.nit.hc2 R.h4 L.nag.hsn L.hca (n' + 1)
    ⟨m5, Locals.init []⟩ us dO dL _ _ 0 0) (callW_of_callE h6)
  simp only at hca
  rw [hs6] at hca
  rw [nnewE.k_nest_cont_new_active.arm1]
  generalize hra : [ra6.headD 0, ra6.tail.headD 0] = ra at hca
  have u0 : ra6.headD 0 = ra.headD 0 := by rw [← hra]; rfl
  have u1 : ra6.tail.headD 0 = ra.tail.headD 0 := by rw [← hra]; rfl
  rw [u0, u1]
  obtain ⟨hS6, hg6, hka, hkab⟩ := caW_ok dn vis fe us dO dL ds hus (n' + 1) m5 m6 a5 _ _ 0 0 grp [] ra hca hS5
    (hds.grow (OMono.decHL _ _) hg15) (by simpa using hgl5) hgb5 hgrp5 (KsB.nil _ _) (by simp)
  simp only [List.nil_append] at hka
  obtain ⟨hp6, hk0', ha0, hn0⟩ := nsb_words hns htop
  have hg16 := hg15.trans hg6
  rw [pos2_ns_rd hg16 hp6 htop 2 (by decide), pos2_ns_rd hg16 hp6 htop 3 (by decide)]
  cases h7 : callE p (n' + 1) "sl_append" [ra.headD 0, ra.tail.headD 0, rdW (m.arr64 IW) (ns + 2),
      rdW (m.arr64 IW) (ns + 3)] m6 with
  | error e7 =>
    rw [nnewE.k_sl_append.none]
    exact fun hG => ErrClaim.of_callE_nv hG.nv (_root_.L.Checker.nv_mem (by decide +kernel)) h7
  | ok q7 =>
  obtain ⟨rap7, m7⟩ := q7
  obtain ⟨s7, hs7, -, hap⟩ := triple_of_callW (slAppend_specW p R.ha L.nit.hc2 L.hap (n' + 1) ⟨m6, Locals.init []⟩
    _ _ _ _) (callW_of_callE h7)
  simp only at hap
  rw [hs7] at hap
  rw [nnewE.k_sl_append.arm1]
  generalize hrap : rap7 = rap at hap ⊢
  obtain ⟨hS7, hg7, h70, h71, ht7, hw71, hw72⟩ := appendW_stage hap hS6 hkab
    (by have := hns.b2; have := hg16.iw; omega)
  have hact7 : KsB m7 (rap.headD 0).toNat (rap.tail.headD 0).toNat
      (grp.map (fun x => (⟨x.1, decI us, ds⟩ : NestKey)) ++ NS.active) := by
    rw [h70, h71]
    exact pos2_decB_append decNK_mono hka (ha0.grow hg16) hg7 (by omega) hw71 hw72
  have hg17 := hg16.trans hg7
  rw [pos2_rd_grow hg17 (by omega), pos2_ns_rd hg17 hp6 htop 1 (by decide),
    pos2_ns_rd hg17 hp6 htop 4 (by decide), pos2_ns_rd hg17 hp6 htop 5 (by decide)]
  cases h8 : callE p (n' + 1) "rec6" [rdW (m.arr64 IW) ns, rdW (m.arr64 IW) (ns + 1), rap.headD 0, rap.tail.headD 0,
      rdW (m.arr64 IW) (ns + 4), rdW (m.arr64 IW) (ns + 5)] m7 with
  | error e8 =>
    rw [nnewE.k_rec6.none]
    exact fun hG => ErrClaim.of_callE_nv hG.nv (_root_.L.Checker.nv_mem (by decide +kernel)) h8
  | ok q8 =>
  obtain ⟨rq8, m8⟩ := q8
  obtain ⟨s8, hs8, -, hq1⟩ := triple_of_callW (rec6_specW p R.ha L.h6 (n' + 1) ⟨m7, Locals.init []⟩ _ _ _ _ _ _)
    (callW_of_callE h8)
  simp only at hq1
  rw [hs8] at hq1
  rw [nnewE.k_rec6.arm1]
  generalize hns1 : rq8.headD 0 = ns1 at hq1 ⊢
  obtain ⟨hS8, hg8, hq8, ht8, hget8⟩ := posRecW_stage hq1 hS7 (by simp)
  simp only [List.length_cons, List.length_nil] at ht8
  have hg18 := hg17.trans hg8
  have hns1 := nsb_rec6 (m' := m8) (q := ns1) (keys := NS.keys.toList)
    (act := grp.map (fun x => (⟨x.1, decI us, ds⟩ : NestKey)) ++ NS.active) (nfs := NS.ctorNfs.toList) (by omega)
    (Nat.lt_of_le_of_lt hS8.iw.iw hS8.iw.iwSize) hget8 (hk0'.grow hg18) (by have := hns.b0; have := hg18.iw; omega)
    (hact7.grow hg8) (by have := hg8.iw; omega) (hn0.grow hg18) (by have := hns.b4; have := hg18.iw; omega)
  simp only [Array.toArray_toList] at hns1
  have hA8 : AbsOK m8 := posRecW_afr hq1 (appendW_afr hap (caW_afr _ _ _ _ _ _ _ _ _ _ _ hca hA5))
  have hC8 : StageC dn vis fe env m8 a5 := hC.of_cstep hS8 hA8 c12
  have hg58 := (hg6.trans hg7).trans hg8
  have hhwP : (nhiW m2b ctx (rw.tail.headD 0)).toNat = ctxP.hiAt (ConLeche.nestWalkStack ctxP progP dsP).length := by
    rw [hhw, ConRon.Bridge.Inductives.hiAt_eq hctx, hwpl]
  -- the frame
  have hR9 := ih.frame m8 a5 ctx fu (rw.headD 0) (rw.tail.headD 0) (nhiW m2b ctx (rw.tail.headD 0)) us dO dL nPc
    (rg.headD 0) (rg.tail.headD 0) ns1 c wp ds grp
    _ ctxP _ usP dsP grpV
    ⟨nsP.keys, grpV.map (fun p => (⟨p.1, usP, dsP⟩ : ConLeche.NestKey)) ++ nsP.active, nsP.ctorNfs⟩
    hC8 (hWp2.grow ((hg24.trans hg5).trans hg58)) hhw hus (hds.grow (OMono.decHL _ _) hg18)
    (by have := hg18.iw; omega) (by simpa using hgl5) (by have := hg58.iw; omega) (hgrp5.grow hgb5 hg58) hns1
    (((hP5.fr (caW_mfr _ _ _ _ _ _ _ _ _ _ _ hca)).fr (appendW_mfr hap)).fr (posRecW_mfr hq1)) hA8
    hc (dCtx_ext _ hx05 _ _ hctx) (dProg_ext hx05 _ _ hwpP) (ConRon.Bridge.denoteLs_ext husP hx05)
    (ConRon.Bridge.denoteEList_ext hx05 _ _ hdsP) hgrp
    (ConRon.Bridge.Inductives.dState_mk hk1 (ConRon.Bridge.Inductives.mapM_option_append
      (ConRon.Bridge.Inductives.dKeys_grp (ConRon.Bridge.denoteLs_ext husP hx05)
        (ConRon.Bridge.denoteEList_ext hx05 _ _ hdsP) hgrp) hk2) hk3)
    (by rw [hhwP]; exact hdsw) (fun x hx => by rw [hhwP]; exact hgs x hx _ hdsw)
  rw [hhw] at hR9
  have hsp9 := nfrE_spec p L.pframe (n' + 1) ⟨m8, Locals.init []⟩ vis ctx fu (rw.headD 0) (rw.tail.headD 0)
    (nhiW m2b ctx (rw.tail.headD 0)) us dO dL nPc (rg.headD 0) (rg.tail.headD 0) ns1
  cases h9 : callE p (n' + 1) "nest_frame" [vis, ctx, fu, rw.headD 0, rw.tail.headD 0, nhiW m2b ctx (rw.tail.headD 0),
      us, dO, dL, nPc, rg.headD 0, rg.tail.headD 0, ns1] m8 with
  | error e9 =>
    rw [nnewE.k_nest_frame.none]
    exact RefE.bind_left fun hG => RefE.run_err hsp9 True.intro hG hR9 h9
  | ok q9 =>
  obtain ⟨r9, m9⟩ := q9
  rw [nnewE.k_nest_frame.arm1]
  obtain ⟨s9, hs9, -, x9, a9, hrun9, hpost9⟩ := RefE.run_ok hsp9 hR9 h9
  dsimp only at hpost9
  rw [hs9] at hpost9
  obtain ⟨hC9, hg9, hns9, hP9, hA9, c9⟩ := hpost9
  refine RefE.bind_right hrun9 ?_
  -- the cache
  have hg19 := hg18.trans hg9
  cases h10 : callE p (n' + 1) "nest_cont_new_finish" [ctx, us, dO, dL, rg.headD 0, rg.tail.headD 0, r9.headD 0,
      rdW (m9.arr64 IW) (ns + 2), rdW (m9.arr64 IW) (ns + 3), kb] m9 with
  | error e10 =>
    rw [nnewE.k_nest_cont_new_finish.none]
    exact fun hG => ErrClaim.of_callE_nv hG.nv (_root_.L.Checker.nv_mem (by decide +kernel)) h10
  | ok q10 =>
  obtain ⟨r10, m10⟩ := q10
  obtain ⟨s10, hs10, -, hcf⟩ := triple_of_callW (nestContNewFinish_spec p L.nag L.dc L.h6 L.hcf (n' + 1)
    ⟨m9, Locals.init []⟩ ctx us dO dL _ _ _ _ _ kb) (callW_of_callE h10)
  simp only at hcf
  rw [hs10] at hcf
  rw [nnewE.k_nest_cont_new_finish.arm1]
  rw [pos2_ns_rd hg19 hp6 htop 2 (by decide), pos2_ns_rd hg19 hp6 htop 3 (by decide)] at hcf
  obtain ⟨x, a', hrun10, hS10, hg10, -, hk10, hns10⟩ := cfW_ok dn vis fe hcf hC9.stage (hW.u.grow hg19) hhi0 hus
    (hds.grow (OMono.decHL _ _) hg19) (by have := hg19.iw; omega) (by simpa using hgl5)
    (by have := (hg58.trans hg9).iw; omega) (hgrp5.grow hgb5 (hg58.trans hg9)) hns9 (ha0.grow hg19)
    (by have := hns.b2; have := hg19.iw; omega)
  have p10 := cfT_pstep hrun10 hC9.check.state (ConRon.Bridge.denoteEList_ext (hx05.trans c9.ext) _ _ hdsP)
  have hA10 : AbsOK m10 := cfW_afr hcf hA9
  exact RefE.ret hrun10 ⟨hC9.of_pstep hS10 hA10 p10, hg19.trans hg10, by simpa using hk10, by simpa using hns10,
    hP9.fr (cfW_mfr hcf), hA10, (c12.trans c9).trans (p10.toCore hC9.check)⟩

end steps

end L.Ind
