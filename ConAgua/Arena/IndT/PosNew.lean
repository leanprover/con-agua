import ConAgua.Arena.IndT.PosNit
import ConAgua.Arena.IndT.PosDefs
import ConAgua.Arena.IndT.RecGen19
import ConAgua.Arena.IndPosSpec.Pos2DecHLSplit

/-!
# `nest_cont_new` under `StageC` (lane `indstaget`, helper `indstaget-pos`)

`newOK_step`'s proof (`IndPos2SpecS`) with the twin side of con-ron's `nestContNew_spec`: the walk
stack (`nestWalkStack_spec`), the group grown (`nestGrowGroup_spec`), the frame (the block's
`FrameOKC` at `n`), the cache (`closedAll_spec`).
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

/-- A member of a denoted name list denotes. -/
theorem denoteNList_memN : ∀ {st : NStore} {l : List NIdx} {L : List ConLeche.Name},
    Frontend.denoteNList st l = some L → ∀ n ∈ l, ∃ x, denoteN st n = some x
  | _, [], _, _, _, hn => absurd hn List.not_mem_nil
  | _, _ :: _, _, h, n, hn => by
    obtain ⟨l, L', h1, h2, -⟩ := ConRon.Bridge.denoteNList_cons_inv h
    rcases List.mem_cons.mp hn with rfl | hn
    · exact ⟨l, h1⟩
    · exact denoteNList_memN h2 n hn

section steps
variable (p : Prog) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) {env : ConLeche.Env}

theorem newOKC_step (hIlpf : IlpfF p) (hcl : CoreStageClosed p) (hLC : LvlCacheProg p) (n : Nat) (ih : NbOKC p dn vis fe env n) : NewOKC p dn vis fe env (n + 1) := by
  obtain ⟨-, -, -, -, -, -, hFrame, -, -, -, -⟩ := ih
  intro m m' a ctx fu po pl kb nn us dO dL nPc cty ns c prog ds NS r ctxP progP nP usP dsP ctyP nsP h hC hW hnn hus
    hds hdsb hcty hns hP hA hc hctx hprog hnP husP hdsP hctyP hnsP hwds hni
  have hS := hC.stage
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  have hdsD := hds.get (OMono.decHL _ _)
  have hhi0 : c.hiAt 0 < 2 ^ 64 := by have := hW.hb; simp only [NestCtx.hiAt] at this ⊢; omega
  obtain ⟨-, -, hfind, -, -, -⟩ := ConRon.Bridge.Inductives.dCtx_fields hctx
  rw [nbNewW_succ] at h
  -- the walk stack
  cases n with
  | zero => simp [nwsWf, nbNewK1] at h
  | succ n' =>
  simp only [nwsWf] at h
  rcases hws : nwsW n' m ctx dO dL po pl with _ | ⟨rw, m1⟩ <;> rw [hws] at h; · simp [nbNewK1] at h
  rw [nbNewK1_some] at h
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
  -- the mates
  rcases hfm : nfmW (n' + 1) m1 vis nn with _ | ⟨rm, m2⟩ <;> rw [hfm] at h; · simp [nbNewK2] at h
  rw [nbNewK2_some] at h
  obtain ⟨hS2, hg2, hmd, hmb⟩ := nfmW_ok hfm hS1 hnn
  have htop2 : iwTop m2 < 2 ^ 64 := Nat.lt_of_le_of_lt hS2.2.1 hS2.2.2.2.1
  have hWp2 := hWp.grow hg2
  have hhw : (nhiW m2 ctx (rw.tail.headD 0)).toNat = c.hiAt wp.length := hWp2.hi htop2
  -- the group, from the instantiation met
  rcases hpr : posRecW m2 [nn, cty] with _ | ⟨pw, m3⟩ <;> rw [hpr] at h; · simp [nbNewK3] at h
  rw [nbNewK3_some] at h
  obtain ⟨hS3, hg3, hpq, ht3, hget3⟩ := posRecW_stage hpr hS2 (by simp)
  simp only [List.length_cons, List.length_nil] at ht3
  rcases hn1 : new1W m3 pw with _ | ⟨g0, m4⟩ <;> rw [hn1] at h; · simp [nbNewK4] at h
  rw [nbNewK4_some] at h
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
      by rw [hg4.2.2.1 _ (by omega)]; exact e0, hnn, rfl, by rw [hg4.2.2.1 _ (by omega)]; exact e1, hcty, rfl⟩
  rw [hg0] at h
  simp only [List.headD_cons, List.tail_cons] at h
  have hg24 := hg3.trans hg4
  -- grown by the mates
  have hmates := ConRon.Bridge.Inductives.nestFrameMates_rel c1.ok.state c1.ok.ienv ctxP hfind
    (ConRon.Bridge.denoteN_ext hnP p1.ext)
  have hA4 : AbsOK m4 := new1W_afr hn1 (posRecW_afr hpr (nfmW_afr hfm (nwsW_afr hws hA)))
  have hC4 : StageC dn vis fe env m4 a1 := hC.of_pstep hS4 hA4 p1
  rcases hgg : ggW (realCall p) (n' + 1) m4 vis ctx (nhiW m2 ctx (rw.tail.headD 0)) us dO dL (rm.headD 0)
      (rm.tail.headD 0) (g0.headD 0) 1 with _ | ⟨rg, m5⟩; · rw [hgg] at h; simp [nbNewK5] at h
  rw [hgg, nbNewK5_some] at h
  have hg14 := hg1.trans (hg2.trans hg24)
  obtain ⟨grp, a5, hrun5, hS5, hg5, hgl5, hgb5, hgrp5, hP5, hJ5⟩ := ggW_ok dn fe vis ctx (nhiW m2 ctx (rw.tail.headD 0)) us
    dO dL (c.hiAt wp.length) hhw c ds hus (realCall p) (IlpFr.real hIlpf)
    (fun m' a' => StageC dn vis fe env m' a' ∧ AbsOK m' ∧ ConRon.Arena.Ext a1.store a'.store)
    (nestFrameMates fe (decI nn)) (fun _ _ hJ => IlpRd.realC hIlpf hJ.1) (fun m' _ => AbsOK m')
    (fun k' _ a' key n0 hJ hn0 => by
      obtain ⟨hCm, hAm, hxm⟩ := hJ
      obtain ⟨n0P, hn0P⟩ := denoteNList_memN hmates n0 hn0
      have hxa := p1.ext.trans hxm
      exact nitLe_realC hcl hLC k' _ _ key c _ hCm hAm (dCtx_ext _ hxa _ _ hctx)
        (keyP := ⟨n0P, usP, dsP⟩) (by
          simp [ConRon.Bridge.Inductives.dKey, ConRon.Bridge.denoteN_ext hn0P hxm,
            ConRon.Bridge.denoteLs_ext husP hxa, ConRon.Bridge.denoteEList_ext hxa _ _ hdsP]))
    (fun _ _ _ hJ hf hS' => ⟨hJ.1.of_pstep hS' (hJ.2.1.iw hf) (PStep.refl hJ.1.check.state), hJ.2.1.iw hf, hJ.2.2⟩)
    (fun _ _ _ a' a'' _ n0 x _ hJ hn0 _ hrun hS' _ hAm' => by
      obtain ⟨hCm, hAm, hxm⟩ := hJ
      obtain ⟨n0P, hn0P⟩ := denoteNList_memN hmates n0 hn0
      have hxa := p1.ext.trans hxm
      obtain ⟨c4, -⟩ := ConRon.Bridge.Inductives.nestInstType_spec hc c (c.hiAt wp.length) ⟨n0, decI us, ds⟩
        ⟨n0P, usP, dsP⟩ a' a'' x hCm.check
        ⟨dCtx_ext _ hxa _ _ hctx, by
          simp [ConRon.Bridge.Inductives.dKey, ConRon.Bridge.denoteN_ext hn0P hxm,
            ConRon.Bridge.denoteLs_ext husP hxa, ConRon.Bridge.denoteEList_ext hxa _ _ hdsP]⟩ hrun
      exact ⟨hCm.of_cstep hS' hAm' c4, hAm', hxm.trans c4.ext⟩)
    (n' + 1) m4 m5 a1 (rm.headD 0) (rm.tail.headD 0) (g0.headD 0) 1
    (nestFrameMates fe (decI nn)) [(decI nn, decI cty)] rg hgg hS4 ⟨hC4, hA4, ConRon.Arena.Ext.refl _⟩
    (fun _ h => h) (hW.u.grow hg14)
    (by rw [decHL_agree (RdS.of_grow hg14) (fun j hj => by omega)]; exact hdsD) (by have := hg14.1; omega)
    (by rw [decHL_agree (RdS.of_grow hg24) (fun j hj => by omega)]; exact hmd)
    (fun j hj => by have := hg24.1; omega) (by simp) (by simp only [List.length_cons, List.length_nil]; omega) hgrp0
    ((((hP.fr (nwsW_mfr hws)).fr (nfmW_mfr hfm)).fr (posRecW_mfr hpr)).fr (new1W_mfr hn1))
  have hA5 : AbsOK m5 := hJ5.2.1
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
  have htop5 : iwTop m5 < 2 ^ 64 := Nat.lt_of_le_of_lt hS5.2.1 hS5.2.2.2.1
  -- its keys, then the active list
  rcases hca : caW (n' + 1) m5 us dO dL (rg.headD 0) (rg.tail.headD 0) 0 0 with _ | ⟨ra, m6⟩ <;> rw [hca] at h; · simp [nbNewK6] at h
  rw [nbNewK6_some] at h
  obtain ⟨hS6, hg6, hka, hkab⟩ := caW_ok dn vis fe us dO dL ds hus (n' + 1) m5 m6 a5 _ _ 0 0 grp [] ra hca hS5
    (hds.grow (OMono.decHL _ _) hg15) (by simpa using hgl5) hgb5 hgrp5 (KsB.nil _ _) (by simp)
  simp only [List.nil_append] at hka
  obtain ⟨hp6, hk0, ha0, hn0⟩ := nsb_words hns htop
  have hg16 := hg15.trans hg6
  rw [pos2_ns_rd hg16 hp6 htop 2 (by decide), pos2_ns_rd hg16 hp6 htop 3 (by decide)] at h
  rcases hap : appendW (n' + 1) m6 (ra.headD 0) (ra.tail.headD 0) (rdW (m.arr64 IW) (ns + 2))
      (rdW (m.arr64 IW) (ns + 3)) with _ | ⟨rap, m7⟩; · rw [hap] at h; simp [nbNewK7] at h
  rw [hap, nbNewK7_some] at h
  obtain ⟨hS7, hg7, h70, h71, ht7, hw71, hw72⟩ := appendW_stage hap hS6 hkab
    (by have := hns.b2; have := hg16.1; omega)
  have hact7 : KsB m7 (rap.headD 0).toNat (rap.tail.headD 0).toNat
      (grp.map (fun x => (⟨x.1, decI us, ds⟩ : NestKey)) ++ NS.active) := by
    rw [h70, h71]
    exact pos2_decB_append decNK_mono hka (ha0.grow hg16) hg7 (by omega) hw71 hw72
  have hg17 := hg16.trans hg7
  rw [pos2_rd_grow hg17 (by omega), pos2_ns_rd hg17 hp6 htop 1 (by decide), pos2_ns_rd hg17 hp6 htop 4 (by decide),
    pos2_ns_rd hg17 hp6 htop 5 (by decide)] at h
  rcases hq1 : posRecW m7 [rdW (m.arr64 IW) ns, rdW (m.arr64 IW) (ns + 1), rap.headD 0, rap.tail.headD 0,
      rdW (m.arr64 IW) (ns + 4), rdW (m.arr64 IW) (ns + 5)] with _ | ⟨ns1, m8⟩; · rw [hq1] at h; simp [nbNewK8] at h
  rw [hq1, nbNewK8_some] at h
  obtain ⟨hS8, hg8, hq8, ht8, hget8⟩ := posRecW_stage hq1 hS7 (by simp)
  simp only [List.length_cons, List.length_nil] at ht8
  have hg18 := hg17.trans hg8
  have hns1 := nsb_rec6 (m' := m8) (q := ns1) (keys := NS.keys.toList)
    (act := grp.map (fun x => (⟨x.1, decI us, ds⟩ : NestKey)) ++ NS.active) (nfs := NS.ctorNfs.toList) (by omega)
    (Nat.lt_of_le_of_lt hS8.2.1 hS8.2.2.2.1) hget8 (hk0.grow hg18) (by have := hns.b0; have := hg18.1; omega)
    (hact7.grow hg8) (by have := hg8.1; omega) (hn0.grow hg18) (by have := hns.b4; have := hg18.1; omega)
  simp only [Array.toArray_toList] at hns1
  have hA8 : AbsOK m8 := posRecW_afr hq1 (appendW_afr hap (caW_afr _ _ _ _ _ _ _ _ _ _ _ hca hA5))
  have hC8 : StageC dn vis fe env m8 a5 := hC.of_cstep hS8 hA8 c12
  -- the frame
  rcases hfr : nbFrameW (realCall p) (n' + 1) m8 vis ctx fu (rw.headD 0) (rw.tail.headD 0) (nhiW m2 ctx (rw.tail.headD 0))
      us dO dL nPc (rg.headD 0) (rg.tail.headD 0) ns1 with _ | ⟨r9, m9⟩; · rw [hfr] at h; simp [nbNewK9] at h
  rw [hfr, nbNewK9_some] at h
  have hg58 := (hg6.trans hg7).trans hg8
  have hhwP : (nhiW m2 ctx (rw.tail.headD 0)).toNat = ctxP.hiAt (ConLeche.nestWalkStack ctxP progP dsP).length := by
    rw [hhw, ConRon.Bridge.Inductives.hiAt_eq hctx, hwpl]
  obtain ⟨x9, a9, hrun9, hC9, hg9, hns9, hP9, hA9, c9⟩ := hFrame m8 m9 a5 ctx fu _ _ _ us dO dL nPc _ _ ns1 c wp ds grp
    _ r9 ctxP _ usP dsP grpV
    ⟨nsP.keys, grpV.map (fun p => (⟨p.1, usP, dsP⟩ : ConLeche.NestKey)) ++ nsP.active, nsP.ctorNfs⟩ hfr
    hC8 (hWp2.grow ((hg24.trans hg5).trans hg58)) hhw hus (hds.grow (OMono.decHL _ _) hg18)
    (by have := hg18.1; omega) (by simpa using hgl5) (by have := hg58.1; omega) (hgrp5.grow hgb5 hg58) hns1
    (((hP5.fr (caW_mfr _ _ _ _ _ _ _ _ _ _ _ hca)).fr (appendW_mfr hap)).fr (posRecW_mfr hq1)) hA8
    hc (dCtx_ext _ hx05 _ _ hctx) (dProg_ext hx05 _ _ hwpP) (ConRon.Bridge.denoteLs_ext husP hx05)
    (ConRon.Bridge.denoteEList_ext hx05 _ _ hdsP) hgrp
    (ConRon.Bridge.Inductives.dState_mk hk1 (ConRon.Bridge.Inductives.mapM_option_append
      (ConRon.Bridge.Inductives.dKeys_grp (ConRon.Bridge.denoteLs_ext husP hx05)
        (ConRon.Bridge.denoteEList_ext hx05 _ _ hdsP) hgrp) hk2) hk3)
    (by rw [hhwP]; exact hdsw) (fun x hx => by rw [hhwP]; exact hgs x hx _ hdsw)
  have hg19 := hg18.trans hg9
  rw [pos2_ns_rd hg19 hp6 htop 2 (by decide), pos2_ns_rd hg19 hp6 htop 3 (by decide)] at h
  rcases hcf : cfW (n' + 1) m9 ctx us dO dL (rg.headD 0) (rg.tail.headD 0) (r9.headD 0) (rdW (m.arr64 IW) (ns + 2))
      (rdW (m.arr64 IW) (ns + 3)) kb with _ | ⟨r10, m10⟩; · rw [hcf] at h; simp [nbAppK6] at h
  rw [hcf, nbAppK6_some] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨x, a', hrun10, hS10, hg10, -, hk10, hns10⟩ := cfW_ok dn vis fe hcf hC9.stage (hW.u.grow hg19) hhi0 hus
    (hds.grow (OMono.decHL _ _) hg19) (by have := hg19.1; omega) (by simpa using hgl5)
    (by have := (hg58.trans hg9).1; omega) (hgrp5.grow hgb5 (hg58.trans hg9)) hns9 (ha0.grow hg19)
    (by have := hns.b2; have := hg19.1; omega)
  have p10 := cfT_pstep hrun10 hC9.check.state (ConRon.Bridge.denoteEList_ext (hx05.trans c9.ext) _ _ hdsP)
  have hA10 : AbsOK m10 := cfW_afr hcf hA9
  refine ⟨x, a', ?_, hC9.of_pstep hS10 hA10 p10, hg19.trans hg10, by simpa using hk10, by simpa using hns10,
    hP9.fr (cfW_mfr hcf), hA10, (c12.trans c9).trans (p10.toCore hC9.check)⟩
  rw [hhw] at hrun9
  simp only [ConRon.Arena.nestContNew.eq_def, StateT.run_bind, hrun1, except_ok_bind, hrun5, hrun9]
  exact hrun10

end steps

end L.Ind
