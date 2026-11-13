module

import ConAgua.Arena.IndPosSpec.FgW
public import ConAgua.Verdict.PosE
import ConAgua.Arena.IndRealAbsPos
import ConAgua.Arena.IndPosSpec.Snoc
import ConAgua.Arena.IndPosSpec.GgW
import ConAgua.Arena.IndPosSpec.SnocWMfr
import ConAgua.Arena.RecClassSpec.CloseLams
import ConAgua.Checker.NoVerdictTree
import ConAgua.Arena.IndPosSpec.CfW
import ConAgua.L.WordOff

@[expose] public section

/-!
# `nest_ctors` refines `nestCtors`, both outcomes

`ctorsRef_step` walks the unified model `nctE` (`Verdict/PosE3Cm`) against con-ron's `nestCtors`:
one constructor (the block's `OneRef` at `n` on `oneT`, `oneK_split`; its out record and state
denoting), the record appended (L only, `rec3` and `sl_snoc` outside the verdict closure), the
rest (the block's `CtorsRef` at `n`).
-/


open ConRon.Arena
open ConRon.Bridge.Inductives (PStep dCtx dProg dState dCtx_ext dProg_ext dState_ext dOut dCtors kindOf)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

theorem CtorsPre.ext {st st' : EStore} {us : LsIdx} {ds : List EIdx} {names : List NIdx} {holes : List EIdx}
    {hi : Nat} {usP : List ConLeche.Level} {dsP : List ConLeche.Expr} {namesP : List ConLeche.Name}
    {holesP : List ConLeche.Expr} (h : CtorsPre st us ds names holes hi usP dsP namesP holesP)
    (hx : ConRon.Arena.Ext st st') : CtorsPre st' us ds names holes hi usP dsP namesP holesP :=
  ⟨ConRon.Bridge.denoteLs_ext h.hus hx, ConRon.Bridge.denoteEList_ext hx _ _ h.hds,
    ConRon.Bridge.denoteNListE_ext hx _ _ h.hnames, ConRon.Bridge.denoteEList_ext hx _ _ h.hholes,
    h.wds, h.wholes, h.hlen⟩

section steps
variable {p : Prog} (L : NbLook p) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
  {env : ConLeche.Env}

include L in
theorem ctorsRef_step (n : Nat) (ih : NbRef p dn vis fe env n) : CtorsRef p dn vis fe env (n + 1) := by
  have R := L.ct.cr.rx
  intro m a ctx root fu po pl hi us dO dL no nl hO hL cO cL ns oO oL c prog ds names holes cs NS outs ctxP
    progP usP dsP namesP holesP csP nsP outsP hC hW hCc hcl hcb hcs hns hout houtb hP hA hc hctx hprog hpre
    hcsP hcsF hnsP houtsP
  have hS := hC.stage
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.iw.iw hS.iw.iwSize
  by_cases h0 : cL = 0
  · rw [nctE.arm1 p n m vis ctx root fu po pl hi us dO dL no nl hO hL cO cL ns oO oL h0]
    subst h0
    have : cs = [] := List.eq_nil_of_length_eq_zero (by simpa using hcl.symm)
    subst this
    exact RefE.ret (y := (outs, NS)) (by rw [ConRon.Arena.nestCtors.eq_def]; rfl) ⟨hC, IWGrow.refl _, hout, houtb,
      hns, hP, hA, ConRon.Bridge.CoreStep.refl hC.check⟩
  rw [nctE.arm2 p n m vis ctx root fu po pl hi us dO dL no nl hO hL cO cL ns oO oL h0]
  obtain ⟨⟨cvv, nFn⟩, cs', rfl⟩ : ∃ x cs', cs = x :: cs' := by
    cases cs with
    | nil => exact absurd (UInt64.toNat_inj.mp (by simpa using hcl)) h0
    | cons x cs' => exact ⟨x, cs', rfl⟩
  simp only [List.length_cons] at hcl hcb
  -- the twin's head constructor
  obtain ⟨cP, csP', rfl, hcP, hcsP'⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hcsP
  simp only [ConRon.Bridge.Inductives.dCtor, Option.map_eq_some_iff] at hcP
  obtain ⟨cvP, hcvP, rfl⟩ := hcP
  obtain ⟨w, hw, hcn⟩ := hcs 0 (by simp)
  obtain ⟨hp0, hp1, q, hq, hcvv, hnF⟩ := hcn
  simp only [Nat.add_zero, List.getElem_cons_zero] at hw hcvv hnF
  have hrw : rdW (m.arr64 IW) cO = w := by simp [rdW, hw]
  have hw1 : (w + 1).toNat = w.toNat + 1 := _root_.L.toNat_add_of_lt _ _ (by simp; omega)
  have hrq : (rdW (m.arr64 IW) w).toNat = q := by
    have := rd_iwN (m := m) (p := w) (i := 0) (by simpa using hq) (by simp; omega); simpa using this
  have hrn : (rdW (m.arr64 IW) (w + 1)).toNat = nFn := rd_iwN (by simpa using hnF) (by simp; omega)
  rw [hrw]
  obtain ⟨-, -, hty⟩ := decCV_eq_some.mp hcvv
  obtain ⟨wt, hwt, -⟩ := hd?_some hty
  have hq3 : q + 3 < 2 ^ 64 := by
    have := _root_.L.Arena.erecP_lt64 hwt; omega
  rw [nestCtors_cons, oneK_split]
  -- one constructor
  have hR1 := ih.one m a ctx root fu po pl hi us dO dL no nl hO hL (rdW (m.arr64 IW) w) (rdW (m.arr64 IW) (w + 1))
    ns c prog ds names holes cvv NS ctxP progP usP dsP namesP holesP cvP nsP hC hW hCc (by rw [hrq]; exact hcvv)
    (by rw [hrq]; exact hq3) hns hP hA hc hctx hprog hpre hcvP (hcsF _ List.mem_cons_self) hnsP
  rw [hrn] at hR1
  have hs1 := noE_spec p L.pone n ⟨m, Locals.init []⟩ vis ctx root fu po pl hi us dO dL no nl hO hL
    (rdW (m.arr64 IW) w) (rdW (m.arr64 IW) (w + 1)) ns
  rcases c1 : callE p n "nest_ctors_one" [vis, ctx, root, fu, po, pl, hi, us, dO, dL, no, nl, hO, hL,
      rdW (m.arr64 IW) w, rdW (m.arr64 IW) (w + 1), ns] m with e1 | ⟨r1, m1⟩
  · rw [nctE.k_nest_ctors_one.none]
    exact RefE.bind_left fun hG => RefE.run_err hs1 True.intro hG hR1 c1
  rw [nctE.k_nest_ctors_one.arm1]
  obtain ⟨s1, hs1', -, ⟨⟨ks, closed⟩, NS3⟩, a1, hK1, hpost⟩ := RefE.run_ok hs1 hR1 c1
  rw [hs1'] at hpost
  obtain ⟨hC1, hg1, hks, hksb, hclH, hcld, hns3, hP1, hA1, c1', ⟨oP, hoP, -⟩, ⟨nsP3, hns3P⟩⟩ := hpost
  dsimp only at hC1 hg1 hks hksb hclH hcld hns3 hP1 hA1 c1' hoP hns3P
  have hS1 := hC1.stage
  refine RefE.bind_right hK1 ?_
  -- its record, appended
  rcases c2 : callE p n "rec3" [r1.headD 0, r1.tail.headD 0, r1.tail.tail.headD 0] m1 with e2 | ⟨rr, m2⟩
  · rw [nctE.k_rec3.none]
    exact fun hG => ErrClaim.of_callE_nv hG.nv (_root_.L.Checker.nv_mem (by decide +kernel)) c2
  obtain ⟨s2, hs2, -, hr3⟩ := triple_of_callW (_root_.L.Ind.rec3_specW_iw p R.ha L.h3 n ⟨m1, Locals.init []⟩ _ _ _)
    (callW_of_callE c2)
  simp only at hr3
  rw [hs2] at hr3
  rw [nctE.k_rec3.arm1]
  obtain ⟨hS2, hg2, hrq2, ht2, hget2⟩ := posRecW_stage hr3 hS1 (by simp)
  simp only [List.length_cons, List.length_nil] at ht2
  have hke := pos2_ke_rec (by omega) hget2 (hks.grow hg2) hclH hcld
  rcases c3 : callE p n "sl_snoc" [oO, oL, rr.headD 0] m2 with e3 | ⟨ro, m3⟩
  · rw [nctE.k_sl_snoc.none]
    exact fun hG => ErrClaim.of_callE_nv hG.nv (_root_.L.Checker.nv_mem (by decide +kernel)) c3
  obtain ⟨s3, hs3, -, hsn⟩ := triple_of_callW (slSnoc_specW p R.ha L.nit.hc2 L.nag.hsn n ⟨m2, Locals.init []⟩ _ _ _)
    (callW_of_callE c3)
  simp only at hsn
  rw [hs3] at hsn
  rw [nctE.k_sl_snoc.arm1]
  have hg12 := hg1.trans hg2
  obtain ⟨hS3, hg3, h30, h31, ht3, hw3, hx3⟩ := snocW_words hsn hS2 (by have := hg12.iw; omega)
  have hout3 : OutsB m3 (ro.headD 0).toNat (ro.tail.headD 0).toNat (outs ++ [(ks, closed)]) := by
    rw [h30, h31]
    exact pos2_decB_snoc decKE_mono (hout.grow hg12) hg3 (by omega) hw3 hx3 (DecB.grow (decKE_mono _) hg3 hke)
  have hg13 := hg12.trans hg3
  have hcO1 : (cO + 1).toNat = cO.toNat + 1 := _root_.L.toNat_add_of_lt _ _ (by simp; omega)
  have hcL1 : (cL - 1).toNat = cs'.length := by rw [_root_.L.toNat_sub_one_of_ne h0]; omega
  have hA3 : AbsOK m3 := snocW_afr hsn (posRecW_afr hr3 hA1)
  have hC3 : StageC dn vis fe env m3 a1 := hC1.of_pstep hS3 hA3 (PStep.refl hC1.check.state)
  -- the rest
  have hR4 := ih.ctors m3 a1 ctx root fu po pl hi us dO dL no nl
    hO hL (cO + 1) (cL - 1) _ _ _ c prog ds names holes cs' NS3 (outs ++ [(ks, closed)]) ctxP progP usP dsP namesP
    holesP csP' nsP3 (outsP ++ [oP]) hC3 (hW.grow hg13)
    ⟨hCc.hus, hCc.hds.grow (OMono.decHL _ _) hg13, by have := hCc.hdsb; have := hg13.iw; omega,
      by rw [decHL_agree (RdS.of_grow hg13) (fun j hj => by have := hCc.hnamesb; omega)]; exact hCc.hnames,
      by have := hCc.hnamesb; have := hg13.iw; omega, hCc.hnn,
      by rw [decHL_agree (RdS.of_grow hg13) (fun j hj => by have := hCc.hholesb; omega)]; exact hCc.hholes,
      by have := hCc.hholesb; have := hg13.iw; omega⟩
    hcL1 (by rw [hcO1]; have := hg13.iw; omega) (by rw [hcO1]; exact (hcs.grow (by simpa using hcb) hg13).tail)
    ((hns3.grow hg2 (Nat.lt_of_le_of_lt hS1.iw.iw hS1.iw.iwSize)).grow hg3 (Nat.lt_of_le_of_lt hS2.iw.iw hS2.iw.iwSize))
    hout3 (by rw [h30, h31]; omega) ((hP1.fr (posRecW_mfr hr3)).fr (snocW_mfr hsn)) hA3
    hc (dCtx_ext _ c1'.ext _ _ hctx) (dProg_ext c1'.ext _ _ hprog) (hpre.ext c1'.ext)
    (ConRon.Bridge.Inductives.dCtors_ext c1'.ext _ _ hcsP') (fun x hx => hcsF x (List.mem_cons_of_mem _ hx))
    hns3P (ConRon.Bridge.Inductives.mapM_option_append
      (ConRon.Bridge.Inductives.dOut_ext.list c1'.ext _ _ houtsP) (by simp [hoP]))
  have hs4 := nctE_spec p L.pctors n ⟨m3, Locals.init []⟩ vis ctx root fu po pl hi us dO dL no nl hO hL (cO + 1)
    (cL - 1) (r1.tail.tail.tail.headD 0) (ro.headD 0) (ro.tail.headD 0)
  rcases c4 : callE p n "nest_ctors" [vis, ctx, root, fu, po, pl, hi, us, dO, dL, no, nl, hO, hL, cO + 1, cL - 1,
      r1.tail.tail.tail.headD 0, ro.headD 0, ro.tail.headD 0] m3 with e4 | ⟨r4, m4⟩
  · rw [nctE.k_nest_ctors.none]
    exact fun hG => RefE.run_err hs4 True.intro hG hR4 c4
  rw [nctE.k_nest_ctors.arm1]
  obtain ⟨s4, hs4', -, x, a', hrun, hpost⟩ := RefE.run_ok hs4 hR4 c4
  rw [hs4'] at hpost
  exact RefE.ret hrun ⟨hpost.stage, hg13.trans hpost.grow, hpost.outs, hpost.outsb, hpost.ns, hpost.pos, hpost.abs,
    c1'.trans hpost.core⟩

end steps

end L.Ind
