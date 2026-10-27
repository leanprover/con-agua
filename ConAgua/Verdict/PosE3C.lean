import ConAgua.Verdict.PosE3O
import ConAgua.Arena.IndT.PosCtors
import ConAgua.Checker.NoVerdictTree

/-!
# `nest_ctors`' error claim step (lane `verdicts-b`, helper `ia2`, fork `kn2b`)

`ctorsOKC_step`'s proof (`PosCtors.lean`) on the error model `nctE`: the head constructor's error is
the block's `OneOKE` at `n` (its fragment `oneK` with the rest of `nestCtors` as continuation), the
rest's the block's `CtorsOKE` at `n`; `rec3`, `sl_snoc` claim nothing.
-/


open ConRon.Arena
open ConRon.Bridge.Inductives (PStep dCtx dProg dState dCtx_ext dProg_ext dState_ext dOut kindOf)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section steps
variable {p : Prog} (L : NbLook p) (hnv : closedNV p _root_.L.Checker.nvFns = true)
  (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) {env : ConLeche.Env}

include L hnv in
theorem ctorsOKE_step (n : Nat) (ihC : NbOKC p dn vis fe env n) (ihE : NbOKE p dn vis fe env n) :
    CtorsOKE p dn vis fe env (n + 1) := by
  obtain ⟨-, -, -, -, -, -, -, -, hOne, -, -⟩ := ihC
  obtain ⟨-, -, -, -, -, -, -, hCtorsE, hOneE, -, -⟩ := ihE
  have hSp := nbSpec_all L (realCall p) (realCall_spec p) n
  have R := L.ct.cr.rx
  intro m a ctx root fu po pl hi us dO dL no nl hO hL cO cL ns oO oL c prog ds names holes cs NS outs ctxP
    progP usP dsP namesP holesP csP nsP outsP hC hW hCc hcl hcb hcs hns hout houtb hP hA hc hctx hprog hpre
    hcsP hcsF hnsP houtsP e he
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  replace he := triple_of_callE_err (nctE_spec p L.pctors (n + 1) ⟨m, Locals.init []⟩ vis ctx root fu po pl hi us dO
    dL no nl hO hL cO cL ns oO oL) he (Err.code_ne_of_cls hk0)
  simp only at he
  have hS := hC.stage
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  by_cases h0 : cL = 0
  · rw [nctE.arm1 p n m vis ctx root fu po pl hi us dO dL no nl hO hL cO cL ns oO oL h0] at he; cases he
  rw [nctE.arm2 p n m vis ctx root fu po pl hi us dO dL no nl hO hL cO cL ns oO oL h0] at he
  obtain ⟨⟨cvv, nFn⟩, cs', rfl⟩ : ∃ x cs', cs = x :: cs' := by
    cases cs with
    | nil => exact absurd (UInt64.toNat_inj.mp (by simpa using hcl)) h0
    | cons x cs' => exact ⟨x, cs', rfl⟩
  simp only [List.length_cons] at hcl hcb
  obtain ⟨cP, csP', rfl, hcP, hcsP'⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hcsP
  simp only [ConRon.Bridge.Inductives.dCtor, Option.map_eq_some_iff] at hcP
  obtain ⟨cvP, hcvP, rfl⟩ := hcP
  obtain ⟨w, hw, hcn⟩ := hcs 0 (by simp)
  obtain ⟨hp0, hp1, q, hq, hcvv, hnF⟩ := hcn
  simp only [Nat.add_zero, List.getElem_cons_zero] at hw hcvv hnF
  have hrw : rdW (m.arr64 IW) cO = w := by simp [rdW, hw]
  have hw1 : (w + 1).toNat = w.toNat + 1 := word_add_toNat (by simp; omega)
  have hrq : (rdW (m.arr64 IW) w).toNat = q := by
    have := rd_iwN (m := m) (p := w) (i := 0) (by simpa using hq) (by simp; omega); simpa using this
  have hrn : (rdW (m.arr64 IW) (w + 1)).toNat = nFn := rd_iwN (by simpa using hnF) (by simp; omega)
  rw [hrw] at he
  obtain ⟨-, -, hty⟩ := decCV_some hcvv
  obtain ⟨wt, hwt, -⟩ := hd?_some hty
  have hq3 : q + 3 < 2 ^ 64 := by
    have := (Array.getElem?_eq_some_iff.mp hwt).1; have := erecP_size_lt m; omega
  rw [nestCtors_cons]
  -- one constructor
  cases c1 : callE p n "nest_ctors_one" [vis, ctx, root, fu, po, pl, hi, us, dO, dL, no, nl, hO, hL,
      rdW (m.arr64 IW) w, rdW (m.arr64 IW) (w + 1), ns] m with
  | error e1 =>
    rw [c1, nctE.k_nest_ctors_one.none] at he; cases he
    rw [← hrn]
    exact hOneE m a ctx root fu po pl hi us dO dL no nl hO hL _ _ ns c prog ds names holes cvv NS ctxP progP usP
      dsP namesP holesP cvP nsP hC hW hCc (by rw [hrq]; exact hcvv) (by rw [hrq]; exact hq3) hns hP hA hc hctx hprog
      hpre hcvP (hcsF _ List.mem_cons_self) hnsP _ c1 _
  | ok q1 =>
  obtain ⟨r1', m1⟩ := q1
  obtain ⟨s1, hs1, -, ho⟩ := triple_of_callW (hSp.2.2.2.2.2.2.2.2.1 ⟨m, Locals.init []⟩ vis ctx root fu po pl hi us dO
    dL no nl hO hL _ _ ns) (callW_of_callE c1)
  simp only at ho
  rw [hs1] at ho
  rw [c1, nctE.k_nest_ctors_one.arm1] at he
  obtain ⟨ks, closed, NS3, a1, hK1, hC1, hg1, hks, hksb, hclH, hcld, hns3, hP1, hA1, c1', ⟨oP, hoP, -⟩,
      ⟨nsP3, hns3P⟩⟩ :=
    hOne m m1 a ctx root fu po pl hi us dO dL no nl hO hL _ _ ns c prog ds names holes cvv NS _ ctxP progP usP dsP
      namesP holesP cvP nsP ho hC hW hCc (by rw [hrq]; exact hcvv) (by rw [hrq]; exact hq3) hns hP hA hc hctx hprog
      hpre hcvP (hcsF _ List.mem_cons_self) hnsP
  simp only [List.headD_cons, List.tail_cons] at hks hksb hclH hcld hns3
  have hS1 := hC1.stage
  rw [hrn] at hK1
  refine ErrClaim.of_runEq2 (hK1 _) (fun ce h => h) ?_
  -- its record, appended
  cases c2 : callE p n "rec3" [r1'.headD 0, r1'.tail.headD 0, r1'.tail.tail.headD 0] m1 with
  | error e2 =>
    rw [c2, nctE.k_rec3.none] at he; cases he
    exact ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) c2
  | ok q2 =>
  obtain ⟨rr, m2⟩ := q2
  obtain ⟨s2, hs2, -, hr3⟩ := triple_of_callW (posRec3_specW p R.ha L.h3 n ⟨m1, Locals.init []⟩ _ _ _)
    (callW_of_callE c2)
  simp only at hr3
  rw [hs2] at hr3
  rw [c2, nctE.k_rec3.arm1] at he
  obtain ⟨hS2, hg2, hrq2, ht2, hget2⟩ := posRecW_stage hr3 hS1 (by simp)
  simp only [List.length_cons, List.length_nil] at ht2
  have hke := pos2_ke_rec (by omega) hget2 (hks.grow hg2) hclH hcld
  cases c3 : callE p n "sl_snoc" [oO, oL, rr.headD 0] m2 with
  | error e3 =>
    rw [c3, nctE.k_sl_snoc.none] at he; cases he
    exact ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) c3
  | ok q3 =>
  obtain ⟨ro, m3⟩ := q3
  obtain ⟨s3, hs3, -, hsn⟩ := triple_of_callW (slSnoc_specW p R.ha L.nit.hc2 L.nag.hsn n ⟨m2, Locals.init []⟩ _ _ _)
    (callW_of_callE c3)
  simp only at hsn
  rw [hs3] at hsn
  rw [c3, nctE.k_sl_snoc.arm1] at he
  have hg12 := hg1.trans hg2
  obtain ⟨hS3, hg3, h30, h31, ht3, hw3, hx3⟩ := snocW_words hsn hS2 (by have := hg12.1; omega)
  have hout3 : OutsB m3 (ro.headD 0).toNat (ro.tail.headD 0).toNat (outs ++ [(ks, closed)]) := by
    rw [h30, h31]
    exact pos2_decB_snoc decKE_mono (hout.grow hg12) hg3 (by omega) hw3 hx3 (DecB.grow (decKE_mono _) hg3 hke)
  have hg13 := hg12.trans hg3
  have hcO1 : (cO + 1).toNat = cO.toNat + 1 := word_add_toNat (by simp; omega)
  have hcL1 : (cL - 1).toNat = cs'.length := by rw [pos2_word_pred h0]; omega
  have hA3 : AbsOK m3 := snocW_afr hsn (posRecW_afr hr3 hA1)
  have hC3 : StageC dn vis fe env m3 a1 := hC1.of_pstep hS3 hA3 (PStep.refl hC1.check.state)
  cases c4 : callE p n "nest_ctors" [vis, ctx, root, fu, po, pl, hi, us, dO, dL, no, nl, hO, hL, cO + 1, cL - 1,
      r1'.tail.tail.tail.headD 0, ro.headD 0, ro.tail.headD 0] m3 with
  | ok q4 => obtain ⟨r4, m4⟩ := q4; rw [c4, nctE.k_nest_ctors.arm1] at he; cases he
  | error e4 =>
  rw [c4, nctE.k_nest_ctors.none] at he; cases he
  exact hCtorsE m3 a1 ctx root fu po pl hi us dO dL no nl
    hO hL (cO + 1) (cL - 1) _ _ _ c prog ds names holes cs' NS3 (outs ++ [(ks, closed)]) ctxP progP usP dsP namesP
    holesP csP' nsP3 (outsP ++ [oP]) hC3 (hW.grow hg13)
    ⟨hCc.hus, hCc.hds.grow (OMono.decHL _ _) hg13, by have := hCc.hdsb; have := hg13.1; omega,
      by rw [decHL_agree (RdS.of_grow hg13) (fun j hj => by have := hCc.hnamesb; omega)]; exact hCc.hnames,
      by have := hCc.hnamesb; have := hg13.1; omega, hCc.hnn,
      by rw [decHL_agree (RdS.of_grow hg13) (fun j hj => by have := hCc.hholesb; omega)]; exact hCc.hholes,
      by have := hCc.hholesb; have := hg13.1; omega⟩
    hcL1 (by rw [hcO1]; have := hg13.1; omega) (by rw [hcO1]; exact (hcs.grow (by simpa using hcb) hg13).tail)
    ((hns3.grow hg2 (Nat.lt_of_le_of_lt hS1.2.1 hS1.2.2.2.1)).grow hg3 (Nat.lt_of_le_of_lt hS2.2.1 hS2.2.2.2.1))
    hout3 (by rw [h30, h31]; omega) ((hP1.fr (posRecW_mfr hr3)).fr (snocW_mfr hsn)) hA3
    hc (dCtx_ext _ c1'.ext _ _ hctx) (dProg_ext c1'.ext _ _ hprog) (hpre.ext c1'.ext)
    (ConRon.Bridge.Inductives.dCtors_ext c1'.ext _ _ hcsP') (fun x hx => hcsF x (List.mem_cons_of_mem _ hx))
    hns3P (ConRon.Bridge.Inductives.mapM_option_append
      (ConRon.Bridge.Inductives.dOut_ext.list c1'.ext _ _ houtsP) (by simp [hoP])) _ c4

end steps

end L.Ind
