import ConAgua.Arena.IndT.Lift
import ConAgua.Arena.IndT.PosDefs
import ConAgua.Arena.IndPosSpec.GgW2
import ConAgua.Arena.IndPosSpec.Pos2DecHLSplit
import ConAgua.Arena.IndRealAbsPos
import ConAgua.Arena.IndPosSpec.Snoc

/-!
# `nest_ctors` under `StageC` (lane `indstaget`, helper `indstaget-pos`)

`ctorsOK_step`'s proof (`IndPosSpec/Pos2DecHLSplit`) with the twin side of con-ron's `nestCtors_spec`: one
constructor (the block's `OneOKC` at `n`, its out record and state denoting), the record appended
(L only), the rest (the block's `CtorsOKC` at `n`).
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
variable (p : Prog) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)

theorem ctorsOKC_step (n : Nat) (ih : NbOKC p dn vis fe env n) : CtorsOKC p dn vis fe env (n + 1) := by
  obtain ⟨-, -, -, -, -, -, -, hCtors, hOne, -, -⟩ := ih
  intro m m' a ctx root fu po pl hi us dO dL no nl hO hL cO cL ns oO oL c prog ds names holes cs NS outs r ctxP
    progP usP dsP namesP holesP csP nsP outsP h hC hW hCc hcl hcb hcs hns hout houtb hP hA hc hctx hprog hpre
    hcsP hcsF hnsP houtsP
  have hS := hC.stage
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  rw [nbCtorsW_succ] at h
  by_cases h0 : cL = 0
  · rw [ite_eq_left h0] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    subst h0
    have : cs = [] := List.eq_nil_of_length_eq_zero (by simpa using hcl.symm)
    subst this
    exact ⟨(outs, NS), a, by rw [ConRon.Arena.nestCtors.eq_def]; rfl, hC, IWGrow.refl _, hout, houtb, hns, hP, hA,
      ConRon.Bridge.CoreStep.refl hC.check⟩
  rw [ite_eq_right h0] at h
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
  have hw1 : (w + 1).toNat = w.toNat + 1 := word_add_toNat (by simp; omega)
  have hrq : (rdW (m.arr64 IW) w).toNat = q := by
    have := rd_iwN (m := m) (p := w) (i := 0) (by simpa using hq) (by simp; omega); simpa using this
  have hrn : (rdW (m.arr64 IW) (w + 1)).toNat = nFn := rd_iwN (by simpa using hnF) (by simp; omega)
  rw [hrw] at h
  obtain ⟨-, -, hty⟩ := decCV_some hcvv
  obtain ⟨wt, hwt, -⟩ := hd?_some hty
  have hq3 : q + 3 < 2 ^ 64 := by
    have := (Array.getElem?_eq_some_iff.mp hwt).1; have := erecP_size_lt m; omega
  -- one constructor
  rcases ho : nbOneW (realCall p) n m vis ctx root fu po pl hi us dO dL no nl hO hL (rdW (m.arr64 IW) w)
      (rdW (m.arr64 IW) (w + 1)) ns with _ | ⟨r1, m1⟩; · rw [ho] at h; simp [nbCtorsK1] at h
  rw [ho, nbCtorsK1_some] at h
  obtain ⟨ks, closed, NS3, a1, hK1, hC1, hg1, hks, hksb, hclH, hcld, hns3, hP1, hA1, c1, ⟨oP, hoP, -⟩,
      ⟨nsP3, hns3P⟩⟩ :=
    hOne m m1 a ctx root fu po pl hi us dO dL no nl hO hL _ _ ns c prog ds names holes cvv NS r1 ctxP progP usP dsP
      namesP holesP cvP nsP ho hC hW hCc (by rw [hrq]; exact hcvv) (by rw [hrq]; exact hq3) hns hP hA hc hctx hprog
      hpre hcvP (hcsF _ List.mem_cons_self) hnsP
  have hS1 := hC1.stage
  rw [hrn] at hK1
  -- its record, appended
  rcases hr3 : posRecW m1 [r1.headD 0, r1.tail.headD 0, r1.tail.tail.headD 0] with _ | ⟨rec, m2⟩ <;> rw [hr3] at h; · simp [nbCtorsK2] at h
  rw [nbCtorsK2_some] at h
  obtain ⟨hS2, hg2, hrq2, ht2, hget2⟩ := posRecW_stage hr3 hS1 (by simp)
  simp only [List.length_cons, List.length_nil] at ht2
  have hke := pos2_ke_rec (by omega) hget2 (hks.grow hg2) hclH hcld
  rcases hsn : snocW n m2 oO oL rec with _ | ⟨ro, m3⟩ <;> rw [hsn] at h; · simp [nbCtorsK3] at h
  rw [nbCtorsK3_some] at h
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
  obtain ⟨x, a', hrun, hC', hg', hO', hOb', hns', hP', hA', c2⟩ := hCtors m3 m' a1 ctx root fu po pl hi us dO dL no nl
    hO hL (cO + 1) (cL - 1) _ _ _ c prog ds names holes cs' NS3 (outs ++ [(ks, closed)]) r ctxP progP usP dsP namesP
    holesP csP' nsP3 (outsP ++ [oP]) h hC3 (hW.grow hg13)
    ⟨hCc.hus, hCc.hds.grow (OMono.decHL _ _) hg13, by have := hCc.hdsb; have := hg13.1; omega,
      by rw [decHL_agree (RdS.of_grow hg13) (fun j hj => by have := hCc.hnamesb; omega)]; exact hCc.hnames,
      by have := hCc.hnamesb; have := hg13.1; omega, hCc.hnn,
      by rw [decHL_agree (RdS.of_grow hg13) (fun j hj => by have := hCc.hholesb; omega)]; exact hCc.hholes,
      by have := hCc.hholesb; have := hg13.1; omega⟩
    hcL1 (by rw [hcO1]; have := hg13.1; omega) (by rw [hcO1]; exact (hcs.grow (by simpa using hcb) hg13).tail)
    ((hns3.grow hg2 (Nat.lt_of_le_of_lt hS1.2.1 hS1.2.2.2.1)).grow hg3 (Nat.lt_of_le_of_lt hS2.2.1 hS2.2.2.2.1))
    hout3 (by rw [h30, h31]; omega) ((hP1.fr (posRecW_mfr hr3)).fr (snocW_mfr hsn)) hA3
    hc (dCtx_ext _ c1.ext _ _ hctx) (dProg_ext c1.ext _ _ hprog) (hpre.ext c1.ext)
    (ConRon.Bridge.Inductives.dCtors_ext c1.ext _ _ hcsP') (fun x hx => hcsF x (List.mem_cons_of_mem _ hx))
    hns3P (ConRon.Bridge.Inductives.mapM_option_append
      (ConRon.Bridge.Inductives.dOut_ext.list c1.ext _ _ houtsP) (by simp [hoP]))
  refine ⟨x, a', ?_, hC', hg13.trans hg', hO', hOb', hns', hP', hA', c1.trans c2⟩
  rw [nestCtors_cons, hK1]
  exact hrun

end steps

end L.Ind
