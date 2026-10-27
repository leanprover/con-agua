import ConAgua.Arena.IndT.PosDefs
import ConAgua.Arena.IndT.Lift
import ConAgua.Arena.IndPosSpec.GgW2
import ConAgua.Arena.IndPosSpec.Pos2DecHLSplit

/-!
# `nest_fields` under `StageC` (lane `indstaget`, helper `indstaget-pos`)

`fieldsOK_step`'s proof (`IndPos2SpecS`) with the twin side of con-ron's `nestFields_spec`: the
field's domain walked (the block's `PosOKC` at `n`, con-ron's `nestPos_spec` on its run for the
walked domain's and the state's denotations), its variable interned (`internFVarE_run`), the body
opened (`instantiate1Fast_run`), the rest by the block's `FieldsOKC` at `n`.
-/


open ConRon.Arena
open ConRon.Bridge.Inductives (PStep dCtx dProg dState dCtx_ext dProg_ext dState_ext kindOf RPos)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- The core's spec at `.verified` (con-ron's `CoreSpec.of_core`). -/
theorem coreSpecV : ConRon.Bridge.CoreSpec V checkFuel := ConRon.Bridge.CoreSpec.of_core rfl

section steps
variable (p : Prog) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) {env : ConLeche.Env}
  (henv : ConLeche.EnvWF env)

include henv in
theorem fieldsOKC_step (n : Nat) (ih : NbOKC p dn vis fe env n) :
    FieldsOKC p dn vis fe env (n + 1) := by
  obtain ⟨hPos, -, -, -, -, -, -, -, -, -, hFields⟩ := ih
  intro m m' a ctx fu po pl base nF j cur ns kO kL dO dL c prog NS ks nds r ctxP progP curP nsP ndsP
    h hC hW hcur hns hks hkb hnd hndb hP hA hc hctx hprog hcurP hnsP hndsP hw
  have hS := hC.stage
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  rw [nbFieldsW_succ] at h
  by_cases h0 : nF = 0
  · rw [ite_eq_left h0] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    subst h0
    refine ⟨(ks, nds, decI cur, NS), a, by rw [ConRon.Arena.nestFields.eq_def]; rfl, hC, IWGrow.refl _, hks, hkb,
      hnd, hndb, hcur, rfl, hns, by simp, by simp, by simp, hP, hA, ConRon.Bridge.CoreStep.refl hC.check⟩
  rw [ite_eq_right h0] at h
  by_cases h6 : cur >>> 28 ≠ 6
  · rw [ite_eq_left h6] at h; cases h
  rw [ite_eq_right h6] at h
  have h6' : cur >>> 28 = 6 := by simpa using h6
  by_cases hov : base + j < base
  · rw [ite_eq_left hov] at h; cases h
  rw [ite_eq_right hov] at h
  by_cases hov1 : base + j + 1 = 0
  · rw [ite_eq_left hov1] at h; cases h
  rw [ite_eq_right hov1] at h
  by_cases hev : eViewW m cur = []
  · rw [ite_eq_left hev] at h; cases h
  rw [ite_eq_right hev] at h
  obtain ⟨d, b, hv, hd, hb, hvb, htag⟩ := pos2_forall_view hS hcur h6' hev
  simp only [hv, List.tail_cons, List.headD_cons] at h
  have hbj : (base + j).toNat = base.toNat + j.toNat := pos2_word_add hov
  have hbj1 : (base + j + 1).toNat = base.toNat + j.toNat + 1 := by rw [pos2_word_succ hov1, hbj]
  obtain ⟨nF', hnF'⟩ : ∃ nF', nF.toNat = nF' + 1 := ⟨nF.toNat - 1, by
    have : nF.toNat ≠ 0 := fun e => h0 (UInt64.toNat_inj.mp (by simpa using e)); omega⟩
  -- the twin's view of the `Π`
  obtain ⟨-, hvbS⟩ := ConRon.Bridge.Inductives.viewBind_run hvb
  obtain ⟨dP, bP, rfl, hdP, hbP⟩ := ConRon.Bridge.denote_forallE_inv hC.check.state.wf
    (ConRon.Bridge.view_forallE_of_viewBind (by simp [htag]) hvbS.symm) hcurP
  simp only [ConLeche.Expr.WScoped] at hw
  -- the field's domain walked
  rcases hp : nbPosW (realCall p) n m vis ctx fu po pl (base + j) 0 d ns with _ | ⟨rp, m1⟩ <;> rw [hp] at h; · simp [nbFieldsK1] at h
  simp only [nbFieldsK1_some, List.tail_cons, List.headD_cons] at h
  obtain ⟨x1, a1, hrun1, hC1, hg1, hk1, hnd1H, hnd1, hns1, hP1, hA1, c1⟩ := hPos m m1 a ctx fu po pl
    (base + j) 0 d ns c prog NS rp ctxP progP dP nsP hp hC hW hd hns hP hA hc hctx hprog hdP hnsP
    (by rw [hbj]; exact hw.1)
  have hS1 := hC1.stage
  obtain ⟨-, v1, ⟨-, hnd1P, hns1P, hwnd⟩, -⟩ := ConRon.Bridge.Inductives.nestPos_spec coreSpecV henv hc
    fu.toNat prog progP (base + j).toNat (0 : Word).toNat (decI d) dP NS nsP (by rw [hbj]; exact hw.1)
    a a1 x1 hC.check ⟨hctx, hprog, hdP, hnsP⟩ hrun1
  -- the field's variable
  rcases hfv : fvinternW m1 (base + j) d with _ | ⟨fv, m2⟩ <;> rw [hfv] at h; · simp [nbFieldsK2] at h
  rw [nbFieldsK2_some] at h
  by_cases hfvb : 4294967296 ≤ fv
  · rw [ite_eq_left hfvb] at h; cases h
  simp only [ite_eq_right hfvb, List.tail_cons, List.headD_cons] at h
  have hfvH : H fv := by
    have : ¬ (4294967296 : Word).toNat ≤ fv.toNat := fun e => hfvb (UInt64.le_iff_toNat_le.mpr e)
    simp only [H]; simpa using this
  obtain ⟨a2, hrun2, hS2, hg2⟩ := internFVar_stage hS1 (base + j) d hd hfv
  have e2 : (internFVarE (base.toNat + j.toNat) (decI d)).run a1 = .ok (decI fv, a2) := by
    simpa [internFVarE, hbj, decE_eq] using hrun2
  obtain ⟨p2, hfvP⟩ := ConRon.Bridge.Inductives.internFVarE_run hC1.check.state
    (ConRon.Bridge.denote_ext hdP c1.ext) e2
  -- the body opened
  rcases hin : i1F m2 [CWF, b, fv, 0] with _ | ⟨rb, m3⟩ <;> rw [hin] at h; · simp [nbFieldsK3] at h
  rw [nbFieldsK3_some] at h
  obtain ⟨b2, a3, hrun3, hS3, hg3, hb2H, hb2d⟩ := i1F_ok dn vis fe b fv 0 hb m2 m3 a2 rb hin hS2
  rw [CWF_eq] at hrun3
  have e3 : (instantiate1Fast coreWalkFuel (decI b) (decI fv) 0).run a2 = .ok (b2, a3) := by simpa using hrun3
  have hbP2 : denoteE a2.store (decI b) = some bP := ConRon.Bridge.denote_ext hbP (c1.ext.trans p2.ext)
  obtain ⟨q1, q2, q4, q5, -, q7⟩ := ConRon.Bridge.ExprOps.instantiate1Fast_run p2.ok hfvP
    (by rw [hbP2]; rfl) e3
  have p3 : PStep a2 a3 := PStep.of_caches q1 q2 q4 q5
  have hb2P : denoteE a3.store b2 = some (bP.instantiate1 (.fvar (base.toNat + j.toNat) dP) 0) := q7 _ hbP2
  have hg13 := (hg1.trans hg2).trans hg3
  -- the kind and the walked domain appended
  rcases hs1 : snocW n m3 kO kL (rp.headD 0) with _ | ⟨rk, m4⟩ <;> rw [hs1] at h; · simp [nbFieldsK4] at h
  rw [nbFieldsK4_some] at h
  obtain ⟨hS4, hg4, hk40, hk41, ht4, hw4, hx4⟩ := snocW_words hs1 hS3 (by have := hg13.1; omega)
  have hks4 : KlB m4 (rk.headD 0).toNat (rk.tail.headD 0).toNat (ks ++ [x1.1]) := by
    rw [hk40, hk41]
    exact KlB.snoc ((hks.grow hg13)) hg4 (by omega) hw4 hx4 hk1
  rcases hs2 : snocW n m4 dO dL (rp.tail.headD 0) with _ | ⟨rd, m5⟩ <;> rw [hs2] at h; · simp [nbFieldsK5] at h
  rw [nbFieldsK5_some] at h
  have hg14 := hg13.trans hg4
  obtain ⟨hrd, hnd5, hg5, -, hl5, ht5⟩ := snocW_decK hs2 hS4.2.2.2.1 hS4.2.2.2.2.2 (by have := hg14.1; omega)
    hnd1H (by rw [decHL_agree (RdS.of_grow hg14) (fun i hi => by omega)]; exact hnd)
  have hS5 := snocW_stage hs2 hS4
  have hg15 := hg14.trans hg5
  have hA5 : AbsOK m5 := snocW_afr hs2 (snocW_afr hs1 (i1F_afr hin (fvinternW_afr hfv hA1)))
  have p23 := p2.trans p3
  have hC5 : StageC dn vis fe env m5 a3 := hC1.of_pstep hS5 hA5 p23
  have c3 : ConRon.Bridge.CoreStep V env fe a a3 := c1.trans (p23.toCore hC1.check)
  have hx13 := c1.ext.trans p23.ext
  -- the rest of the fields
  have hj1 : (j + 1).toNat = j.toNat + 1 := word_add_toNat (by have := (base + j + 1).toNat_lt; simp; omega)
  have hnF1 : (nF - 1).toNat = nF' := by rw [pos2_word_pred h0]; omega
  have hb2P' : denoteE a3.store (decI (rb.headD 0)) =
      some (bP.instantiate1 (.fvar (base.toNat + j.toNat) dP) 0) := by
    rw [show (decI (rb.headD 0) : EIdx) = b2 by simpa [decE_eq] using hb2d]; exact hb2P
  have hndP' : Frontend.denoteEList a3.store (nds ++ [decI (rp.tail.headD 0)]) = some (ndsP ++ [v1.2.1]) :=
    ConRon.Bridge.ExprOps.denoteEList_snoc
      (by rw [hnd1]; exact ConRon.Bridge.denote_ext hnd1P p23.ext) _ _
      (ConRon.Bridge.denoteEList_ext hx13 _ _ hndsP)
  obtain ⟨x, a', hrun, hC', hg', hK', hKb', hD', hDb', hcH', hcd', hns', hl1, hl2, hov', hP', hA', c5⟩ :=
    hFields m5 m' a3 ctx fu po pl base (nF - 1) (j + 1) (rb.headD 0) (rp.tail.tail.headD 0) (rk.headD 0)
      (rk.tail.headD 0) (rd.headD 0) (rd.tail.headD 0) c prog x1.2.2 (ks ++ [x1.1]) (nds ++ [decI (rp.tail.headD 0)])
      r ctxP progP _ v1.2.2 (ndsP ++ [v1.2.1]) h hC5 (hW.grow (hg15.trans (IWGrow.refl _))) (by simpa using hb2H)
      ((hns1.grow (hg2.trans hg3) (Nat.lt_of_le_of_lt hS1.2.1 hS1.2.2.2.1)).grow (hg4.trans hg5)
        (Nat.lt_of_le_of_lt hS3.2.1 hS3.2.2.2.1))
      (hks4.grow hg5) (by rw [hk40, hk41]; have := hg5.1; omega)
      (by rw [hrd]; simpa using hnd5) (by rw [hrd]; simp only [List.headD_cons, List.tail_cons]; omega)
      ((((hP1.fr (fvinternW_mfr hfv)).fr (MFr.ofI1F hin)).fr (snocW_mfr hs1)).fr (snocW_mfr hs2)) hA5
      hc (dCtx_ext _ hx13 _ _ hctx) (dProg_ext hx13 _ _ hprog) hb2P'
      (by rw [show x1.2.2 = x1.2.2 from rfl]; exact dState_ext p23.ext _ _ hns1P) hndP'
      (by rw [hj1, show base.toNat + (j.toNat + 1) = base.toNat + j.toNat + 1 by omega]
          exact ConLeche.Expr.WScoped.instantiate1 hw.1 0 hw.2)
  refine ⟨x, a', ?_, hC', hg15.trans hg', hK', hKb', hD', hDb', hcH', hcd', hns', ?_, ?_, ?_, hP', hA', c3.trans c5⟩
  · rw [hnF', ConRon.Arena.nestFields.eq_def]
    simp only [htag, beq_self_eq_true, ite_true, StateT.run_bind, hvb, except_ok_bind]
    have e1 := hrun1; simp only [hbj, UInt64.toNat_zero] at e1
    rw [e1]; simp only [except_ok_bind]; rw [e2]; simp only [except_ok_bind]; rw [e3]; simp only [except_ok_bind]
    rw [hnF1, hj1, hb2d, hnd1] at hrun
    exact hrun
  · rw [hl1]; simp; omega
  · rw [hl2]; simp; omega
  · right; rcases hov' with h' | h'
    · rw [hnF1] at h'; subst h'; have := (base + j + 1).toNat_lt; omega
    · rw [hj1, hnF1] at h'; omega

end steps

end L.Ind
