import ConAgua.Verdict.PosE
import ConAgua.Verdict.PosE3Fm

/-!
# `nest_fields`' error claim step (lane `verdicts-b`, helper `ia2`, fork `kn2b`)

`fieldsOKC_step`'s proof (`PosFields.lean`) on the error model `nfE`: the walked domain's error is
`nest_pos`'s claim (the block's `PosOKE` at `n`), the rest of the fields' the block's `FieldsOKE`
at `n`; the reject site (the telescope not a `Π`) is the twin's `fail`.
-/


open ConRon.Arena
open ConRon.Bridge.Inductives (PStep dCtx dProg dState dCtx_ext dProg_ext dState_ext kindOf RPos)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- A twin run that fails as another one does (from another state). -/
theorem ErrClaim.of_run {α : Type} {T T' : AM α} {a a' : AState} {e : Err}
    (h' : ErrClaim T' a' e) (h : ∀ ce, T'.run a' = .error ce → T.run a = .error ce) :
    ErrClaim T a e := fun hk => by
  obtain ⟨ce, hce, hc⟩ := h' hk
  exact ⟨ce, h ce hce, hc⟩

/-- A twin run equal to another's. -/
theorem ErrClaim.of_runEq {α : Type} {T T' : AM α} {a : AState} {e : Err}
    (h : T.run a = T'.run a) (h' : ErrClaim T' a e) : ErrClaim T a e := fun hk => by
  obtain ⟨ce, hce, hc⟩ := h' hk
  exact ⟨ce, by rw [h]; exact hce, hc⟩

theorem Err.cls_abort0 : (Err.abort 0).cls = 0 := rfl

section steps
variable {p : Prog} (L : NbLook p) (hnv : closedNV p _root_.L.Checker.nvFns = true)
  (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) {env : ConLeche.Env}
  (henv : ConLeche.EnvWF env)

include L hnv henv in
theorem fieldsOKE_step (n : Nat) (ihC : NbOKC p dn vis fe env n) (ihE : NbOKE p dn vis fe env n) :
    FieldsOKE p dn vis fe env (n + 1) := by
  obtain ⟨hPos, -, -, -, -, -, -, -, -, -, -⟩ := ihC
  obtain ⟨hPosE, -, -, -, -, -, -, -, -, -, hFieldsE⟩ := ihE
  have hSp := nbSpec_all L (realCall p) (realCall_spec p) n
  have R := L.ct.cr.rx
  intro m a ctx fu po pl base nF j cur ns kO kL dO dL c prog NS ks nds ctxP progP curP nsP ndsP
    hC hW hcur hns hks hkb hnd hndb hP hA hc hctx hprog hcurP hnsP hndsP hw e he
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  replace he := triple_of_callE_err (nfE_spec p L.pfields (n + 1) ⟨m, Locals.init []⟩ vis ctx fu po pl base nF j
    cur ns kO kL dO dL) he (Err.code_ne_of_cls hk0)
  simp only at he
  have hS := hC.stage
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  by_cases h0 : nF = 0
  · rw [nfE.arm1 p n m vis ctx fu po pl base nF j cur ns kO kL dO dL h0] at he; cases he
  obtain ⟨nF', hnF'⟩ : ∃ nF', nF.toNat = nF' + 1 := ⟨nF.toNat - 1, by
    have : nF.toNat ≠ 0 := fun e => h0 (UInt64.toNat_inj.mp (by simpa using e)); omega⟩
  by_cases h6 : cur >>> 28 ≠ 6
  · rw [nfE.abort1 p n m vis ctx fu po pl base nF j cur ns kO kL dO dL h0 h6] at he
    cases he
    have htag : ¬ (decI cur : EIdx).tag = ETag.forallE := by
      rw [← decE_eq]; exact fun e' => h6 ((decE_tag_forall _ hcur).mp e')
    rw [hnF', ConRon.Arena.nestFields.eq_def]
    simp only [htag, beq_iff_eq, ite_false]
    exact ErrClaim.fail _ _ (by decide)
  have h6' : cur >>> 28 = 6 := by simpa using h6
  by_cases hov : base + j < base
  · rw [nfE.abort2 p n m vis ctx fu po pl base nF j cur ns kO kL dO dL h0 h6' hov] at he; cases he
    exact absurd Err.cls_abort0 hk0
  by_cases hov1 : base + j + 1 = 0
  · rw [nfE.abort3 p n m vis ctx fu po pl base nF j cur ns kO kL dO dL h0 h6' hov hov1] at he; cases he
    exact absurd Err.cls_abort0 hk0
  rw [nfE.arm2 p n m vis ctx fu po pl base nF j cur ns kO kL dO dL h0 h6' hov hov1] at he
  -- `e_view`
  cases c1 : callE p n "e_view" [cur] m with
  | error e1 =>
    rw [c1, nfE.k_e_view.none] at he; cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) c1
  | ok q1 =>
  obtain ⟨rv, mv⟩ := q1
  obtain ⟨sv, hsv, hsv', hrne, hrv⟩ := triple_of_callW (eView_spec p R.hl.hv n ⟨m, Locals.init []⟩ cur)
    (callW_of_callE c1)
  have hmv : m = mv := by rw [← hsv, hsv']
  subst hmv
  rw [c1, nfE.k_e_view.arm1] at he
  have hev : eViewW m cur ≠ [] := by simp only at hrv; rw [← hrv]; exact hrne
  obtain ⟨d, b, hv, hd, hb, hvb, htag⟩ := pos2_forall_view hS hcur h6' hev
  simp only at hrv
  rw [hrv, hv] at he
  simp only [List.tail_cons, List.headD_cons] at he
  have hbj : (base + j).toNat = base.toNat + j.toNat := pos2_word_add hov
  obtain ⟨-, hvbS⟩ := ConRon.Bridge.Inductives.viewBind_run hvb
  obtain ⟨dP, bP, rfl, hdP, hbP⟩ := ConRon.Bridge.denote_forallE_inv hC.check.state.wf
    (ConRon.Bridge.view_forallE_of_viewBind (by simp [htag]) hvbS.symm) hcurP
  simp only [ConLeche.Expr.WScoped] at hw
  -- the twin up to the domain's walk
  have hT :
      (ConRon.Arena.nestFields V fe c fu.toNat prog base.toNat nF.toNat j.toNat (decI cur) NS ks nds).run a =
        (ConRon.Arena.nestPos V fe c fu.toNat prog (base + j).toNat (0 : Word).toNat (decI d) NS >>= fun v =>
          (do
            let fv ← internFVarE (base.toNat + j.toNat) (decI d)
            let b2 ← instantiate1Fast coreWalkFuel (decI b) fv 0
            ConRon.Arena.nestFields V fe c fu.toNat prog base.toNat nF' (j.toNat + 1) b2 v.2.2 (ks ++ [v.1])
              (nds ++ [v.2.1]))).run a := by
    rw [hnF', ConRon.Arena.nestFields.eq_def]
    simp only [htag, beq_self_eq_true, ite_true, StateT.run_bind, hvb, except_ok_bind, hbj, UInt64.toNat_zero]
  -- `nest_pos`
  cases c2 : callE p n "nest_pos" [vis, ctx, fu, po, pl, base + j, 0, d, ns] m with
  | error e2 =>
    rw [c2, nfE.k_nest_pos.none] at he; cases he
    refine ErrClaim.of_runEq hT ?_
    exact ErrClaim.bind_left (hPosE m a ctx fu po pl (base + j) 0 d ns c prog NS ctxP progP dP nsP
      hC hW hd hns hP hA hc hctx hprog hdP hnsP (by rw [hbj]; exact hw.1) _ c2)
  | ok q2 =>
  obtain ⟨r2, m1⟩ := q2
  obtain ⟨s2, hs2, -, hp⟩ := triple_of_callW (hSp.1 ⟨m, Locals.init []⟩ vis ctx fu po pl (base + j) 0 d ns)
    (callW_of_callE c2)
  simp only at hp
  rw [hs2] at hp
  rw [c2, nfE.k_nest_pos.arm1] at he
  obtain ⟨x1, a1, hrun1, hC1, hg1, hk1, hnd1H, hnd1, hns1, hP1, hA1, c1⟩ := hPos m m1 a ctx fu po pl
    (base + j) 0 d ns c prog NS _ ctxP progP dP nsP hp hC hW hd hns hP hA hc hctx hprog hdP hnsP
    (by rw [hbj]; exact hw.1)
  simp only [List.tail_cons, List.headD_cons] at hk1 hnd1H hnd1 hns1
  have hS1 := hC1.stage
  obtain ⟨-, v1, ⟨-, hnd1P, hns1P, hwnd⟩, -⟩ := ConRon.Bridge.Inductives.nestPos_spec coreSpecV henv hc
    fu.toNat prog progP (base + j).toNat (0 : Word).toNat (decI d) dP NS nsP (by rw [hbj]; exact hw.1)
    a a1 x1 hC.check ⟨hctx, hprog, hdP, hnsP⟩ hrun1
  refine ErrClaim.of_runEq hT ?_
  refine ErrClaim.bind_right hrun1 ?_
  -- the field's variable
  cases c3 : callE p n "intern_fvar" [base + j, d] m1 with
  | error e3 =>
    rw [c3, nfE.k_intern_fvar.none] at he; cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) c3
  | ok q3 =>
  obtain ⟨r3, m2⟩ := q3
  obtain ⟨s3, hs3, -, hfv⟩ := triple_of_callW (internFVar_spec p R.hl.hff R.hl.hfp R.hl.hif n ⟨m1, Locals.init []⟩
    (base + j) d) (callW_of_callE c3)
  simp only at hfv
  rw [hs3] at hfv
  rw [c3] at he
  by_cases hfvb : 4294967296 ≤ r3.headD 0
  · rw [nfE.k_intern_fvar.abort1 p n vis ctx fu po pl base nF j kO kL dO dL b _ _ _ r3 m2 hfvb] at he; cases he
    exact absurd Err.cls_abort0 hk0
  rw [nfE.k_intern_fvar.arm1 p n vis ctx fu po pl base nF j kO kL dO dL b _ _ _ r3 m2 hfvb] at he
  have hfvH : H (r3.headD 0) := by
    have : ¬ (4294967296 : Word).toNat ≤ (r3.headD 0).toNat := fun e => hfvb (UInt64.le_iff_toNat_le.mpr e)
    simp only [H]; simpa using this
  obtain ⟨a2, hrun2, hS2, hg2⟩ := internFVar_stage hS1 (base + j) d hd hfv
  have e2 : (internFVarE (base.toNat + j.toNat) (decI d)).run a1 = .ok (decI (r3.headD 0), a2) := by
    simpa [internFVarE, hbj, decE_eq] using hrun2
  obtain ⟨p2, hfvP⟩ := ConRon.Bridge.Inductives.internFVarE_run hC1.check.state
    (ConRon.Bridge.denote_ext hdP c1.ext) e2
  refine ErrClaim.bind_right e2 ?_
  -- the body opened
  cases c4 : callE p n "instantiate1_fast" [CWF, b, r3.headD 0, 0] m2 with
  | error e4 =>
    rw [c4, nfE.k_instantiate1_fast.none] at he; cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) c4
  | ok q4 =>
  obtain ⟨rb, m3⟩ := q4
  obtain ⟨s4, hs4, -, hin⟩ := triple_of_callW (i1F_spec p L.hi1 n ⟨m2, Locals.init []⟩ [CWF, b, r3.headD 0, 0])
    (callW_of_callE c4)
  simp only at hin
  rw [hs4] at hin
  rw [c4, nfE.k_instantiate1_fast.arm1] at he
  obtain ⟨b2, a3, hrun3, hS3, hg3, hb2H, hb2d⟩ := i1F_ok dn vis fe b (r3.headD 0) 0 hb m2 m3 a2 rb hin hS2
  rw [CWF_eq] at hrun3
  have e3 : (instantiate1Fast coreWalkFuel (decI b) (decI (r3.headD 0)) 0).run a2 = .ok (b2, a3) := by
    simpa using hrun3
  have hbP2 : denoteE a2.store (decI b) = some bP := ConRon.Bridge.denote_ext hbP (c1.ext.trans p2.ext)
  obtain ⟨q1, q2, q4, q5, -, q7⟩ := ConRon.Bridge.ExprOps.instantiate1Fast_run p2.ok hfvP
    (by rw [hbP2]; rfl) e3
  have p3 : PStep a2 a3 := PStep.of_caches q1 q2 q4 q5
  have hb2P : denoteE a3.store b2 = some (bP.instantiate1 (.fvar (base.toNat + j.toNat) dP) 0) := q7 _ hbP2
  have hg13 := (hg1.trans hg2).trans hg3
  refine ErrClaim.bind_right e3 ?_
  -- the kind and the walked domain appended
  cases c5 : callE p n "sl_snoc" [kO, kL, r2.headD 0] m3 with
  | error e5 =>
    rw [c5, nfE.k_sl_snoc.none] at he; cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) c5
  | ok q5 =>
  obtain ⟨rk, m4⟩ := q5
  obtain ⟨s5, hs5, -, hs1⟩ := triple_of_callW (slSnoc_specW p R.ha L.nit.hc2 L.nag.hsn n ⟨m3, Locals.init []⟩
    kO kL (r2.headD 0)) (callW_of_callE c5)
  simp only at hs1
  rw [hs5] at hs1
  rw [c5, nfE.k_sl_snoc.arm1] at he
  obtain ⟨hS4, hg4, hk40, hk41, ht4, hw4, hx4⟩ := snocW_words hs1 hS3 (by have := hg13.1; omega)
  have hks4 : KlB m4 (rk.headD 0).toNat (rk.tail.headD 0).toNat (ks ++ [x1.1]) := by
    rw [hk40, hk41]
    exact KlB.snoc ((hks.grow hg13)) hg4 (by omega) hw4 hx4 hk1
  cases c6 : callE p n "sl_snoc" [dO, dL, r2.tail.headD 0] m4 with
  | error e6 =>
    rw [c6, nfE.k_sl_snoc_2.none] at he; cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) c6
  | ok q6 =>
  obtain ⟨rd, m5⟩ := q6
  obtain ⟨s6, hs6, -, hs2'⟩ := triple_of_callW (slSnoc_specW p R.ha L.nit.hc2 L.nag.hsn n ⟨m4, Locals.init []⟩
    dO dL (r2.tail.headD 0)) (callW_of_callE c6)
  simp only at hs2'
  rw [hs6] at hs2'
  rw [c6, nfE.k_sl_snoc_2.arm1] at he
  have hg14 := hg13.trans hg4
  obtain ⟨hrd, hnd5, hg5, -, hl5, ht5⟩ := snocW_decK hs2' hS4.2.2.2.1 hS4.2.2.2.2.2 (by have := hg14.1; omega)
    hnd1H (by rw [decHL_agree (RdS.of_grow hg14) (fun i hi => by omega)]; exact hnd)
  have hS5 := snocW_stage hs2' hS4
  have hg15 := hg14.trans hg5
  have hA5 : AbsOK m5 := snocW_afr hs2' (snocW_afr hs1 (i1F_afr hin (fvinternW_afr hfv hA1)))
  have p23 := p2.trans p3
  have hC5 : StageC dn vis fe env m5 a3 := hC1.of_pstep hS5 hA5 p23
  have hx13 := c1.ext.trans p23.ext
  -- the rest of the fields
  have hbj1 : (base + j + 1).toNat = base.toNat + j.toNat + 1 := by rw [pos2_word_succ hov1, hbj]
  have hj1 : (j + 1).toNat = j.toNat + 1 := word_add_toNat (by have := (base + j + 1).toNat_lt; simp; omega)
  have hnF1 : (nF - 1).toNat = nF' := by rw [pos2_word_pred h0]; omega
  have hb2P' : denoteE a3.store (decI (rb.headD 0)) =
      some (bP.instantiate1 (.fvar (base.toNat + j.toNat) dP) 0) := by
    rw [show (decI (rb.headD 0) : EIdx) = b2 by simpa [decE_eq] using hb2d]; exact hb2P
  have hndP' : Frontend.denoteEList a3.store (nds ++ [decI (r2.tail.headD 0)]) = some (ndsP ++ [v1.2.1]) :=
    ConRon.Bridge.ExprOps.denoteEList_snoc
      (by rw [hnd1]; exact ConRon.Bridge.denote_ext hnd1P p23.ext) _ _
      (ConRon.Bridge.denoteEList_ext hx13 _ _ hndsP)
  cases c7 : callE p n "nest_fields" [vis, ctx, fu, po, pl, base, nF - 1, j + 1, rb.headD 0, r2.tail.tail.headD 0,
      rk.headD 0, rk.tail.headD 0, rd.headD 0, rd.tail.headD 0] m5 with
  | ok q7 => obtain ⟨r7, m7⟩ := q7; rw [c7, nfE.k_nest_fields.arm1] at he; cases he
  | error e7 =>
  rw [c7, nfE.k_nest_fields.none] at he; cases he
  have hcl := hFieldsE m5 a3 ctx fu po pl base (nF - 1) (j + 1) (rb.headD 0) (r2.tail.tail.headD 0) (rk.headD 0)
      (rk.tail.headD 0) (rd.headD 0) (rd.tail.headD 0) c prog x1.2.2 (ks ++ [x1.1]) (nds ++ [decI (r2.tail.headD 0)])
      ctxP progP _ v1.2.2 (ndsP ++ [v1.2.1]) hC5 (hW.grow (hg15.trans (IWGrow.refl _))) (by simpa using hb2H)
      ((hns1.grow (hg2.trans hg3) (Nat.lt_of_le_of_lt hS1.2.1 hS1.2.2.2.1)).grow (hg4.trans hg5)
        (Nat.lt_of_le_of_lt hS3.2.1 hS3.2.2.2.1))
      (hks4.grow hg5) (by rw [hk40, hk41]; have := hg5.1; omega)
      (by rw [hrd]; simpa using hnd5) (by rw [hrd]; simp only [List.headD_cons, List.tail_cons]; omega)
      ((((hP1.fr (fvinternW_mfr hfv)).fr (MFr.ofI1F hin)).fr (snocW_mfr hs1)).fr (snocW_mfr hs2')) hA5
      hc (dCtx_ext _ hx13 _ _ hctx) (dProg_ext hx13 _ _ hprog) hb2P'
      (dState_ext p23.ext _ _ hns1P) hndP'
      (by rw [hj1, show base.toNat + (j.toNat + 1) = base.toNat + j.toNat + 1 by omega]
          exact ConLeche.Expr.WScoped.instantiate1 hw.1 0 hw.2) _ c7
  rw [hnF1, hj1, hb2d, hnd1] at hcl
  exact hcl

end steps

end L.Ind
