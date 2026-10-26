import ConAgua.Verdict.PosE2M

/-!
# The positivity walk's error claims: `nest_cont_new`, `nest_frame` and their leaves
`nest_grow_group`, `nest_group_ctors` (lane `verdicts-b`, helper `ia2`, fork `kn2a`)

The error halves of `newOKC_step` (`PosNew.lean`), `frameOKC_step` (`PosFrame.lean`),
`ggW_ok` and `gcW_ok`, on the generated error models (`PosE2M.lean`).
-/

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dCtx dProg dState dCtx_ext dProg_ext dState_ext dGrp dKey kindOf)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## `nest_group_ctors` -/

/-- **`nest_group_ctors`' error claim** (`gcW_ok`'s hypotheses): a container that is none, or
whose parameter count disagrees, rejects as the twin's `nestGroupCtors` does. -/
theorem ngcE_claim {p : Prog} (L : NbLook p) (hnv : closedNV p _root_.L.Checker.nvFns = true)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis nPc : Word) (k : Nat) :
    ∀ (m : Mem) (a : AState) (off l oo ol : Word) (cs : List NIdx) (out : List (IConstantVal × Nat)),
    StageR dn vis fe m a →
    decHL m off.toNat l.toNat = some cs → (∀ j < l.toNat, off.toNat + j < iwTop m) →
    ol.toNat = out.length → oo.toNat + out.length ≤ iwTop m → CsAt m oo.toNat out (· < iwTop m) →
    ∀ e, ngcE p k m vis nPc off l oo ol = .error e →
      ErrClaim (ConRon.Arena.nestGroupCtors fe nPc.toNat cs out) a e := by
  induction k with
  | zero =>
    intro m a off l oo ol cs out _ _ _ _ _ _ e he
    rw [ngcE.eq_1] at he; cases he; exact ErrClaim.of_cls0 Err.cls_outOfFuel
  | succ k ih =>
    intro m a off l oo ol cs out hS hcs' hcb hol hob hout e he
    by_cases hl0 : l = 0
    · rw [ngcE.arm1 p k m vis nPc off l oo ol hl0] at he; cases he
    rw [ngcE.arm2 p k m vis nPc off l oo ol hl0] at he
    have hl : l.toNat ≠ 0 := fun e => hl0 (UInt64.toNat_inj.mp (by simpa using e))
    obtain ⟨l', hl'⟩ : ∃ l', l.toNat = l' + 1 := ⟨l.toNat - 1, by omega⟩
    have hcs2 := hcs'
    simp only [decHL, hl', hslice?_succ, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hcs2
    obtain ⟨c, hc, cs', hcs'', rfl⟩ := hcs2
    obtain ⟨hcH, hcd⟩ := rd_iwH0E (m := m) (o := off) (k := IdxKind.name) (by simpa [iwH, iwA] using hc)
    have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
    have hoff1 : (off + 1).toNat = off.toNat + 1 :=
      word_add_toNat (show off.toNat + 1 < 2 ^ 64 by have := hcb 0 (by omega); omega)
    have hl1 : (l - 1).toNat = l' := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
    cases h1 : callE p k "nest_container" [vis, rdW (m.arr64 IW) off] m with
    | error e1 =>
      rw [h1, ngcE.k_nest_container.none] at he; cases he
      exact ErrClaim.of_callE_nv hnv (by decide +kernel) h1
    | ok q1 =>
    obtain ⟨r1, m1⟩ := q1
    obtain ⟨s1, hs1, -, hnt⟩ := triple_of_callW (nt_spec' p L.nt k ⟨m, Locals.init []⟩ vis _)
      (callW_of_callE h1)
    simp only at hnt
    rw [hs1] at hnt
    cases k with
    | zero => simp [ntWf] at hnt
    | succ k =>
    simp only [ntWf] at hnt
    obtain ⟨x, a1, hrun1, hS1, hg1, hnc⟩ := ntW_ok dn fe vis _ hcH k m m1 a r1 hnt hS
    rw [hcd] at hrun1
    rw [h1] at he
    simp only [ConRon.Arena.nestGroupCtors.eq_2]
    refine ErrClaim.bind_right hrun1 ?_
    cases x with
    | none =>
      have h0 : r1.headD 0 = 0 := hnc
      rw [ngcE.k_nest_container.abort1 p _ vis nPc off l oo ol r1 m1 h0] at he; cases he
      exact ErrClaim.fail _ _ (by decide)
    | some pc =>
    obtain ⟨nPc2, ctors⟩ := pc
    obtain ⟨h0, h1', h3, h2b, hcs3⟩ := hnc
    have hne0 : r1.headD 0 ≠ 0 := by rw [h0]; decide
    by_cases hbad : r1.tail.headD 0 ≠ nPc ∧ r1.tail.tail.tail.headD 0 ≠ 0
    · rw [ngcE.k_nest_container.abort2 p _ vis nPc off l oo ol r1 m1 hne0 hbad] at he; cases he
      have hneq : nPc2 ≠ nPc.toNat := fun e => hbad.1 (UInt64.toNat_inj.mp (by rw [h1', e]))
      have hlen : ctors.length ≠ 0 := by
        intro e; apply hbad.2; apply UInt64.toNat_inj.mp; rw [h3, e]; rfl
      have hc : (!(nPc2 == nPc.toNat || ctors.length == 0)) = true := by
        simp [hneq, hlen]
      show ErrClaim (if (!(nPc2 == nPc.toNat || ctors.length == 0)) = true then _ else _) a1 _
      rw [if_pos hc]
      exact ErrClaim.fail _ _ (by decide)
    rw [ngcE.k_nest_container.arm1 p _ vis nPc off l oo ol r1 m1 hne0 hbad] at he
    have hchk : (nPc2 == nPc.toNat || ctors.length == 0) = true := by
      by_cases hp1 : r1.tail.headD 0 = nPc
      · rw [← h1', hp1]; simp
      · have : r1.tail.tail.tail.headD 0 = 0 := by
          by_cases hh : r1.tail.tail.tail.headD 0 = 0
          · exact hh
          · exact absurd ⟨hp1, hh⟩ hbad
        have : ctors.length = 0 := by rw [← h3, this]; rfl
        simp [this]
    show ErrClaim (if (!(nPc2 == nPc.toNat || ctors.length == 0)) = true then _ else _) a1 _
    rw [hchk]
    simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    cases h2 : callE p (k + 1) "sl_append" [oo, ol, r1.tail.tail.headD 0, r1.tail.tail.tail.headD 0] m1 with
    | error e2 =>
      rw [h2, ngcE.k_sl_append.none] at he; cases he
      exact ErrClaim.of_callE_nv hnv (by decide +kernel) h2
    | ok q2 =>
    obtain ⟨r2, m2⟩ := q2
    obtain ⟨s2, hs2, -, hap⟩ := triple_of_callW (slAppend_specW p L.nt.ha L.nit.hc2 L.hap (k + 1)
      ⟨m1, Locals.init []⟩ _ _ _ _) (callW_of_callE h2)
    simp only at hap
    rw [hs2] at hap
    rw [h2, ngcE.k_sl_append.arm1] at he
    obtain ⟨hS2, hg2, hr20, hr21, ht2, hw1, hw2⟩ := appendW_stage hap hS1 (by have := hg1.1; omega)
      (by rw [h3]; exact h2b)
    rw [h3] at hr21 ht2 hw2
    have hcsA : CsAt m2 (r2.headD 0).toNat (out ++ ctors) (· < iwTop m2) := by
      intro i hi
      rw [hr20]
      by_cases hio : i < out.length
      · obtain ⟨w, hw, hc'⟩ := hout i hio
        refine ⟨w, ?_, ?_⟩
        · rw [hw1 i (by omega), hg1.2.2.1 _ (by omega)]; exact hw
        · rw [List.getElem_append_left hio]; exact (hc'.grow hg1).grow hg2
      · simp only [List.length_append] at hi
        obtain ⟨w, hw, hc'⟩ := hcs3 (i - out.length) (by omega)
        refine ⟨w, ?_, ?_⟩
        · have := hw2 (i - out.length) (by omega)
          rw [show iwTop m1 + ol.toNat + (i - out.length) = iwTop m1 + i by omega] at this
          rw [this]; exact hw
        · rw [List.getElem_append_right (by omega)]; exact hc'.grow hg2
    cases h3' : ngcE p (k + 1) m2 vis nPc (off + 1) (l - 1) (r2.headD 0) (r2.tail.headD 0) with
    | ok q3 => obtain ⟨r3, m3⟩ := q3; rw [h3', ngcE.k_nest_group_ctors.arm1] at he; cases he
    | error e3 =>
    rw [h3', ngcE.k_nest_group_ctors.none] at he; cases he
    exact ih m2 a1 (off + 1) (l - 1) (r2.headD 0) (r2.tail.headD 0) cs' (out ++ ctors) hS2
        (by rw [hoff1, hl1, decHL_agree (RdS.of_grow (hg1.trans hg2)) (fun j hj => by
              have := hcb (j + 1) (by omega); omega)]
            simpa [decHL] using hcs'')
        (fun j hj => by rw [hoff1, hl1] at *; have := hcb (j + 1) (by omega); have := hg1.1; have := hg2.1; omega)
        (by rw [hr21]; simp [hol]) (by rw [hr20]; simp; omega) hcsA _ h3'

/-! ## `nest_grow_group` -/

/-- **`nest_grow_group`'s error claim** (`ggW_ok`'s hypotheses at `realCall p`, the invariant
`StageC ∧ AbsOK ∧ Ext a0` of `newOKC_step`): only `nest_inst_type` (`NitE`) claims. -/
theorem nggE_claim {p : Prog} (L : NbLook p) (hIlpf : IlpfF p) (hcl : CoreStageClosed p) (hLC : LvlCacheProg p)
    (hnv : closedNV p _root_.L.Checker.nvFns = true)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) {env : ConLeche.Env}
    (hNit : NitE p dn vis fe env) (ctx hi us dO dL : Word) (HI : Nat) (hHI : hi.toNat = HI) (c : NestCtx)
    (ds : List EIdx) (hus : H us) (a0 : AState) (csA : List NIdx) {ctxP : ConLeche.NestCtx}
    {usP : List ConLeche.Level} {dsP : List ConLeche.Expr} {matesP : List ConLeche.Name}
    (hc : ConLeche.NestCtxOk ctxP) (hctx : dCtx a0.store env.find? c = some ctxP)
    (husP : denoteLs a0.store.lss (decI us) = some usP) (hdsP : Frontend.denoteEList a0.store ds = some dsP)
    (hmates : Frontend.denoteNList a0.store.ns csA = some matesP) (k : Nat) :
    ∀ (m : Mem) (a : AState) (cO cL gO gL : Word) (cs : List NIdx) (grp : List (NIdx × EIdx)),
    StageC dn vis fe env m a → AbsOK m → ConRon.Arena.Ext a0.store a.store → (∀ n ∈ cs, n ∈ csA) →
    UCtx dn vis fe m ctx c → decHL m dO.toNat dL.toNat = some ds → dO.toNat + dL.toNat ≤ iwTop m →
    decHL m cO.toNat cL.toNat = some cs → (∀ j < cL.toNat, cO.toNat + j < iwTop m) →
    gL.toNat = grp.length → gO.toNat + grp.length ≤ iwTop m → GrpAt m gO.toNat grp → PosMR m →
    ∀ e, nggE p k m vis ctx hi us dO dL cO cL gO gL = .error e →
      ErrClaim (ConRon.Arena.nestGrowGroup fe c HI (decI us) ds cs grp) a e := by
  have R := L.ct.cr.rx
  induction k with
  | zero =>
    intro m a cO cL gO gL cs grp _ _ _ _ _ _ _ _ _ _ _ _ _ e he
    rw [nggE.eq_1] at he; cases he; exact ErrClaim.of_cls0 Err.cls_outOfFuel
  | succ k ih =>
    intro m a cO cL gO gL cs grp hC hA hx0 hcsA hU hds hdb hcs hcb hgl hgb hgrp hP e he
    have hS := hC.stage
    have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
    by_cases hc0 : cL = 0
    · rw [nggE.arm1 p k m vis ctx hi us dO dL cO cL gO gL hc0] at he; cases he
    rw [nggE.arm2 p k m vis ctx hi us dO dL cO cL gO gL hc0] at he
    have hlz : cL.toNat ≠ 0 := fun e => hc0 (UInt64.toNat_inj.mp (by simpa using e))
    obtain ⟨l', hl'⟩ : ∃ l', cL.toNat = l' + 1 := ⟨cL.toNat - 1, by omega⟩
    have hcs2 := hcs
    simp only [decHL, hl', hslice?_succ, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hcs2
    obtain ⟨n0, hn0, cs', hcs', rfl⟩ := hcs2
    obtain ⟨hcH, hcd⟩ := rd_iwH0E (m := m) (o := cO) (k := IdxKind.name) (by simpa [iwH, iwA] using hn0)
    generalize hcw : rdW (m.arr64 IW) cO = cw at he hcH hcd
    have hcO1 : (cO + 1).toNat = cO.toNat + 1 :=
      word_add_toNat (show cO.toNat + 1 < 2 ^ 64 by have := hcb 0 (by omega); omega)
    have hcL1 : (cL - 1).toNat = l' := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
    -- the key record
    cases h1 : callE p k "rec4" [cw, us, dO, dL] m with
    | error e1 =>
      rw [h1, nggE.k_rec4.none] at he; cases he
      exact ErrClaim.of_callE_nv hnv (by decide +kernel) h1
    | ok q1 =>
    obtain ⟨rk, m1⟩ := q1
    obtain ⟨s1, hs1, -, hk⟩ := triple_of_callW (posRec4_specW p R.ha R.h4 k ⟨m, Locals.init []⟩ cw us dO dL)
      (callW_of_callE h1)
    simp only at hk
    rw [hs1] at hk
    rw [h1, nggE.k_rec4.arm1] at he
    generalize hkey : rk.headD 0 = key at hk he
    obtain ⟨hS1, hg1, hkq, ht1, hget1⟩ := posRecW_stage hk hS (by simp)
    have hA1 : AbsOK m1 := hA.iw (posRecW_iwFr hk)
    have hC1 : StageC dn vis fe env m1 a := hC.of_pstep hS1 hA1 (PStep.refl hC.check.state)
    simp only [List.length_cons, List.length_nil] at ht1
    have hds1 : decHL m1 dO.toNat dL.toNat = some ds := by
      rw [decHL_agree (RdS.of_grow hg1) (fun j hj => by omega)]; exact hds
    have hdk : decNK m1 key.toNat = some ⟨n0, decI us, ds⟩ := by
      rw [← hcd]
      exact decNK_of_words (by simpa using hget1 0 (by simp)) hcH (by simpa using hget1 1 (by simp)) hus
        (by simpa using hget1 2 (by simp)) (by simpa using hget1 3 (by simp)) hds1
    have hkin : NKIn m1 key.toNat (· < iwTop m1) := by
      refine ⟨fun j hj => by omega, fun o l ho hl j hj => ?_⟩
      have e2 : o = dO.toNat := by
        have h' : (m1.arr64 IW)[key.toNat + 2]? = some dO := by simpa using hget1 2 (by simp)
        have : iwN m1 (key.toNat + 2) = some dO.toNat := by simp [iwN, nat?, iwA, h']
        rw [this] at ho; exact (Option.some.inj ho).symm
      have e3 : l = dL.toNat := by
        have h' : (m1.arr64 IW)[key.toNat + 3]? = some dL := by simpa using hget1 3 (by simp)
        have : iwN m1 (key.toNat + 3) = some dL.toNat := by simp [iwN, nat?, iwA, h']
        rw [this] at hl; exact (Option.some.inj hl).symm
      subst e2 e3; omega
    have hksl : NKSl m1 key := by
      have htop1 : iwTop m1 < 2 ^ 64 := Nat.lt_of_le_of_lt hS1.2.1 hS1.2.2.2.1
      have e2 : (key + 2).toNat = key.toNat + 2 := word_add_toNat (by simp; omega)
      have e3 : (key + 3).toNat = key.toNat + 3 := word_add_toNat (by simp; omega)
      unfold NKSl
      have r2 : rdW (m1.arr64 IW) (key + 2) = dO := by
        simp only [rdW, e2]; rw [show (m1.arr64 IW)[key.toNat + 2]? = some dO by simpa using hget1 2 (by simp)]; rfl
      have r3 : rdW (m1.arr64 IW) (key + 3) = dL := by
        simp only [rdW, e3]; rw [show (m1.arr64 IW)[key.toNat + 3]? = some dL by simpa using hget1 3 (by simp)]; rfl
      rw [r2, r3]; omega
    have hP1 : PosMR m1 := hP.fr (posRecW_mfr hk)
    obtain ⟨n0P, hn0P⟩ := denoteNList_memN hmates n0 (hcsA n0 List.mem_cons_self)
    have hkeyP : dKey a.store ⟨n0, decI us, ds⟩ = some ⟨n0P, usP, dsP⟩ := by
      simp [ConRon.Bridge.Inductives.dKey, ConRon.Bridge.denoteN_ext hn0P hx0,
        ConRon.Bridge.denoteLs_ext husP hx0, ConRon.Bridge.denoteEList_ext hx0 _ _ hdsP]
    have hctxa : dCtx a.store env.find? c = some ctxP := dCtx_ext _ hx0 _ _ hctx
    rw [ConRon.Arena.nestGrowGroup]
    -- `nest_inst_type`
    cases h2 : callE p k "nest_inst_type" [vis, ctx, hi, key] m1 with
    | error e2 =>
      rw [h2, nggE.k_nest_inst_type.none] at he; cases he
      exact ErrClaim.bind_left (hNit k m1 a ctx hi key HI c _ ctxP _ hC1 hA1 hHI (hU.grow hg1) hdk hkin hksl
        hP1 hctxa hkeyP _ h2)
    | ok q2 =>
    obtain ⟨r2, m2⟩ := q2
    obtain ⟨s2, hs2, -, hnit⟩ := triple_of_callW
      (nestInstType_spec' p L.nit (realCall p) (realCall_spec p) k ⟨m1, Locals.init []⟩ vis ctx hi key)
      (callW_of_callE h2)
    simp only at hnit
    rw [hs2] at hnit
    rw [h2, nggE.k_nest_inst_type.arm1] at he
    cases k with
    | zero => simp [nitWf] at hnit
    | succ k =>
    simp only [nitWf] at hnit
    obtain ⟨x, a2, hrun2, hS2, hg2, hx1, htH, htd, hP2, -, hA2⟩ := nitW_ok k dn fe vis ctx hi HI hHI c m1 m2 a key
      _ _ (realCall p) (IlpRd.realC hIlpf hC1) (IlpFr.real hIlpf) _
      (nitLe_realC hcl hLC k _ _ key c _ hC1 hA1 hctxa hkeyP) hnit hS1
      (hU.grow hg1) hdk hkin hksl hP1
    obtain ⟨c4, -⟩ := ConRon.Bridge.Inductives.nestInstType_spec hc c HI ⟨n0, decI us, ds⟩
      ⟨n0P, usP, dsP⟩ a a2 x hC1.check ⟨hctxa, hkeyP⟩ hrun2
    have hC2 : StageC dn vis fe env m2 a2 := hC1.of_cstep hS2 hA2 c4
    have hx2 := hx0.trans c4.ext
    refine ErrClaim.bind_right hrun2 ?_
    obtain ⟨x1, x2⟩ := x
    simp only at htd ⊢
    -- the pair record and the snoc
    cases h3 : callE p (k + 1) "rec2" [cw, r2.tail.headD 0] m2 with
    | error e3 =>
      rw [h3, nggE.k_rec2.none] at he; cases he
      exact ErrClaim.of_callE_nv hnv (by decide +kernel) h3
    | ok q3 =>
    obtain ⟨rp, m3⟩ := q3
    obtain ⟨s3, hs3, -, hpr⟩ := triple_of_callW (posRec2_specW p R.ha R.h2 (k + 1) ⟨m2, Locals.init []⟩ _ _)
      (callW_of_callE h3)
    simp only at hpr
    rw [hs3] at hpr
    rw [h3, nggE.k_rec2.arm1] at he
    generalize hpw : rp.headD 0 = pw at hpr he
    obtain ⟨hS3, hg3, hpq, ht3, hget3⟩ := posRecW_stage hpr hS2 (by simp)
    have hA3 : AbsOK m3 := hA2.iw (posRecW_iwFr hpr)
    simp only [List.length_cons, List.length_nil] at ht3
    have hg13 := (hg1.trans hg2).trans hg3
    cases h4 : callE p (k + 1) "sl_snoc" [gO, gL, pw] m3 with
    | error e4 =>
      rw [h4, nggE.k_sl_snoc.none] at he; cases he
      exact ErrClaim.of_callE_nv hnv (by decide +kernel) h4
    | ok q4 =>
    obtain ⟨r4, m4⟩ := q4
    obtain ⟨s4, hs4, -, hsn⟩ := triple_of_callW (slSnoc_specW p R.ha L.nit.hc2 L.nag.hsn (k + 1)
      ⟨m3, Locals.init []⟩ _ _ _) (callW_of_callE h4)
    simp only at hsn
    rw [hs4] at hsn
    rw [h4, nggE.k_sl_snoc.arm1] at he
    obtain ⟨hS4, hg4, hr40, hr41, ht4, hw4, hx4⟩ := snocW_words hsn hS3 (by have := hg13.1; omega)
    have hA4 : AbsOK m4 := hA3.iw (snocW_iwFr hsn)
    have hC4 : StageC dn vis fe env m4 a2 := hC2.of_pstep hS4 hA4 (PStep.refl hC2.check.state)
    have hg14 := hg13.trans hg4
    have hgrp4 : GrpAt m4 (r4.headD 0).toNat (grp ++ [(n0, x2)]) := by
      rw [hr40]
      intro i hi
      simp only [List.length_append, List.length_cons, List.length_nil] at hi
      by_cases hio : i < grp.length
      · obtain ⟨w, c1, t1, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hgrp i hio
        refine ⟨w, c1, t1, ?_, by have := hg14.1; omega, by rw [hg14.2.2.1 _ (by omega)]; exact h3, h4,
          by rw [List.getElem_append_left hio]; exact h5, by rw [hg14.2.2.1 _ (by omega)]; exact h6, h7,
          by rw [List.getElem_append_left hio]; exact h8⟩
        rw [hw4 i (by omega), hg13.2.2.1 _ (by omega)]; exact h1
      · have hie : i = grp.length := by omega
        subst hie
        refine ⟨pw, cw, r2.tail.headD 0, ?_, ?_, ?_, hcH, ?_, ?_, htH, ?_⟩
        · rw [← hgl]; exact hx4
        · have := hg4.1; omega
        · rw [hg4.2.2.1 _ (by omega)]; simpa using hget3 0 (by simp)
        · simp [hcd]
        · rw [hg4.2.2.1 _ (by omega)]; simpa using hget3 1 (by simp)
        · simpa using htd
    cases h5 : nggE p (k + 1) m4 vis ctx hi us dO dL (cO + 1) (cL - 1) (r4.headD 0) (r4.tail.headD 0) with
    | ok q5 => obtain ⟨r5, m5⟩ := q5; rw [h5, nggE.k_nest_grow_group.arm1] at he; cases he
    | error e5 =>
    rw [h5, nggE.k_nest_grow_group.none] at he; cases he
    exact ih m4 a2 (cO + 1) (cL - 1) _ _ cs' (grp ++ [(n0, x2)]) hC4 hA4 hx2
      (fun n hn => hcsA n (List.mem_cons_of_mem _ hn)) (hU.grow hg14)
      (by rw [decHL_agree (RdS.of_grow hg14) (fun j hj => by omega)]; exact hds)
      (by have := hg14.1; omega)
      (by rw [hcO1, hcL1, decHL_agree (RdS.of_grow hg14) (fun j hj => by have := hcb (j + 1) (by omega); omega)]
          simpa [decHL] using hcs')
      (fun j hj => by rw [hcO1, hcL1] at *; have := hcb (j + 1) (by omega); have := hg14.1; omega)
      (by rw [hr41]; simp [hgl]) (by rw [hr40]; simp; omega) hgrp4 ((hP2.fr (posRecW_mfr hpr)).fr (snocW_mfr hsn))
      _ h5

end L.Ind
