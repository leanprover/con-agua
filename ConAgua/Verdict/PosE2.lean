import ConAgua.Verdict.PosE2M
import ConAgua.Verdict.DeclValE

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

/-! ## `nest_frame` -/

/-- The twin's runs agree: an error claim moves along an equation of runs. -/
theorem ErrClaim.of_run_eq' {α β : Type} {T : AM α} {T' : AM β} {a a' : AState} {e : Err}
    (h : ∀ ce, T'.run a' = .error ce → T.run a = .error ce) (h' : ErrClaim T' a' e) : ErrClaim T a e :=
  fun hk => by
    obtain ⟨ce, hce, hc⟩ := h' hk
    exact ⟨ce, h ce hce, hc⟩

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
variable {p : Prog} (LK : NbLook p) (hq : KnotStageProg p) (hnv : closedNV p _root_.L.Checker.nvFns = true)
  (hcE : CoreStubsE p) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
  {env : ConLeche.Env} (henv : ConLeche.EnvWF env)

include LK hq hnv hcE henv in
/-- **`nest_frame`'s error claim at L fuel `n + 1`** (`frameOKC_step`'s proof on the model `nfrE`):
`infer_type_core` by `CoreStubsE`, `nest_group_ctors` by `ngcE_claim`, `nest_ctors` by the block's
`CtorsOKE` at `n`. -/
theorem frameOKE_step (n : Nat) (hn : n ≤ 2 ^ 62) (ihC : NbOKC p dn vis fe env n)
    (ihE : NbOKE p dn vis fe env n) : FrameOKE p dn vis fe env (n + 1) := by
  obtain ⟨-, -, -, -, -, -, -, hCtors, -, -, -⟩ := ihC
  obtain ⟨-, -, -, -, -, -, -, eCtors, -, -, -⟩ := ihE
  have R := LK.ct.cr.rx
  have SP := nbSpec_all LK (realCall p) (realCall_spec p) n
  intro m a ctx fu po pl hi us dO dL nPc gO gL ns c prog ds grp NS ctxP progP usP dsP grpP nsP hC hW hhi hus
    hds hdsb hgl hgb hgrp hns hP hA hc hctx hprog husP hdsP hgrpP hnsP hwds hwg er he
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  replace he := triple_of_callE_err (nfrE_spec p LK.pframe (n + 1) ⟨m, Locals.init []⟩ vis ctx fu po pl hi us dO dL
    nPc gO gL ns) he (Err.code_ne_of_cls hk0)
  simp only at he
  have hS := hC.stage
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  obtain ⟨-, -, hfind, -, -, -⟩ := ConRon.Bridge.Inductives.dCtx_fields hctx
  -- the group's head name, as `frameOKC_step`'s `nbFrameK1` argument
  obtain ⟨rn, m1, hX, he⟩ : ∃ rn m1,
      (if gL = 0 then naF m [] else some ([rdW (m.arr64 IW) (rdW (m.arr64 IW) gO)], m)) = some (rn, m1) ∧
      nfrE.j1 p n vis ctx fu po pl hi us dO dL nPc gO gL ns (rn.headD 0) m1 = .error er := by
    by_cases h0 : gL = 0
    · rw [nfrE.arm1 p n m vis ctx fu po pl hi us dO dL nPc gO gL ns h0] at he
      cases h1 : callE p n "intern_nanon" [] m with
      | error e1 =>
        rw [h1, nfrE.k_intern_nanon.none] at he; cases he
        exact absurd (callE_nv hnv (by decide +kernel) n [] m h1) hk0
      | ok q1 =>
      obtain ⟨rn, m1⟩ := q1
      obtain ⟨s1, hs1, -, hna⟩ := triple_of_callW (naF_spec p LK.na n ⟨m, Locals.init []⟩ []) (callW_of_callE h1)
      simp only at hna
      rw [hs1] at hna
      rw [h1, nfrE.k_intern_nanon.arm1] at he
      exact ⟨rn, m1, by rw [if_pos h0]; exact hna, he⟩
    · rw [nfrE.arm2 p n m vis ctx fu po pl hi us dO dL nPc gO gL ns h0] at he
      exact ⟨[rdW (m.arr64 IW) (rdW (m.arr64 IW) gO)], m, by rw [if_neg h0], he⟩
  have hhn : (if gL = 0 then naF m [] else some ([rdW (m.arr64 IW) (rdW (m.arr64 IW) gO)], m)) =
        none ∨ ∃ (rn : List Word) (m1 : Mem) (a1 : AState),
      (if gL = 0 then naF m [] else some ([rdW (m.arr64 IW) (rdW (m.arr64 IW) gO)], m)) =
        some (rn, m1) ∧ StageR dn vis fe m1 a1 ∧ IWGrow m m1 ∧ MFr [] [] m m1 ∧ AFr m m1 ∧ H (rn.headD 0) ∧
      (nestHeadT grp).run a = .ok (decI (rn.headD 0), a1) := by
    by_cases h0 : gL = 0
    · rw [if_pos h0]
      have : grp = [] := List.eq_nil_of_length_eq_zero (by rw [← hgl, h0]; rfl)
      subst this
      rcases hst : naF m [] with _ | ⟨rn, m1⟩; · exact Or.inl rfl
      obtain ⟨x, a1, hrun, hS1, hg1, hxH, hxd⟩ := naF_ok dn vis fe m m1 a rn hst hS
      exact Or.inr ⟨rn, m1, a1, rfl, hS1, hg1, MFr.of_frame (naF_frame hst) (by simp [NAREC, NASLOT]) (by simp),
        naF_afr hst, hxH, by rw [hxd]; exact hrun⟩
    · rw [if_neg h0]
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
  rw [nfrE.j1.arm1 p n vis ctx fu po pl hi us dO dL nPc gO gL ns _ m1 hrnb] at he
  refine ErrClaim.of_run_eq' (fun ce h => by rw [nestFrame_run hrun1]; exact h) ?_
  unfold nestFrameRest
  -- the instantiation `hn.{us} ds`, typed
  cases h2 : callE p n "intern_const" [rn.headD 0, us] m1 with
  | error e2 =>
    rw [h2, nfrE.k_intern_const.none] at he; cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h2
  | ok q2 =>
  obtain ⟨rc2, m2⟩ := q2
  obtain ⟨s2, hs2, -, hic⟩ := triple_of_callW (internConst_spec p R.cf R.cp R.ci n ⟨m1, Locals.init []⟩ _ _)
    (callW_of_callE h2)
  simp only at hic
  rw [hs2] at hic
  rw [h2] at he
  generalize hhc : rc2.headD 0 = hc' at hic he
  by_cases hcb : 4294967296 ≤ hc'
  · have := nfrE.k_intern_const.abort1 p n vis ctx fu po pl hi us dO dL nPc gO gL ns rc2 m2 (by rw [hhc]; exact hcb)
    rw [this] at he; cases he; exact absurd rfl hk0
  rw [nfrE.k_intern_const.arm1 p n vis ctx fu po pl hi us dO dL nPc gO gL ns rc2 m2 (by rw [hhc]; exact hcb), hhc] at he
  have hcH : H hc' := by
    have : ¬ (4294967296 : Word).toNat ≤ hc'.toNat := fun e => hcb (UInt64.le_iff_toNat_le.mpr e)
    simp only [H]; simpa using this
  obtain ⟨a2, hrun2, hS2, hg2⟩ := internConst_stage hS1 (rn.headD 0) us hrnH hus hic
  have e2 : (internConstE (decI (rn.headD 0)) (decI us)).run a1 = .ok (decI hc', a2) := hrun2
  obtain ⟨p2, hc2⟩ := ConRon.Bridge.Inductives.internConstE_run p1.ok hhn'
    (ConRon.Bridge.denoteLs_ext husP p1.ext) e2
  have hA2 : AbsOK m2 := ceinternW_afr hic hA1
  have hg12 := hg1.trans hg2
  refine ErrClaim.bind_right e2 ?_
  cases h3 : callE p n "mk_app_n_f" [hc', dO, dL] m2 with
  | error e3 =>
    rw [h3, nfrE.k_mk_app_n_f.none] at he; cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h3
  | ok q3 =>
  obtain ⟨ra, m3⟩ := q3
  obtain ⟨s3, hs3, -, hma⟩ := triple_of_callW (mknF_spec p LK.nt.ad n ⟨m2, Locals.init []⟩ _) (callW_of_callE h3)
  simp only at hma
  rw [hs3] at hma
  rw [h3, nfrE.k_mk_app_n_f.arm1] at he
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
  refine ErrClaim.bind_right hrun3 ?_
  cases h4 : callE p n "infer_type_core" [vis, hi, ra.headD 0] m3 with
  | error e4 =>
    rw [h4, nfrE.k_infer_type_core.none] at he; cases he
    refine ErrClaim.bind_left ?_
    rw [← happd]
    exact hcE.inferTypeCore n hn hC3.stageT hi (ra.headD 0) happH _ h4
  | ok q4 =>
  obtain ⟨rt, m4⟩ := q4
  have hit : realCall p n "infer_type_core" [vis, hi, ra.headD 0] m3 = some (rt, m4) := callW_of_callE h4
  rw [h4, nfrE.k_infer_type_core.arm1] at he
  obtain ⟨ty, a4, hrun4, hC4, hg4, -, hA4, c4, -⟩ :=
    inferC_rsim hq henv n hn hC3 hA3 hi (ra.headD 0) happH (by rw [happd]; exact happ) hwapp _ hit
  dsimp only at hC4 hg4 hA4
  have hS4 := hC4.stage
  have hg14 := (hg12.trans hg3).trans hg4
  have c3 := p13.toCore hC.check
  rw [happd] at hrun4
  refine ErrClaim.bind_right hrun4 ?_
  -- the stack grown and the names
  cases h5 : callE p n "nest_frame_grp" [hi, us, dO, dL, gO, gL, po, pl, 0, 0] m4 with
  | error e5 =>
    rw [h5, nfrE.k_nest_frame_grp.none] at he; cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h5
  | ok q5 =>
  obtain ⟨r5, m5⟩ := q5
  obtain ⟨s5, hs5, -, hfg⟩ := triple_of_callW (nestFrameGrp_spec p R.ha LK.nit.hc2 R.h2 R.h4 LK.nag.hsn LK.hfg n
    ⟨m4, Locals.init []⟩ hi us dO dL gO gL po pl 0 0) (callW_of_callE h5)
  simp only at hfg
  rw [hs5] at hfg
  rw [h5, nfrE.k_nest_frame_grp.arm1] at he
  generalize hrp : [r5.headD 0, r5.tail.headD 0, r5.tail.tail.headD 0, r5.tail.tail.tail.headD 0] = rp at hfg
  have e0 : r5.headD 0 = rp.headD 0 := by rw [← hrp]; rfl
  have e1 : r5.tail.headD 0 = rp.tail.headD 0 := by rw [← hrp]; rfl
  have e2' : r5.tail.tail.headD 0 = rp.tail.tail.headD 0 := by rw [← hrp]; rfl
  have e3 : r5.tail.tail.tail.headD 0 = rp.tail.tail.tail.headD 0 := by rw [← hrp]; rfl
  rw [e0, e1, e2', e3] at he
  obtain ⟨hS5, hg5, hP5, hN5, hNb5⟩ := fgW_ok dn vis fe hi us dO dL ds hus n m4 m5 a4 gO gL po pl 0 0 grp prog [] rp
    hfg hS4 (hds.grow (OMono.decHL _ _) hg14) hgl (by have := hg14.1; omega) (hgrp.grow hgb hg14)
    (hW.hs.grow hg14) (by simp [decHL, hslice?]) (by simp)
  simp only [List.nil_append] at hP5 hN5
  have hx04 := c3.ext.trans c4.ext
  have hgrp4 := ConRon.Bridge.Inductives.dGrp_ext hx04 _ _ hgrpP
  dsimp only
  -- the group's constructors
  cases h6 : callE p n "nest_group_ctors" [vis, nPc, rp.tail.tail.headD 0, rp.tail.tail.tail.headD 0, 0, 0] m5 with
  | error e6 =>
    rw [h6, nfrE.k_nest_group_ctors.none] at he; cases he
    have hE := triple_of_callE_err (ngcE_spec p LK.hgc n ⟨m5, Locals.init []⟩ vis nPc _ _ 0 0) h6
      (Err.code_ne_of_cls hk0)
    simp only at hE
    exact ErrClaim.bind_left (ngcE_claim LK hnv dn fe vis nPc n m5 a4 _ _ 0 0 (grp.map (·.1)) [] hS5 hN5
      (fun j hj => by omega) (by simp) (by simp) (fun i hi => by simp at hi) _ hE)
  | ok q6 =>
  obtain ⟨r6, m6⟩ := q6
  obtain ⟨s6, hs6, -, hgc⟩ := triple_of_callW (nestGroupCtors_spec p LK.nt LK.nit.hc2 LK.hap LK.hgc n
    ⟨m5, Locals.init []⟩ vis nPc _ _ 0 0) (callW_of_callE h6)
  simp only at hgc
  rw [hs6] at hgc
  rw [h6, nfrE.k_nest_group_ctors.arm1] at he
  generalize hrc : [r6.headD 0, r6.tail.headD 0] = rc at hgc
  have f0 : r6.headD 0 = rc.headD 0 := by rw [← hrc]; rfl
  have f1 : r6.tail.headD 0 = rc.tail.headD 0 := by rw [← hrc]; rfl
  rw [f0, f1] at he
  obtain ⟨ctors, a6, hrun6, hS6, hg6, hcl6, hcb6, hcs6⟩ := gcW_ok dn fe vis nPc n m5 m6 a4 _ _ 0 0 (grp.map (·.1)) []
    rc hgc hS5 hN5 (fun j hj => by omega) (by simp) (by simp) (fun i hi => by simp at hi)
  obtain ⟨p5, vc, hvc, -, hvcl⟩ := ConRon.Bridge.Inductives.nestGroupCtors_spec ctxP hfind hc nPc.toNat _ _ [] []
    a4 a6 ctors hC4.check.state ⟨hC4.check.ienv.toS, ConRon.Bridge.Inductives.dGrp_names hgrp4, rfl⟩ hrun6
  simp only [List.nil_append] at hvc
  refine ErrClaim.bind_right hrun6 ?_
  -- the holes
  have hg46 := hg5.trans hg6
  cases h7 : callE p n "nest_frame_holes" [hi, gO, gL, 0, 0] m6 with
  | error e7 =>
    rw [h7, nfrE.k_nest_frame_holes.none] at he; cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h7
  | ok q7 =>
  obtain ⟨r7, m7⟩ := q7
  obtain ⟨s7, hs7, -, hfh⟩ := triple_of_callW (nestFrameHoles_spec p R.ha LK.nit.hc2 LK.nag.hsn R.hl.hff R.hl.hfp
    R.hl.hif LK.hfh n ⟨m6, Locals.init []⟩ hi gO gL 0 0) (callW_of_callE h7)
  simp only at hfh
  rw [hs7] at hfh
  rw [h7] at he
  generalize hrh : [r7.headD 0, r7.tail.headD 0] = rh at hfh
  have g0 : r7.headD 0 = rh.headD 0 := by rw [← hrh]; rfl
  have g1 : r7.tail.headD 0 = rh.tail.headD 0 := by rw [← hrh]; rfl
  obtain ⟨holes, a7, hrun7, hS7, hg7, hH7, hHb7⟩ := fhW_ok dn vis fe n m6 m7 a6 hi gO gL 0 0 grp [] rh hfh hS6 hgl
    (by have := (hg14.trans hg46).1; omega) (hgrp.grow hgb (hg14.trans hg46)) (by simp [decHL, hslice?]) (by simp)
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
  refine ErrClaim.bind_right hrun7' ?_
  by_cases hov : hi + gL < hi
  · rw [nfrE.k_nest_frame_holes.abort1 p n vis ctx fu hi us dO dL gL ns _ _ _ _ _ _ r7 m7 hov] at he; cases he
    exact ErrClaim.of_cls0 rfl
  by_cases hov2 : dL + gL < dL
  · rw [nfrE.k_nest_frame_holes.abort2 p n vis ctx fu hi us dO dL gL ns _ _ _ _ _ _ r7 m7 hov hov2] at he; cases he
    exact ErrClaim.of_cls0 rfl
  rw [nfrE.k_nest_frame_holes.arm1 p n vis ctx fu hi us dO dL gL ns _ _ _ _ _ _ r7 m7 hov hov2, g0, g1] at he
  have hhg : (hi + gL).toNat = hi.toNat + gL.toNat := pos2_word_add hov
  have hdg : (dL + gL).toNat = dL.toNat + gL.toNat := pos2_word_add hov2
  have hg47 := (hg5.trans hg6).trans hg7
  have hg17 := (hg14.trans hg47)
  have htop7 : iwTop m7 < 2 ^ 64 := Nat.lt_of_le_of_lt hS7.2.1 hS7.2.2.2.1
  have hA7 : AbsOK m7 := fhW_afr _ _ _ _ _ _ _ _ _ hfh (gcW_afr _ _ _ _ _ _ _ _ _ _ hgc
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
  cases h8 : callE p n "nest_ctors" [vis, ctx, 0, fu, rp.headD 0, rp.tail.headD 0, hi + gL, us, dO, dL,
      rp.tail.tail.headD 0, rp.tail.tail.tail.headD 0, rh.headD 0, rh.tail.headD 0, rc.headD 0, rc.tail.headD 0,
      ns, 0, 0] m7 with
  | ok q8 => obtain ⟨r8, m8⟩ := q8; rw [h8, nfrE.k_nest_ctors.arm1] at he; cases he
  | error e8 =>
  rw [h8, nfrE.k_nest_ctors.none] at he; cases he
  have hcl := eCtors m7 a7 ctx 0 fu _ _ (hi + gL) us dO dL _ _ _ _ _ _ ns 0 0 c
    (prog ++ grp.map fun x => (⟨⟨x.1, decI us, ds⟩, hi.toNat⟩ : NestHole)) ds (grp.map (·.1)) holes ctors
    NS [] ctxP _ usP dsP (grpP.map (·.1)) (ConLeche.Cached.frameHoles hi.toNat grpP) vc nsP []
    hC7 ⟨hW.u.grow hg17, hP7, by
      have := hW.hb; rw [hW.len] at hhi; simp only [NestCtx.hiAt] at this hhi ⊢; rw [hpl2]
      have := (hi + gL).toNat_lt; omega⟩
    ⟨hus, hds.grow (OMono.decHL _ _) hg17, by have := hg17.1; omega,
      by rw [decHL_agree (RdS.of_grow (hg6.trans hg7)) (fun j hj => by omega)]; exact hN5,
      by have := (hg6.trans hg7).1; omega, by simp only [List.length_map]; rw [← hgl, ← hdg]; exact (dL + gL).toNat_lt,
      hH7, hHb7⟩
    hcl6 (by have := hg7.1; omega) (hcs6.grow hcb6 hg7) (hns.grow hg17 htop) (OutsB.nil _ _) (by simp)
    ((((((hP.fr hf1).fr (ceinternW_mfr hic)).fr (MFr.ofMknF hma)).fr (coreF_mfr hq (by decide) hit)).fr
      (fgW_mfr _ _ _ _ _ _ _ _ _ _ _ _ _ _ hfg)).fr (gcW_mfr _ _ _ _ _ _ _ _ _ _ hgc) |>.fr
      (fhW_mfr _ _ _ _ _ _ _ _ _ hfh)) hA7
    hc (dCtx_ext _ hx07 _ _ hctx) hprog2 hpre (ConRon.Bridge.Inductives.dCtors_ext p6.ext _ _ hvc) hvcl
    (dState_ext hx07 _ _ hnsP) rfl _ h8
  rw [hhg, hgl] at hcl
  exact ErrClaim.bind_left (by simpa using hcl)

end steps

end L.Ind
