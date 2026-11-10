module

public import ConAgua.Verdict.PosE2M
public import ConAgua.Verdict.PosFt
import ConAgua.Verdict.PosE1N
import ConAgua.Arena.IndPosSpec.FgW
import ConAgua.Arena.IndPosSpec.GgW
import ConAgua.Arena.IndPosSpec.GgW2
import ConAgua.Arena.IndPosSpec.Grow
import ConAgua.Arena.IndPosSpec.SnocWMfr
import ConAgua.Arena.RefWalk
public import ConAgua.Arena.IndRealIlpL
public import ConLeche.Verify.Inductives.NestScope
import ConRon.Bridge.Inductives.Positivity
public import ConAgua.Arena.IndPosSpec.UCtx
import ConAgua.L.WordOff

@[expose] public section
/-!
# `nest_grow_group`: one refinement for both outcomes

`ngg_ref` on the unified model `nggE` (`PosE2M.lean`; the record and slice writers lifted,
`nest_inst_type` as its unified model, `nit_ref`), for
`nest_cont_new`'s refinement (`newRef_step`, `Arena/IndT/PosNew.lean`).
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dCtx dProg dState dCtx_ext dProg_ext dState_ext dGrp dKey kindOf)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- A member of a denoted name list denotes. -/
theorem denoteNList_memN : ∀ {st : NStore} {l : List NIdx} {L : List ConLeche.Name},
    Frontend.denoteNList st l = some L → ∀ n ∈ l, ∃ x, denoteN st n = some x
  | _, [], _, _, _, hn => absurd hn List.not_mem_nil
  | _, _ :: _, _, h, n, hn => by
    obtain ⟨l, L', h1, h2, -⟩ := ConRon.Bridge.denoteNList_cons_inv h
    rcases List.mem_cons.mp hn with rfl | hn
    · exact ⟨l, h1⟩
    · exact denoteNList_memN h2 n hn

/-! ## `nest_grow_group` -/

/-- What `nest_grow_group` gives (from `m`; the twin's store an extension of `a0`'s): the stage,
the growth, the group grown (`r`: its offset and length; `res`: the twin's), the frames, `AbsOK`. -/
structure NggPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (a0 : AState) (m : Mem) (r : List Word) (res : List (NIdx × EIdx)) (m' : Mem) (a' : AState) : Prop where
  stage : StageC dn vis fe env m' a'
  grow : IWGrow m m'
  length : (r.tail.headD 0).toNat = res.length
  bound : (r.headD 0).toNat + res.length ≤ iwTop m'
  grp : GrpAt m' (r.headD 0).toNat res
  pos : PosMR m'
  abs : AbsOK m'
  ext : ConRon.Arena.Ext a0.store a'.store

/-- **`nest_grow_group` refines `nestGrowGroup`, both outcomes** (under `StageC ∧ AbsOK`, the twin's
store an extension of `a0`'s): only `nest_inst_type` claims (`nit_ref`). -/
theorem ngg_ref {p : Prog} (L : NbLook p) (hIlpf : IlpfF p) (hq : KnotStageProg p) (hLC : LvlCacheProg p)
    (hF : FtProg p) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) {env : ConLeche.Env}
    (henv : ConLeche.EnvWF env)
    (ctx hi us dO dL : Word) (HI : Nat) (hHI : hi.toNat = HI) (c : NestCtx)
    (ds : List EIdx) (hus : H us) (a0 : AState) (csA : List NIdx) {ctxP : ConLeche.NestCtx}
    {usP : List ConLeche.Level} {dsP : List ConLeche.Expr} {matesP : List ConLeche.Name}
    (hc : ConLeche.NestCtxOk ctxP) (hctx : dCtx a0.store env.find? c = some ctxP)
    (husP : denoteLs a0.store.lss (decI us) = some usP) (hdsP : Frontend.denoteEList a0.store ds = some dsP)
    (hmates : Frontend.denoteNList a0.store.ns csA = some matesP) (k : Nat) :
    k ≤ 2 ^ 62 → ∀ (m : Mem) (a : AState) (cO cL gO gL : Word) (cs : List NIdx) (grp : List (NIdx × EIdx)),
    StageC dn vis fe env m a → AbsOK m → ConRon.Arena.Ext a0.store a.store → (∀ n ∈ cs, n ∈ csA) →
    UCtx dn vis fe m ctx c → decHL m dO.toNat dL.toNat = some ds → dO.toNat + dL.toNat ≤ iwTop m →
    decHL m cO.toNat cL.toNat = some cs → (∀ j < cL.toNat, cO.toNat + j < iwTop m) →
    gL.toNat = grp.length → gO.toNat + grp.length ≤ iwTop m → GrpAt m gO.toNat grp → PosMR m →
    RefE (WtG p) (nggE p k m vis ctx hi us dO dL cO cL gO gL)
      (ConRon.Arena.nestGrowGroup V fe c HI (decI us) ds cs grp) a
      (fun v res a' => NggPost dn vis fe env a0 m v.1 res v.2 a') := by
  induction k with
  | zero => intros; rw [nggE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  | succ k ih =>
    intro hk m a cO cL gO gL cs grp hC hA hx0 hcsA hU hds hdb hcs hcb hgl hgb hgrp hP
    have hS := hC.stage
    have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.iw.iw hS.iw.iwSize
    by_cases hc0 : cL = 0
    · rw [nggE.arm1 p k m vis ctx hi us dO dL cO cL gO gL hc0]
      subst hc0
      have : cs = [] := by simpa [decHL, hslice?] using hcs.symm
      subst this
      exact RefE.ret (by rw [ConRon.Arena.nestGrowGroup]; rfl) ⟨hC, IWGrow.refl _, by simpa using hgl,
        by simpa using hgb, by simpa using hgrp, hP, hA, hx0⟩
    rw [nggE.arm2 p k m vis ctx hi us dO dL cO cL gO gL hc0]
    have hlz : cL.toNat ≠ 0 := fun e => hc0 (UInt64.toNat_inj.mp (by simpa using e))
    obtain ⟨l', hl'⟩ : ∃ l', cL.toNat = l' + 1 := ⟨cL.toNat - 1, by omega⟩
    have hcs2 := hcs
    simp only [decHL, hl', hslice?_succ, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hcs2
    obtain ⟨n0, hn0, cs', hcs', rfl⟩ := hcs2
    obtain ⟨hcH, hcd⟩ := rd_iwH0E (m := m) (o := cO) (k := IdxKind.name) (by simpa [iwH, iwA] using hn0)
    generalize hcw : rdW (m.arr64 IW) cO = cw at hcH hcd ⊢
    have hcO1 : (cO + 1).toNat = cO.toNat + 1 :=
      _root_.L.toNat_add_of_lt _ _ (show cO.toNat + 1 < 2 ^ 64 by have := hcb 0 (by omega); omega)
    have hcL1 : (cL - 1).toNat = l' := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
    -- the key record
    rw [ConRon.Arena.nestGrowGroup]
    refine RefE.onlySim (fun _ => nggE.k_rec4.none ..)
      (fun _ _ h => And.intro h (posRecW_stage h hS (by simp))) fun key m1 ⟨hk, hS1, hg1, hkq, ht1, hget1⟩ => ?_
    rw [nggE.k_rec4.arm1]
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
      have htop1 : iwTop m1 < 2 ^ 64 := Nat.lt_of_le_of_lt hS1.iw.iw hS1.iw.iwSize
      have e2 : (key + 2).toNat = key.toNat + 2 := _root_.L.toNat_add_of_lt _ _ (by simp; omega)
      have e3 : (key + 3).toNat = key.toNat + 3 := _root_.L.toNat_add_of_lt _ _ (by simp; omega)
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
    -- `nest_inst_type`
    refine RefE.bindE (fun _ => nggE.k_nest_inst_type.none ..) id
      (nit_ref L.nit hq.closed hIlpf hLC hq hF henv k (by omega) hC1 hA1 hHI (hU.grow hg1) hdk hkin hksl hP1 hctxa hkeyP)
      fun ⟨r2, m2⟩ ⟨x1, x2⟩ a2 hrun2 ⟨hS2, hg2, hx1, htH, htd, hP2, hA2⟩ => ?_
    rw [nggE.k_nest_inst_type.arm1]
    obtain ⟨c4, -⟩ := ConRon.Bridge.Inductives.nestInstType_spec
      (ConRon.Bridge.CoreSpec.of_core : ConRon.Bridge.CoreSpec checkFuel) henv hc c HI ⟨n0, decI us, ds⟩
      ⟨n0P, usP, dsP⟩ a a2 _ hC1.check ⟨hctxa, hkeyP⟩ hrun2
    have hC2 : StageC dn vis fe env m2 a2 := hC1.of_check hS2 hA2 c4.ok c4.ext
    have hx2 := hx0.trans c4.ext
    dsimp only at htd ⊢
    -- the pair record and the snoc
    refine RefE.onlySim (fun _ => nggE.k_rec2.none ..)
      (fun _ _ h => And.intro h (posRecW_stage h hS2 (by simp))) fun pw m3 ⟨hpr, hS3, hg3, hpq, ht3, hget3⟩ => ?_
    rw [nggE.k_rec2.arm1]
    have hA3 : AbsOK m3 := hA2.iw (posRecW_iwFr hpr)
    simp only [List.length_cons, List.length_nil] at ht3
    have hg13 := (hg1.trans hg2).trans hg3
    refine RefE.onlySim (fun _ => nggE.k_sl_snoc.none ..)
      (fun _ _ h => And.intro h (snocW_words h hS3 (by have := hg13.iw; omega)))
      fun r4 m4 ⟨hsn, hS4, hg4, hr40, hr41, ht4, hw4, hx4⟩ => ?_
    rw [nggE.k_sl_snoc.arm1]
    have hA4 : AbsOK m4 := hA3.iw (snocW_iwFr hsn)
    have hC4 : StageC dn vis fe env m4 a2 := hC2.of_pstep hS4 hA4 (PStep.refl hC2.check.state)
    have hg14 := hg13.trans hg4
    have hgrp4 : GrpAt m4 (r4.headD 0).toNat (grp ++ [(n0, x2)]) := by
      rw [hr40]
      intro i hi
      simp only [List.length_append, List.length_cons, List.length_nil] at hi
      by_cases hio : i < grp.length
      · obtain ⟨w, c1, t1, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hgrp i hio
        refine ⟨w, c1, t1, ?_, by have := hg14.iw; omega, by rw [hg14.iwGet _ (by omega)]; exact h3, h4,
          by rw [List.getElem_append_left hio]; exact h5, by rw [hg14.iwGet _ (by omega)]; exact h6, h7,
          by rw [List.getElem_append_left hio]; exact h8⟩
        rw [hw4 i (by omega), hg13.iwGet _ (by omega)]; exact h1
      · have hie : i = grp.length := by omega
        subst hie
        refine ⟨pw, cw, r2.tail.headD 0, ?_, ?_, ?_, hcH, ?_, ?_, htH, ?_⟩
        · rw [← hgl]; exact hx4
        · have := hg4.iw; omega
        · rw [hg4.iwGet _ (by omega)]; simpa using hget3 0 (by simp)
        · simp [hcd]
        · rw [hg4.iwGet _ (by omega)]; simpa using hget3 1 (by simp)
        · simpa using htd
    refine RefE.lastE (fun _ => nggE.k_nest_grow_group.none ..) (fun _ => nggE.k_nest_grow_group.arm1 ..) id
      (ih (by omega) m4 a2 (cO + 1) (cL - 1) _ _ cs' (grp ++ [(n0, x2)]) hC4 hA4 hx2
      (fun n hn => hcsA n (List.mem_cons_of_mem _ hn)) (hU.grow hg14)
      (by rw [decHL_agree (RdS.of_grow hg14) (fun j hj => by omega)]; exact hds)
      (by have := hg14.iw; omega)
      (by rw [hcO1, hcL1, decHL_agree (RdS.of_grow hg14) (fun j hj => by have := hcb (j + 1) (by omega); omega)]
          simpa [decHL] using hcs')
      (fun j hj => by rw [hcO1, hcL1] at *; have := hcb (j + 1) (by omega); have := hg14.iw; omega)
      (by rw [hr41]; simp [hgl]) (by rw [hr40]; simp; omega) hgrp4 ((hP2.fr (posRecW_mfr hpr)).fr (snocW_mfr hsn)))
      fun _ _ _ _ hR => ⟨hR.stage, hg14.trans hR.grow, hR.length, hR.bound, hR.grp, hR.pos, hR.abs, hR.ext⟩

end L.Ind
