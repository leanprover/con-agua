import ConAgua.Arena.IndPosSpec.CfW
import ConAgua.Arena.IndPosSpec.NcnW2
import ConAgua.Arena.IndPosSpec.NitW
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.Arena.IndPosSpec.NbPosW
import ConAgua.Arena.IndPosSpec.NbKeyK2
import ConAgua.Arena.IndPosSpec.NbLook

/-!
# GgW2

`nestGrowGroup_spec`, `posRecW_iwFr`, `snocW_iwFr`, `ggW_ok`, `nestFrameMates_specW`, `slNew1_specW` and the lemmas only they use.
-/

section

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem nestGrowGroup_spec (p : Prog) (hl : NitLook p) (h2 : p.lookup "rec2" = some rec2)
    (h4 : p.lookup "rec4" = some rec4) (hsn : p.lookup "sl_snoc" = some slSnoc)
    (hp : p.lookup "nest_grow_group" = some nestGrowGroupL) (cR : CallM) (hcR : CallSpec p cR) (k : Nat) :
    ∀ (s₀ : St) (vis ctx hi us dO dL cO cL gO gL : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "nest_grow_group" [vis, ctx, hi, us, dO, dL, cO, cL, gO, gL]
    ⦃fun r s' => LocEq s' s₀ ∧
      ggW cR k s₀.mem vis ctx hi us dO dL cO cL gO gL = some ([r.headD 0, r.tail.headD 0], s'.mem); ⊤⦄ := by
  induction k with
  | zero =>
    intro s₀ vis ctx hi us dO dL cO cL gO gL
    rw [invoke_eq _ hp]; simp only [callFn, nestGrowGroupL]; vcgen [exec] <;> grind
  | succ k ih =>
    intro s₀ vis ctx hi us dO dL cO cL gO gL
    simp only [invoke_eq _ hp, callFn, nestGrowGroupL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        posRec4_specW p hl.ty.ha h4 k, nestInstType_spec' p hl cR hcR k, posRec2_specW p hl.ty.ha h2 k,
        slSnoc_specW p hl.ty.ha hl.hc2 hsn k, ih] <;>
      finish (gen := 20) (instances := 5000) [rdW_eq, Locals.init_cons_zero]

/-- `posRecW` writes the record pool only. -/
theorem posRecW_iwFr {m m' : Mem} {ws : List Word} {q : Word} (h : posRecW m ws = some (q, m')) :
    MemFrame [IW] [200] m m' := by
  simp only [posRecW] at h
  rcases hal : allocW m (UInt64.ofNat ws.length) with _ | ⟨q1, m1⟩ <;> rw [hal] at h; · simp at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  exact (allocW_iwFrame hal).trans (wrIW_frame _ _ _)

/-- `snocW` writes the record pool only. -/
theorem snocW_iwFr {n : Nat} {m m' : Mem} {o l x : Word} {r : List Word} (h : snocW n m o l x = some (r, m')) :
    MemFrame [IW] [200] m m' := by
  unfold snocW at h
  split at h; · simp at h
  split at h; · simp at h
  rename_i q m1 hal
  split at h; · simp at h
  rename_i m2 hc
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  exact ((allocW_iwFrame hal).trans (posmemo_copyW_iw _ _ _ _ _ _ hc)).trans (set64IW_frame _ _ _)

/-- **`nest_grow_group`'s model refines `nestGrowGroup`**, its `nest_inst_type` calls read through
`cR`: an invariant `J` (the caller's: `True` for the stubs, `StageC` for the program's own reading)
gives `nest_inst_type_ty`'s ok half (`NtyOk`) at each call's start and is kept by the pool writers and each
`nest_inst_type`. -/
theorem ggW_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis ctx hi us dO dL : Word) (HI : Nat)
    (hHI : hi.toNat = HI) (c : NestCtx) (ds : List EIdx) (hus : H us) (cR : CallM)
    (J : Mem → AState → Prop) (csA : List NIdx)
    (hJty : ∀ k m a key, J m a → NtyOk cR dn vis fe k m a key) (Qn : Mem → AState → Prop)
    (hJle : ∀ (k : Nat) (m : Mem) (a : AState) (key : Word) (n0 : NIdx), J m a → n0 ∈ csA →
      NitLe cR k dn vis fe ctx hi key c ⟨n0, decI us, ds⟩ Qn m a)
    (hJiw : ∀ m m' a, J m a → MemFrame [IW] [200] m m' → StageR dn vis fe m' a → J m' a)
    (hJnit : ∀ (k : Nat) (m m' : Mem) (a a' : AState) (key : Word) (n0 : NIdx) (x : Nat × EIdx)
      (r : List Word), J m a → n0 ∈ csA → nitW cR k m vis ctx hi key = some (r, m') →
      (ConRon.Arena.nestInstType fe c HI ⟨n0, decI us, ds⟩).run a = .ok (x, a') →
      StageR dn vis fe m' a' → (∀ r1 m1, ntyR cR k m vis key = some (r1, m1) → AFr m m1) → Qn m' a' →
      J m' a')
    (k : Nat) :
    ∀ (m m' : Mem) (a : AState) (cO cL gO gL : Word) (cs : List NIdx) (grp : List (NIdx × EIdx))
      (r : List Word),
    ggW cR k m vis ctx hi us dO dL cO cL gO gL = some (r, m') → StageR dn vis fe m a → J m a →
    (∀ n ∈ cs, n ∈ csA) →
    UCtx dn vis fe m ctx c → decHL m dO.toNat dL.toNat = some ds → dO.toNat + dL.toNat ≤ iwTop m →
    decHL m cO.toNat cL.toNat = some cs → (∀ j < cL.toNat, cO.toNat + j < iwTop m) →
    gL.toNat = grp.length → gO.toNat + grp.length ≤ iwTop m → GrpAt m gO.toNat grp → PosMR m →
    ∃ res a', (ConRon.Arena.nestGrowGroup fe c HI (decI us) ds cs grp).run a = .ok (res, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ (r.tail.headD 0).toNat = res.length ∧
      (r.headD 0).toNat + res.length ≤ iwTop m' ∧ GrpAt m' (r.headD 0).toNat res ∧ PosMR m' ∧ J m' a' := by
  induction k with
  | zero => intro m m' a cO cL gO gL cs grp r h; simp [ggW] at h
  | succ k ih =>
    intro m m' a cO cL gO gL cs grp r h hS hJ hcsA hU hds hdb hcs hcb hgl hgb hgrp hP
    have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
    by_cases hc0 : cL = 0
    · rw [ggW_nil (h := hc0)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      subst hc0
      have : cs = [] := by simpa [decHL, hslice?] using hcs.symm
      subst this
      exact ⟨grp, a, by rw [ConRon.Arena.nestGrowGroup]; rfl, hS, IWGrow.refl _, by simpa using hgl,
        by simpa using hgb, by simpa using hgrp, hP, hJ⟩
    rw [ggW_cons (h := hc0)] at h
    have hlz : cL.toNat ≠ 0 := fun e => hc0 (UInt64.toNat_inj.mp (by simpa using e))
    obtain ⟨l', hl'⟩ : ∃ l', cL.toNat = l' + 1 := ⟨cL.toNat - 1, by omega⟩
    have hcs2 := hcs
    simp only [decHL, hl', hslice?_succ, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hcs2
    obtain ⟨n0, hn0, cs', hcs', rfl⟩ := hcs2
    obtain ⟨hcH, hcd⟩ := rd_iwH0E (m := m) (o := cO) (k := IdxKind.name) (by simpa [iwH, iwA] using hn0)
    generalize hcw : rdW (m.arr64 IW) cO = cw at h hcH hcd
    have hcO1 : (cO + 1).toNat = cO.toNat + 1 :=
      word_add_toNat (show cO.toNat + 1 < 2 ^ 64 by have := hcb 0 (by omega); omega)
    have hcL1 : (cL - 1).toNat = l' := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
    -- the key record
    rcases hk : posRecW m [cw, us, dO, dL] with _ | ⟨key, m1⟩ <;> rw [hk] at h; · simp [ggK1] at h
    rw [ggK1_some] at h
    obtain ⟨hS1, hg1, hkq, ht1, hget1⟩ := posRecW_stage hk hS (by simp)
    have hJ1 := hJiw m m1 a hJ (posRecW_iwFr hk) hS1
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
    -- `nest_inst_type`
    cases k with
    | zero => simp [nitWf, ggK2] at h
    | succ k =>
    simp only [nitWf] at h
    rcases hnit : nitW cR k m1 vis ctx hi key with _ | ⟨r2, m2⟩ <;> rw [hnit] at h; · simp [ggK2] at h
    rw [ggK2_some] at h
    obtain ⟨x, a2, hrun2, hS2, hg2, hx1, htH, htd, hP2, hAty, hQ2⟩ := nitW_ok k dn fe vis ctx hi HI hHI c m1 m2 a key
      _ r2 cR (hJty k m1 a key hJ1) Qn (hJle k m1 a key n0 hJ1 (hcsA n0 List.mem_cons_self)) hnit hS1
      (hU.grow hg1) hdk hkin hksl (hP.fr (posRecW_mfr hk))
    have hJ2 := hJnit k m1 m2 a a2 key n0 x r2 hJ1 (hcsA n0 List.mem_cons_self) hnit hrun2 hS2 hAty hQ2
    -- the pair record and the snoc
    rcases hpr : posRecW m2 [cw, r2.tail.headD 0] with _ | ⟨pw, m3⟩ <;> rw [hpr] at h; · simp [ggK3] at h
    rw [ggK3_some] at h
    obtain ⟨hS3, hg3, hpq, ht3, hget3⟩ := posRecW_stage hpr hS2 (by simp)
    have hJ3 := hJiw m2 m3 a2 hJ2 (posRecW_iwFr hpr) hS3
    simp only [List.length_cons, List.length_nil] at ht3
    have hg13 := (hg1.trans hg2).trans hg3
    rcases hsn : snocW (k + 1) m3 gO gL pw with _ | ⟨r4, m4⟩ <;> rw [hsn] at h; · simp [ggK4] at h
    rw [ggK4_some] at h
    obtain ⟨hS4, hg4, hr40, hr41, ht4, hw4, hx4⟩ := snocW_words hsn hS3 (by have := hg13.1; omega)
    have hJ4 := hJiw m3 m4 a2 hJ3 (snocW_iwFr hsn) hS4
    have hg14 := hg13.trans hg4
    have hgrp4 : GrpAt m4 (r4.headD 0).toNat (grp ++ [(n0, x.2)]) := by
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
        · rw [htd]; simp
    obtain ⟨res, a', hrun, hS', hg', h1, h2, h3, hP', hJ'⟩ := ih m4 m' a2 (cO + 1) (cL - 1) _ _ cs' (grp ++ [(n0, x.2)]) r h
      hS4 hJ4 (fun n hn => hcsA n (List.mem_cons_of_mem _ hn)) (hU.grow hg14) (by rw [decHL_agree (RdS.of_grow hg14) (fun j hj => by omega)]; exact hds)
      (by have := hg14.1; omega)
      (by rw [hcO1, hcL1, decHL_agree (RdS.of_grow hg14) (fun j hj => by have := hcb (j + 1) (by omega); omega)]
          simpa [decHL] using hcs')
      (fun j hj => by rw [hcO1, hcL1] at *; have := hcb (j + 1) (by omega); have := hg14.1; omega)
      (by rw [hr41]; simp [hgl]) (by rw [hr40]; simp; omega) hgrp4 ((hP2.fr (posRecW_mfr hpr)).fr (snocW_mfr hsn))
    refine ⟨res, a', ?_, hS', hg14.trans hg', h1, h2, h3, hP', hJ'⟩
    simp only [ConRon.Arena.nestGrowGroup, StateT.run_bind, hrun2, except_ok_bind]
    exact hrun

end L.Ind

end

end

section

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem nestFrameMates_specW (p : Prog) (L : FmLook p) (n : Nat) (s₀ : St) (vis c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_frame_mates" [vis, c]
    ⦃fun r s' => LocEq s' s₀ ∧ nfmW n s₀.mem vis c = some (r, s'.mem); ⊤⦄ := by
  simp only [invoke_eq _ L.hp, callFn, nestFrameMatesL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        nestBlockOf_specW p L.hx L.hg L.hf L.hbo n,
        nestFrameMatesGo_spec p L.hc L.ha L.hcp L.hsn L.hgo n] <;>
      finish (gen := 20) [nfmW]

theorem slNew1_specW (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hp : p.lookup "sl_new1" = some slNew1) (n : Nat) (s₀ : St) (x : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "sl_new1" [x]
    ⦃fun r s' => LocEq s' s₀ ∧ new1W s₀.mem x = some (r, s'.mem); ⊤⦄ := by
  simp only [invoke_eq _ hp, callFn, slNew1]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, iwAlloc_specW p ha n] <;>
      finish [new1W, allocMem, allocW]

end L.Ind

namespace L.Ind

open L.Arena

theorem nestFrameGrp_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc2 : p.lookup "iw_copy" = some iwCopy) (h2 : p.lookup "rec2" = some rec2)
    (h4 : p.lookup "rec4" = some rec4) (hsn : p.lookup "sl_snoc" = some slSnoc)
    (hp : p.lookup "nest_frame_grp" = some nestFrameGrpL) (n : Nat) :
    ∀ (s₀ : St) (hi us dO dL gO gL pO pL nO nL : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_frame_grp" [hi, us, dO, dL, gO, gL, pO, pL, nO, nL]
    ⦃fun r s' => LocEq s' s₀ ∧ fgW n s₀.mem hi us dO dL gO gL pO pL nO nL =
      some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, r.tail.tail.tail.headD 0], s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ hi us dO dL gO gL pO pL nO nL
    rw [invoke_eq _ hp]; simp only [callFn, nestFrameGrpL]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ hi us dO dL gO gL pO pL nO nL
    simp only [invoke_eq _ hp, callFn, nestFrameGrpL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        posRec4_specW p ha h4 n, posRec2_specW p ha h2 n, slSnoc_specW p ha hc2 hsn n, ih] <;>
      finish (gen := 20) (instances := 5000) [rdW_eq, Locals.init_cons_zero]

end L.Ind

namespace L.Ind

open L.Arena

theorem nestFrameHoles_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc2 : p.lookup "iw_copy" = some iwCopy) (hsn : p.lookup "sl_snoc" = some slSnoc)
    (hff : p.lookup "fvar_find" = some fvarFind) (hfp : p.lookup "fvar_push" = some fvarPush)
    (hif : p.lookup "intern_fvar" = some internFVar)
    (hp : p.lookup "nest_frame_holes" = some nestFrameHolesL) (n : Nat) :
    ∀ (s₀ : St) (hi gO gL aO aL : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_frame_holes" [hi, gO, gL, aO, aL]
    ⦃fun r s' => LocEq s' s₀ ∧ fhW n s₀.mem hi gO gL aO aL = some ([r.headD 0, r.tail.headD 0], s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ hi gO gL aO aL
    rw [invoke_eq _ hp]; simp only [callFn, nestFrameHolesL]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ hi gO gL aO aL
    simp only [invoke_eq _ hp, callFn, nestFrameHolesL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        internFVar_spec p hff hfp hif n, slSnoc_specW p ha hc2 hsn n, ih] <;>
      finish (gen := 20) (instances := 5000) [rdW_eq, Locals.init_cons_zero]

end L.Ind

namespace L.Ind

open L.Arena

theorem nestContNewActive_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hc2 : p.lookup "iw_copy" = some iwCopy) (h4 : p.lookup "rec4" = some rec4)
    (hsn : p.lookup "sl_snoc" = some slSnoc)
    (hp : p.lookup "nest_cont_new_active" = some nestContNewActiveL) (n : Nat) :
    ∀ (s₀ : St) (us dO dL gO gL aO aL : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_cont_new_active" [us, dO, dL, gO, gL, aO, aL]
    ⦃fun r s' => LocEq s' s₀ ∧ caW n s₀.mem us dO dL gO gL aO aL = some ([r.headD 0, r.tail.headD 0], s'.mem);
      ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ us dO dL gO gL aO aL
    rw [invoke_eq _ hp]; simp only [callFn, nestContNewActiveL]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ us dO dL gO gL aO aL
    simp only [invoke_eq _ hp, callFn, nestContNewActiveL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        posRec4_specW p ha h4 n, slSnoc_specW p ha hc2 hsn n, ih] <;>
      finish (gen := 20) (instances := 5000) [rdW_eq, Locals.init_cons_zero]

end L.Ind

end

end

section

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem nestContNewFinish_spec (p : Prog) (L : NagLook p) (hd : DcLook p) (h6 : p.lookup "rec6" = some rec6)
    (hp : p.lookup "nest_cont_new_finish" = some nestContNewFinishL) (n : Nat) (s₀ : St)
    (ctx us dO dL gO gL ns2 aO aL kb : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_cont_new_finish" [ctx, us, dO, dL, gO, gL, ns2, aO, aL, kb]
    ⦃fun r s' => LocEq s' s₀ ∧
      cfW n s₀.mem ctx us dO dL gO gL ns2 aO aL kb = some ([r.headD 0, r.tail.headD 0], s'.mem); ⊤⦄ := by
  simp only [invoke_eq _ hp, callFn, nestContNewFinishL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        dc_spec' p hd.hf hd.hh hd.hg hd.hp n, nestAcceptGroup_spec p L n, rec6_specW p L.ha h6 n] <;>
      finish (gen := 20) (instances := 5000) [cfW, nestedW, rdW_eq]

end L.Ind

namespace L.Ind

open L.Arena

theorem nestPosHoleKind_spec (p : Prog) (hh : p.lookup "nest_ctx_hi_at" = some nestCtxHiAt)
    (hp : p.lookup "nest_pos_hole_kind" = some nestPosHoleKindL) (n : Nat) (s₀ : St) (ctx kb i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_pos_hole_kind" [ctx, kb, i]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ hkWf n s₀.mem ctx kb i = some (r.headD 0); ⊤⦄ := by
  simp only [invoke_eq _ hp, callFn, nestPosHoleKindL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, nestCtxHiAt_specE p hh n] <;>
      finish (gen := 20) [hkWf, hkW, rdW_eq, LocEq]

end L.Ind

namespace L.Ind

open L.Arena

theorem nestHoleAt_spec' (p : Prog) (L : PfLook p) (k : Nat) (s₀ : St) (ctx po pl i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "nest_hole_at" [ctx, po, pl, i]
    ⦃fun r s' => LocEq s' s₀ ∧ haWf k s₀.mem ctx po pl i = some (r, s'.mem); ⊤⦄ := by
  cases k with
  | zero => rw [invoke_eq _ L.hha]; simp only [callFn, nestHoleAt]; vcgen [exec] <;> grind
  | succ k => exact nestHoleAt_spec p L.ha L.h2 L.h4 L.hrg L.hr L.hc L.hap L.hha k s₀ ctx po pl i

theorem nestArity_spec' (p : Prog) (hl : NaLook p) (k : Nat) (s₀ : St) (vis c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "nest_arity" [vis, c]
    ⦃fun r s' => LocEq s' s₀ ∧ naWf k s₀.mem vis c = some (r, s'.mem); ⊤⦄ := by
  cases k with
  | zero => rw [invoke_eq _ hl.hp]; simp only [callFn, nestArityL]; vcgen [exec] <;> grind
  | succ k => exact nestArity_spec p hl k s₀ vis c

end L.Ind

namespace L.Ind

open L.Arena

theorem structUsedLater_spec' (p : Prog) (L : UslLook p) (n : Nat) (s₀ : St) (cty nP j : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "struct_used_later" [cty, nP, j]
    ⦃fun r s' => LocEq s' s₀ ∧ ustWf n s₀.mem cty nP j = some (r.headD 0, s'.mem); ⊤⦄ := by
  match n with
  | 0 => rw [invoke_eq _ L.hp]; simp only [callFn, structUsedLaterL]; vcgen [exec] <;> grind
  | 1 =>
    rw [invoke_eq _ L.hp]; simp only [callFn, structUsedLaterL]
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, invoke_exec0 p] <;> grind
  | n + 2 => exact structUsedLater_spec p L.hv L.hf L.hput L.hins L.hgo L.hbp L.hst L.hcl L.hfast L.hp n s₀ cty nP j

theorem nestCtorsU4_spec (p : Prog) (L : UslLook p) (hp : p.lookup "nest_ctors_u4" = some nestCtorsU4L)
    (n : Nat) : ∀ (s₀ : St) (ko nF cl i : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_ctors_u4" [ko, nF, cl, i]
    ⦃fun r s' => LocEq s' s₀ ∧ u4W n s₀.mem ko nF cl i = some ([r.headD 0], s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ ko nF cl i
    rw [invoke_eq _ hp]; simp only [callFn, nestCtorsU4L]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ ko nF cl i
    simp only [invoke_eq _ hp, callFn, nestCtorsU4L]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, structUsedLater_spec' p L n, ih] <;>
      finish (gen := 20) [rdW_eq]

end L.Ind

namespace L.Ind

open L.Arena

theorem nestCtorsResOk_spec (p : Prog) (hl : NoLook p) (hoa : p.lookup "nest_occ_any" = some nestOccAnyL)
    (hrh : p.lookup "nest_res_head" = some nestResHeadL) (had : AdF p)
    (hp : p.lookup "nest_ctors_res_ok" = some nestCtorsResOkL) (n : Nat) (s₀ : St) (ctx hi cur : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_ctors_res_ok" [ctx, hi, cur]
    ⦃fun r s' => LocEq s' s₀ ∧ roW n s₀.mem ctx hi cur = some ([r.headD 0], s'.mem); ⊤⦄ := by
  simp only [invoke_eq _ hp, callFn, nestCtorsResOkL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        nestResHead_spec p hrh had n, gaaF_spec p had n, nestOccAny_spec p hl hoa n] <;>
      finish (gen := 20) [roW, roK0_eq, rdW_eq]

end L.Ind

end

end


section


/-! # `IndPos2`, the `nestPos` block (lane `indproofs2`, helper `pos2`): the L side — every
function of the block refines its word model, by one induction on the exec fuel. -/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem posRec3_eq (m : Mem) (a b c : Word) :
    (match allocW m 3 with | none => none | some (q, _) => some (q, rec3Mem m a b c)) =
      posRecW m [a, b, c] := by
  rw [posRecW_eq m [a, b, c] 3 rfl]
  cases allocW m 3 with
  | none => rfl
  | some pr =>
    simp only [rec3Mem, wrIW]
    rw [show rdW (m.arr64 CTL) 200 + 1 + 1 = rdW (m.arr64 CTL) 200 + 2 by
      rw [UInt64.add_assoc]; rfl]

theorem posRec3_specW (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc) (h3 : p.lookup "rec3" = some rec3)
    (n : Nat) (s₀ : St) (a b c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rec3" [a, b, c]
    ⦃fun r s' => LocEq s' s₀ ∧ posRecW s₀.mem [a, b, c] = some (r.headD 0, s'.mem); ⊤⦄ := by
  simp only [← posRec3_eq, invoke_eq _ h3, callFn, rec3]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        iwAlloc_specW p ha n] <;>
      finish [rec3Mem, allocMem, allocW]

theorem pos2_getElem_getD (a : Array Word) (i : Nat) (h : i < a.size) : a[i] = a[i]?.getD 0 := by
  simp [h]

theorem nestCtorNf_spec' (p : Prog) (L : NbLook p) (k : Nat) (s₀ : St) (ctx po pl us dO dL cv closed : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "nest_ctor_nf" [ctx, po, pl, us, dO, dL, cv, closed]
    ⦃fun r s' => LocEq s' s₀ ∧ ncnWf k s₀.mem ctx po pl us dO dL cv closed = some ([r.headD 0], s'.mem); ⊤⦄ := by
  match k with
  | 0 => exact triple_post (invoke_exec0 p _ _ s₀) (fun _ _ h => h.elim)
  | k + 1 =>
    refine triple_post (nestCtorNf_spec p L.ct.cr.rx L.hnf k s₀ ctx po pl us dO dL cv closed) ?_
    rintro r s' ⟨h1, h2⟩
    exact ⟨h1, by simp [ncnWf, h2]⟩

theorem nestWalkStack_spec' (p : Prog) (L : NbLook p) (n : Nat) (s₀ : St) (ctx off l po pl : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_walk_stack" [ctx, off, l, po, pl]
    ⦃fun r s' => LocEq s' s₀ ∧ nwsWf n s₀.mem ctx off l po pl = some (r, s'.mem); ⊤⦄ := by
  match n with
  | 0 => exact triple_post (invoke_exec0 p _ _ s₀) (fun _ _ h => h.elim)
  | n + 1 => exact nestWalkStack_spec p L.dc L.hws n s₀ ctx off l po pl

end L.Ind

end

end
