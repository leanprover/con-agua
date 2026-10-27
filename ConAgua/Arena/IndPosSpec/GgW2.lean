import ConAgua.Arena.IndPosSpec.Nb
import ConAgua.Arena.IndPosSpec.NcnW2
import ConAgua.Arena.IndPosSpec.NitW
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr

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
gives the `inst_lp_fast` contract at each call's start and is kept by the pool writers and each
`nest_inst_type`. -/
theorem ggW_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis ctx hi us dO dL : Word) (HI : Nat)
    (hHI : hi.toNat = HI) (c : NestCtx) (ds : List EIdx) (hus : H us) (cR : CallM) (hF : IlpFr cR)
    (J : Mem → AState → Prop) (csA : List NIdx)
    (hJI : ∀ m a, J m a → IlpRd cR dn vis fe (IlpBase m a)) (Qn : Mem → AState → Prop)
    (hJle : ∀ (k : Nat) (m : Mem) (a : AState) (key : Word) (n0 : NIdx), J m a → n0 ∈ csA →
      NitLe cR k dn vis fe ctx hi key c ⟨n0, decI us, ds⟩ Qn m a)
    (hJiw : ∀ m m' a, J m a → MemFrame [IW] [200] m m' → StageR dn vis fe m' a → J m' a)
    (hJnit : ∀ (k : Nat) (m m' : Mem) (a a' : AState) (key : Word) (n0 : NIdx) (x : Nat × EIdx)
      (r : List Word), J m a → n0 ∈ csA → nitW cR k m vis ctx hi key = some (r, m') →
      (ConRon.Arena.nestInstType fe c HI ⟨n0, decI us, ds⟩).run a = .ok (x, a') →
      StageR dn vis fe m' a' → (∀ r1 m1, ntyWf cR k m vis key = some (r1, m1) → AFr m m1) → Qn m' a' →
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
      _ r2 cR (hJI m1 a hJ1) hF Qn (hJle k m1 a key n0 hJ1 (hcsA n0 List.mem_cons_self)) hnit hS1
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

theorem nestPosFvar_spec (p : Prog) (L : PfLook p) (n : Nat) (s₀ : St) (vis ctx po pl kb hi i aO aL : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_pos_fvar" [vis, ctx, po, pl, kb, hi, i, aO, aL]
    ⦃fun r s' => LocEq s' s₀ ∧ pfW n s₀.mem vis ctx po pl kb hi i aO aL = some ([r.headD 0], s'.mem); ⊤⦄ := by
  simp only [invoke_eq _ L.hp, callFn, nestPosFvarL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        nestHoleAt_spec' p L n, nestOccAny_spec p L.no L.hoa n, nestArity_spec' p L.na n,
        nestPosHoleKind_spec p L.hh L.hk n] <;>
      finish (gen := 20) (instances := 5000) [pfW, p2pfK1_eq, p2pfK2_eq, p2pfK3_eq, rdW_eq]

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

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The models' arms -/

theorem nbBindK6_some (k ns2 : Word) (z : Word) (m6 : Mem) :
    nbBindK6 k ns2 (some (z, m6)) = if 4294967296 ≤ z then none else some ([k, z, ns2], m6) := rfl
theorem nbBindK5_some (a k ns2 : Word) (r : List Word) (m5 : Mem) :
    nbBindK5 a k ns2 (some (r, m5)) = nbBindK6 k ns2 (mkForallW m5 a (r.headD 0)) := rfl
theorem nbBindK4_some (dep a : Word) (r : List Word) (m4 : Mem) :
    nbBindK4 dep a (some (r, m4)) = nbBindK5 a (r.headD 0) (r.tail.tail.headD 0)
      (abF m4 [CWF, r.tail.headD 0, dep, 0]) := rfl
theorem nbBindK3_some (posF : MW9) (vis ctx fu po pl dep kb : Word) (v : List Word) (ns : Word) (r : List Word) (m3 : Mem) :
    nbBindK3 posF vis ctx fu po pl dep kb v ns (some (r, m3)) = nbBindK4 dep (v.tail.headD 0) (posF m3 vis ctx fu po pl (dep + 1) (kb + 1) (r.headD 0) ns) := rfl
theorem nbBindK2_some (posF : MW9) (vis ctx fu po pl dep kb : Word) (v : List Word) (ns : Word) (fv : Word) (m2 : Mem) :
    nbBindK2 posF vis ctx fu po pl dep kb v ns (some (fv, m2)) =
    if 4294967296 ≤ fv then none
    else nbBindK3 posF vis ctx fu po pl dep kb v ns (i1F m2 [CWF, v.tail.tail.headD 0, fv, 0]) := rfl
theorem nbBindK1_some (posF : MW9) (vis ctx fu po pl dep kb : Word) (v : List Word) (ns : Word) (o : Word) (m1 : Mem) :
    nbBindK1 posF vis ctx fu po pl dep kb v ns (some (o, m1)) =
    if o ≠ 0 then none
    else if dep + 1 = 0 then none
    else if kb + 1 = 0 then none
    else nbBindK2 posF vis ctx fu po pl dep kb v ns (fvinternW m1 dep (v.tail.headD 0)) := rfl
theorem nbPosK3_some (w e ns : Word) (o : Word) (m3 : Mem) :
    nbPosK3 w e ns (some (o, m3)) = if o ≠ 0 then some ([0, w, ns], m3) else some ([0, e, ns], m3) := rfl
theorem nbPosK4_some (r : List Word) (m3 : Mem) :
    nbPosK4 (some (r, m3)) = some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0], m3) := rfl
theorem nbPosK5_some (w : Word) (r : List Word) (m3 : Mem) :
    nbPosK5 w (some (r, m3)) = some ([r.headD 0, w, r.tail.headD 0], m3) := rfl
theorem nbPosK2_some (n : Nat) (bindF appF : MW9) (vis ctx fu po pl dep kb e ns hi w : Word) (o : Word) (m2 : Mem) :
    nbPosK2 n bindF appF vis ctx fu po pl dep kb e ns hi w (some (o, m2)) =
    if o = 0 then nbPosK3 w e ns (noConstWf n m2 (rdW (m2.arr64 IW) ctx) (rdW (m2.arr64 IW) (ctx + 1))
      (rdW (m2.arr64 IW) (ctx + 4)) hi e)
    else if w >>> 28 = 6 then nbPosK4 (bindF m2 vis ctx fu po pl dep kb w ns)
    else nbPosK5 w (appF m2 vis ctx fu po pl kb hi w ns) := rfl
theorem nbPosK1_some (n : Nat) (bindF appF : MW9) (vis ctx fu po pl dep kb e ns hi : Word) (r : List Word) (m1 : Mem) :
    nbPosK1 n bindF appF vis ctx fu po pl dep kb e ns hi (some (r, m1)) = nbPosK2 n bindF appF vis ctx fu po pl dep kb e ns hi (r.headD 0)
      (noConstWf n m1 (rdW (m1.arr64 IW) ctx) (rdW (m1.arr64 IW) (ctx + 1)) (rdW (m1.arr64 IW) (ctx + 4)) hi
        (r.headD 0)) := rfl
theorem nbAppK4_some (ns : Word) (r : List Word) (m3 : Mem) :
    nbAppK4 ns (some (r, m3)) = some ([r.headD 0, ns], m3) := rfl
theorem nbAppK6_some (r : List Word) (m3 : Mem) :
    nbAppK6 (some (r, m3)) = some ([r.headD 0, r.tail.headD 0], m3) := rfl
theorem nbAppK5_some (contF : MW11) (m2 : Mem) (vis ctx fu po pl kb ns aO aL : Word) (v : List Word) (o : Word) :
    nbAppK5 contF m2 vis ctx fu po pl kb ns aO aL v (some o) = if o ≠ 0 then none
    else nbAppK6 (contF m2 vis ctx fu po pl kb (v.tail.headD 0) (v.tail.tail.headD 0) aO aL ns) := rfl
theorem nbAppK2_some (n : Nat) (contF : MW11) (vis ctx fu po pl kb hi ns aO aL : Word) (rh : List Word) (m2 : Mem) :
    nbAppK2 n contF vis ctx fu po pl kb hi ns aO aL (some (rh, m2)) =
    if eViewW m2 (rh.headD 0) = [] then none
    else if (eViewW m2 (rh.headD 0)).headD 0 = 1 then
      nbAppK4 ns (pfW n m2 vis ctx po pl kb hi ((eViewW m2 (rh.headD 0)).tail.headD 0) aO aL)
    else if (eViewW m2 (rh.headD 0)).headD 0 = 3 then
      nbAppK5 contF m2 vis ctx fu po pl kb ns aO aL (eViewW m2 (rh.headD 0))
        (containsW n m2 (rdW (m2.arr64 IW) ctx) (rdW (m2.arr64 IW) (ctx + 1)) ((eViewW m2 (rh.headD 0)).tail.headD 0))
    else none := rfl
theorem nbAppK1_some (n : Nat) (contF : MW11) (vis ctx fu po pl kb hi w ns : Word) (ra : List Word) (m1 : Mem) :
    nbAppK1 n contF vis ctx fu po pl kb hi w ns (some (ra, m1)) = nbAppK2 n contF vis ctx fu po pl kb hi ns (ra.headD 0) (ra.tail.headD 0)
      (gafF m1 [CWF, w]) := rfl
theorem nbContK4_some (keyF : MW13) (vis ctx fu po pl kb nn us aO aL ns nPc : Word) (r4 : List Word) (m4 : Mem) :
    nbContK4 keyF vis ctx fu po pl kb nn us aO aL ns nPc (some (r4, m4)) =
    if aL ≠ nPc + r4.headD 0 then none
    else nbAppK6 (keyF m4 vis ctx fu po pl kb nn us aO nPc nPc (r4.tail.headD 0) ns) := rfl
theorem nbContK3_some (cR : CallM) (k : Nat) (keyF : MW13) (vis ctx fu po pl kb nn us aO aL ns nPc hp : Word) (key : Word) (m3 : Mem) :
    nbContK3 cR k keyF vis ctx fu po pl kb nn us aO aL ns nPc hp (some (key, m3)) = nbContK4 keyF vis ctx fu po pl kb nn us aO aL ns nPc (nitWf cR k m3 vis ctx hp key) := rfl
theorem nbContK2_some (cR : CallM) (k : Nat) (keyF : MW13) (vis ctx fu po pl kb nn us aO aL ns nPc hp : Word) (w_ : List Word) (m2 : Mem) :
    nbContK2 cR k keyF vis ctx fu po pl kb nn us aO aL ns nPc hp (some (w_, m2)) = nbContK3 cR k keyF vis ctx fu po pl kb nn us aO aL ns nPc hp (posRecW m2 [nn, us, aO, nPc]) := rfl
theorem nbContK1_some (cR : CallM) (k : Nat) (keyF : MW13) (vis ctx fu po pl kb nn us aO aL ns : Word) (r : List Word) (m1 : Mem) :
    nbContK1 cR k keyF vis ctx fu po pl kb nn us aO aL ns (some (r, m1)) =
    if r.headD 0 = 0 then none
    else if aL < r.tail.headD 0 then none
    else nbContK2 cR k keyF vis ctx fu po pl kb nn us aO aL ns (r.tail.headD 0) (nhiW m1 ctx pl)
      (p2ccW k m1 ctx (nhiW m1 ctx pl) nn aO (r.tail.headD 0) (aO + r.tail.headD 0) (aL - r.tail.headD 0)) := rfl
theorem nbKeyK2_some (k : Nat) (newF : MW13) (vis ctx fu po pl kb nn us dO dL nPc cty ns key : Word) (r : List Word) (m2 : Mem) :
    nbKeyK2 k newF vis ctx fu po pl kb nn us dO dL nPc cty ns key (some (r, m2)) =
    if r.headD 0 ≠ 0 then
      match nkcW k m2 (rdW (m2.arr64 IW) ns) (rdW (m2.arr64 IW) (ns + 1)) key with
      | none => none
      | some b => if b ≠ 0 then some ([nestedW kb, ns], m2)
        else nbAppK6 (newF m2 vis ctx fu po pl kb nn us dO dL nPc cty ns)
    else nbAppK6 (newF m2 vis ctx fu po pl kb nn us dO dL nPc cty ns) := rfl
theorem nbKeyK1_some (k : Nat) (newF : MW13) (vis ctx fu po pl kb nn us dO dL nPc cty ns : Word) (key : Word) (m1 : Mem) :
    nbKeyK1 k newF vis ctx fu po pl kb nn us dO dL nPc cty ns (some (key, m1)) =
    match nkcW k m1 (rdW (m1.arr64 IW) (ns + 2)) (rdW (m1.arr64 IW) (ns + 3)) key with
    | none => none
    | some b => if b ≠ 0 then none
      else nbKeyK2 k newF vis ctx fu po pl kb nn us dO dL nPc cty ns key (dcWf k m1 ctx dO dL) := rfl
theorem nbNewK9_some (k : Nat) (ctx kb us dO dL ns gO gL : Word) (r : List Word) (m9 : Mem) :
    nbNewK9 k ctx kb us dO dL ns gO gL (some (r, m9)) = nbAppK6 (cfW k m9 ctx us dO dL gO gL (r.headD 0) (rdW (m9.arr64 IW) (ns + 2))
      (rdW (m9.arr64 IW) (ns + 3)) kb) := rfl
theorem nbNewK8_some (k : Nat) (frameF : MW13) (vis ctx fu kb us dO dL nPc ns wO wL hw gO gL : Word) (ns1 : Word) (m8 : Mem) :
    nbNewK8 k frameF vis ctx fu kb us dO dL nPc ns wO wL hw gO gL (some (ns1, m8)) = nbNewK9 k ctx kb us dO dL ns gO gL
      (frameF m8 vis ctx fu wO wL hw us dO dL nPc gO gL ns1) := rfl
theorem nbNewK7_some (k : Nat) (frameF : MW13) (vis ctx fu kb us dO dL nPc ns wO wL hw gO gL : Word) (ra : List Word) (m7 : Mem) :
    nbNewK7 k frameF vis ctx fu kb us dO dL nPc ns wO wL hw gO gL (some (ra, m7)) = nbNewK8 k frameF vis ctx fu kb us dO dL nPc ns wO wL hw gO gL
      (posRecW m7 [rdW (m7.arr64 IW) ns, rdW (m7.arr64 IW) (ns + 1), ra.headD 0, ra.tail.headD 0,
        rdW (m7.arr64 IW) (ns + 4), rdW (m7.arr64 IW) (ns + 5)]) := rfl
theorem nbNewK6_some (k : Nat) (frameF : MW13) (vis ctx fu kb us dO dL nPc ns wO wL hw gO gL : Word) (ra : List Word) (m6 : Mem) :
    nbNewK6 k frameF vis ctx fu kb us dO dL nPc ns wO wL hw gO gL (some (ra, m6)) = nbNewK7 k frameF vis ctx fu kb us dO dL nPc ns wO wL hw gO gL
      (appendW k m6 (ra.headD 0) (ra.tail.headD 0) (rdW (m6.arr64 IW) (ns + 2)) (rdW (m6.arr64 IW) (ns + 3))) := rfl
theorem nbNewK5_some (k : Nat) (frameF : MW13) (vis ctx fu kb us dO dL nPc ns wO wL hw : Word) (rg : List Word) (m5 : Mem) :
    nbNewK5 k frameF vis ctx fu kb us dO dL nPc ns wO wL hw (some (rg, m5)) = nbNewK6 k frameF vis ctx fu kb us dO dL nPc ns wO wL hw (rg.headD 0) (rg.tail.headD 0)
      (caW k m5 us dO dL (rg.headD 0) (rg.tail.headD 0) 0 0) := rfl
theorem nbNewK4_some (cR : CallM) (k : Nat) (frameF : MW13) (vis ctx fu kb us dO dL nPc ns wO wL mO mL hw : Word) (g0 : List Word) (m4 : Mem) :
    nbNewK4 cR k frameF vis ctx fu kb us dO dL nPc ns wO wL mO mL hw (some (g0, m4)) = nbNewK5 k frameF vis ctx fu kb us dO dL nPc ns wO wL hw
      (ggW cR k m4 vis ctx hw us dO dL mO mL (g0.headD 0) (g0.tail.headD 0)) := rfl
theorem nbNewK3_some (cR : CallM) (k : Nat) (frameF : MW13) (vis ctx fu kb us dO dL nPc ns wO wL mO mL hw : Word) (pr : Word) (m3 : Mem) :
    nbNewK3 cR k frameF vis ctx fu kb us dO dL nPc ns wO wL mO mL hw (some (pr, m3)) = nbNewK4 cR k frameF vis ctx fu kb us dO dL nPc ns wO wL mO mL hw (new1W m3 pr) := rfl
theorem nbNewK2_some (cR : CallM) (k : Nat) (frameF : MW13) (vis ctx fu kb nn us dO dL nPc cty ns wO wL : Word) (rm : List Word) (m2 : Mem) :
    nbNewK2 cR k frameF vis ctx fu kb nn us dO dL nPc cty ns wO wL (some (rm, m2)) = nbNewK3 cR k frameF vis ctx fu kb us dO dL nPc ns wO wL (rm.headD 0) (rm.tail.headD 0)
      (nhiW m2 ctx wL) (posRecW m2 [nn, cty]) := rfl
theorem nbNewK1_some (cR : CallM) (k : Nat) (frameF : MW13) (vis ctx fu kb nn us dO dL nPc cty ns : Word) (rw : List Word) (m1 : Mem) :
    nbNewK1 cR k frameF vis ctx fu kb nn us dO dL nPc cty ns (some (rw, m1)) = nbNewK2 cR k frameF vis ctx fu kb nn us dO dL nPc cty ns (rw.headD 0) (rw.tail.headD 0)
      (nfmW k m1 vis nn) := rfl
theorem nbFrameK8_some (r : List Word) (m8 : Mem) :
    nbFrameK8 (some (r, m8)) = some ([r.tail.tail.headD 0], m8) := rfl
theorem nbFrameK7_some (ctorsF : MW19) (vis ctx fu hi us dO dL gL ns p2O p2L nO nL cO cL : Word) (rh : List Word) (m7 : Mem) :
    nbFrameK7 ctorsF vis ctx fu hi us dO dL gL ns p2O p2L nO nL cO cL (some (rh, m7)) =
    if hi + gL < hi then none
    else if dL + gL < dL then none
    else nbFrameK8 (ctorsF m7 vis ctx 0 fu p2O p2L (hi + gL) us dO dL nO nL (rh.headD 0) (rh.tail.headD 0)
      cO cL ns 0 0) := rfl
theorem nbFrameK6_some (k : Nat) (ctorsF : MW19) (vis ctx fu hi us dO dL gO gL ns p2O p2L nO nL : Word) (rc : List Word) (m6 : Mem) :
    nbFrameK6 k ctorsF vis ctx fu hi us dO dL gO gL ns p2O p2L nO nL (some (rc, m6)) = nbFrameK7 ctorsF vis ctx fu hi us dO dL gL ns p2O p2L nO nL (rc.headD 0) (rc.tail.headD 0)
      (fhW k m6 hi gO gL 0 0) := rfl
theorem nbFrameK5_some (k : Nat) (ctorsF : MW19) (vis ctx fu hi us dO dL nPc gO gL ns : Word) (rp : List Word) (m5 : Mem) :
    nbFrameK5 k ctorsF vis ctx fu hi us dO dL nPc gO gL ns (some (rp, m5)) = nbFrameK6 k ctorsF vis ctx fu hi us dO dL gO gL ns (rp.headD 0) (rp.tail.headD 0)
      (rp.tail.tail.headD 0) (rp.tail.tail.tail.headD 0)
      (gcW k m5 vis nPc (rp.tail.tail.headD 0) (rp.tail.tail.tail.headD 0) 0 0) := rfl
theorem nbFrameK4_some (k : Nat) (ctorsF : MW19) (vis ctx fu po pl hi us dO dL nPc gO gL ns : Word) (w_ : List Word) (m4 : Mem) :
    nbFrameK4 k ctorsF vis ctx fu po pl hi us dO dL nPc gO gL ns (some (w_, m4)) = nbFrameK5 k ctorsF vis ctx fu hi us dO dL nPc gO gL ns
      (fgW k m4 hi us dO dL gO gL po pl 0 0) := rfl
theorem nbFrameK3_some (cR : CallM) (k : Nat) (ctorsF : MW19) (vis ctx fu po pl hi us dO dL nPc gO gL ns : Word) (ra : List Word) (m3 : Mem) :
    nbFrameK3 cR k ctorsF vis ctx fu po pl hi us dO dL nPc gO gL ns (some (ra, m3)) = nbFrameK4 k ctorsF vis ctx fu po pl hi us dO dL nPc gO gL ns
      (cR k "infer_type_core" [vis, hi, ra.headD 0] m3) := rfl
theorem nbFrameK2_some (cR : CallM) (k : Nat) (ctorsF : MW19) (vis ctx fu po pl hi us dO dL nPc gO gL ns : Word) (hc : Word) (m2 : Mem) :
    nbFrameK2 cR k ctorsF vis ctx fu po pl hi us dO dL nPc gO gL ns (some (hc, m2)) =
    if 4294967296 ≤ hc then none
    else nbFrameK3 cR k ctorsF vis ctx fu po pl hi us dO dL nPc gO gL ns (mknF m2 [hc, dO, dL]) := rfl
theorem nbFrameK1_some (cR : CallM) (k : Nat) (ctorsF : MW19) (vis ctx fu po pl hi us dO dL nPc gO gL ns : Word) (rn : List Word) (m1 : Mem) :
    nbFrameK1 cR k ctorsF vis ctx fu po pl hi us dO dL nPc gO gL ns (some (rn, m1)) =
    if 4294967296 ≤ rn.headD 0 then none
    else nbFrameK2 cR k ctorsF vis ctx fu po pl hi us dO dL nPc gO gL ns (ceinternW m1 (rn.headD 0) us) := rfl
theorem nbCtorsK3_some (ctorsF : MW19) (vis ctx root fu po pl hi us dO dL no nl hO hL cO cL ns2 : Word) (r : List Word) (m3 : Mem) :
    nbCtorsK3 ctorsF vis ctx root fu po pl hi us dO dL no nl hO hL cO cL ns2 (some (r, m3)) = ctorsF m3 vis ctx root fu po pl hi us dO dL no nl hO hL (cO + 1) (cL - 1) ns2
      (r.headD 0) (r.tail.headD 0) := rfl
theorem nbCtorsK2_some (k : Nat) (ctorsF : MW19) (vis ctx root fu po pl hi us dO dL no nl hO hL cO cL oO oL ns2 : Word) (rec : Word) (m2 : Mem) :
    nbCtorsK2 k ctorsF vis ctx root fu po pl hi us dO dL no nl hO hL cO cL oO oL ns2 (some (rec, m2)) = nbCtorsK3 ctorsF vis ctx root fu po pl hi us dO dL no nl hO hL cO cL ns2 (snocW k m2 oO oL rec) := rfl
theorem nbCtorsK1_some (k : Nat) (ctorsF : MW19) (vis ctx root fu po pl hi us dO dL no nl hO hL cO cL oO oL : Word) (r : List Word) (m1 : Mem) :
    nbCtorsK1 k ctorsF vis ctx root fu po pl hi us dO dL no nl hO hL cO cL oO oL (some (r, m1)) = nbCtorsK2 k ctorsF vis ctx root fu po pl hi us dO dL no nl hO hL cO cL oO oL
      (r.tail.tail.tail.headD 0) (posRecW m1 [r.headD 0, r.tail.headD 0, r.tail.tail.headD 0]) := rfl
theorem nbOneK7_some (ksO ksL closed : Word) (q : Word) (m7 : Mem) :
    nbOneK7 ksO ksL closed (some (q, m7)) = some ([ksO, ksL, closed, q], m7) := rfl
theorem nbOneK6_some (ksO ksL closed ns2 : Word) (r : List Word) (m6 : Mem) :
    nbOneK6 ksO ksL closed ns2 (some (r, m6)) = nbOneK7 ksO ksL closed (posRecW m6 [rdW (m6.arr64 IW) ns2, rdW (m6.arr64 IW) (ns2 + 1),
      rdW (m6.arr64 IW) (ns2 + 2), rdW (m6.arr64 IW) (ns2 + 3), r.headD 0, r.tail.headD 0]) := rfl
theorem nbOneK5_some (k : Nat) (ksO ksL closed ns2 : Word) (r : List Word) (m5 : Mem) :
    nbOneK5 k ksO ksL closed ns2 (some (r, m5)) = nbOneK6 ksO ksL closed ns2
      (snocW k m5 (rdW (m5.arr64 IW) (ns2 + 4)) (rdW (m5.arr64 IW) (ns2 + 5)) (r.headD 0)) := rfl
theorem nbOneK4_some (k : Nat) (ctx po pl us dO dL cv ksO ksL closed ns2 : Word) (r : List Word) (m4 : Mem) :
    nbOneK4 k ctx po pl us dO dL cv ksO ksL closed ns2 (some (r, m4)) =
    if r.headD 0 = 0 then none
    else nbOneK5 k ksO ksL closed ns2 (ncnWf k m4 ctx po pl us dO dL cv closed) := rfl
theorem nbOneK3_some (k : Nat) (ctx po pl hi us dO dL cv ksO ksL cur closed ns2 : Word) (r : List Word) (m3 : Mem) :
    nbOneK3 k ctx po pl hi us dO dL cv ksO ksL cur closed ns2 (some (r, m3)) =
    if r.headD 0 ≠ 0 then none
    else nbOneK4 k ctx po pl us dO dL cv ksO ksL closed ns2 (roW k m3 ctx hi cur) := rfl
theorem nbOneK2_some (k : Nat) (ctx po pl hi us dO dL cv nF : Word) (rw : List Word) (m2 : Mem) :
    nbOneK2 k ctx po pl hi us dO dL cv nF (some (rw, m2)) = nbOneK3 k ctx po pl hi us dO dL cv (rw.headD 0) (rw.tail.headD 0) (rw.tail.tail.headD 0)
      (rw.tail.tail.tail.headD 0) (rw.tail.tail.tail.tail.headD 0)
      (u4W k m2 (rw.headD 0) nF (rw.tail.tail.tail.headD 0) 0) := rfl
theorem nbOneK1_some (k : Nat) (walkF : MW10) (vis ctx root fu po pl hi us dO dL cv nF ns : Word) (rc : List Word) (m1 : Mem) :
    nbOneK1 k walkF vis ctx root fu po pl hi us dO dL cv nF ns (some (rc, m1)) = nbOneK2 k ctx po pl hi us dO dL cv nF
      (walkF m1 vis ctx root fu po pl hi nF (rc.headD 0) ns) := rfl
theorem nbWalkK3_some (ksO ksL cur ns : Word) (r : List Word) (m3 : Mem) :
    nbWalkK3 ksO ksL cur ns (some (r, m3)) = some ([ksO, ksL, cur, r.headD 0, ns], m3) := rfl
theorem nbWalkK2_some (k : Nat) (hi : Word) (r : List Word) (m2 : Mem) :
    nbWalkK2 k hi (some (r, m2)) = nbWalkK3 (r.headD 0) (r.tail.headD 0) (r.tail.tail.tail.tail.headD 0)
      (r.tail.tail.tail.tail.tail.headD 0)
      (closeW k m2 (r.tail.tail.headD 0) (r.tail.tail.tail.headD 0) hi (r.tail.tail.tail.tail.headD 0)) := rfl
theorem nbWalkK1_some (k : Nat) (fieldsF : MW14) (vis ctx po pl hi nF crest ns : Word) (rf : List Word) (m1 : Mem) :
    nbWalkK1 k fieldsF vis ctx po pl hi nF crest ns (some (rf, m1)) = nbWalkK2 k hi (fieldsF m1 vis ctx (rf.headD 0) po pl hi nF 0 crest ns 0 0 0 0) := rfl
theorem nbFieldsK5_some (fieldsF : MW14) (vis ctx fu po pl base nF j ns2 b kO kL : Word) (rd : List Word) (m5 : Mem) :
    nbFieldsK5 fieldsF vis ctx fu po pl base nF j ns2 b kO kL (some (rd, m5)) = fieldsF m5 vis ctx fu po pl base (nF - 1) (j + 1) b ns2 kO kL (rd.headD 0) (rd.tail.headD 0) := rfl
theorem nbFieldsK4_some (k : Nat) (fieldsF : MW14) (vis ctx fu po pl base nF j dO dL nd ns2 b : Word) (rk : List Word) (m4 : Mem) :
    nbFieldsK4 k fieldsF vis ctx fu po pl base nF j dO dL nd ns2 b (some (rk, m4)) = nbFieldsK5 fieldsF vis ctx fu po pl base nF j ns2 b (rk.headD 0) (rk.tail.headD 0)
      (snocW k m4 dO dL nd) := rfl
theorem nbFieldsK3_some (k : Nat) (fieldsF : MW14) (vis ctx fu po pl base nF j kO kL dO dL kd nd ns2 : Word) (rb : List Word) (m3 : Mem) :
    nbFieldsK3 k fieldsF vis ctx fu po pl base nF j kO kL dO dL kd nd ns2 (some (rb, m3)) = nbFieldsK4 k fieldsF vis ctx fu po pl base nF j dO dL nd ns2 (rb.headD 0) (snocW k m3 kO kL kd) := rfl
theorem nbFieldsK2_some (k : Nat) (fieldsF : MW14) (vis ctx fu po pl base nF j kO kL dO dL : Word) (v : List Word) (kd nd ns2 : Word) (fv : Word) (m2 : Mem) :
    nbFieldsK2 k fieldsF vis ctx fu po pl base nF j kO kL dO dL v kd nd ns2 (some (fv, m2)) =
    if 4294967296 ≤ fv then none
    else nbFieldsK3 k fieldsF vis ctx fu po pl base nF j kO kL dO dL kd nd ns2
      (i1F m2 [CWF, v.tail.tail.headD 0, fv, 0]) := rfl
theorem nbFieldsK1_some (k : Nat) (fieldsF : MW14) (vis ctx fu po pl base nF j kO kL dO dL : Word) (v : List Word) (rp : List Word) (m1 : Mem) :
    nbFieldsK1 k fieldsF vis ctx fu po pl base nF j kO kL dO dL v (some (rp, m1)) = nbFieldsK2 k fieldsF vis ctx fu po pl base nF j kO kL dO dL v (rp.headD 0) (rp.tail.headD 0)
      (rp.tail.tail.headD 0) (fvinternW m1 (base + j) (v.tail.headD 0)) := rfl
attribute [ind_grind] nbBindK6_some nbBindK5_some nbBindK4_some nbBindK3_some nbBindK2_some nbBindK1_some nbPosK3_some nbPosK4_some nbPosK5_some nbPosK2_some nbPosK1_some nbAppK4_some nbAppK6_some nbAppK5_some nbAppK2_some nbAppK1_some nbContK4_some nbContK3_some nbContK2_some nbContK1_some nbKeyK2_some nbKeyK1_some nbNewK9_some nbNewK8_some nbNewK7_some nbNewK6_some nbNewK5_some nbNewK4_some nbNewK3_some nbNewK2_some nbNewK1_some nbFrameK8_some nbFrameK7_some nbFrameK6_some nbFrameK5_some nbFrameK4_some nbFrameK3_some nbFrameK2_some nbFrameK1_some nbCtorsK3_some nbCtorsK2_some nbCtorsK1_some nbOneK7_some nbOneK6_some nbOneK5_some nbOneK4_some nbOneK3_some nbOneK2_some nbOneK1_some nbWalkK3_some nbWalkK2_some nbWalkK1_some nbFieldsK5_some nbFieldsK4_some nbFieldsK3_some nbFieldsK2_some nbFieldsK1_some

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

section spec
variable (p : Prog)

variable {p} (L : NbLook p) (cR : CallM) (hcR : CallSpec p cR) (n : Nat) (ih : NbSpec p cR n)
include L hcR ih

theorem nbFields_step (s₀ : St) (vis ctx fu po pl base nF j cur ns kO kL dO dL : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nest_fields" [vis, ctx, fu, po, pl, base, nF, j, cur, ns, kO,
      kL, dO, dL]
    ⦃fun r s' => LocEq s' s₀ ∧ nbFieldsW cR (n + 1) s₀.mem vis ctx fu po pl base nF j cur ns kO kL dO dL =
      some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, r.tail.tail.tail.headD 0,
        r.tail.tail.tail.tail.headD 0, r.tail.tail.tail.tail.tail.headD 0], s'.mem); ⊤⦄ := by
  obtain ⟨hPos, -, -, -, -, -, -, -, -, -, hFields⟩ := ih
  have R := L.ct.cr.rx
  simp only [invoke_eq _ L.pfields, callFn, nestFieldsL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      eView_spec p R.hl.hv n, hPos, internFVar_spec p R.hl.hff R.hl.hfp R.hl.hif n,
      i1F_spec p L.hi1 n, slSnoc_specW p R.ha L.nit.hc2 L.nag.hsn n, hFields] <;>
    simp_all [nbFieldsW_succ, nbFieldsK1_some, nbFieldsK2_some, nbFieldsK3_some, nbFieldsK4_some,
      nbFieldsK5_some, LocEq, BinOp.eval, St.setLocs_cons, Cmp.eval, St.setLoc_loc, St.setLoc_mem,
      St.setLocs_nil, Sig.retVal, Sig.retOr, Locals.init_cons_zero, Locals.init_cons_succ]

theorem nbWalk_step (s₀ : St) (vis ctx root fu po pl hi nF crest ns : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nest_ctors_walk" [vis, ctx, root, fu, po, pl, hi, nF, crest, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ nbWalkW cR (n + 1) s₀.mem vis ctx root fu po pl hi nF crest ns =
      some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, r.tail.tail.tail.headD 0,
        r.tail.tail.tail.tail.headD 0], s'.mem); ⊤⦄ := by
  obtain ⟨hPos, hBind, hApp, hCont, hKey, hNew, hFrame, hCtors, hOne, hWalk, hFields⟩ := ih
  have R := L.ct.cr.rx
  simp only [invoke_eq _ L.pwalk, callFn, nestCtorsWalkL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      whnfWalkFuel_spec' p L n, hFields,
      closeTelescope_spec p R.hk.hd R.hk.forF R.hk.forP R.hk.forI R.hk.forM L.hcl L.ab n] <;>
    simp_all [nbWalkW_succ, nbWalkK1_some, nbWalkK2_some, nbWalkK3_some,
      LocEq, St.setLocs_cons, Cmp.eval, St.setLoc_loc, St.setLoc_mem,
      St.setLocs_nil, Sig.retVal, Sig.retOr, Locals.init_cons_zero, Locals.init_cons_succ]

theorem nbOne_step (s₀ : St) (vis ctx root fu po pl hi us dO dL no nl hO hL cv nF ns : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nest_ctors_one" [vis, ctx, root, fu, po, pl, hi, us, dO, dL, no, nl, hO, hL, cv, nF, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ nbOneW cR (n + 1) s₀.mem vis ctx root fu po pl hi us dO dL no nl hO hL cv nF ns =
      some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, r.tail.tail.tail.headD 0], s'.mem); ⊤⦄ := by
  obtain ⟨hPos, hBind, hApp, hCont, hKey, hNew, hFrame, hCtors, hOne, hWalk, hFields⟩ := ih
  have R := L.ct.cr.rx
  simp only [invoke_eq _ L.pone, callFn, nestCtorsOneL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      nestCtorsCrest_spec p L.ct cR hcR n, hWalk, nestCtorsU4_spec p L.usl L.hu4 n,
      nestCtorsResOk_spec p L.nit.no L.nit.hoa L.hrh L.nt.ad L.hro n, nestCtorNf_spec' p L n,
      slSnoc_specW p R.ha L.nit.hc2 L.nag.hsn n, rec6_specW p R.ha L.h6 n] <;>
    simp_all [nbOneW_succ, nbOneK1_some, nbOneK2_some, nbOneK3_some, nbOneK4_some, nbOneK5_some,
      nbOneK6_some, nbOneK7_some,
      LocEq, BinOp.eval, St.setLocs_cons, Cmp.eval, St.setLoc_loc, St.setLoc_mem,
      St.setLocs_nil, Sig.retVal, Sig.retOr, Locals.init_cons_zero, Locals.init_cons_succ, rdW, pos2_getElem_getD]

theorem nbCtors_step (s₀ : St) (vis ctx root fu po pl hi us dO dL no nl hO hL cO cL ns oO oL : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nest_ctors" [vis, ctx, root, fu, po, pl, hi, us, dO, dL, no, nl, hO, hL, cO, cL, ns, oO, oL]
    ⦃fun r s' => LocEq s' s₀ ∧ nbCtorsW cR (n + 1) s₀.mem vis ctx root fu po pl hi us dO dL no nl hO hL cO cL ns oO oL =
      some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0], s'.mem); ⊤⦄ := by
  obtain ⟨hPos, hBind, hApp, hCont, hKey, hNew, hFrame, hCtors, hOne, hWalk, hFields⟩ := ih
  have R := L.ct.cr.rx
  simp only [invoke_eq _ L.pctors, callFn, nestCtorsL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      hOne, posRec3_specW p R.ha L.h3 n, slSnoc_specW p R.ha L.nit.hc2 L.nag.hsn n, hCtors] <;>
    simp_all [nbCtorsW_succ, nbCtorsK1_some, nbCtorsK2_some, nbCtorsK3_some,
      LocEq, BinOp.eval, St.setLocs_cons, Cmp.eval, St.setLoc_loc, St.setLoc_mem,
      St.setLocs_nil, Sig.retVal, Sig.retOr, Locals.init_cons_zero, Locals.init_cons_succ, rdW, pos2_getElem_getD]

theorem nbFrame_step (s₀ : St) (vis ctx fu po pl hi us dO dL nPc gO gL ns : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nest_frame" [vis, ctx, fu, po, pl, hi, us, dO, dL, nPc, gO, gL, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ nbFrameW cR (n + 1) s₀.mem vis ctx fu po pl hi us dO dL nPc gO gL ns = some ([r.headD 0], s'.mem); ⊤⦄ := by
  obtain ⟨hPos, hBind, hApp, hCont, hKey, hNew, hFrame, hCtors, hOne, hWalk, hFields⟩ := ih
  have R := L.ct.cr.rx
  simp only [invoke_eq _ L.pframe, callFn, nestFrameL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      naF_spec p L.na n, internConst_spec p R.cf R.cp R.ci n,
      mknF_spec p L.nt.ad n, hcR n "infer_type_core",
      nestFrameGrp_spec p R.ha L.nit.hc2 R.h2 R.h4 L.nag.hsn L.hfg n,
      nestGroupCtors_spec p L.nt L.nit.hc2 L.hap L.hgc n,
      nestFrameHoles_spec p R.ha L.nit.hc2 L.nag.hsn R.hl.hff R.hl.hfp R.hl.hif L.hfh n, hCtors] <;>
    simp_all [nbFrameW_succ, nbFrameK1_some, nbFrameK2_some, nbFrameK3_some, nbFrameK4_some,
      nbFrameK5_some, nbFrameK6_some, nbFrameK7_some, nbFrameK8_some,
      LocEq, BinOp.eval, St.setLocs_cons, Cmp.eval, St.setLoc_loc, St.setLoc_mem,
      St.setLocs_nil, Sig.retVal, Sig.retOr, Locals.init_cons_zero, Locals.init_cons_succ, rdW, pos2_getElem_getD]

theorem nbNew_step (s₀ : St) (vis ctx fu po pl kb nn us dO dL nPc cty ns : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nest_cont_new" [vis, ctx, fu, po, pl, kb, nn, us, dO, dL, nPc, cty, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ nbNewW cR (n + 1) s₀.mem vis ctx fu po pl kb nn us dO dL nPc cty ns =
      some ([r.headD 0, r.tail.headD 0], s'.mem); ⊤⦄ := by
  obtain ⟨hPos, hBind, hApp, hCont, hKey, hNew, hFrame, hCtors, hOne, hWalk, hFields⟩ := ih
  have R := L.ct.cr.rx
  simp only [invoke_eq _ L.pnew, callFn, nestContNewL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      nestWalkStack_spec' p L n, nestFrameMates_specW p L.fm n, nestCtxHiAt_specE p R.hi n,
      posRec2_specW p R.ha R.h2 n, slNew1_specW p R.ha L.hn1 n,
      nestGrowGroup_spec p L.nit R.h2 R.h4 L.nag.hsn L.hgg cR hcR n,
      nestContNewActive_spec p R.ha L.nit.hc2 R.h4 L.nag.hsn L.hca n,
      slAppend_specW p R.ha L.nit.hc2 L.hap n, rec6_specW p R.ha L.h6 n, hFrame,
      nestContNewFinish_spec p L.nag L.dc L.h6 L.hcf n] <;>
    simp_all [nbNewW_succ, nbNewK1_some, nbNewK2_some, nbNewK3_some, nbNewK4_some, nbNewK5_some,
      nbNewK6_some, nbNewK7_some, nbNewK8_some, nbNewK9_some, nbAppK6_some,
      LocEq, BinOp.eval, St.setLocs_cons, St.setLoc_loc, St.setLoc_mem,
      St.setLocs_nil, Sig.retVal, Sig.retOr, Locals.init_cons_zero, Locals.init_cons_succ, rdW, pos2_getElem_getD]

theorem nbKey_step (s₀ : St) (vis ctx fu po pl kb nn us dO dL nPc cty ns : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nest_cont_key" [vis, ctx, fu, po, pl, kb, nn, us, dO, dL, nPc, cty, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ nbKeyW cR (n + 1) s₀.mem vis ctx fu po pl kb nn us dO dL nPc cty ns =
      some ([r.headD 0, r.tail.headD 0], s'.mem); ⊤⦄ := by
  obtain ⟨hPos, hBind, hApp, hCont, hKey, hNew, hFrame, hCtors, hOne, hWalk, hFields⟩ := ih
  have R := L.ct.cr.rx
  simp only [invoke_eq _ L.pkey, callFn, nestContKeyL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      posRec4_specW p R.ha R.h4 n, nestKeysContains_spec p L.nag.hq L.nag.he L.nag.hkc n,
      dc_spec' p L.dc.hf L.dc.hh L.dc.hg L.dc.hp n, hNew] <;>
    simp_all [nbKeyW_succ, nbKeyK1_some, nbKeyK2_some, nbAppK6_some, nestedW, Cmp.evalW,
      LocEq, BinOp.eval, St.setLocs_cons, Cmp.eval, St.setLoc_loc, St.setLoc_mem,
      St.setLocs_nil, Sig.retVal, Sig.retOr, Locals.init_cons_zero, Locals.init_cons_succ, rdW, pos2_getElem_getD]

theorem nbCont_step (s₀ : St) (vis ctx fu po pl kb nn us aO aL ns : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nest_cont" [vis, ctx, fu, po, pl, kb, nn, us, aO, aL, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ nbContW cR (n + 1) s₀.mem vis ctx fu po pl kb nn us aO aL ns =
      some ([r.headD 0, r.tail.headD 0], s'.mem); ⊤⦄ := by
  obtain ⟨hPos, hBind, hApp, hCont, hKey, hNew, hFrame, hCtors, hOne, hWalk, hFields⟩ := ih
  have R := L.ct.cr.rx
  simp only [invoke_eq _ L.pcont, callFn, nestContL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      nt_spec' p L.nt n, nestCtxHiAt_specE p R.hi n,
      nestContChecks_spec p L.nit.no L.nit.hoa L.hpa L.usl.hbp L.dc.hf L.hpc L.hcc n, posRec4_specW p R.ha R.h4 n,
      nestInstType_spec' p L.nit cR hcR n, hKey] <;>
    simp_all [nbContW_succ, nbContK1_some, nbContK2_some, nbContK3_some, nbContK4_some, nbAppK6_some,
      LocEq, BinOp.eval, St.setLocs_cons, Cmp.eval, St.setLoc_loc, St.setLoc_mem,
      St.setLocs_nil, Sig.retVal, Sig.retOr, Locals.init_cons_zero, Locals.init_cons_succ]

theorem nbApp_step (s₀ : St) (vis ctx fu po pl kb hi w ns : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nest_pos_app" [vis, ctx, fu, po, pl, kb, hi, w, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ nbAppW cR (n + 1) s₀.mem vis ctx fu po pl kb hi w ns =
      some ([r.headD 0, r.tail.headD 0], s'.mem); ⊤⦄ := by
  obtain ⟨hPos, hBind, hApp, hCont, hKey, hNew, hFrame, hCtors, hOne, hWalk, hFields⟩ := ih
  have R := L.ct.cr.rx
  simp only [invoke_eq _ L.papp, callFn, nestPosAppL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      gaaF_spec p L.nt.ad n, gafF_spec p L.nt.ad n, eView_spec p R.hl.hv n,
      nestPosFvar_spec p L.pf n, slContains_spec p L.nit.no.hc n, hCont] <;>
    simp_all [nbAppW_succ, nbAppK1_some, nbAppK2_some, nbAppK4_some, nbAppK5_some, nbAppK6_some,
      LocEq, BinOp.eval, St.setLocs_cons, Cmp.eval, St.setLoc_loc, St.setLoc_mem,
      St.setLocs_nil, Sig.retVal, Sig.retOr, Locals.init_cons_zero, Locals.init_cons_succ, rdW, pos2_getElem_getD]

theorem nbBind_step (s₀ : St) (vis ctx fu po pl dep kb w ns : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nest_pos_bind" [vis, ctx, fu, po, pl, dep, kb, w, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ nbBindW cR (n + 1) s₀.mem vis ctx fu po pl dep kb w ns =
      some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0], s'.mem); ⊤⦄ := by
  obtain ⟨hPos, hBind, hApp, hCont, hKey, hNew, hFrame, hCtors, hOne, hWalk, hFields⟩ := ih
  have R := L.ct.cr.rx
  simp only [invoke_eq _ L.pbind, callFn, nestPosBindL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      nestCtxHiAt_specE p R.hi n, eView_spec p R.hl.hv n, nestOcc_spec' p L.nit.no n,
      internFVar_spec p R.hl.hff R.hl.hfp R.hl.hif n, i1F_spec p L.hi1 n, hPos,
      abF_spec p L.ab n, mkForall_spec p R.hk.hd R.hk.forF R.hk.forP R.hk.forI R.hk.forM n] <;>
    simp_all [nbBindW_succ, nbBindK1_some, nbBindK2_some, nbBindK3_some, nbBindK4_some, nbBindK5_some,
      nbBindK6_some,
      LocEq, BinOp.eval, St.setLocs_cons, Cmp.eval, St.setLoc_loc, St.setLoc_mem,
      St.setLocs_nil, Sig.retVal, Sig.retOr, Locals.init_cons_zero, Locals.init_cons_succ, rdW, pos2_getElem_getD]

theorem nbPos_step (s₀ : St) (vis ctx fu po pl dep kb e ns : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nest_pos" [vis, ctx, fu, po, pl, dep, kb, e, ns]
    ⦃fun r s' => LocEq s' s₀ ∧ nbPosW cR (n + 1) s₀.mem vis ctx fu po pl dep kb e ns =
      some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0], s'.mem); ⊤⦄ := by
  obtain ⟨hPos, hBind, hApp, hCont, hKey, hNew, hFrame, hCtors, hOne, hWalk, hFields⟩ := ih
  have R := L.ct.cr.rx
  simp only [invoke_eq _ L.ppos, callFn, nestPosL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      nestCtxHiAt_specE p R.hi n, hcR n "whnf_top", nestOcc_spec' p L.nit.no n, hBind, hApp] <;>
    simp_all [nbPosW_succ, nbPosK1_some, nbPosK2_some, nbPosK3_some, nbPosK4_some, nbPosK5_some,
      LocEq, BinOp.eval, St.setLocs_cons, Cmp.eval, St.setLoc_loc, St.setLoc_mem,
      St.setLocs_nil, Sig.retVal, Sig.retOr, Locals.init_cons_zero, Locals.init_cons_succ, rdW, pos2_getElem_getD]

end spec

end L.Ind

namespace L.Ind

open L.Arena

theorem nbSpec_zero (p : Prog) (cR : CallM) : NbSpec p cR 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;>
    exact triple_post (invoke_exec0 p _ _ _) (fun _ _ h => h.elim)

/-- **The block refines its word models**, at every exec fuel. -/
theorem nbSpec_all {p : Prog} (L : NbLook p) (cR : CallM) (hcR : CallSpec p cR) (n : Nat) : NbSpec p cR n := by
  induction n with
  | zero => exact nbSpec_zero p cR
  | succ n ih =>
    exact ⟨nbPos_step L cR hcR n ih, nbBind_step L cR hcR n ih, nbApp_step L cR hcR n ih, nbCont_step L cR hcR n ih, nbKey_step L cR hcR n ih,
      nbNew_step L cR hcR n ih, nbFrame_step L cR hcR n ih, nbCtors_step L cR hcR n ih, nbOne_step L cR hcR n ih, nbWalk_step L cR hcR n ih,
      nbFields_step L cR hcR n ih⟩

end L.Ind

end

end
