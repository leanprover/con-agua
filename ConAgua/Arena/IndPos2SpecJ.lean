import ConAgua.Arena.IndPos2SpecI

/-! # `IndPos2`'s leaves, continued (lane `indproofs2`, helpers `pos` (fork E) and `pos2`): `nestGrowGroup`;
`sl_snoc` over words. -/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `sl_snoc` over words -/

/-- **`sl_snoc` keeps the stage relation**: the pool grew by the new slice, whose words are the
source's and `x` (any words: pointers too). -/
theorem snocW_words {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {o l x : Word} {r : List Word}
    (h : snocW n m o l x = some (r, m')) (hS : StageR dn vis fe m a)
    (hsrc : o.toNat + l.toNat ≤ iwTop m) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧ (r.headD 0).toNat = iwTop m ∧
      (r.tail.headD 0).toNat = l.toNat + 1 ∧ iwTop m' = iwTop m + l.toNat + 1 ∧
      (∀ i < l.toNat, (m'.arr64 IW)[iwTop m + i]? = (m.arr64 IW)[o.toNat + i]?) ∧
      (m'.arr64 IW)[iwTop m + l.toNat]? = some x := by
  obtain ⟨hr, hl1, hqt, -, hg, htop, hget⟩ := snocW_core h hS.2.2.2.1 hS.2.2.2.2.2 hsrc
  subst hr
  refine ⟨snocW_stage h hS, hg, by simp [hqt], by simp [hl1], by omega, fun i hi => ?_, ?_⟩
  · rw [hget, ite_eq_right (by omega), ite_eq_left (by omega)]; congr 2; omega
  · rw [hget, ite_eq_left rfl]

/-! ## `nest_grow_group` refines `nestGrowGroup` -/

/-- A group's `(name, type)` pair records at `o, o + 1, …`, their words below the top. -/
def GrpAt (m : Mem) (o : Nat) (grp : List (NIdx × EIdx)) : Prop :=
  ∀ i (hi : i < grp.length), ∃ w c t : Word, (m.arr64 IW)[o + i]? = some w ∧ w.toNat + 1 < iwTop m ∧
    (m.arr64 IW)[w.toNat]? = some c ∧ H c ∧ decI c = grp[i].1 ∧
    (m.arr64 IW)[w.toNat + 1]? = some t ∧ H t ∧ decI t = grp[i].2

theorem GrpAt.grow {m m' : Mem} {o : Nat} {grp : List (NIdx × EIdx)} (h : GrpAt m o grp)
    (hb : o + grp.length ≤ iwTop m) (hg : IWGrow m m') : GrpAt m' o grp := fun i hi => by
  obtain ⟨w, c, t, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h i hi
  exact ⟨w, c, t, by rw [hg.2.2.1 _ (by omega)]; exact h1, by have := hg.1; omega,
    by rw [hg.2.2.1 _ (by omega)]; exact h3, h4, h5, by rw [hg.2.2.1 _ (by omega)]; exact h6, h7, h8⟩

/-- `nest_inst_type` at any exec fuel. -/
def nitWf (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | k + 1, m, vis, ctx, hi, key => nitW cR k m vis ctx hi key

theorem nestInstType_spec' (p : Prog) (hl : NitLook p) (cR : CallM) (hcR : CallSpec p cR) (k : Nat) (s₀ : St)
    (vis ctx hi key : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "nest_inst_type" [vis, ctx, hi, key]
    ⦃fun r s' => LocEq s' s₀ ∧ nitWf cR k s₀.mem vis ctx hi key = some ([r.headD 0, r.tail.headD 0], s'.mem); ⊤⦄ := by
  cases k with
  | zero => exact triple_post (invoke_exec0 p _ _ s₀) (fun _ _ h => h.elim)
  | succ k => exact nestInstType_spec p hl cR hcR k s₀ vis ctx hi key

mutual
def ggW (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _, _ => none
  | k + 1, m, vis, ctx, hi, us, dO, dL, cO, cL, gO, gL =>
    if cL = 0 then some ([gO, gL], m)
    else ggK1 cR k vis ctx hi us dO dL cO cL gO gL (rdW (m.arr64 IW) cO)
      (posRecW m [rdW (m.arr64 IW) cO, us, dO, dL])
def ggK1 (cR : CallM) (k : Nat) (vis ctx hi us dO dL cO cL gO gL c : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (key, m1) => ggK2 cR k vis ctx hi us dO dL cO cL gO gL c (nitWf cR k m1 vis ctx hi key)
def ggK2 (cR : CallM) (k : Nat) (vis ctx hi us dO dL cO cL gO gL c : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => ggK3 cR k vis ctx hi us dO dL cO cL gO gL (posRecW m2 [c, r2.tail.headD 0])
def ggK3 (cR : CallM) (k : Nat) (vis ctx hi us dO dL cO cL gO gL : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (pr, m3) => ggK4 cR k vis ctx hi us dO dL cO cL (snocW k m3 gO gL pr)
def ggK4 (cR : CallM) (k : Nat) (vis ctx hi us dO dL cO cL : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) => ggW cR k m4 vis ctx hi us dO dL (cO + 1) (cL - 1) (r4.headD 0) (r4.tail.headD 0)
end

section arms
variable (cR : CallM) (k : Nat) (m m1 m2 m3 m4 : Mem) (vis ctx hi us dO dL cO cL gO gL c key pr : Word) (r2 r4 : List Word)
theorem ggW_nil (h : cL = 0) : ggW cR (k + 1) m vis ctx hi us dO dL cO cL gO gL = some ([gO, gL], m) := by
  simp [ggW, h]
theorem ggW_cons (h : ¬ cL = 0) : ggW cR (k + 1) m vis ctx hi us dO dL cO cL gO gL =
    ggK1 cR k vis ctx hi us dO dL cO cL gO gL (rdW (m.arr64 IW) cO)
      (posRecW m [rdW (m.arr64 IW) cO, us, dO, dL]) := by simp [ggW, h]
theorem ggK1_some : ggK1 cR k vis ctx hi us dO dL cO cL gO gL c (some (key, m1)) =
    ggK2 cR k vis ctx hi us dO dL cO cL gO gL c (nitWf cR k m1 vis ctx hi key) := by rw [ggK1]
theorem ggK2_some : ggK2 cR k vis ctx hi us dO dL cO cL gO gL c (some (r2, m2)) =
    ggK3 cR k vis ctx hi us dO dL cO cL gO gL (posRecW m2 [c, r2.tail.headD 0]) := by rw [ggK2]
theorem ggK3_some : ggK3 cR k vis ctx hi us dO dL cO cL gO gL (some (pr, m3)) =
    ggK4 cR k vis ctx hi us dO dL cO cL (snocW k m3 gO gL pr) := by rw [ggK3]
theorem ggK4_some : ggK4 cR k vis ctx hi us dO dL cO cL (some (r4, m4)) =
    ggW cR k m4 vis ctx hi us dO dL (cO + 1) (cL - 1) (r4.headD 0) (r4.tail.headD 0) := by rw [ggK4]
end arms
attribute [ind_grind] ggW_nil ggW_cons ggK1_some ggK2_some ggK3_some ggK4_some

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

section census
variable (p : Prog) (hl : NitLook p) (h2 : p.lookup "rec2" = some rec2)
  (h4 : p.lookup "rec4" = some rec4) (hsn : p.lookup "sl_snoc" = some slSnoc)
  (hp : p.lookup "nest_grow_group" = some nestGrowGroupL)
include hl h2 h4 hsn hp

end census

end L.Ind
