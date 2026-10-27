import ConAgua.Arena.IndPosSpec.FgW
import ConAgua.Arena.IndPosSpec.NtyLook
import ConAgua.Arena.IndPosSpec.UnW
import ConAgua.Arena.IndPartsSpec.BlockCounts

/-!
# NtyW

`noaW_ok`, `ntyK6_none`, `ntyK3_none`, `nestInstTypeTy_spec`, `nestInstTypeTy_spec'`, `nestInstType_spec` and the lemmas only they use.
-/

section

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem noaW_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis no nl lo hi : Word) (names : List NIdx)
    (k : Nat) :
    ∀ (m m' : Mem) (a : AState) (off l : Word) (xs : List EIdx) (r : List Word),
    noaW k m no nl lo hi off l = some (r, m') → StageR dn vis fe m a →
    decHL m no.toNat nl.toNat = some names → no.toNat + nl.toNat ≤ iwTop m →
    decHL m off.toNat l.toNat = some xs → (∀ j < l.toNat, off.toNat + j < iwTop m) → PosMR m →
    ∃ b, (xs.anyM (fun x => ConRon.Arena.nestOcc names lo.toNat hi.toNat x)).run a = .ok (b, a) ∧
      StageR dn vis fe m' a ∧ IWGrow m m' ∧ r.headD 0 = (if b then 1 else 0) ∧ PosMR m' := by
  induction k with
  | zero => intro m m' a off l xs r h; simp [noaW] at h
  | succ k ih =>
    intro m m' a off l xs r h hS hn hnb hxs hxb hP
    have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
    by_cases hl0 : l = 0
    · rw [noaW_nil (h := hl0)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      subst hl0
      have : xs = [] := by simpa [decHL, hslice?] using hxs.symm
      subst this
      exact ⟨false, rfl, hS, IWGrow.refl _, rfl, hP⟩
    rw [noaW_cons (h := hl0)] at h
    have hlz : l.toNat ≠ 0 := fun e => hl0 (UInt64.toNat_inj.mp (by simpa using e))
    obtain ⟨l', hl'⟩ : ∃ l', l.toNat = l' + 1 := ⟨l.toNat - 1, by omega⟩
    have hxs2 := hxs
    simp only [decHL, hl', hslice?_succ, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hxs2
    obtain ⟨x, hx, xs', hxs', rfl⟩ := hxs2
    obtain ⟨hxH, hxd⟩ := rd_iwH0E (m := m) (o := off) (k := IdxKind.expr) (by simpa [iwH, iwA] using hx)
    have hoff1 : (off + 1).toNat = off.toNat + 1 :=
      word_add_toNat (show off.toNat + 1 < 2 ^ 64 by have := hxb 0 (by omega); omega)
    have hl1 : (l - 1).toNat = l' := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
    obtain ⟨mp0, hM0⟩ := hP.no
    rcases hno : noConstWf k m no nl lo hi (rdW (m.arr64 IW) off) with _ | ⟨b1, m1⟩ <;> rw [hno] at h; · simp [noaK] at h
    obtain ⟨c1, hrun1, hc1, hM1, hS1, hg1, hf1⟩ := noConstWf_ok k dn fe vis m m1 a no nl lo hi _ b1 names mp0 hno hS hxH
      hn (by omega) hM0
    have hP1 := hP.setNo hf1 ⟨∅, hM1⟩
    rw [decE_eq, hxd] at hrun1
    rw [List.anyM_cons]
    by_cases hb : b1 ≠ 0
    · rw [noaK_hit (h := hb)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have : c1 = true := by rw [← hc1]; simpa using hb
      subst this
      refine ⟨true, ?_, hS1, hg1, rfl, hP1⟩
      simp only [StateT.run_bind, hrun1, except_ok_bind, ite_true]; rfl
    · rw [noaK_miss (h := hb)] at h
      have : c1 = false := by rw [← hc1]; simpa using hb
      subst this
      obtain ⟨b, hrun, hS', hg', hr, hP'⟩ := ih m1 m' a (off + 1) (l - 1) xs' r h hS1
        (by rw [decHL_agree (RdS.of_grow hg1) (fun j hj => by omega)]; exact hn) (by have := hg1.1; omega)
        (by rw [hoff1, hl1, decHL_agree (RdS.of_grow hg1) (fun j hj => by have := hxb (j + 1) (by omega); omega)]
            simpa [decHL] using hxs')
        (fun j hj => by rw [hoff1, hl1] at *; have := hxb (j + 1) (by omega); have := hg1.1; omega) hP1
      refine ⟨b, ?_, hS', hg1.trans hg', hr, hP'⟩
      simp only [StateT.run_bind, hrun1, except_ok_bind, Bool.false_eq_true, ite_false]
      exact hrun

section arms
variable (cR : CallM) (k : Nat) (m1 m3 m4 m5 m6 : Mem) (key cvC : Word) (r r3 r4 r5 r6 : List Word)
theorem ntyK6_none (h : r6.headD 0 = 0) : ntyK6 (some (r6, m6)) = none := by rw [ntyK6, ite_eq_left h]
theorem ntyK3_none (h : r3.headD 0 = 0) : ntyK3 cR k key cvC (some (r3, m3)) = none := by rw [ntyK3, ite_eq_left h]
end arms
attribute [ind_grind] ntyK6_none ntyK3_none

theorem nestInstTypeTy_spec (p : Prog) (hl : NtyLook p) (cR : CallM) (hcR : CallSpec p cR) (k : Nat) (s₀ : St)
    (vis key : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "nest_inst_type_ty" [vis, key]
    ⦃fun r s' => LocEq s' s₀ ∧ ntyW cR k s₀.mem vis key = some ([r.headD 0], s'.mem); ⊤⦄ := by
  simp only [invoke_eq _ hl.hp, callFn, nestInstTypeTyL]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      envFind_specW p hl.hx hl.hg hl.hf k, viewLsLen_specE p hl.hls hl.hvl k,
      stripPis_specF p hl.hst k, cvLps_spec p hl.ha hl.hc hl.he hl.hcv k,
      hcR k "inst_lp_fast", instPisWith_spec p hl.hv hl.hip hl.hi1 k] <;>
    finish (gen := 20) [ntyW, rdW_eq, Locals.init_cons_zero]

theorem nestInstTypeTy_spec' (p : Prog) (hl : NtyLook p) (cR : CallM) (hcR : CallSpec p cR) (k : Nat) (s₀ : St)
    (vis key : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "nest_inst_type_ty" [vis, key]
    ⦃fun r s' => LocEq s' s₀ ∧ ntyWf cR k s₀.mem vis key = some ([r.headD 0], s'.mem); ⊤⦄ := by
  cases k with
  | zero => exact triple_post (invoke_exec0 p _ _ s₀) (fun _ _ h => h.elim)
  | succ k => exact nestInstTypeTy_spec p hl cR hcR k s₀ vis key

theorem nestInstType_spec (p : Prog) (hl : NitLook p) (cR : CallM) (hcR : CallSpec p cR) (k : Nat) (s₀ : St)
    (vis ctx hi key : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "nest_inst_type" [vis, ctx, hi, key]
    ⦃fun r s' => LocEq s' s₀ ∧ nitW cR k s₀.mem vis ctx hi key = some ([r.headD 0, r.tail.headD 0], s'.mem); ⊤⦄ := by
  simp only [invoke_eq _ hl.hp, callFn, nestInstTypeL]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      nestInstTypeTy_spec' p hl.ty cR hcR k, piBinders_spec p hl.ty.ha hl.hc2 hl.ty.hv hl.hs hl.hpb k,
      eView_spec p hl.ty.hv k, nestOccAny_spec p hl.no hl.hoa k, lvlEqFueled_specC p hl.hlf cR hcR k] <;>
    finish (gen := 20) [nitW, rdW_eq, Locals.init_cons_zero, List.getD_cons_zero, List.getD_cons_succ]

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

theorem ntyW_ok (k : Nat) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (m m' : Mem)
    (a : AState) (key : Word) (kk : NestKey) (r : List Word) (cR : CallM)
    (hI : IlpRd cR dn vis fe (IlpBase m a))
    (h : ntyW cR k m vis key = some (r, m')) (hS : StageR dn vis fe m a)
    (hk : decNK m key.toNat = some kk) (hkin : NKIn m key.toNat (· < iwTop m)) (hksl : NKSl m key)
 :
    ∃ cv caps a3 q a4 tl a5 ty, fe.find? kk.cname = some (.indInfo cv caps) ∧
      a.store.lss.viewLen kk.lvls = some cv.levelParams.length ∧
      (stripPis kk.ds.length cv.type).run a = .ok (some q, a3) ∧
      (instLPFast coreWalkFuel cv.levelParams kk.lvls cv.type).run a3 = .ok (tl, a4) ∧
      (ConRon.Arena.instPisWith kk.ds tl).run a4 = .ok (some ty, a5) ∧
      StageR dn vis fe m' a5 ∧ IWGrow m m' ∧ H (r.headD 0) ∧ decI (r.headD 0) = ty ∧ AFr m m' := by
  have hE := hS.1.env
  have hR := hS.1.arena.1
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  have hEb : erTop m ≤ (m.arr64 EREC).size := hS.2.2.1
  have hEs : (m.arr64 EREC).size < 2 ^ 64 := hS.2.2.2.2.1
  obtain ⟨hcH, hcd, hlH, hld, hds, hdsb, hk4⟩ := nk_fields hk hkin htop
  unfold ntyW at h
  rcases hef : envFindW m (rdW (m.arr64 IW) key) vis with _ | ⟨r1, m1⟩ <;> rw [hef] at h; · simp [ntyK1] at h
  have hm1 := envFindW_mem hef
  rw [hm1] at h hef
  rw [ntyK1_eq] at h
  by_cases hf0 : r1.headD 0 = 0
  · rw [ite_eq_left hf0] at h; simp at h
  rw [ite_eq_right hf0] at h
  obtain ⟨-, hfind, ci, hci⟩ := envFindW_hit hef hE hcH hf0
  rw [hci] at hfind
  by_cases h3 : rdW (m.arr64 EREC) (r1.tail.headD 0) ≠ 3
  · rw [ite_eq_left h3] at h; simp at h
  rw [ite_eq_right h3] at h
  generalize r1.tail.headD 0 = q at h hfind hci h3
  have hciq := decCI_idx hci
  have hszE := erecP_size_le m
  have hk3 : nat? (erecP m) q.toNat = some 3 := by
    have : (erecP m)[q.toNat]? = (m.arr64 EREC)[q.toNat]? := erecP_getE (by omega)
    simp only [nat?, this]
    have hb : q.toNat < (m.arr64 EREC).size := by omega
    have : rdW (m.arr64 EREC) q = 3 := by simpa using h3
    simp [rdW, hb] at this ⊢; rw [this]; rfl
  obtain ⟨cv, caps, rfl, hcaps⟩ := decCI_kind3 hci hk3
  have hb16 := decCI_indInfo_bound hci
  have hcv : decCV (erecP m) (q.toNat + 1) = some cv := by
    simp only [decCI, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at hci
    obtain ⟨kd, hkd, hci⟩ := hci
    rw [hk3] at hkd; cases hkd
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at hci
    obtain ⟨cv', h1, _, _, h2⟩ := hci
    cases h2; exact h1
  have e1 : (q + 1).toNat = q.toNat + 1 := word_add_toNat (by simp; omega)
  have e12 : (q + 1 + 2).toNat = q.toNat + 1 + 1 + 1 := by
    rw [word_add_toNat (by rw [e1]; simp; omega), e1]; rfl
  have e13 : (q + 1 + 3).toNat = q.toNat + 1 + 3 := by
    rw [word_add_toNat (by rw [e1]; simp; omega), e1]; rfl
  obtain ⟨-, hlps, hty⟩ := decCV_some hcv
  obtain ⟨wt, hwt, hwtH, hwtd⟩ := hd?_some hty
  have hrdt : rdW (m.arr64 EREC) (q + 1 + 3) = wt := by simp [rdW, e13, erecP_get hwt]
  simp only [hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hlps
  obtain ⟨lo, hlo, ll, hll, hsl⟩ := hlps
  have hlen : (rdW (m.arr64 EREC) (q + 1 + 2)).toNat = cv.levelParams.length := by
    rw [erecP_rdN hll e12]; simpa using (mapM_opt_length _ _ _ hsl).symm
  -- the level list's length
  rcases lsNodeW_cases m (rdW (m.arr64 IW) (key + 1)) with hln | ⟨o', l', hln⟩
  · rw [ite_eq_left hln] at h; simp at h
  rw [ite_eq_right (by rw [hln]; simp)] at h
  by_cases hneq : (lsNodeW m (rdW (m.arr64 IW) (key + 1))).tail.headD 0 ≠ rdW (m.arr64 EREC) (q + 1 + 2)
  · rw [ite_eq_left hneq] at h; simp at h
  rw [ite_eq_right hneq] at h
  have hvl := lsNodeW_viewLen hR hlH hln
  rw [hld] at hvl
  have hl'eq : l'.toNat = cv.levelParams.length := by
    rw [← hlen]; rw [hln] at hneq; rw [show l' = rdW (m.arr64 EREC) (q + 1 + 2) by simpa using hneq]
  rw [hl'eq] at hvl
  rw [hrdt] at h
  -- `strip_pis`
  rcases hst : stripF 6 m [rdW (m.arr64 IW) (key + 3), wt] with _ | ⟨r3, m3⟩ <;> rw [hst] at h; · simp [ntyK3] at h
  obtain ⟨x3, a3, hrun3, hS3, hg3, hx3⟩ := stripF_pis_ok dn vis fe _ wt hwtH m m3 a r3 hst hS
  have ha3 : a3 = a := stripPis_st _ _ _ _ _ hrun3
  subst a3
  have hdsl := decHL_length m hds
  rw [← hdsl, ← hwtd] at hrun3
  cases x3 with
  | none => have : r3.headD 0 = 0 := hx3; rw [ntyK3_none (h := this)] at h; simp at h
  | some q3 =>
  rw [ntyK3_some (h := by rw [hx3.1]; decide)] at h
  -- `cv_lps`
  have hcv3 : decCVp m3 (q + 1).toNat = some cv := by
    rw [e1]; exact (erecP_ext m3).decCV ((GrowX.of_grow (q := 0) (n := 0) hg3).erecP.decCV hcv)
  rcases hlp : cvLpsW k m3 (q + 1) with _ | ⟨r4, m4⟩ <;> rw [hlp] at h; · simp [ntyK4] at h
  rw [ntyK4_some] at h
  obtain ⟨hS4, hg4, hE4, hdec4, -⟩ := pos2_cvLpsW_stage hlp hS3 hcv3 (by rw [e1]; have := hg3.2.1; omega)
  have hg34 := hg3.trans hg4
  have hlv4 : rdW (m4.arr64 IW) (key + 1) = rdW (m.arr64 IW) (key + 1) := by
    have e : (key + 1).toNat = key.toNat + 1 := word_add_toNat (by simp; omega)
    simp only [rdW, e]; rw [hg34.2.2.1 _ (by omega)]
  have hwt4 : rdW (m4.arr64 EREC) (q + 1 + 3) = wt := by
    rw [hE4]
    have : (m3.arr64 EREC)[(q + 1 + 3).toNat]? = (m.arr64 EREC)[(q + 1 + 3).toNat]? := by
      rw [e13]; exact hg3.2.2.2 _ (by omega)
    simp only [rdW, this]; exact hrdt
  rw [hlv4, hwt4] at h
  -- `inst_lp_fast`
  rcases hil : cR k "inst_lp_fast" [CWF, r4.headD 0, r4.tail.headD 0, rdW (m.arr64 IW) (key + 1), wt] m4 with _ | ⟨r5, m5⟩ <;> rw [hil] at h; · simp [ntyK5] at h
  rw [ntyK5_some] at h
  obtain ⟨tl, a4, hrun4, ⟨hS5, hg5, htlH, htld⟩, -, hA5⟩ :=
    hI k CWF _ _ _ _ cv.levelParams m4 m5 a r5 hlH hwtH ⟨rfl, (stripF_frame hst).trans (erToIwW_iwFr hlp)⟩ hS4
      hdec4 hil
  rw [CWF_eq, hld, ← hwtd] at hrun4
  have hg35 := hg34.trans hg5
  have hrd2 : rdW (m5.arr64 IW) (key + 2) = rdW (m.arr64 IW) (key + 2) := by
    have e : (key + 2).toNat = key.toNat + 2 := word_add_toNat (by simp; omega)
    simp only [rdW, e]; rw [hg35.2.2.1 _ (by omega)]
  have hrd3 : rdW (m5.arr64 IW) (key + 3) = rdW (m.arr64 IW) (key + 3) := by
    have e : (key + 3).toNat = key.toNat + 3 := word_add_toNat (by simp; omega)
    simp only [rdW, e]; rw [hg35.2.2.1 _ (by omega)]
  rw [hrd2, hrd3] at h
  -- `inst_pis_with`
  rcases hiw : instW k m5 (rdW (m.arr64 IW) (key + 2)) (rdW (m.arr64 IW) (key + 3)) (r5.headD 0) with _ | ⟨r6, m6⟩ <;> rw [hiw] at h; · simp [ntyK6] at h
  obtain ⟨x6, a5, hrun5, hS6, hg6, hx6⟩ := instW_ok k dn fe vis m5 m6 a4 _ _ _ kk.ds r6 hiw hS5 htlH
    (by rw [decHL_agree (RdS.of_grow hg35) (fun j hj => hdsb j hj)]; exact hds) (by unfold NKSl at hksl; omega)
    (by have := hg35.1; exact Nat.le_trans hksl this)
  rw [htld] at hrun5
  cases x6 with
  | none => have : r6.headD 0 = 0 := hx6; rw [ntyK6_none (h := this)] at h; simp at h
  | some ty =>
  obtain ⟨hx61, hx6H, hx6d⟩ := hx6
  rw [ntyK6_some (h := by rw [hx61]; decide)] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  exact ⟨cv, caps, a, q3, a4, tl, a5, ty, by rw [← hcd]; exact hfind, hvl, hrun3, hrun4, hrun5, hS6,
    (hg35.trans hg6), hx6H, hx6d, (AFr.iw (stripF_frame hst)).trans ((AFr.iw (erToIwW_iwFr hlp)).trans
      (hA5.trans (instW_afr _ _ _ _ _ _ _ hiw)))⟩

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

theorem nestInstType_spec' (p : Prog) (hl : NitLook p) (cR : CallM) (hcR : CallSpec p cR) (k : Nat) (s₀ : St)
    (vis ctx hi key : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "nest_inst_type" [vis, ctx, hi, key]
    ⦃fun r s' => LocEq s' s₀ ∧ nitWf cR k s₀.mem vis ctx hi key = some ([r.headD 0, r.tail.headD 0], s'.mem); ⊤⦄ := by
  cases k with
  | zero => exact triple_post (invoke_exec0 p _ _ s₀) (fun _ _ h => h.elim)
  | succ k => exact nestInstType_spec p hl cR hcR k s₀ vis ctx hi key

end L.Ind

end

end
