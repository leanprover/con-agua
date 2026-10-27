import ConAgua.Arena.DeclDivModSpec.DmCgW
import ConAgua.Arena.DeclDivModSpec.EqAt1
import ConAgua.Arena.IndRealApdT
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen

/-!
# Sc0List

`DmProg5`, `applied_ref`, `sc0List_specW`, `sc0ListW`, `sc0List_ref`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

structure DmProg5 (p : Prog) : Prop extends DmProg2 p where
  lSlCons : p.lookup "sl_cons" = some slCons
  lIwCopy : p.lookup "iw_copy" = some iwCopy
  lSubstConst0 : p.lookup "subst_const0" = some substConst0L
  lSubstConstAll : p.lookup "subst_const_all" = some substConstAllL
  lSubstConst0List : p.lookup "subst_const0_list" = some substConst0ListL
  lConstsResolveAll : p.lookup "consts_resolve_all" = some constsResolveAllL
  lDivModCertGuard : p.lookup "div_mod_cert_guard" = some divModCertGuardL
  bvb : BvbProg p
  hf : HfF p
  /-- `all_level_params_defined`'s program (the guards under `StageT`, `DeclDivGateT1.lean`). -/
  apd : ApdF p

section applied
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {p : Prog}

set_option maxHeartbeats 1600000 in
theorem applied_ref (hD : DmProg5 p) (pr ho hl : Word) (hyps : List EIdx) :
    CallRef p "div_mod_cert_applied" [pr, ho, hl]
      (fun m s => StageR dn vis fe m s ∧ H pr ∧ decHL m ho.toNat hl.toNat = some hyps ∧
        ho.toNat + hl.toNat ≤ iwTop m)
      (divModCertApplied (decE pr) hyps) (KeepPost dn vis fe decW0E) := by
  refine CallRef.of_sim (M := fun k mq => appliedW p (k + 1) mq pr ho hl)
    (fun k s₀ => applied_specW p hD.lDivModCertApplied (k + 1) s₀ pr ho hl) fun k m s ⟨hS, hpr, hd, hb⟩ => ?_
  rw [appliedW.arm1]; unfold divModCertApplied
  have hM := hD.toMasterProg
  refine Sim.ntB ((natVar_ref hD.toDmProg2 0).simG hS (.refl m)) fun r1 _ m1 a1 ⟨hS1, hg1, hl1, rfl⟩ => ?_
  refine Sim.ntB ((natVar_ref hD.toDmProg2 1).simG hS1 hg1) fun r2 _ m2 a2 ⟨hS2, hg2, hl2, rfl⟩ => ?_
  refine Sim.ntB ((mkApp_ref hM pr (r1.headD 0)).simG hS2 hg2) fun r3 _ m3 a3 ⟨hS3, hg3, hl3, rfl⟩ => ?_
  refine Sim.ntB ((mkApp_ref hM (r3.headD 0) (r2.headD 0)).simG hS3 hg3) fun r4 _ m4 a4 ⟨hS4, hG4, hl4, rfl⟩ => ?_
  have hlen := decHL_length m hd
  have h1w : (1 : Word).toNat = 1 := rfl
  have h2w : (2 : Word).toNat = 2 := rfl
  rcases hyps with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · have hn1 : hl ≠ 1 := fun e => by rw [e] at hlen; simp at hlen
    have hn2 : hl ≠ 2 := fun e => by rw [e] at hlen; simp at hlen
    rw [ite_eq_right hn1, ite_eq_right hn2]; exact Sim.ret ⟨hS4, hG4, hl4, rfl⟩
  · obtain rfl : hl = 1 := UInt64.toNat_inj.mp (by simp at hlen ⊢; omega)
    obtain ⟨-, hwlt, rfl, -⟩ := decHL_cons_iw hS.2.2.2.1 hd
    rw [ite_eq_left rfl, iw_rd_grow hG4 (by simp only [h1w] at hb; omega)]
    refine Sim.ntB ((internFVar_ref hM 2 _ hwlt).simG hS4 hG4) fun r5 _ m5 a5 ⟨hS5, hg5, hl5, rfl⟩ => ?_
    exact Sim.ntRet ((mkApp_ref hM (r4.headD 0) (r5.headD 0)).simG hS5 hg5) fun _ _ _ _ _ h => h
  · obtain rfl : hl = 2 := UInt64.toNat_inj.mp (by simp at hlen ⊢; omega)
    obtain ⟨-, hwlt, rfl, hrest⟩ := decHL_cons_iw hS.2.2.2.1 hd
    obtain ⟨-, hwlt2, rfl, -⟩ := decHL_cons_iw hS.2.2.2.1 hrest
    have hlt2 : (ho + 1).toNat < iwTop m := by
      have h1 := hS.2.1; have h2 := hS.2.2.2.1; simp only [h2w] at hb; have e := word_add_one (w := ho) (by omega); omega
    rw [ite_eq_right (by decide), ite_eq_left rfl, iw_rd_grow hG4 (by simp only [h2w] at hb; omega)]
    refine Sim.ntB ((internFVar_ref hM 2 _ hwlt).simG hS4 hG4) fun r5 _ m5 a5 ⟨hS5, hg5, hl5, rfl⟩ => ?_
    refine Sim.ntB ((mkApp_ref hM (r4.headD 0) (r5.headD 0)).simG hS5 hg5) fun r6 _ m6 a6 ⟨hS6, hg6, hl6, rfl⟩ => ?_
    rw [iw_rd_grow hg6 hlt2]
    refine Sim.ntB ((internFVar_ref hM 3 _ hwlt2).simG hS6 hg6) fun r7 _ m7 a7 ⟨hS7, hg7, hl7, rfl⟩ => ?_
    exact Sim.ntRet ((mkApp_ref hM (r6.headD 0) (r7.headD 0)).simG hS7 hg7) fun _ _ _ _ _ h => h
  · have hn1 : hl ≠ 1 := fun e => by rw [e] at hlen; simp at hlen
    have hn2 : hl ≠ 2 := fun e => by rw [e] at hlen; simp at hlen
    rw [ite_eq_right hn1, ite_eq_right hn2]; exact Sim.ret ⟨hS4, hG4, hl4, rfl⟩

/-! ## `subst_const0_list` -/

/-- **`subst_const0_list` is its model `sc0ListW`** (generated). -/
l_model sc0List_specW (p : Prog) (hp : p.lookup "subst_const0_list" = some substConst0ListL)
  fns [hp ↦ sc0ListW list]
  specs [callW_spec p n "subst_const0", callW_spec p n "subst_const0_list", callW_spec p n "sl_cons"]
  grind [arena_grind] finish [ntBW, rdW_eq] gen 30 heartbeats 1600000 bind ntBW instances 10000

theorem sc0List_ref (hD : DmProg5 p) (hs0 : SubstC0 p dn vis fe) (nm r : Word) (hn : H nm) (hr : H r) :
    ∀ (hyps : List EIdx) (o l : Word) (k : Nat) (m : Mem) (a : AState) (res : List Word) (m' : Mem),
      StageR dn vis fe m a → decHL m o.toNat l.toNat = some hyps → o.toNat + l.toNat ≤ iwTop m →
      callW p k "subst_const0_list" [nm, r, o, l] m = some (res, m') →
      ∃ x a', (substConst0List (decI nm) (decE r) hyps).run a = .ok (x, a') ∧
        KeepPost dn vis fe (decRL (fun m => decHL m) 0) m m' a' res x := by
  intro hyps
  induction hyps with
  | nil =>
    intro o l k m a res m' hS hd hb hc
    have hl0 : l = 0 := by
      have := decHL_length m hd
      exact UInt64.toNat_inj.mp (by simp at this ⊢; omega)
    cases k with
    | zero => rw [callW_zero] at hc; cases hc
    | succ k =>
    have hw := callW_model (M := fun mm => sc0ListW p (k + 1) mm nm r o l)
      (sc0List_specW p hD.lSubstConst0List (k + 1) · nm r o l) hc
    simp only [sc0ListW.eq_2, hl0, ite_true, Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    refine ⟨[], a, rfl, hS, IWGrow.refl _, ?_⟩
    simp only [decRL, List.getD_cons_zero, List.getD_cons_succ]
    exact ⟨by simp [decHL, hslice?], by simp⟩
  | cons h hs ih =>
    intro o l k m a res m' hS hd hb hc
    cases k with
    | zero => rw [callW_zero] at hc; cases hc
    | succ k =>
    obtain ⟨hl0, hwlt, hh, hrest⟩ := decHL_cons_iw hS.2.2.2.1 hd
    subst hh
    have hw := callW_model (M := fun mm => sc0ListW p (k + 1) mm nm r o l)
      (sc0List_specW p hD.lSubstConst0List (k + 1) · nm r o l) hc
    rw [sc0ListW.eq_2] at hw
    rw [ite_eq_right hl0] at hw
    replace hw := ntBW_some hw; obtain ⟨r1, m1, h1, hw⟩ := hw
    obtain ⟨x1, a1, hrun1, hS1, hg1, hl1, hx1⟩ := hs0 nm r _ hn hr hwlt k m a r1 m1 hS h1
    replace hw := ntBW_some hw; obtain ⟨r2, m2, h2, hw⟩ := hw
    have hlpos : 0 < l.toNat := Nat.pos_of_ne_zero (fun e => hl0 (UInt64.toNat_inj.mp (by simpa using e)))
    have hsz := hS.2.2.2.1
    have hI1 := hS.2.1
    have ho1 : (o + 1).toNat = o.toNat + 1 := by
      rw [UInt64.toNat_add]; simp; omega
    have hl1' : (l - 1).toNat = l.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
    have hrest1 : decHL m1 (o + 1).toNat (l - 1).toNat = some hs := by
      rw [ho1, hl1']
      rw [ho1, hl1'] at hrest
      rw [decHL_grow hg1 (by omega)]; exact hrest
    obtain ⟨x2, a2, hrun2, hS2, hg2, hd2⟩ := ih (o + 1) (l - 1) k m1 a1 r2 m2 hS1 hrest1
      (by rw [ho1, hl1']; have := hg1.1; omega) h2
    replace hw := ntBW_some hw; obtain ⟨r3, m3, h3, hw⟩ := hw
    simp only [Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨rfl, rfl⟩ := hw
    obtain ⟨s', hs', -, hcons⟩ := triple_of_callW (s₀ := ⟨m2, Locals.init []⟩)
      (slCons_specW p hD.lIwAlloc hD.lIwCopy hD.lSlCons k _ (r1.headD 0) (r2.headD 0) (r2.tail.headD 0)) h3
    have hcons' : consW k m2 (r1.headD 0) (r2.headD 0) (r2.tail.headD 0) = some (r3, m3) := by
      rw [← hs']; exact hcons
    simp only [decRL, Nat.zero_add, ntGetD0, ntGetD1] at hd2
    obtain ⟨hS3, hg3, hd3, ht3⟩ := consW_stage hcons' hS2 hd2.2 hl1 hd2.1
    refine ⟨x1 :: x2, a2, ?_, hS3, hg1.trans (hg2.trans hg3), ?_⟩
    · simp only [substConst0List, StateT.run_bind, StateT.run_pure]
      have hrun1' : (substConst0 (decI nm) (decE r) coreWalkFuel (decI (rdW (m.arr64 IW) o))).run a =
          .ok (x1, a1) := hrun1
      simp only [hrun1', exc_ok_bind', hrun2]
      rfl
    · simp only [decRL, Nat.zero_add, ntGetD0, ntGetD1, List.headD_cons, List.tail_cons]
      rw [← hx1]
      exact ⟨hd3, by omega⟩

end applied

end L.Ind

end
