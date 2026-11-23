module

public import ConAgua.Arena.IotaFrameCtor
import ConAgua.Arena.RecClassSpec.IhW
import ConAgua.L.WordOff

@[expose] public section

/-!
# `iota_parts_at_body` refines `iotaPartsAtBody` (lane ronsync8)

`instantiate_lift_fast` (a core walk with its memo) needs the walk memos `AbsOK`; the relation
carries them.
-/

open ConRon.Arena
open Std.WP

namespace L.Ind

open L.Arena

/-- **`iota_parts_at_body` refines `iotaPartsAtBody`**, the walk memos kept. -/
@[refines ConRon.Arena.iotaPartsAtBody]
theorem iotaPartsAtBody_rel {p : Prog} (P : IotaFrameProg p) (n : Nat) (vis : Word) (fe : IFEnv)
    (cnP mI rP r lvls parO parL pdO pdL ctorBody : Word) (rl : IRecRule) (params pd : List EIdx)
    (hb : H ctorBody) :
    RelW (fun m args => callW p n "iota_parts_at_body" args m)
      [cnP, mI, rP, r, lvls, parO, parL, pdO, pdL, ctorBody]
      (fun m a => StageR vis fe m a ∧ AbsOK m ∧ decRule (erecP m) r.toNat = some rl ∧
        decHL m parO.toNat parL.toNat = some params ∧ parO.toNat + parL.toNat ≤ iwTop m ∧
        decHL m pdO.toNat pdL.toNat = some pd ∧ pdO.toNat + pdL.toNat ≤ iwTop m ∧
        lvls.toNat < 2 ^ 32)
      (iotaPartsAtBody cnP.toNat mI.toNat rP.toNat rl (decI lvls) params pd (decI ctorBody))
      (fun m m' a r x => KeepPost vis fe decOIPD m m' a r x ∧ AbsOK m') := by
  intro m m' a r0 hc ⟨hS, hA, hrl, hpar, hparb, hpd, hpdb, hlv⟩
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (iotaPartsAtBody_specW p P.iota_parts_at_body n _ cnP mI rP r lvls parO parL pdO pdL ctorBody) hc
  have hplen : params.length = parL.toNat := decHL_length m hpar
  rcases n with _ | n
  · simp [iotaPartsAtBodyW] at hW
  simp only [iotaPartsAtBodyW] at hW
  -- `instantiate_lift_fast`
  rcases h1 : callW p n "instantiate_lift_fast" [CWF, ctorBody, parO, parL, 0] m with _ | ⟨q1, m1⟩
  · rw [h1] at hW; simp [iotaPartsAtBodyW.k_instantiate_lift_fast] at hW
  rw [h1] at hW
  obtain ⟨s1, hs1, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (i1lF_spec p P.i1l n _ _) h1
  rw [hs1] at hW1
  obtain ⟨x1, a1, hrun1, ⟨hS1, hg1, hx1, hd1⟩, hA1⟩ :=
    i1lF_ok (fun _ => none) vis fe CWF ctorBody parO parL 0 hb params m m1 a q1 hW1 ⟨hS, hA, hpar⟩
  rw [CWF_eq, UInt64.toNat_zero] at hrun1
  unfold iotaPartsAtBody
  rw [StateT.run_bind, hrun1, except_ok_bind]
  simp only [iotaPartsAtBodyW.k_instantiate_lift_fast] at hW
  -- `strip_pis`
  rcases h2 : callW p n "strip_pis" [erRd m1 (r + Rule.nfields), q1.headD 0] m1 with _ | ⟨q2, m2⟩
  · rw [h2] at hW; simp [iotaPartsAtBodyW.k_strip_pis] at hW
  rw [h2] at hW
  have hs2 := stripF_of_callW P.strip h2
  obtain ⟨x2, a2, hrun2, hS2, hg2, hd2⟩ := stripF_pis_ok vis fe _ _ hx1 m1 m2 a1 q2 hs2 hS1
  have hA2 : AbsOK m2 := AFr.of_frame (stripF_frame hs2) (by decide) (by decide) hA1
  rw [rule_nfields_at hg1 hrl, hd1] at hrun2
  rw [StateT.run_bind, hrun2, except_ok_bind]
  simp only [iotaPartsAtBodyW.k_strip_pis] at hW
  rcases x2 with _ | ⟨fd, concl⟩
  · simp only [decOLE] at hd2
    rw [ite_eq_left hd2] at hW
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    exact ⟨none, a2, rfl, ⟨hS2, hg1.trans hg2, rfl⟩, hA2⟩
  obtain ⟨h21, hfd, hconcl⟩ := hd2
  rw [ite_eq_right (by rw [h21]; decide)] at hW
  dsimp only
  simp only [decW0E, headD_drop3] at hconcl
  -- `get_app_args_f`
  rcases h3 : callW p n "get_app_args_f" [CWF, q2.tail.tail.tail.headD 0] m2 with _ | ⟨q3, m3⟩
  · rw [h3] at hW; simp [iotaPartsAtBodyW.k_get_app_args_f] at hW
  rw [h3] at hW
  obtain ⟨s3, hs3, -, hg3'⟩ := triple_of_callW (s₀ := ⟨m2, Locals.init []⟩) (gaaF_spec0 p P.gaa _ _ _) h3
  rw [hs3] at hg3'
  obtain ⟨x3, a3, hrun3, hS3, hg3, hd3⟩ := gaaF_ok (fun _ => none) vis fe CWF _ hconcl.1 m2 m3 a2 q3 hg3' hS2
  have hA3 : AbsOK m3 := AFr.of_frame (gaaF_frame hg3') (by decide) (by decide) hA2
  rw [CWF_eq, hconcl.2] at hrun3
  rw [StateT.run_bind, hrun3, except_ok_bind]
  simp only [iotaPartsAtBodyW.k_get_app_args_f] at hW
  obtain ⟨hargs, hargsb⟩ := hd3
  simp only [L.getD_zero, Nat.zero_add, L.getD_one] at hargs hargsb
  have hlen := decHL_length _ hargs
  have hT3 := iwTop_lt' m3
  obtain ⟨io, il, hidx, hil, hj⟩ : ∃ io il : Word,
      decHL m3 io.toNat il.toNat = some (x3.drop cnP.toNat) ∧ io.toNat + il.toNat ≤ iwTop m3 ∧
      iotaPartsAtBodyW.j1 p cnP mI rP lvls parO parL pdO pdL (q2.tail.headD 0) (q2.tail.tail.headD 0)
        io il m3 = some (r0, s'.mem) := by
    by_cases c : q3.tail.headD 0 < cnP
    · rw [ite_eq_left c] at hW
      refine ⟨_, 0, ?_, ?_, hW⟩
      · have : x3.drop cnP.toNat = [] := by
          rw [List.drop_eq_nil_of_le]; rw [UInt64.lt_iff_toNat_lt] at c; omega
        rw [this]; simp [decHL, hslice?]
      · rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega), UInt64.toNat_zero]; omega
    · rw [ite_eq_right c] at hW
      refine ⟨_, _, ?_, ?_, hW⟩
      · have c' : cnP.toNat ≤ (q3.tail.headD 0).toNat := by
          have : ¬ _ := fun h => c (UInt64.lt_iff_toNat_lt.mpr h); omega
        rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega),
          UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)]
        exact decHL_drop _ hargs c'
      · have c' : cnP.toNat ≤ (q3.tail.headD 0).toNat := by
          have : ¬ _ := fun h => c (UInt64.lt_iff_toNat_lt.mpr h); omega
        rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega),
          UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)]
        omega
  clear hW
  simp only [iotaPartsAtBodyW.j1] at hj
  have hg13 := hg1.trans (hg2.trans hg3)
  have hilen := decHL_length _ hidx
  by_cases g1 : parL ≠ cnP
  · rw [ite_eq_left g1] at hj
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hj)
    have : ¬ params.length = cnP.toNat := by
      rw [hplen]; exact fun h => g1 (UInt64.toNat_inj.mp h)
    exact ⟨none, a3, by rw [ite_eq_right this]; rfl, ⟨hS3, hg13, rfl⟩, hA3⟩
  rw [ite_eq_right g1] at hj
  have g1' : params.length = cnP.toNat := by rw [hplen, Classical.not_not.mp g1]
  rw [ite_eq_left g1']
  by_cases g2 : mI < rP
  · rw [ite_eq_left g2] at hj
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hj)
    have : ¬ rP.toNat ≤ mI.toNat := by rw [UInt64.lt_iff_toNat_lt] at g2; omega
    exact ⟨none, a3, by rw [ite_eq_right this]; rfl, ⟨hS3, hg13, rfl⟩, hA3⟩
  rw [ite_eq_right g2] at hj
  have g2' : rP.toNat ≤ mI.toNat := by
    have : ¬ _ := fun h => g2 (UInt64.lt_iff_toNat_lt.mpr h); omega
  rw [ite_eq_left g2']
  have hmr : (mI - rP).toNat = mI.toNat - rP.toNat :=
    UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)
  by_cases g3 : il ≠ mI - rP
  · rw [ite_eq_left g3] at hj
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hj)
    have : ¬ (x3.drop cnP.toNat).length = mI.toNat - rP.toNat := by
      rw [hilen, ← hmr]; exact fun h => g3 (UInt64.toNat_inj.mp h)
    exact ⟨none, a3, by rw [ite_eq_right this]; rfl, ⟨hS3, hg13, rfl⟩, hA3⟩
  rw [ite_eq_right g3] at hj
  have g3' : (x3.drop cnP.toNat).length = mI.toNat - rP.toNat := by
    rw [hilen, ← hmr, Classical.not_not.mp g3]
  rw [ite_eq_left g3']
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hj)
  refine ⟨_, a3, rfl, ⟨hS3, hg13, rfl, ⟨?_, ⟨hidx, hil⟩, ⟨hlv, rfl⟩, ?_⟩, ?_⟩, hA3⟩
  · have := decRL_hl_grow hg3 hfd
    simp only [decRL, L.getD_one, L.getD_two, List.getD_cons_succ, List.getD_cons_zero,
      Nat.reduceAdd] at this ⊢
    exact this
  · simp only [decRL, List.getD_cons_succ, List.getD_cons_zero, Nat.reduceAdd]
    exact ⟨decHL_grow' hg13 hparb hpar, Nat.le_trans hparb hg13.iw⟩
  · simp only [decRL, List.getD_cons_succ, List.getD_cons_zero, Nat.reduceAdd]
    exact ⟨decHL_grow' hg13 hpdb hpd, Nat.le_trans hpdb hg13.iw⟩

end L.Ind
