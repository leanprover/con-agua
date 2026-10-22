import ConAgua.Arena.RecClassSpecK

/-!
# `RecClass`: `ClassGen.minorTy` — the conclusion and the composition (lane `indproofs2`, helper `rec2`)
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

section sims
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

/-- The model of `class_gen_minor_ty_concl2` simulates the twin's tail of `minorTy`. -/
theorem c2W_sim (n : Nat) (m : Mem) (a : AState) (g c d nPc fo fl ihso ihsl rao ral capp : Word)
    (G : ClassGen) (NPC : Nat) (fvs ihs ra : List EIdx) (hS : StageR dn vis fe m a)
    (hG : DecB (fun m => decCG m g.toNat) m G) (hns : G.nP + G.slots.length < 2 ^ 64)
    (hnpc : nPc.toNat = NPC)
    (hfvs : decHL m fo.toNat fl.toNat = some fvs) (hfb : fo.toNat + fl.toNat ≤ iwTop m)
    (hihs : decHL m ihso.toNat ihsl.toNat = some ihs) (hib : ihso.toNat + ihsl.toNat ≤ iwTop m)
    (hra : decHL m rao.toNat ral.toNat = some ra) (hrb : rao.toNat + ral.toNat ≤ iwTop m) (hcapp : H capp) :
    RSim (c2W (n + 1) m g c d nPc fo fl ihso ihsl rao ral capp) (do
      let mc ← G.motVar c.toNat
      let concl ← mkAppN mc (List.drop NPC ra ++ [decI capp])
      let fbs ← List.mapM G.binder fvs
      let r ← ConRon.Arena.closeTelescope (fbs ++ ihs) d.toNat concl
      pure (some r)) a (KP dn vis fe m decOE) := by
  rw [c2W_eq]
  refine RSim.bind (K := c2K1 n d nPc fo fl ihso ihsl rao ral capp) rfl (rec2SimMotVar n hS c hG hns) ?_
  rintro ⟨r1, m1⟩ mc a1 - ⟨hS1, hg1, hmcH, hmcd⟩
  dsimp only at hS1 hg1 hmcH hmcd
  subst hmcd
  rw [c2K1_some]
  have hra1 : decHL m1 rao.toNat ral.toNat = some ra := by rw [decHL_grow hg1 hrb]; exact hra
  have hrb1 := Nat.le_trans hrb hg1.1
  have hsl : decHL m1 (if nPc < ral then rao + nPc else rao).toNat (if nPc < ral then ral - nPc else 0).toNat =
      some (ra.drop NPC) ∧
      (if nPc < ral then rao + nPc else rao).toNat + (if nPc < ral then ral - nPc else 0).toNat ≤ iwTop m1 := by
    have hlen := decHL_length m1 hra1
    by_cases hc : nPc < ral
    · have hc' : nPc.toNat < ral.toNat := UInt64.lt_iff_toNat_lt.mp hc
      have e1 : (rao + nPc).toNat = rao.toNat + nPc.toNat := by
        rw [UInt64.toNat_add]; have := hS1.lt64 hrb1; omega
      have e2 : (ral - nPc).toNat = ral.toNat - nPc.toNat := by
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt hc)]
      simp only [if_pos hc, e1, e2]
      rw [← hnpc]
      exact ⟨decHL_drop nPc.toNat hra1 (by omega), by omega⟩
    · have hc' : ral.toNat ≤ nPc.toNat := by
        have : ¬ nPc.toNat < ral.toNat := fun x => hc (UInt64.lt_iff_toNat_lt.mpr x)
        omega
      simp only [if_neg hc]
      rw [List.drop_eq_nil_of_le (by rw [← hnpc]; omega)]
      exact ⟨by simp [decHL, hslice?], by simp; omega⟩
  refine RSim.lstep (K := c2K2 n d fo fl ihso ihsl (r1.headD 0)) rfl fun ⟨r2, m2⟩ h2 => ?_
  obtain ⟨hr2, hd2, hg2, -, -, ht2⟩ := snocW_dec h2 hS1.2.2.2.1 hS1.2.2.2.2.2 hsl.2 hcapp hsl.1
  have hS2 := snocW_stage h2 hS1
  rw [c2K2_some, hr2]
  simp only [List.headD_cons, List.tail_cons]
  refine RSim.bind (K := c2K2b n d fo fl ihso ihsl) rfl
    ((mkAppN_spec dn vis fe _ _ _ hmcH (ra.drop NPC ++ [decI capp])).sim ⟨hS2, hd2⟩) ?_
  rintro ⟨r3, m3⟩ body a3 - ⟨hS3, hg3, hbH, hbd⟩
  dsimp only at hS3 hg3 hbH hbd
  subst hbd
  rw [c2K2b_some, rec2MapM_genBinder]
  have hg13 := hg1.trans (hg2.trans hg3)
  cases n with
  | zero => intro b hb; simp [mcW, c2K3] at hb
  | succ n =>
  rw [mcW_eq]
  refine RSim.bind (K := fun o => c2K3 (mcK1 n d ihso ihsl (r3.headD 0) o)) rfl
    ((fvarTypeDs_spec dn vis fe _ _ fvs).sim ⟨hS3, by rw [decHL_grow hg13 hfb]; exact hfvs⟩) ?_
  rintro ⟨r4, m4⟩ fbs a4 - ⟨hS4, hg4, hfbs, hfbb⟩
  dsimp only at hS4 hg4 hfbs hfbb
  simp only [getD_zero, Nat.zero_add, getD_one] at hfbs hfbb
  rw [mcK1_some]
  have hg14 := hg13.trans hg4
  refine RSim.lstep (K := fun o => c2K3 (mcK2 n d (r3.headD 0) o)) rfl fun ⟨r5, m5⟩ h5 => ?_
  obtain ⟨hS5, hg5, hd5, hb5⟩ := rec2AppendW_dec h5 hS4 (decHL_decB hfbs hfbb)
    (by rw [decHL_grow hg14 hib]; exact hihs) (Nat.le_trans hib hg14.1)
  by_cases hov : d + r5.tail.headD 0 < d
  · rw [mcK2_big (h := hov)]; exact RSim.none
  rw [mcK2_ok (h := hov)]
  have hdl : d.toNat + (r5.tail.headD 0).toNat < 2 ^ 64 := by
    have : ¬ (d + r5.tail.headD 0).toNat < d.toNat := fun x => hov (UInt64.lt_iff_toNat_lt.mpr x)
    rw [UInt64.toNat_add] at this
    have h1 := d.toNat_lt; have h2 := (r5.tail.headD 0).toNat_lt
    omega
  refine RSim.bind (K := fun o => c2K3 (mcK3 o)) rfl (Q1 := fun b a' x =>
    StageR dn vis fe b.2 a' ∧ IWGrow m5 b.2 ∧ decW0E b.2 b.1 x) ?_ ?_
  · rintro ⟨r6, m6⟩ h6
    obtain ⟨x, a', hrun, hS', hg, hx⟩ := closeW_ok n dn fe vis m5 m6 a4 _ _ d _ _ r6 h6 hS5 hbH hd5
      (hS5.lt64 hb5) hb5 hdl
    exact ⟨x, a', hrun, hS', hg, hx⟩
  rintro ⟨r6, m6⟩ x a6 - ⟨hS6, hg6, hx⟩
  simp only [mcK3_some, c2K3_some]
  exact RSim.pure_some ⟨hS6, hg14.trans (hg5.trans hg6), rfl, by simpa [decW0E] using hx⟩

end sims

end L.Ind
