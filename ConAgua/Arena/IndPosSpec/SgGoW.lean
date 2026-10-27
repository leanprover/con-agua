import ConAgua.Arena.IndPosSpec.FgW
import ConAgua.Arena.IndPosSpec.MapOKStep
import ConAgua.Arena.IndPosSpec.SgF
import ConAgua.Arena.IndPosSpec.SgGoW2
import ConAgua.Arena.IndPosSpec.Snoc

/-!
# SgGoW

`rpConstW_fr`, `PosMR.setRf`, `sgK1_big`, `sgGoW_ok`.
-/

section

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem rpConstW_fr {n : Nat} {m m' : Mem} {no nl us b nn e r : Word}
    (h : rpConstW n m no nl us b nn e = some (r, m')) : RfFr m m' :=
  RfFr.of_mfr (rpConstW_mfr h) (by decide) (by decide)

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

/-- Across the banked `replace_fvars` walk. -/
theorem PosMR.setRf {m m' : Mem} (h : PosMR m) (hf : RxFr m m') (hn : ∃ M G g, RfInv m' M G g) :
    PosMR m' := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩, -⟩ := h
  exact ⟨⟨a, noMR_mfr hf (by decide) (by decide) ha⟩, ⟨b, dpMR_mfr hf (by decide) (by decide) hb⟩,
    ⟨c, rpMR_mfr hf (by decide) (by decide) hc⟩, ⟨d, hbMR_mfr hf (by decide) (by decide) hd⟩, hn⟩

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

section arms
variable (k : Nat) (m m1 m2 : Mem) (ctx f dO dL q j y z : Word)
theorem sgK1_big (h : 4294967296 ≤ y) : sgK1 k ctx f dO dL q j (some (y, m1)) = none := by simp [sgK1, h]
end arms
attribute [ind_grind] sgK1_big

section rel
variable (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)

theorem sgGoW_ok (k : Nat) :
    ∀ (m0 m m' : Mem) (a : AState) (ctx f dO dL q j : Word) (c : NestCtx) (holes ds acc : List EIdx)
      (M : Std.HashMap (EIdx × Word) EIdx) (G g : Word),
    sgGoW k m ctx f dO dL q j = some m' → StageR dn vis fe m a → IWGrow m0 m → iwTop m0 ≤ q.toNat →
    q.toNat + dL.toNat ≤ iwTop m → decCtx m0 ctx.toNat = some c → CtxIn m0 ctx.toNat (· < iwTop m0) →
    CtxSl m0 ctx.toNat → c.nP + c.names.length < 2 ^ 64 → FMOk m0 f.toNat (.keyMap c.params holes) →
    decHL m0 dO.toNat dL.toNat = some ds → (∀ j < dL.toNat, dO.toNat + j < iwTop m0) → j.toNat ≤ dL.toNat →
    decHL m q.toNat j.toNat = some acc → RfInv m M G g → PosMR m →
    ∃ ys a', ((ds.drop j.toNat).mapM (sgF c holes)).run a = .ok (ys, a') ∧
      decHL m' q.toNat dL.toNat = some (acc ++ ys) ∧ StageR dn vis fe m' a' ∧ IWGrow m0 m' ∧
      iwTop m ≤ iwTop m' ∧ (∃ M' G', RfInv m' M' G' g ∧ GKeep M M' G ∧ G ≤ G') ∧ PosMR m' := by
  induction k with
  | zero => intro m0 m m' a ctx f dO dL q j c holes ds acc M G g h; simp [sgGoW] at h
  | succ k ih =>
  intro m0 m m' a ctx f dO dL q j c holes ds acc M G g h hS hg0 hq0 hql hc hin hsl hb hfm hds hdsb hj hacc hR hP
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  have hxl := decHL_length m0 hds
  have hal := decHL_length m hacc
  by_cases hd : dL ≤ j
  · rw [sgGoW_done (h := hd)] at h
    cases h
    have hjl : j.toNat = dL.toNat := by have := UInt64.le_iff_toNat_le.mp hd; omega
    refine ⟨[], a, ?_, by rw [← hjl]; simpa using hacc, hS, hg0, Nat.le_refl _, ⟨M, G, hR, GKeep.refl _ _,
      UInt64.le_refl _⟩, hP⟩
    rw [List.drop_eq_nil_of_le (by omega)]; rfl
  rw [sgGoW_step (h := hd)] at h
  have hjl : j.toNat < dL.toNat := by
    have : ¬ dL.toNat ≤ j.toNat := fun e => hd (UInt64.le_iff_toNat_le.mpr e)
    omega
  -- the context's fields, in `m`
  obtain ⟨ec, hcin⟩ := hin.grow hg0
  have hcm : decCtx m ctx.toNat = some c := by rw [ec]; exact hc
  obtain ⟨hn, hn', -, -, hnP, hlvH, hlv, -, -, h11⟩ := ctx_fields hcm hcin htop
  have hnsum : (rdW (m.arr64 IW) ctx).toNat + (rdW (m.arr64 IW) (ctx + 1)).toNat ≤ iwTop m := by
    have hsl' := hsl.grow hin hg0
    obtain ⟨hnm, -⟩ := decCtx_some hcm
    obtain ⟨o, l, ho, hl, -⟩ := decAt_some hnm
    have r0 : (rdW (m.arr64 IW) ctx).toNat = o := by
      have := rd_iwN (m := m) (p := ctx) (i := 0) (by simpa using ho) (by simp; omega); simpa using this
    have r1 : (rdW (m.arr64 IW) (ctx + 1)).toNat = l := rd_iwN (by simpa using hl) (by simp; omega)
    rw [r0, r1]; exact hsl' 0 (by omega) o l (by simpa using ho) (by simpa using hl)
  -- the parameter
  have hoj := hdsb j.toNat hjl
  obtain ⟨hxH, hxd⟩ := rd_iwH (m := m) (p := dO) (i := j)
    (by rw [iwH_agree (RdS.of_grow hg0) hoj]; exact decHL_getI hds _ hjl) (by omega)
  generalize rdW (m.arr64 IW) (dO + j) = x at h hxH hxd
  cases k with
  | zero => simp [posRpW, sgK1] at h
  | succ k' =>
  simp only [posRpW] at h
  rcases hra : rpConstW k' m (rdW (m.arr64 IW) ctx) (rdW (m.arr64 IW) (ctx + 1)) (rdW (m.arr64 IW) (ctx + 10)) 0
      (rdW (m.arr64 IW) (ctx + 4)) x with _ | ⟨y, m1⟩; · rw [hra] at h; simp [sgK1] at h
  rw [hra] at h
  obtain ⟨mp0, hM⟩ := hP.rp
  obtain ⟨a1, hr1, hM1, hS1, hg1⟩ := rpConstW_ok k' dn fe vis m m1 a _ _ _ 0 _ x y c.nP c.names mp0 hra hS hxH hlvH hn
    (by omega) hnsum hnP (by rw [hnP]; omega) (by simp; omega) hM
  have hR1 := hR.frame (rpConstW_fr hra)
  by_cases hyb : 4294967296 ≤ y
  · rw [sgK1_big (h := hyb)] at h; simp at h
  rw [sgK1_ok (h := hyb)] at h
  rcases hrf : rxW (k' + 1) m1 f y with _ | ⟨z, m2⟩ <;> rw [hrf] at h; · simp [sgK2] at h
  rw [sgK2_some] at h
  have hg01 := hg0.trans hg1
  obtain ⟨a2, hr2, hzH, M2, G2, hS2, hg2, hR2, hk2, hG2⟩ := (rxOK_all dn fe vis (k' + 1)).2.2.2.2.2.2 m1 m2 a1 f y
    _ z M G g hrf hS1 (hfm.grow hg01) (lt_of_notbig hyb) hR1
  have hqj : (q + j).toNat = q.toNat + j.toNat := word_add_toNat (by omega)
  have hj1 : (j + 1).toNat = j.toNat + 1 := word_add_toNat (show j.toNat + 1 < 2 ^ 64 by have := dL.toNat_lt; omega)
  have hg12 := hg1.trans hg2
  have hacc2 : decHL m2 q.toNat j.toNat = some acc := by rw [decHL_grow hg12 (by omega)]; exact hacc
  have hdec3 := decHL_write m2 q j z acc hzH hS2.2.2.2.1 (by have := hS2.2.1; have := hg12.1; omega) hacc2
  have hS3 := hS2.set_iw (q + j) z
  have hg03 : IWGrow m0 (m2.set64 IW (q + j) z) := (hg0.trans hg12).set_iw (q + j) z (by omega)
  have ht3 : iwTop (m2.set64 IW (q + j) z) = iwTop m2 := by
    simp only [iwTop]; rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  have hP3 : PosMR (m2.set64 IW (q + j) z) :=
    ((hP.setRp (rpConstW_mfr hra) ⟨∅, hM1⟩).setRf (rxW_mfr hrf) ⟨M2, G2, g, hR2⟩).fr (MFr.set_iw _ _ _)
  obtain ⟨ys, a', hrun, hdec', hS', hg', ht', ⟨M', G', hR', hk', hG'⟩, hP'⟩ := ih m0 _ m' a2 ctx f dO dL q (j + 1) c
    holes ds (acc ++ [decE z]) M2 G2 g h hS3 hg03 hq0 (by rw [ht3]; have := hg12.1; omega) hc hin hsl hb hfm hds hdsb
    (by rw [hj1]; omega) (by rw [hj1]; exact hdec3) (hR2.frame (RfFr.set_iw _ _ _)) hP3
  refine ⟨decE z :: ys, a', ?_, by simpa using hdec', hS', hg', by have := hg12.1; omega, ⟨M', G', hR',
    hk2.trans hk' hG2, UInt64.le_trans hG2 hG'⟩, hP'⟩
  simp only [List.drop_eq_getElem_cons (show j.toNat < ds.length by omega), List.mapM_cons, StateT.run_bind, sgF, ← hxd, show (decI x : EIdx) = decE x from rfl, ← hlv]
  simp only [show ((0 : Word).toNat) = 0 from rfl] at hr1
  simp only [hr1, except_ok_bind, hr2]
  rw [hj1] at hrun
  rw [hrun]
  rfl

end rel

end L.Ind

end

end
