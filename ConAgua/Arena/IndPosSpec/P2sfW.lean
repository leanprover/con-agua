import ConAgua.Arena.IndPosSpec.BvbWMfr
import ConAgua.Arena.IndPosSpec.Mfr
import ConAgua.Arena.IndPosSpec.P2rtW
import ConAgua.Arena.IndPosSpec.Pos2WfWfSome
import ConAgua.Arena.IndPosSpec.RootOutsB

/-!
# P2sfW

`PosMR.setDp`, `p2sfW_ok`.
-/

section

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- Across a `depth` walk. -/
theorem PosMR.setDp {m m' : Mem} (h : PosMR m) (hf : MFr [DPM] [206, 207] m m')
    (hn : ∃ mp, dpMR m' mp) : PosMR m' := by
  obtain ⟨⟨a, ha⟩, -, ⟨c, hc⟩, ⟨d, hd⟩, ⟨M, G, g, hR⟩⟩ := h
  exact ⟨⟨a, noMR_mfr hf (by decide) (by decide) ha⟩, hn, ⟨c, rpMR_mfr hf (by decide) (by decide) hc⟩,
    ⟨d, hbMR_mfr hf (by decide) (by decide) hd⟩, ⟨M, G, g, hR.mfr hf (by decide) (by decide)⟩⟩

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

local notation "V" => ConLeche.CheckMode.verified

theorem p2sfW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (dO dL : Word) (ds : List EIdx) (m0 : Mem) (hlen : ds.length = dL.toNat)
    (hel : ∀ j < dL.toNat, ∃ w, (m0.arr64 IW)[dO.toNat + j]? = some w ∧ H w ∧ ds[j]? = some (decI w))
    (hb : dO.toNat + dL.toNat ≤ iwTop m0) :
    ∀ (n : Nat) (m m' : Mem) (a : AState) (k f : Word) (r : List Word),
    p2sfW n m dO dL k f = some (r, m') → StageR dn vis fe m a → IWGrow m0 m → k.toNat ≤ dL.toNat → PosMR m →
    ∃ a', ((ds.drop k.toNat).foldlM pos2FuelF f.toNat).run a = .ok ((r.headD 0).toNat, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ PosMR m'
  | 0, m, m', a, k, f, r, h, _, _, _, _ => by simp [p2sfW] at h
  | n + 1, m, m', a, k, f, r, h, hS, hg0, hk, hP => by
    have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
    by_cases hd : dL ≤ k
    · rw [p2sfW_done (h := hd)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have : k.toNat = dL.toNat := Nat.le_antisymm hk (UInt64.le_iff_toNat_le.mp hd)
      rw [this, ← hlen, List.drop_length]
      exact ⟨a, rfl, hS, IWGrow.refl _, hP⟩
    rw [p2sfW_step (h := hd)] at h
    have hkl : k.toNat < dL.toNat := by
      have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hd); omega
    obtain ⟨w, hw, hH, hdj⟩ := hel k.toNat hkl
    have hg0t := hg0.1
    have hrd : rdW (m.arr64 IW) (dO + k) = w := by
      have e : (dO + k).toNat = dO.toNat + k.toNat := word_add_toNat (by omega)
      simp only [rdW, e]; rw [hg0.2.2.1 _ (by omega), hw]; rfl
    rw [hrd] at h
    rcases hwf : wfWf n m w with _ | ⟨rw, m1⟩ <;> rw [hwf] at h; · simp [p2sfK] at h
    rw [p2sfK_some] at h
    obtain ⟨n', wv, hn, hwW, rfl⟩ := pos2_wfWf_some hwf
    obtain ⟨mp, hmp⟩ := hP.dp
    obtain ⟨d, hrunw, hwd, hM1, hS1, hg1, hf1⟩ := wfW_ok n' dn fe vis m m1 a w wv mp hwW hS hH hmp
    have hk1 : (k + 1).toNat = k.toNat + 1 := word_add_toNat (by simp; omega)
    obtain ⟨a', hrun, hS', hg', hP'⟩ := p2sfW_ok dn vis fe dO dL ds m0 hlen hel hb n m1 m' a (k + 1) _ r h hS1
      (hg0.trans hg1) (by omega) (hP.setDp hf1 ⟨∅, hM1⟩)
    refine ⟨a', ?_, hS', hg1.trans hg', hP'⟩
    have hdk : ds[k.toNat]'(by omega) = decI w := by
      have := hdj; rw [List.getElem?_eq_getElem (by omega)] at this; exact Option.some.inj this
    have hmax : (if f < [wv].headD 0 then [wv].headD 0 else f).toNat = max f.toNat d := by
      have e1 := @UInt64.lt_iff_toNat_lt f wv
      by_cases hlt : f < wv
      · simp only [List.headD_cons, hlt, ite_true]; have := e1.mp hlt; omega
      · simp only [List.headD_cons, hlt, ite_false]; have : ¬ f.toNat < wv.toNat := fun x => hlt (e1.mpr x); omega
    rw [hmax, hk1] at hrun
    rw [List.drop_eq_getElem_cons (by omega), List.foldlM_cons, hdk]
    simp only [pos2FuelF, StateT.run_bind, ← decE_eq, hrunw, except_ok_bind] at hrun ⊢
    exact hrun

end L.Ind

end

end
