import ConAgua.Front.IndApplyRefine5
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# The apply step of an `inductive` line against the twin, VIII: `vi_order`

`orderW_twin`: `vi_order` allocates the ordered slice above the pool's top and fills it, every
constructor checked as the twin checks it (`CtorOK`, per type `k` and position `c`).
-/

open L.Arena
open ConRon.Arena
open ConRon.Arena.Frontend
open ConLeche.Frontend (IndCtorRec IndTypeRec IndRecRec)


namespace L.Front.Ind

theorem psum_congr {m m' : Mem} (h : m'.arr64 IFR = m.arr64 IFR) (to : Word) (i : Nat) :
    psum m' to i = psum m to i := by
  unfold psum
  congr 1
  apply List.map_congr_left
  intro k _
  simp only [cntF, wd, h]

theorem orderW_twin {b : ByteArray} {n : Nat} {m m' : Mem} {a : AState} {st : StateD}
    (hR : ArenaR m a) (hD : StateDR m st) {cts : List IndCtorRec}
    {to tn tyn fo cno co cn fuel np oo : Word} (hT : TopOK m)
    (hCt : ListF (CtF b m) m 10 co.toNat cts) (hcn : cn.toNat = cts.length)
    (hCN : ∀ k, k < cts.length → (wd m IFL (cno.toNat + k)).toNat < 2 ^ 32)
    (hcnB : cno.toNat + cts.length ≤ topN m IFL + 1) (hnp : np.toNat < 10 ^ 18)
    (hco : co.toNat + 10 * cts.length < 2 ^ 63) (h1 : 1 ≤ cno.toNat ∧ 1 ≤ fo.toNat ∧ 1 ≤ tyn.toNat)
    (hto : to.toNat + 11 * tn.toNat < 2 ^ 63) (htyn : tyn.toNat + tn.toNat ≤ topN m IFL + 1)
    (hfo : ∀ p, p < psum m to tn.toNat → fo.toNat + p ≤ topN m IFL ∧ (wd m IFL (fo.toNat + p)).toNat < 2 ^ 32)
    (hps : psum m to tn.toNat ≤ cts.length)
    (h : orderW n m to tn tyn fo cno co cn fuel np = some (oo, m')) :
    oo.toNat = topN m IFL + 1 ∧ IExt m m' ∧ TopOK m' ∧ topN m' IFL = topN m IFL + cts.length ∧
    ∀ k, k < tn.toNat → ∀ c, c < cntF m to k →
      ∃ kk, wd m' IFL (oo.toNat + psum m to k + c) = co + 10 * UInt64.ofNat kk ∧
        CtorOK st a cts (islice m cno.toNat cts.length) (decI (wd m IFL (fo.toNat + psum m to k + c)))
          c (decI (wd m IFL (tyn.toNat + k))) np.toNat fuel.toNat kk := by
  obtain ⟨h1a, h1b, h1c⟩ := h1
  cases n with
  | zero => simp [orderW] at h
  | succ n =>
  simp only [orderW] at h
  rcases ha : allocW m IFL cn with _ | ⟨oo', m₁⟩ <;> simp only [ha, allocK, reduceCtorEq] at h
  rcases hg : orderGoW n m₁ to tn tyn fo cno co cn fuel np oo' 0 0 with _ | m₂ <;> simp only [hg, mK, reduceCtorEq] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨a1, a2, a3, a4⟩ := allocW_ok hT ha
  obtain ⟨-, -, a5, -, -⟩ := allocW_factsA (by decide) hT.1 (by have := hT.1; have := hT.2; omega) ha
  rw [hcn] at a4 a5
  have hR₁ : ArenaR m₁ a := ArenaR.frame_ext [IFL, LH] [192] (by decide) (by simp) m m₁ a1.frame a hR
  have hD₁ : StateDR m₁ st := hD.frame a1.frame (by decide) (by decide) (by decide) (by decide) (by decide)
  have hps₁ := psum_congr a1.ifr to
  have hkeep : ∀ i, 1 ≤ i → i ≤ topN m IFL → wd m₁ IFL i = wd m IFL i := a1.keep
  have hCN₁ : ∀ k, k < cts.length → (wd m₁ IFL (cno.toNat + k)).toNat < 2 ^ 32 := fun k hk => by
    rw [hkeep _ (by omega) (by omega)]; exact hCN k hk
  have hCt₁ : ListF (CtF b m₁) m₁ 10 co.toNat cts := hCt.ext a1 (fun _ _ x => x.ext a1)
  rw [← hps₁] at hfo hps
  obtain ⟨g1, -, g3⟩ := orderGoW_twin hR₁ hD₁ hCt₁ hcn hCN₁ (by omega) hnp hco
    (by rw [a1.size]; omega) a2.1 hto (by omega)
    (fun p hp => by
      obtain ⟨f1, f2⟩ := hfo p hp
      exact ⟨by omega, by rw [hkeep _ (by omega) f1]; exact f2⟩) hps n m₁ m₂ 0 0 hg
    (IOnly.refl _ _) (UInt64.le_iff_toNat_le.mpr (Nat.zero_le _)) (by simp [psum])
  have ht0 : topN m₂ IFL = topN m₁ IFL := by unfold topN; rw [g1.2 0 (by omega)]
  have hI : IExt m m₂ := ⟨a1.frame.trans (g1.1.mono (by simp) (by simp)), by rw [ht0]; exact a1.top,
    fun i h1 h2 => by rw [g1.2 i (by omega)]; exact a1.keep i h1 h2⟩
  have hcnt : ∀ k, cntF m₁ to k = cntF m to k := fun k => by simp only [cntF, wd, a1.ifr]
  refine ⟨a3, hI, ⟨by rw [g1.1.2.2.1]; exact a2.1, by rw [g1.1.2.2.1, ht0]; exact a2.2⟩,
    by rw [ht0, a4], fun k hk c hc => ?_⟩
  rw [← hcnt] at hc
  obtain ⟨kk, e1, e2⟩ := g3 k (Nat.zero_le _) hk c hc
  rw [hps₁] at e1 e2
  have hp : psum m to k + c < psum m to tn.toNat := by
    have := psum_mono m to (k + 1) tn.toNat (by omega)
    rw [psum_succ, ← hcnt] at this; omega
  obtain ⟨f1, -⟩ := hfo (psum m to k + c) (by rw [hps₁]; exact hp)
  rw [islice_ext a1 _ _ (by omega) hcnB, hkeep _ (by omega) (by omega),
    hkeep _ (by omega) (by omega)] at e2
  exact ⟨kk, e1, e2⟩

end L.Front.Ind
