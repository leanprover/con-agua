import ConAgua.Checker.HoistTargetsRef
import ConAgua.Checker.HoistOrderRef

/-!
# `hoist_nat_op_ground` refines `hoistNatOpGround` (lane `front4`)

The assembly: the name index (`hoistIndexGo_ok`), two fresh slices (targets, stack), the targets
zeroed, the targets pass (`targets_ok`: the twin's `hoistTargets`), `hoist_any` (`isEmpty`), and
the reorder (`hoistApply_ok`: `applyHoist`'s sorted order). When L returns, the twin returns, in
the same state, the records in the order L's result slice gives (`OrdR`); `movedNames` (the second
component) is not computed (docs/deviations.md D30).
-/

open ConRon.Arena ConRon.Arena.Frontend
open L.Arena L.Ind L.Front L.Front.Ind

namespace L.Checker

theorem getElem?_of_rd2 {m m' : Mem} (hs : (m'.arr64 IW).size = (m.arr64 IW).size) {x : Nat}
    (hx : x < 2 ^ 64) (h : rd m' x = rd m x) : (m'.arr64 IW)[x]? = (m.arr64 IW)[x]? := by
  have e : (UInt64.ofNat x).toNat = x := by rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt hx
  simp only [rd, rdW, e] at h
  by_cases hl : x < (m.arr64 IW).size
  · rw [Array.getElem?_eq_getElem (by omega), Array.getElem?_eq_getElem hl] at *
    simp at h; rw [h]
  · rw [Array.getElem?_eq_none (by omega), Array.getElem?_eq_none (by omega)]

/-- The stream relation needs only the `IW` words below `B`, `DECL` and `DLP`. -/
theorem ordR_low {m m' : Mem} {ord : Word} {ds : Array IDeclaration} (B : Nat) (hO : OrdR m ord ds)
    (hB : ord.toNat + ds.size ≤ B) (hBs : B < 2 ^ 64)
    (hIW : ∀ x : Nat, x < B → (m'.arr64 IW)[x]? = (m.arr64 IW)[x]?)
    (hD : m'.arr64 DECL = m.arr64 DECL) (hP : m'.arr64 DLP = m.arr64 DLP) : OrdR m' ord ds := by
  intro k hk
  have hn : (ord + UInt64.ofNat k).toNat = ord.toNat + k := addW_toNat _ _ (by omega)
  have hr : rdW (m'.arr64 IW) (ord + UInt64.ofNat k) = rdW (m.arr64 IW) (ord + UInt64.ofNat k) := by
    simp only [rdW, hn]; rw [hIW _ (by omega)]
  rw [hr, hD, hP]
  exact hO k hk

/-- An allocation is an `AFr`. -/
theorem allocW_afr {m m₁ : Mem} {k q : Word} (hw : allocW m k = some (q, m₁)) (hI : IWOK m) :
    AFr m m₁ ∧ q.toNat = iwTop m ∧ iwTop m₁ = iwTop m + k.toNat ∧ iwTop m + k.toNat ≤ (m.arr64 IW).size := by
  obtain ⟨hq, hm1, hk, hroom, htop⟩ := allocW_post hw hI
  have hf : MemFrame [IW] [200] m m₁ := by
    rw [hm1]; exact (MemFrame.setCtl m 200 _).mono (by simp) (by simp)
  obtain ⟨h1, h2, h3, h4, h5⟩ := hI
  have hsz := hf.2.2.1
  have hER : m₁.arr64 EREC = m.arr64 EREC := hf.1 EREC (by decide) (by decide)
  have h129 : erTop m₁ = erTop m := by simp only [erTop]; rw [hf.2.1 129 (by decide)]
  refine ⟨⟨hf, hk.1, ?_⟩, by rw [hq]; rfl, htop, hroom⟩
  exact ⟨by rw [htop, hsz IW]; exact hroom, by rw [h129, hER]; exact h2, by rw [hsz IW]; exact h3,
    by rw [hER]; exact h4, by rw [hsz CTL]; exact h5⟩

end L.Checker
