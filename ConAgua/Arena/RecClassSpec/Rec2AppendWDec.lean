import ConAgua.Arena.RecClassSpec.ClassGenMajorCi

/-!
# Rec2AppendWDec

`rec2AppendW_norm`, `rec2AppendW_dec`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem rec2AppendW_norm (n : Nat) (m : Mem) (o1 o2 l2 : Word) :
    appendW n m o1 0 o2 l2 = appendW n m 0 0 o2 l2 := by
  have hc : ∀ k m1 q (s : Word), copyW k m1 q s 0 = copyW k m1 q 0 0 := by
    intro k; cases k <;> simp [copyW]
  simp only [appendW, hc]

/-- `sl_append` of a slice decoded below the tops (possibly empty, at any offset) and a slice
below the top. -/
theorem rec2AppendW_dec {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {o1 l1 o2 l2 : Word} {r : List Word} {xs ys : List EIdx}
    (h : appendW n m o1 l1 o2 l2 = some (r, m')) (hS : StageR dn vis fe m a)
    (h1 : DecB (fun m => (decHL m o1.toNat l1.toNat : Option (List EIdx))) m xs)
    (h2 : decHL m o2.toNat l2.toNat = some ys) (hb2 : o2.toNat + l2.toNat ≤ iwTop m) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some (xs ++ ys) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' := by
  have hx0 : decHL m o1.toNat l1.toNat = some xs := h1.get (OMono.decHL _ _)
  have key : ∀ o1' : Word, appendW n m o1' l1 o2 l2 = some (r, m') →
      decHL m o1'.toNat l1.toNat = some xs → o1'.toNat + l1.toNat ≤ iwTop m → _ := fun o1' h' hx hb1 => by
    obtain ⟨hr, hd, -, -, -, htop⟩ := appendW_dec h' hS.2.2.2.1 hS.2.2.2.2.2 hb1 hb2 hx h2
    obtain ⟨hS', hg, -⟩ := appendW_stage h' hS hb1 hb2
    exact (⟨hS', hg, by rw [hr]; exact hd, by rw [hr]; simp only [List.headD_cons, List.tail_cons]; omega⟩ :
      StageR dn vis fe m' a ∧ IWGrow m m' ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some (xs ++ ys) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m')
  by_cases hl : l1 = 0
  · subst hl
    rw [rec2AppendW_norm] at h
    exact key 0 h (by simpa [decHL, hslice?] using hx0) (by simp)
  · have hl' : l1.toNat ≠ 0 := fun h0 => hl (UInt64.toNat_inj.mp (by simpa using h0))
    exact key o1 h hx0 (rec2DecB_HL_top h1 hl')

end L.Ind

end
