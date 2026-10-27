import ConAgua.Arena.PromoteRecRef

/-!
# TakeDropMin

`pnew_ctl`, `take_drop_min`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

theorem pnew_ctl : ∀ x ∈ (129 :: eCtl : List Word),
    x.toNat < 64 ∨ x.toNat = 129 ∨ (140 ≤ x.toNat ∧ x.toNat ≤ 147) := by
  intro x hx
  have := vg_ctl x (by simp only [List.mem_cons] at hx ⊢; rcases hx with h | h; exact Or.inl h; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
  exact this

theorem take_drop_min {α : Type} (L B : List α) (N K : Nat) (hN : (L ++ B).length = N)
    (hL : L.length = min N K) : (L ++ B).take K = L ∧ (L ++ B).drop K = B := by
  by_cases h : K ≤ N
  · have hK : L.length = K := by omega
    exact ⟨List.take_left' hK, List.drop_left' hK⟩
  · have hB : B = [] := by
      simp only [List.length_append] at hN
      exact List.length_eq_zero_iff.mp (by omega)
    subst hB
    simp only [List.append_nil] at *
    exact ⟨List.take_of_length_le (by omega), List.drop_of_length_le (by omega)⟩

end L.Arena
