import ConAgua.Arena.IndDecStab

/-!
# Rec3IwSlice

`rec3SliceLast`, `rec3IwSlice`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

theorem rec3SliceLast {k : IdxKind} {a : Array Word} {o l : Nat} {xs : List (Idx k)} (h : hslice? a o l = some xs)
    (hl : 0 < l) : ∃ w, a[o + (l - 1)]? = some w := by
  have hg := mapM_opt_get (fun j => (hd? a (o + j) : Option (Idx k))) (List.range l) xs h (l - 1) (by simp; omega)
  simp only [List.getElem_range] at hg
  obtain ⟨w, hw, -⟩ := hd?_some hg
  exact ⟨w, hw⟩

theorem rec3IwSlice {k : IdxKind} {m : Mem} {o l : Nat} {xs : List (Idx k)} (h : decHL (truncM m) o l = some xs) :
    o + l ≤ iwTop m ∨ l = 0 := by
  rcases Nat.eq_zero_or_pos l with h0 | h0
  · exact .inr h0
  obtain ⟨w, hw⟩ := rec3SliceLast (show hslice? (iwA (truncM m)) o l = some xs from h) h0
  have := (truncM_iw_get hw).1
  exact .inl (by omega)

end L.Ind

end
