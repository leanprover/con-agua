module

public import ConAgua.Arena.IndDecStab
import ConAgua.Arena.Env
import ConAgua.Arena.IndLibSpec

@[expose] public section

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
  sorry

theorem rec3IwSlice {k : IdxKind} {m : Mem} {o l : Nat} {xs : List (Idx k)} (h : decHL (truncM m) o l = some xs) :
    o + l ≤ iwTop m ∨ l = 0 := by
  sorry

end L.Ind

end
