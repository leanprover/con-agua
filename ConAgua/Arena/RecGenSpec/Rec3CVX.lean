import ConAgua.Arena.RecGenSpec.DecCVX
import ConAgua.Arena.RecStab

/-!
# Rec3CVX

`rec3CVX`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## Stable constant slices -/

theorem rec3CVX {m : Mem} {p : Nat} {cv : IConstantVal} (h : StabD (fun m => decCVX m p) m cv) :
    decCVp m p = some cv ∧ CVExt m p := by
  have := h.get
  simp only [decCVX] at this
  split at this
  · exact ⟨this, by assumption⟩
  · cases this

end L.Ind

end
