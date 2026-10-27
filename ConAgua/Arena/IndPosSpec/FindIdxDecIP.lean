import ConAgua.Arena.IndPosSpec.NestBlockOfKey

/-!
# FindIdxDecIP

`findIdx_decIP`.
-/


noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem findIdx_decIP (ws : List Word) (c : Word) (hws : ∀ w ∈ ws, w.toNat < 2 ^ 32) (hc : c.toNat < 2 ^ 32) :
    (ws.map (fun w => (decI w : NIdx))).findIdx? (· == (decI c : NIdx)) = ws.findIdx? (· == c) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.map_cons, List.findIdx?_cons, decI_beq' w c (hws w (by simp)) hc]
    by_cases h : w = c
    · simp [h]
    · simp [h]
      have := ih (fun x hx => hws x (by simp [hx]))
      simp only [List.findIdx?_map] at this
      rw [this]

end L.Ind

end
