import ConAgua.Arena.IndPosSpec.NbKeyK2

/-!
# Pos2WfWfSome

`pos2_wfWf_some`.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## The seeds' fuel -/

theorem pos2_wfWf_some {n : Nat} {m m1 : Mem} {e : Word} {r : List Word} (h : wfWf n m e = some (r, m1)) :
    ∃ n' w, n = n' + 2 ∧ wfW n' m e = some (w, m1) ∧ r = [w] := by
  match n, h with
  | n' + 2, h =>
    simp only [wfWf] at h
    rcases hc : wfW n' m e with _ | ⟨w, m2⟩ <;> rw [hc] at h; · cases h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact ⟨n', w, rfl, hc, rfl⟩

end L.Ind

end
