module

import ConAgua.Arena.DeclDivModSpec.DivModTypePins
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
public import ConAgua.Rom.PinSets

@[expose] public section

/-!
# DecCIDefnValue

`PinsIW`, `PinsIW.grow`.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open L.Rom (PinSetR)

namespace L.Ind

open L.Arena

/-- **The variant slice**: `IW[o ‥ o + l]` holds pointers to the 40-word records of the variants
`ips`, in order. -/
def PinsIW (m : Mem) (o l : Nat) (ips : List INatOpPinSet) : Prop :=
  o + l ≤ iwTop m ∧ l = ips.length ∧ ∀ (j : Nat) (hj : j < ips.length), ∃ ps : Word,
    iwA m (o + j) = some ps ∧ PinSetR m ps ips[j]

theorem PinsIW.grow {m m' : Mem} {o l : Nat} {ips : List INatOpPinSet} (h : PinsIW m o l ips)
    (hg : IWGrow m m') : PinsIW m' o l ips := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨Nat.le_trans h1 hg.iw, h2, fun j hj => ?_⟩
  obtain ⟨ps, hp, hP⟩ := h3 j hj
  refine ⟨ps, ?_, PinSetR.grow hP hg⟩
  simp only [iwA, aread_apply] at hp ⊢; rw [hg.iwGet _ (by omega)]; exact hp

end L.Ind
