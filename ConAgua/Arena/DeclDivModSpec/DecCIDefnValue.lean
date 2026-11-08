module

import ConAgua.Arena.DeclDivModSpec.DivModTypePins
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.Arena.DeclNatGate
public import ConAgua.Rom.PinSets

@[expose] public section

/-!
# DecCIDefnValue

`PinsIW`, `PinsIW.grow`, `decCI_defn_value`.
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
  sorry

theorem decCI_defn_value {a : Array Word} {dn : NIdx → Option ConLeche.Name} {p : Nat}
    {cv : IConstantVal} {v : EIdx} {hint : ConLeche.ReducibilityHint}
    (h : decCI (aread a) p = some (.defnInfo cv v hint)) :
    a[p]? = some 1 ∧ ∃ w, a[p + 5]? = some w ∧ w.toNat < 2 ^ 32 ∧ v = decI w := by
  sorry

end L.Ind
