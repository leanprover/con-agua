module

import ConAgua.Arena.IndPosSpec.CanonW
import ConRon.Bridge.Grind
public import ConAgua.Arena.IndCopy2

@[expose] public section

/-!
# SnocWDecK

`snocW_decK`.
-/


noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem snocW_decK {k : IdxKind} {n : Nat} {m m' : Mem} {o l x : Word} {r : List Word} {xs : List (Idx k)}
    (h : snocW n m o l x = some (r, m')) (hsz : (m.arr64 IW).size < 2 ^ 64)
    (hc : 200 < (m.arr64 CTL).size) (hsrc : o.toNat + l.toNat ≤ iwTop m)
    (hx : x.toNat < 2 ^ 32) (hxs : decHL m o.toNat l.toNat = some xs) :
    r = [rdW (m.arr64 CTL) 200, l + 1] ∧
    decHL m' (rdW (m.arr64 CTL) 200).toNat (l + 1).toNat = some (xs ++ [decI x]) ∧
    IWGrow m m' ∧ MemFrame [IW] [200] m m' ∧ (l + 1).toNat = l.toNat + 1 ∧
    (rdW (m.arr64 CTL) 200).toNat + (l + 1).toNat = iwTop m' := by
  sorry

end L.Ind

end
