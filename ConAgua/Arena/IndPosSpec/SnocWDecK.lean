import ConAgua.Arena.IndPosSpec.CanonW

/-!
# SnocWDecK

`snocW_decK`.
-/

set_option linter.unusedSectionVars false

/-! Continued from `IndPos2SpecA.lean` (split by size; lane `indproofs`). -/

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
  obtain ⟨hr, hl1, hqt, hfr, hg, htop, hget⟩ := snocW_core h hsz hc hsrc
  refine ⟨hr, ?_, hg, hfr, hl1, by omega⟩
  simp only [decHL]
  rw [hl1, hslice?_add, hqt]
  have h1 : (hslice? (iwA m') (iwTop m) l.toNat : Option (List (Idx k))) = some xs := by
    rw [← hxs]; simp only [decHL]
    apply hslice?_congr
    intro j hj
    simp only [iwA, hget]
    rw [ite_eq_right (by omega), ite_eq_left (by omega)]
    congr 1; omega
  have h2 : (hslice? (iwA m') (iwTop m + l.toNat) 1 : Option (List (Idx k))) = some [decI x] := by
    rw [hslice?_succ]
    have : (hd? (iwA m') (iwTop m + l.toNat) : Option (Idx k)) = some (decI x) := by simp [hd?, iwA, hget, hx]
    rw [this]; simp [hslice?]
  rw [h1, h2]; simp

end L.Ind

end
