import ConAgua.Checker.HoistClosureL

/-!
# The hoist's `Nat` operation tests refine the twin's name lists (lane `front4`)

`nat_op_record` (`natDivModNames`/`natOpNames` into fresh `IW` slices, `slice_has` on each) against
`isNatOpRecord`'s test, and the call of `nat_op_deps` against `natOpDeps`: the twin succeeds in the
same state, and L's memory only grew the pool.
-/

open ConRon.Arena ConRon.Arena.Frontend
open L.Arena L.Ind L.Front L.Front.Ind

namespace L.Checker

/-- The pin table survives an allocation. -/
theorem PinsFull.frameA {m m' : Mem} {ps : Pins} (h : PinsFull m ps) (hf : AFr m m') :
    PinsFull m' ps := by
  sorry

/-- **`nat_op_record(w)`** is "the name `w` is in `natDivModNames` or `natOpNames`". -/
theorem natOpRec_ok (p : Prog) (hx : HoistExt p) (n : Nat) (m m₁ : Mem) (a : AState) (w op : Word)
    (hI : IWOK m) (hP : pinW m 0 ≠ 0 → PinsFull m a.pins) (hw : w.toNat < 2 ^ 32)
    (h : hNatOpRecW p n m w = some (op, m₁)) :
    PinsFull m a.pins ∧ ∃ L₁ L₂ : List NIdx, natDivModNames.run a = .ok (L₁, a) ∧
      natOpNames.run a = .ok (L₂, a) ∧
      (op ≠ 0 ↔ (L₁.contains (decI w) || L₂.contains (decI w)) = true) ∧ AFr m m₁ := by
  sorry

/-- **The call of `nat_op_deps(w)`** is `natOpDeps (decI w)`: its result `(o, l)` is a slice of
the grounds, above the old pool top unless empty. -/
theorem natOpDepsCall_ok (p : Prog) (hx : HoistExt p) (n : Nat) (m m₂ : Mem) (a : AState) (w : Word)
    (r : List Word) (hI : IWOK m) (hP : PinsFull m a.pins) (hw : w.toNat < 2 ^ 32)
    (h : callW p n "nat_op_deps" [w] m = some (r, m₂)) :
    ∃ gs : List NIdx, (natOpDeps (decI w)).run a = .ok (gs, a) ∧ GrR m₂ (r.headD 0) 0 gs ∧
      (r.tail.headD 0).toNat = gs.length ∧
      (gs ≠ [] → iwTop m ≤ (r.headD 0).toNat ∧ (r.headD 0).toNat + gs.length ≤ iwTop m₂) ∧
      AFr m m₂ := by
  sorry

end L.Checker
