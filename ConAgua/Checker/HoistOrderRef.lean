import ConAgua.Checker.HoistRefBase

/-!
# The hoist's reorder refines `applyHoist`'s sort (lane `front4`)

`hoist_apply` (buckets per target, then for each position `p` the records moved to `p` in
position order and `p` itself unless it moved) against `applyHoist`'s
`(List.range ds.size).mergeSort (fun a b => !hoistLt target b a)`: the keys `hoistKey` are pairwise
distinct, so the sorted order is the unique sorted permutation, and L's order is sorted and a
permutation. `hoist_any` is `target.isEmpty`. `reorder` is the map of the order through `ds`.
-/

open ConRon.Arena ConRon.Arena.Frontend
open L.Arena L.Ind L.Front L.Front.Ind

namespace L.Checker

/-- The sorted order of `applyHoist`. -/
def hoistOrder (T : Std.HashMap Nat Nat) (c : Nat) : List Nat :=
  (List.range c).mergeSort (fun a b => !hoistLt T b a)

/-- **`hoist_any` is "the map has an entry"** (from position `k` on). -/
theorem hoistAny_ok (n : Nat) (m m' : Mem) (tg c k r : Word) (T : Std.HashMap Nat Nat)
    (hT : TgtR m tg c.toNat T) (hc : tg.toNat + c.toNat < 2 ^ 64)
    (h : hAnyW n m tg c k = some (r, m')) :
    m' = m ∧ (r = 0 ↔ ∀ j, k.toNat ≤ j → j < c.toNat → T[j]? = none) := by
  sorry

/-- No entry below `c` and none at or beyond it: the map is empty. -/
theorem tgt_isEmpty (T : Std.HashMap Nat Nat) (c : Nat) (hc : ∀ k, c ≤ k → T[k]? = none)
    (h : ∀ j, 0 ≤ j → j < c → T[j]? = none) : T.isEmpty = true := by
  sorry

/-- **`hoist_apply` writes `hoistOrder`** (through `ord`) to a fresh slice `out` of `c` words, every
moved record's target being before it. -/
theorem hoistApply_ok (n : Nat) (m m' : Mem) (ord c tg out : Word) (T : Std.HashMap Nat Nat)
    (hI : IWOK m) (hord : ord.toNat + c.toNat ≤ iwTop m) (htg : tg.toNat + c.toNat ≤ iwTop m)
    (hT : TgtR m tg c.toNat T) (hlt : ∀ (k t : Nat), T[k]? = some t → t < k)
    (h : hApplyW n m ord c tg = some (out, m')) :
    IWOK m' ∧ IWGrow m m' ∧ MemFrame [IW] [200] m m' ∧ iwTop m ≤ out.toNat ∧
      out.toNat + c.toNat ≤ iwTop m' ∧
      ∀ j (hj : j < c.toNat), rdW (m'.arr64 IW) (out + UInt64.ofNat j) =
        rdW (m.arr64 IW) (ord + UInt64.ofNat ((hoistOrder T c.toNat)[j]'(by
          simp [hoistOrder, List.length_mergeSort]; exact hj))) := by
  sorry

/-- **`reorder` is the order mapped through the records.** -/
theorem reorder_eq (ds : Array IDeclaration) (order : List Nat) (h : ∀ k ∈ order, k < ds.size) :
    reorder ds order = (order.map fun k => ds[k]!).toArray := by
  sorry

end L.Checker
