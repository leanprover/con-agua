module

public import ConAgua.Checker.HoistOrderRef3
import ConAgua.Arena.DeclNatBase

@[expose] public section

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
    (hT : TgtR m tg c.toNat T) (_hc : tg.toNat + c.toNat < 2 ^ 64)
    (hlt : ∀ (k t : Nat), T[k]? = some t → t < k)
    (h : hAnyW n m tg c k = some (r, m')) :
    m' = m ∧ (r = 0 ↔ ∀ j, k.toNat ≤ j → j < c.toNat → T[j]? = none) :=
  hAny_ok n m tg c T hT hlt k r m' h

/-- No entry below `c` and none at or beyond it: the map is empty. -/
theorem tgt_isEmpty (T : Std.HashMap Nat Nat) (c : Nat) (hc : ∀ k, c ≤ k → T[k]? = none)
    (h : ∀ j, 0 ≤ j → j < c → T[j]? = none) : T.isEmpty = true := by
  rw [Std.HashMap.isEmpty_iff_forall_not_mem]
  intro a ha
  rw [Std.HashMap.mem_iff_isSome_getElem?] at ha
  have : T[a]? = none := if hac : a < c then h a (Nat.zero_le _) hac else hc a (by omega)
  rw [this] at ha
  cases ha

theorem iwok_alloc {m m1 : Mem} {k q : Word} (h : allocW m k = some (q, m1)) (hI : IWOK m) :
    IWOK m1 := by
  sorry

theorem iwok_frame {m m' : Mem} (hf : MemFrame [IW] [] m m') (hI : IWOK m) : IWOK m' := by
  sorry

theorem getElem?_of_rd {m m' : Mem} (i : Nat) (hs : (m'.arr64 IW).size = (m.arr64 IW).size)
    (hi : i < (m.arr64 IW).size) (hl : (m.arr64 IW).size < 2 ^ 64) (h : rd m' i = rd m i) :
    (m'.arr64 IW)[i]? = (m.arr64 IW)[i]? := by
  simp only [rd, rdW, UInt64.toNat_ofNat_of_lt' (show i < UInt64.size by
    simp [UInt64.size]; omega)] at h
  rw [Array.getElem?_eq_getElem (by omega), Array.getElem?_eq_getElem hi] at h ⊢
  simpa using h

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

theorem reorder_go (ds : Array IDeclaration) : ∀ (order : List Nat) (acc : Array IDeclaration),
    (∀ k ∈ order, k < ds.size) →
    order.foldl (fun acc k => acc ++ (ds[k]?.toArray)) acc = acc ++ (order.map fun k => ds[k]!).toArray
  | [], acc, _ => by simp
  | k :: rest, acc, h => by
    rw [List.foldl_cons, reorder_go ds rest _ (fun k' hk' => h k' (List.mem_cons_of_mem _ hk'))]
    have hk := h k List.mem_cons_self
    simp [hk]

/-- **`reorder` is the order mapped through the records.** -/
theorem reorder_eq (ds : Array IDeclaration) (order : List Nat) (h : ∀ k ∈ order, k < ds.size) :
    reorder ds order = (order.map fun k => ds[k]!).toArray := by
  simp only [reorder]
  rw [reorder_go ds order #[] h, Array.empty_append]

end L.Checker
