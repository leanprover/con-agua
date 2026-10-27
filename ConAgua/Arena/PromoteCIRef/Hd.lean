import ConAgua.Arena.PromoteCIExt

/-!
# Hd

`SlotGrow.hd?`, `SlotGrow.nat?`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

theorem SlotGrow.hd? {m m' : Mem} {lo hi : Nat} (hg : SlotGrow m m' lo hi)
    (_hts : erecTop m ≤ (m.arr64 EREC).size) {i : Nat} {k : IdxKind} {x : Idx k}
    (h : hd? (erecP m) i = some x) (hout : i < lo ∨ hi ≤ i) : hd? (erecP m') i = some x := by
  obtain ⟨w, hw, hl, rfl⟩ := hd?_some h
  obtain ⟨hi1, hw'⟩ := preE_get_lt (m := m) (T := erecTop m) hw
  have := hg.2.1 i hi1 hout
  have hm' := hg.1
  exact hd?_of_pre (m := m') (T := erecTop m') (by omega) (by rw [this]; exact hw') hl

theorem SlotGrow.nat? {m m' : Mem} {lo hi : Nat} (hg : SlotGrow m m' lo hi)
    {i x : Nat} (h : nat? (erecP m) i = some x) (hout : i < lo ∨ hi ≤ i) :
    nat? (erecP m') i = some x := by
  obtain ⟨w, hw, rfl⟩ := nat?_get h
  obtain ⟨hi1, hw'⟩ := preE_get_lt (m := m) (T := erecTop m) hw
  have := hg.2.1 i hi1 hout
  exact nat?_of_pre (m := m') (T := erecTop m') (by have := hg.1; omega) (by rw [this]; exact hw')

end L.Arena
