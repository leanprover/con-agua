import ConAgua.Arena.PromoteCIExt

/-!
# Hslice

`hslice?_congr`, `SlotGrow.hslice?`.
-/

section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

theorem hslice?_congr {a b : Array Word} {o c : Nat} {k : IdxKind}
    (h : ∀ j < c, b[o + j]? = a[o + j]?) :
    (hslice? b o c : Option (List (Idx k))) = hslice? a o c := by
  simp only [hslice?]
  exact mapM_congr' _ _ _ fun j hj => by
    simp only [List.mem_range] at hj
    simp only [hd?, h j hj]

end L.Arena

end

section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- Slices outside the slot decode the same after the slot is rewritten. -/
theorem SlotGrow.hslice? {m m' : Mem} {lo hi : Nat} (hg : SlotGrow m m' lo hi)
    (hts : erecTop m ≤ (m.arr64 EREC).size) (hts' : erecTop m' ≤ (m'.arr64 EREC).size) {o c : Nat} {k : IdxKind} {xs : List (Idx k)}
    (h : hslice? (erecP m) o c = some xs) (hout : c = 0 ∨ hi ≤ o ∨ o + c ≤ lo) :
    hslice? (erecP m') o c = some xs := by
  have hb : c = 0 ∨ o + c ≤ erecTop m := by
    rcases hslice?_bound h with h0 | h0
    · exact .inl h0
    · right; have := erecP_size_le m; omega
  rw [← h]
  refine hslice?_congr (fun j hj => ?_)
  rcases hb with rfl | hb
  · omega
  have hj' : o + j < erecTop m := by omega
  have hout' : o + j < lo ∨ hi ≤ o + j := by omega
  rw [erecP_getElem m' _ (by have := hg.1; omega) hts',
    erecP_getElem m _ hj' hts]
  exact hg.2.1 _ hj' hout'

end L.Arena

end
