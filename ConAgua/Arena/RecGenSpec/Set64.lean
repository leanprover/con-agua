import ConAgua.Arena.IndIface

/-!
# Set64

`KeepW`, `KeepW.refl`, `KeepW.trans`, `KeepW.set64`, `cnfK2`, `iwTop_set_iw`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Every L run keeps the word arrays' sizes -/

/-- Every word array has the same size. -/
def KeepW (m m' : Mem) : Prop := ∀ a, (m'.arr64 a).size = (m.arr64 a).size

theorem KeepW.refl (m : Mem) : KeepW m m := fun _ => rfl

theorem KeepW.trans {m₁ m₂ m₃ : Mem} (h₁ : KeepW m₁ m₂) (h₂ : KeepW m₂ m₃) : KeepW m₁ m₃ :=
  fun a => (h₂ a).trans (h₁ a)

theorem KeepW.set64 {m m' : Mem} (h : KeepW m m') (a : ArrId) (i v : Word) : KeepW m (m'.set64 a i v) := by
  intro b
  rw [← h b]
  simp only [Mem.set64, Mem.arr64]
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds]
  by_cases hb : a = b
  · subst hb
    by_cases ha : a < m'.words.size <;> simp [ha]
  · simp [hb]

/-- After the loop. -/
def cnfK2 (q : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rp, m) => some ([q, rp], m)

/-! ## `class_ctor_of_nfs`: the relational side -/

theorem iwTop_set_iw (m : Mem) (k v : Word) : iwTop (m.set64 IW k v) = iwTop m := by
  simp only [iwTop]; rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]

end L.Ind

end
