import ConAgua.Arena.IndStubs

/-!
# GrpAt

`GrpAt`, `GrpAt.grow`.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `nest_grow_group` refines `nestGrowGroup` -/

/-- A group's `(name, type)` pair records at `o, o + 1, …`, their words below the top. -/
def GrpAt (m : Mem) (o : Nat) (grp : List (NIdx × EIdx)) : Prop :=
  ∀ i (hi : i < grp.length), ∃ w c t : Word, (m.arr64 IW)[o + i]? = some w ∧ w.toNat + 1 < iwTop m ∧
    (m.arr64 IW)[w.toNat]? = some c ∧ H c ∧ decI c = grp[i].1 ∧
    (m.arr64 IW)[w.toNat + 1]? = some t ∧ H t ∧ decI t = grp[i].2

theorem GrpAt.grow {m m' : Mem} {o : Nat} {grp : List (NIdx × EIdx)} (h : GrpAt m o grp)
    (hb : o + grp.length ≤ iwTop m) (hg : IWGrow m m') : GrpAt m' o grp := fun i hi => by
  obtain ⟨w, c, t, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h i hi
  exact ⟨w, c, t, by rw [hg.2.2.1 _ (by omega)]; exact h1, by have := hg.1; omega,
    by rw [hg.2.2.1 _ (by omega)]; exact h3, h4, h5, by rw [hg.2.2.1 _ (by omega)]; exact h6, h7, h8⟩

end L.Ind

end
