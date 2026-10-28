import ConAgua.Arena.IndPosSpec.NuW
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr

/-!
# UnW2

`CssAt`, `CssAt.tail`, `CssAt.grow`.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order
namespace L.Ind
open L.Arena

/-- The members' constructor lists: headers at `off, off + 1, …`, each a `[cv, nF]` pointer slice. -/
def CssAt (m : Mem) (off : Nat) (css : List (List (IConstantVal × Nat))) : Prop :=
  ∀ i (hi : i < css.length), ∃ hdr o l : Word, (m.arr64 IW)[off + i]? = some hdr ∧
    (m.arr64 IW)[hdr.toNat]? = some o ∧ (m.arr64 IW)[hdr.toNat + 1]? = some l ∧
    off + i < iwTop m ∧ hdr.toNat + 1 < iwTop m ∧ l.toNat = css[i].length ∧
    o.toNat + l.toNat ≤ iwTop m ∧ CsAt m o.toNat css[i] (· < iwTop m)

theorem CssAt.tail {m : Mem} {off : Nat} {x : List (IConstantVal × Nat)} {xs : List (List (IConstantVal × Nat))}
    (h : CssAt m off (x :: xs)) : CssAt m (off + 1) xs := fun i hi => by
  obtain ⟨hdr, o, l, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h (i + 1) (by simp; omega)
  exact ⟨hdr, o, l, by rw [show off + 1 + i = off + (i + 1) by omega]; exact h1, h2, h3, by omega, h5,
    by simpa using h6, h7, by simpa using h8⟩

theorem CssAt.grow {m m' : Mem} {off : Nat} {css : List (List (IConstantVal × Nat))} (h : CssAt m off css)
    (hg : IWGrow m m') : CssAt m' off css := fun i hi => by
  obtain ⟨hdr, o, l, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h i hi
  refine ⟨hdr, o, l, by rw [hg.2.2.1 _ h4]; exact h1, by rw [hg.2.2.1 _ (by omega)]; exact h2,
    by rw [hg.2.2.1 _ h5]; exact h3, by have := hg.1; omega, by have := hg.1; omega, h6,
    by have := hg.1; omega, h8.grow (by omega) hg⟩

end L.Ind

end
