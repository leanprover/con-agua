import ConAgua.Arena.RecCheckSpec.ErToIwWStage

/-!
# PdWAfr

`pdW_afr`, `rec2CC_parts`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem pdW_afr : ∀ (n : Nat) (m m' : Mem) (xo xl e : Word) (r : List Word),
    pdW n m xo xl e = some (r, m') → AFr m m'
  | 0, _, _, _, _, _, _, h => by simp [pdW] at h
  | n + 1, m, m', xo, xl, e, r, h => by
    simp only [pdW, pdK1.eq_def, pdK2.eq_def, pdK3.eq_def] at h
    afr_auto h [i1F_afr, pdW_afr n _ _ _ _ _ _, consW_afr]

theorem rec2CC_parts {m : Mem} {x : Nat} {X : ClassCtor} (hX : decCC m x = some X) :
    iwN m (x + 1) = some X.nF ∧ iwH m (x + 4) = some X.tyD ∧ iwH m (x + 5) = some X.tyN := by
  simp only [decCC, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hX
  obtain ⟨q, hq, cv, hcv, nF, hnF, ks, hks, y4, hy4, y5, hy5, rfl⟩ := hX
  exact ⟨hnF, hy4, hy5⟩

end L.Ind

end
