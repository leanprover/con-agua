import ConAgua.Arena.RecCheckSpec.TkhK2

/-!
# TkhK2V2

`tkhK2_v1`, `tkhK2_v2`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

section arms
variable (cR : CallM) (n : Nat) (m : Mem) (vis q fto ftl Mc leafW majDom lh ip usp ii : Word) (r rl rm ra rb : List Word)
theorem tkhK2_v1 (h : ¬ lh >>> 28 ≠ 3) (h2 : ¬ rm.headD 0 >>> 28 ≠ 3) (h3 : eViewW m lh = []) :
    tkhK2 cR n vis q fto ftl Mc leafW majDom lh (some (rm, m)) = none := by
  simp only [tkhK2]; rw [ite_eq_right h, ite_eq_right h2, ite_eq_left h3]
theorem tkhK2_v2 (h : ¬ lh >>> 28 ≠ 3) (h2 : ¬ rm.headD 0 >>> 28 ≠ 3) (h3 : ¬ eViewW m lh = [])
    (h4 : eViewW m (rm.headD 0) = []) :
    tkhK2 cR n vis q fto ftl Mc leafW majDom lh (some (rm, m)) = none := by
  simp only [tkhK2]; rw [ite_eq_right h, ite_eq_right h2, ite_eq_right h3, ite_eq_left h4]
end arms
attribute [ind_grind] tkhK2_v1 tkhK2_v2

end L.Ind

end
