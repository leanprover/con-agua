import ConAgua.Arena.IndSumSpec.CtsK5
import ConAgua.Arena.IndSumSpec.StructProjArgP

/-!
# CtsW

`ctsW`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- **The model of `check_sum_tele_slow`.** -/
def ctsW (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _ => none
  | k + 1, m, vis, cv, n, cvTa0 => ctsK1 cR k vis cv (wtW cR k m vis 0 n (rdW (m.arr64 EREC) (cvTa0 + 3)))

end L.Ind

end
