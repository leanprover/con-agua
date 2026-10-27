import ConAgua.Arena.IndPosSpec.NestBlockOfKey

/-!
# CtsK5

`ctsK5`, `ctsK4`, `ctsK3`, `ctsK2`, `ctsK1`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## `check_sum_tele_slow` -/

/-- After `check_constant_val`. -/
def ctsK5 (q s : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m5) => some ([q, s], m5)
/-- After `cv_new`. -/
def ctsK4 (cR : CallM) (k : Nat) (vis s : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (q, m4) => ctsK5 q s (cR k "check_constant_val" [vis, q] m4)
/-- After `close_telescope`. -/
def ctsK3 (cR : CallM) (k : Nat) (vis cv s : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rt, m3) => ctsK4 cR k vis s (cvNewW m3 (rdW (m3.arr64 EREC) cv) (rdW (m3.arr64 EREC) (cv + 1))
      (rdW (m3.arr64 EREC) (cv + 2)) (rt.headD 0))
/-- After `intern_sort`. -/
def ctsK2 (cR : CallM) (k : Nat) (vis cv bo bl s : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (ss, m2) => if 4294967296 ≤ ss then none else ctsK3 cR k vis cv s (closeW k m2 bo bl 0 ss)
/-- After `whnf_telescope`. -/
def ctsK1 (cR : CallM) (k : Nat) (vis cv : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => ctsK2 cR k vis cv (r1.headD 0) (r1.tail.headD 0) (r1.tail.tail.headD 0)
      (sointernW m1 (r1.tail.tail.headD 0))
end L.Ind

end
