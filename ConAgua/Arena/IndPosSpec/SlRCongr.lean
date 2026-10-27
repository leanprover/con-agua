import ConAgua.Arena.IndLibSpec

/-!
# SlRCongr

`slR_congr`.
-/


noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem slR_congr {m m' : Mem} (hI : m'.arr64 IW = m.arr64 IW) {o l : Word} {ws : List Word}
    (h : SlR m o l ws) : SlR m' o l ws := by
  induction h with
  | nil => exact SlR.nil
  | @cons o l ws hl _ ih =>
    have := SlR.cons (m := m') (o := o) hl ih
    simpa [rdW, hI] using this

end L.Ind

end
