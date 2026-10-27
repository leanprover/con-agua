import ConAgua.Arena.Env
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# The table-row arrays as a frame

A table-row write (`tbl_row_set`, `tblSet`) touches only the six table-row arrays (`TIXA`,
`TIXS`, `TIXN` and their tier-1 copies), which the promotion's table walks and the install's
`env_push_table` both need as a frame.
-/

namespace L.Arena

/-- The table-row arrays (both tiers). -/
abbrev tblArrs : List ArrId := [TIXA, TIXS, TIXN, 385, 386, 387]

theorem tblArr_mem (w : Word) (hw : rowTag w ≤ 2) : tblArr w ∈ tblArrs := by
  rcases tblArr_cases w hw with h | h | h | h | h | h <;> rw [h] <;> decide

theorem tblSet_frame (m : Mem) (w v : Word) (hw : rowTag w ≤ 2) :
    MemFrame tblArrs [] m (tblSet m w v) := by
  have hne : tblArr w ≠ CTL := by
    rcases tblArr_cases w hw with h | h | h | h | h | h <;> rw [h] <;> decide
  exact (MemFrame.set64 m (tblArr w) hne (tixW w) v).mono
    (by simpa using tblArr_mem w hw) (by simp)

end L.Arena
