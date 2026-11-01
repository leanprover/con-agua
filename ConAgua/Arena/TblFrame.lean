module

public import ConAgua.Arena.Env
public import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-!
# The table-row arrays as a frame

A table-row write (`tbl_row_set`, `tblSet`) touches only the six table-row arrays (`TIXA`,
`TIXS`, `TIXN` and their tier-1 copies), which the promotion's table walks and the install's
`env_push_table` both need as a frame.
-/

namespace L.Arena

/-- The table-row arrays (both tiers). -/
abbrev tblArrs : List TieredArray := [TIXA, TIXS, TIXN, tier1 TIXA, tier1 TIXS, tier1 TIXN]

theorem tblArr_mem (w : Word) (_hw : rowTag w ≤ 2) : tblArr w ∈ tblArrs := by
  have ht : rowTier w = 0 ∨ rowTier w = 1 := by have : rowTier w < 2 := Nat.mod_lt _ (by decide); omega
  rcases ht with ht | ht
  · rw [tblArr_tier0 ht]; rcases tixArr_mem (rowTag w) with e | e | e <;> rw [e] <;> decide
  · rw [tblArr_tier1 ht]; rcases tixArr_mem (rowTag w) with e | e | e <;> rw [e] <;> decide

theorem tblSet_frame (m : Mem) (w v : Word) (hw : rowTag w ≤ 2) :
    MemFrame tblArrs [] m (tblSet m w v) := by
  have hne : tblArr w ≠ CTL := tblArr_ne_t0 w (by decide) (by decide) (by decide)
  exact (MemFrame.set64 m (tblArr w) hne (tixW w) v).mono
    (by simpa using tblArr_mem w hw) (by simp)

end L.Arena
