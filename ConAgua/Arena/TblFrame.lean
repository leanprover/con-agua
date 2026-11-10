module

public import Std.Tactic.BVDecide.Normalize.Prop
public import ConAgua.Layout

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

end L.Arena
