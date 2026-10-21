module

public meta import Lean.Meta.Tactic.Grind.Attr
import Lean.Meta.Tactic.Grind.RegisterCommand

public section

/-- The `grind` vocabulary of comparisons on the limb pool (`ConAgua/Arena/NatCmp.lean`): a
prefix is below its weight, the top limb decides, the comparison code `cmpW`. Kept apart from
`arena_grind` because `pv_lt_wt` fires on every `pv` term, which slows the loops that do not
compare (`nat_sub`'s loop timed out with it). -/
register_grind_attr natcmp_grind
