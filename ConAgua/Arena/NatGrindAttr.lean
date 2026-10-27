module

public meta import Lean.Meta.Tactic.Grind.Attr
import Lean.Meta.Tactic.Grind.RegisterCommand

public section

/-- The `grind` vocabulary of comparisons on the limb pool (`ConAgua/Arena/NatCmp.lean`): a
prefix is below its weight, the top limb decides, the comparison code `cmpW`. Kept apart from
`arena_grind` because `pv_lt_wt` fires on every `pv` term, which slows the loops that do not
compare (`nat_sub`'s loop timed out with it). -/
register_grind_attr natcmp_grind

/-- The `grind` vocabulary of the shifts, `pow` and the long division (`NatShl`, `NatShr`,
`NatPow`, `NatDiv`) whose patterns are broad (a one-limb slice, a prepended limb, the quotient
lemmas of the right shift, the powers of two `sh`). Kept apart from `arena_grind` for the same
reason as `natcmp_grind`: in `nat_divmod`'s limb loop they made hundreds of useless instances. -/
register_grind_attr natop_grind
