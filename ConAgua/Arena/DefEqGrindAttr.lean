module

import Lean.Meta.Tactic.Grind.RegisterCommand
public meta import Lean.Meta.Tactic.Grind.Extension

public section

/-- The `grind` vocabulary of the defeq leaves (`ConAgua/Arena/DefEqLeaves.lean`): the guarded
equations of their word models. -/
register_grind_attr defeq_grind
