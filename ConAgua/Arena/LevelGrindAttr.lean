module

public meta import Lean.Meta.Tactic.Grind.Attr
import Lean.Meta.Tactic.Grind.RegisterCommand

public section

/-- The `grind` vocabulary of the level algorithms on the scratch heap (`ConAgua/Arena/Level*.lean`):
the guarded equations of their word models and the continuations. Kept apart from `arena_grind`
so that the level models' arms do not fire in the expression walks. -/
register_grind_attr level_grind
