module

public meta import Lean.Meta.Tactic.Grind.Attr
import Lean.Meta.Tactic.Grind.RegisterCommand

public section

/-- The `grind` vocabulary of the inductive stage (`ConAgua/Arena/Ind*.lean`, `Rec*.lean`): the
guarded equations of the slice library's and the stage's word models. -/
register_grind_attr ind_grind
