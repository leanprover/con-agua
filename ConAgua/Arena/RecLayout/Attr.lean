module

public meta import Lean.Meta.Tactic.Simp.RegisterCommand

public section

/-- The record layouts' facts (`Arena/RecLayout/*.lean`): every field inside its record, as
`toNat` bounds. A proof names the set (`simp [rec_layout]`, `omega` after `have := …`) instead of
unfolding an offset to its number. -/
register_simp_attr rec_layout
