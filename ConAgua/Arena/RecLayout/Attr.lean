module

public meta import Lean.Meta.Tactic.Simp.RegisterCommand

public section

/-- The record layouts' facts (`Arena/RecLayout/*.lean`): every field inside its record, as
`toNat` bounds. A proof names the set (`simp [rec_layout]`, `omega` after `have := …`) instead of
unfolding an offset to its number. -/
register_simp_attr rec_layout

/-- The record layouts' offsets unfolded to their numbers. Only a proof about a whole-record
construction or copy (a writer or a relocation, which walks the record's words in order) may use
it; every other proof states and uses the layout facts (`rec_layout`) and the decoders' facts
(`…Dec.lean`). Each use is listed in the lane journal (`docs/design/recoffs.md`). -/
register_simp_attr rec_unfold
