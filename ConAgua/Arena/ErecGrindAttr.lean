module

public meta import Lean.Meta.Tactic.Grind.Attr
import Lean.Meta.Tactic.Grind.RegisterCommand

public section

/-- The record pool's tagged read unfolded (`ConAgua/Arena/ErecVocab.lean`): `erRd` as its `rdW`
of the tier array. Not in `arena_grind`: in a module with many tagged reads every `erRd` term then
unfolds (ClassNPcOf's elaboration +92 % of instructions), so only the proofs that name the set pay. -/
register_grind_attr erec_grind
