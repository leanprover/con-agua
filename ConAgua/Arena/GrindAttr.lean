module

public meta import Lean.Meta.Tactic.Grind.Attr
import Lean.Meta.Tactic.Grind.RegisterCommand

public section

/-- The `grind` vocabulary of the limb pool (`ConAgua/Arena/Pool.lean`): the abstraction
`pv`, its zero-extended form `xv`, the frame predicate `Agree`, the normal form `Norm`, and the
carry facts about `UInt64` addition. Proofs use it as
`sym only [lang_grind, arena_grind] => vcgen [...] <;> finish`. -/
register_grind_attr arena_grind

/-- The `grind` vocabulary of the store relations (`ConAgua/Arena/LitRefine.lean`): reads of the
memory after a write (`rdW_set64`), the probe run, the record and slot invariants. -/
register_grind_attr store_grind
