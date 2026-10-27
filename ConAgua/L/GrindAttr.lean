module

public meta import Lean.Meta.Tactic.Grind.Attr
import Lean.Meta.Tactic.Grind.RegisterCommand

public section

/-- The `grind` vocabulary of L proofs: equations for the interpreter's helper functions
(`BinOp.eval`, `Mem.len8`, `St.setLoc`, …). Lemmas live in `ConAgua/L/Logic.lean` and next to the
proofs that need them. A proof uses it as `sym only [lang_grind, …] => vcgen [step, …] <;> finish`
or as `vcgen [step, …] with finish [lang_grind]`. -/
register_grind_attr lang_grind
