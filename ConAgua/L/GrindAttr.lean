module

public meta import Lean.Meta.Tactic.Grind.Attr
import Lean.Meta.Tactic.Grind.RegisterCommand

public section

/-- The `grind` vocabulary of L proofs: equations for the interpreter's helper functions
(`BinOp.eval`, `Mem.len8`, `St.setLoc`, …). Lemmas live in `ConAgua/L/Logic.lean` and next to the
proofs that need them. A proof uses it as `sym only [lang_grind, …] => vcgen [step, …] <;> finish`
or as `grind [lang_grind]`: a set goes to the entry point of the grind goal; `finish [S]`,
also in `vcgen … with finish [S]`, accepts a set's name and ignores it (it activates only the
declarations it names; docs/design/syncvocab.md, "Follow-up: duplicate names"). -/
register_grind_attr lang_grind
