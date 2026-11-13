module

public import ConAgua.Arena.RecLayout.Caps

@[expose] public section

/-!
# The layout of a constant record (`IConstantInfo`)

A constant record in the record pool `EREC` (decoder `L.Arena.decCI`, `Arena/EnvRec.lean`): the
kind word, the constant value (`IConstantVal`, 4 words) and the kind's own fields. As for every
record layout (`RecLayout/Caps.lean`), L code and proofs use these names, not numbers.
-/

namespace L.CI

/-- The kind word (0 axiom, 1 definition, 2 theorem, 3 inductive, 4 constructor, 5 recursor). -/
@[reducible] def kind : Word := 0
/-- The constant value (`IConstantVal`); its first word, the name, is the index key. -/
@[reducible] def cv : Word := 1

/-! ## `indInfo` -/

/-- An inductive's capabilities (`Caps.size` words). -/
@[reducible] def indCaps : Word := 5
/-- The size of an inductive's record. -/
@[reducible] def indSize : Word := indCaps + Caps.size

theorem indSize_toNat : indSize.toNat = indCaps.toNat + Caps.size.toNat := by
  simp [indSize, indCaps, Caps.size]
theorem indCaps_le : indCaps.toNat ≤ 64 := by simp [indCaps]
/-- The kind word and the constant value come first. -/
theorem indCaps_ge : 5 ≤ indCaps.toNat := by simp [indCaps]

/-- A field of the capabilities, at its place in an inductive's record, as a number. -/
theorem indCaps_add_toNat {f : Word} (hf : f.toNat < Caps.size.toNat) :
    (indCaps + f).toNat = indCaps.toNat + f.toNat := by
  have := Caps.size_le; have := indCaps_le
  rw [UInt64.toNat_add]; omega

end L.CI
