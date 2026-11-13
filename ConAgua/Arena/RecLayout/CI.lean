module

public import ConAgua.Arena.RecLayout.Caps
public import ConAgua.Arena.RecLayout.CV

@[expose] public section

/-!
# The layout of a constant record (`IConstantInfo`)

A constant record in the record pool `EREC` (decoder `L.Arena.decCI`, `Arena/EnvRec.lean`): the
kind word, the constant value (`IConstantVal`, `CV.size` words, `RecLayout/CV.lean`) and the
kind's own fields. As for every record layout (`RecLayout/Caps.lean`), L code and proofs use these
names, not numbers: a field of the value is `CI.cv + CV.f` (`EREC⦃p + ⟪CI.cv + CV.type⟫⦄`), a
kind's field `CI.<kind><Field>`, the record's size `CI.<kind>Size`.

The kind word is at offset 0, so L reads it as `EREC⦃p⦄` (`p + ⟪CI.kind⟫` would compile to an
extra `add`).

A definition's reducibility hint (decoder `L.Arena.decHint`) is a record of its own, `Hint.size`
words at `CI.defnHint`: its kind (0 opaque, 1 abbrev, 2 regular) and, for `regular`, the height.
-/

namespace L.Hint

/-- The hint's kind (0 opaque, 1 abbrev, 2 regular). -/
@[reducible] def kind : Word := 0
/-- A `regular` hint's height. -/
@[reducible] def height : Word := 1
/-- The record's size in words. -/
@[reducible] def size : Word := 2

end L.Hint

namespace L.CI

/-- The kind word (0 axiom, 1 definition, 2 theorem, 3 inductive, 4 constructor, 5 recursor). -/
@[reducible] def kind : Word := 0
/-- The constant value (`IConstantVal`); its first word, the name, is the index key. -/
@[reducible] def cv : Word := 1

/-- The first word after the constant value: the kinds' own fields start here. -/
theorem cv_end : (cv + CV.size).toNat = 5 := by simp [cv, CV.size]

/-! ## `axiomInfo`, `thmInfo`: the value only -/

/-- The size of an axiom's record. -/
@[reducible] def axiomSize : Word := cv + CV.size
/-- The size of a theorem's record. -/
@[reducible] def thmSize : Word := cv + CV.size

/-! ## `defnInfo` -/

/-- `value`: the definition's body (a handle). The front's declarations come as records of a
definition's shape (`erec_ci`), so a theorem's and an opaque's value is at this word too. -/
@[reducible] def defnValue : Word := 5
/-- `hint`: the reducibility hint (`Hint.size` words). -/
@[reducible] def defnHint : Word := 6
/-- The size of a definition's record. -/
@[reducible] def defnSize : Word := defnHint + Hint.size

/-! ## `ctorInfo` -/

/-- `numParams`: the constructor's number of parameters. -/
@[reducible] def ctorNparams : Word := 5
/-- `numFields`: the constructor's number of fields. -/
@[reducible] def ctorNfields : Word := 6
/-- `induct`: the constructor's inductive type (a name handle). -/
@[reducible] def ctorInduct : Word := 7
/-- The size of a constructor's record. -/
@[reducible] def ctorSize : Word := 8

/-! ## `recInfo` -/

/-- `majorIdx`: the position of the major premise. -/
@[reducible] def recMajor : Word := 5
/-- `rulePrefix`: the twin's `rulePrefix` (`IConstantInfo.recInfo`). -/
@[reducible] def recPrefix : Word := 6
/-- `rules`: the recursor rules, a slice of rule records (offset word). -/
@[reducible] def recRulesOff : Word := 7
/-- `rules`: the slice's length word. -/
@[reducible] def recRulesLen : Word := 8
/-- `isK`: whether the recursor is a K-like one. -/
@[reducible] def recIsK : Word := 9
/-- The size of a recursor's record. -/
@[reducible] def recSize : Word := 10

theorem recRulesLen_eq : recRulesLen = recRulesOff + 1 := by simp [recRulesLen, recRulesOff]

/-- A recursor's two counts are where a constructor's are (`find_pinned` reads either kind's at
the same words). -/
theorem recMajor_eq : recMajor = ctorNparams := by simp [recMajor, ctorNparams]
theorem recPrefix_eq : recPrefix = ctorNfields := by simp [recPrefix, ctorNfields]
theorem recRulesLen_toNat : recRulesLen.toNat = recRulesOff.toNat + 1 := by
  simp [recRulesLen, recRulesOff]

/-! ## The layout facts: every offset is small (`omega`'s bounds) -/

@[rec_layout] theorem cv_le : cv.toNat ≤ 64 := by simp [cv]
@[rec_layout] theorem defnValue_le : defnValue.toNat ≤ 64 := by simp [defnValue]
@[rec_layout] theorem defnHint_le : defnHint.toNat ≤ 64 := by simp [defnHint]
@[rec_layout] theorem ctorNparams_le : ctorNparams.toNat ≤ 64 := by simp [ctorNparams]
@[rec_layout] theorem ctorNfields_le : ctorNfields.toNat ≤ 64 := by simp [ctorNfields]
@[rec_layout] theorem ctorInduct_le : ctorInduct.toNat ≤ 64 := by simp [ctorInduct]
@[rec_layout] theorem recMajor_le : recMajor.toNat ≤ 64 := by simp [recMajor]
@[rec_layout] theorem recPrefix_le : recPrefix.toNat ≤ 64 := by simp [recPrefix]
@[rec_layout] theorem recRulesOff_le : recRulesOff.toNat ≤ 64 := by simp [recRulesOff]
@[rec_layout] theorem recRulesLen_le : recRulesLen.toNat ≤ 64 := by simp [recRulesLen]
@[rec_layout] theorem recIsK_le : recIsK.toNat ≤ 64 := by simp [recIsK]
@[rec_layout] theorem hintHeight_le : Hint.height.toNat ≤ 64 := by simp [Hint.height]

/-- A field of the constant value, at its place in a constant record, as a number. -/
theorem cv_add_toNat {f : Word} (hf : f.toNat ≤ 64) : (cv + f).toNat = cv.toNat + f.toNat :=
  layout_add_toNat cv_le hf

/-- The name word is the value's first word. -/
theorem cv_name_toNat : (cv + CV.name).toNat = cv.toNat := by
  rw [cv_add_toNat CV.name_le, CV.name_toNat, Nat.add_zero]

/-- A regular hint's height word, as a number. -/
theorem defnHeight_toNat : (defnHint + Hint.height).toNat = defnHint.toNat + Hint.height.toNat :=
  layout_add_toNat defnHint_le hintHeight_le

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
