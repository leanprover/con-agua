module

public import ConAgua.L.Syntax
public import ConAgua.Arena.RecLayout.Attr

@[expose] public section

/-!
# The layout of an `IIndCaps` record

An inductive's capabilities (the twin's `IIndCaps`) are a record of `Caps.size` words, the same
in every store that holds one: the record pool `EREC` (inside an `indInfo` constant record, at
`CI.indCaps`), the inductive stage's work pool `IW` and the front's inductive records (`DIND`).
The decoder is `L.Arena.decCaps` (`Arena/EnvRec.lean`). A list field is a slice: its offset word
at `…Off` and its length word right after it, at `…Len`.

**The offsets are names.** L code writes `EREC⦃q + ⟪Caps.nparams⟫⦄`, and the compiler evaluates
the constant, so the compiled program is the one a numeral would give. Proofs keep the names
folded: the facts they need about the layout (each field is inside the record, the fields are
distinct, a slice's length word follows its offset word) are the lemmas below, in the simp set
`rec_layout`; no proof outside this file and `CapsDec.lean` unfolds an offset to its number. To
change the layout, change the definitions here (and the constructions that write a whole record,
which are sized by `Caps.size`).
-/

namespace L.Caps

/-- `eta`: whether the type is a structure-like one whose values are η-expandable. -/
@[reducible] def eta : Word := 0
/-- `nIdx`: the number of indices. -/
@[reducible] def nIdx : Word := 1
/-- `neverZero`: whether the type's universe is never zero. -/
@[reducible] def neverZero : Word := 2
/-- `all`: the block's types, a name slice (offset word). -/
@[reducible] def allOff : Word := 3
/-- `all`: the slice's length word. -/
@[reducible] def allLen : Word := 4
/-- `nparams`: the number of parameters. -/
@[reducible] def nparams : Word := 5
/-- `ctors`: the constructors, a name slice (offset word). -/
@[reducible] def ctorsOff : Word := 6
/-- `ctors`: the slice's length word. -/
@[reducible] def ctorsLen : Word := 7
/-- The record's size in words. -/
@[reducible] def size : Word := 8

/-! ## The layout facts -/

theorem size_le : size.toNat ≤ 64 := by simp [size]

@[rec_layout] theorem eta_lt : eta.toNat < size.toNat := by simp [eta, size]
@[rec_layout] theorem nIdx_lt : nIdx.toNat < size.toNat := by simp [nIdx, size]
@[rec_layout] theorem neverZero_lt : neverZero.toNat < size.toNat := by simp [neverZero, size]
@[rec_layout] theorem allOff_lt : allOff.toNat < size.toNat := by simp [allOff, size]
@[rec_layout] theorem allLen_lt : allLen.toNat < size.toNat := by simp [allLen, size]
@[rec_layout] theorem nparams_lt : nparams.toNat < size.toNat := by simp [nparams, size]
@[rec_layout] theorem ctorsOff_lt : ctorsOff.toNat < size.toNat := by simp [ctorsOff, size]
@[rec_layout] theorem ctorsLen_lt : ctorsLen.toNat < size.toNat := by simp [ctorsLen, size]

/-- A slice's length word follows its offset word. -/
theorem allLen_eq : allLen = allOff + 1 := by simp [allLen, allOff]
theorem ctorsLen_eq : ctorsLen = ctorsOff + 1 := by simp [ctorsLen, ctorsOff]
theorem allLen_toNat : allLen.toNat = allOff.toNat + 1 := by simp [allLen, allOff]
theorem ctorsLen_toNat : ctorsLen.toNat = ctorsOff.toNat + 1 := by simp [ctorsLen, ctorsOff]

/-- The record's size as a number (a `toNat` bound for `omega`). -/
theorem size_pos : 0 < size.toNat := by simp [size]

attribute [rec_unfold] eta nIdx neverZero allOff allLen nparams ctorsOff ctorsLen size

end L.Caps
