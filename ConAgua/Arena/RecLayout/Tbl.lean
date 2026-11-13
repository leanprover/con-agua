module

public import ConAgua.L.Syntax
public import ConAgua.Arena.RecLayout.Attr

@[expose] public section

/-!
# The layout of a projection table record (`IProjTable`)

A structure's projection table is a `Tbl.size`-word record in the record pool `EREC` (not a
constant: the environment's table component); the decoder is `L.Arena.decTbl`
(`Arena/EnvRec.lean`). The level parameters and the bodies are slices: an offset word and a
length word right after it.

The first two words are `Tbl.kindVal` and `0` (the kind and name words of the constant records'
layout; nothing reads them). Words `8`, `11` and `12` are not read (the removed `structSort` and
`guards`): the writer puts `0` there.

**The offsets are names**, as for every record layout (`RecLayout/Caps.lean`): L code writes
`EREC⦃q + ⟪Tbl.ctor⟫⦄`, and the compiler evaluates the constant. The kind word at offset 0 stays
`erec_put(q, …)` in L. The environment hands a table out as its address plus one
(`raw_table`, `find_table`; `0` for none): a read through such a handle `tq` is
`EREC⦃tq + ⟪Tbl.ctor - 1⟫⦄`.
-/

namespace L.Tbl

/-- The kind word (it holds `kindVal`). Offset 0. -/
@[reducible] def kind : Word := 0
/-- The value of the kind word. -/
@[reducible] def kindVal : Word := 6
/-- The name word of the constant records' layout (it holds `0`). -/
@[reducible] def name : Word := 1
/-- `structName`: the structure (a name handle). -/
@[reducible] def structName : Word := 2
/-- `levelParams`, a slice (offset word). -/
@[reducible] def lpsOff : Word := 3
/-- `levelParams`: the slice's length word. -/
@[reducible] def lpsLen : Word := 4
/-- `numParams`. -/
@[reducible] def numParams : Word := 5
/-- `ctor`: the structure's constructor (a name handle). -/
@[reducible] def ctor : Word := 6
/-- `numFields`. -/
@[reducible] def numFields : Word := 7
/-- `bodies`, a slice (offset word). -/
@[reducible] def bodiesOff : Word := 9
/-- `bodies`: the slice's length word. -/
@[reducible] def bodiesLen : Word := 10
/-- The record's size in words. -/
@[reducible] def size : Word := 13

/-! ## The layout facts -/

theorem size_le : size.toNat ≤ 64 := by simp [size]
theorem size_pos : 0 < size.toNat := by simp [size]

@[rec_layout] theorem kind_lt : kind.toNat < size.toNat := by simp [kind, size]
@[rec_layout] theorem name_lt : name.toNat < size.toNat := by simp [name, size]
@[rec_layout] theorem structName_lt : structName.toNat < size.toNat := by simp [structName, size]
@[rec_layout] theorem lpsOff_lt : lpsOff.toNat < size.toNat := by simp [lpsOff, size]
@[rec_layout] theorem lpsLen_lt : lpsLen.toNat < size.toNat := by simp [lpsLen, size]
@[rec_layout] theorem numParams_lt : numParams.toNat < size.toNat := by simp [numParams, size]
@[rec_layout] theorem ctor_lt : ctor.toNat < size.toNat := by simp [ctor, size]
@[rec_layout] theorem numFields_lt : numFields.toNat < size.toNat := by simp [numFields, size]
@[rec_layout] theorem bodiesOff_lt : bodiesOff.toNat < size.toNat := by simp [bodiesOff, size]
@[rec_layout] theorem bodiesLen_lt : bodiesLen.toNat < size.toNat := by simp [bodiesLen, size]

/-- A slice's length word follows its offset word. -/
theorem lpsLen_eq : lpsLen = lpsOff + 1 := by simp [lpsLen, lpsOff]
theorem bodiesLen_eq : bodiesLen = bodiesOff + 1 := by simp [bodiesLen, bodiesOff]
theorem lpsLen_toNat : lpsLen.toNat = lpsOff.toNat + 1 := by simp [lpsLen, lpsOff]
theorem bodiesLen_toNat : bodiesLen.toNat = bodiesOff.toNat + 1 := by simp [bodiesLen, bodiesOff]

end L.Tbl
