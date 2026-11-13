module

public import ConAgua.L.Syntax
public import ConAgua.Arena.RecLayout.Attr
public import ConAgua.Arena.RecLayout.Img

@[expose] public section

/-!
# The layout of a projection table record (`IProjTable`)

A structure's projection table is a `ProjTbl.size`-word record in the record pool `EREC` (not a
constant: the environment's table component); the decoder is `L.Arena.decTbl`
(`Arena/EnvRec.lean`). The level parameters and the bodies are slices: an offset word and a
length word right after it.

The first two words are `ProjTbl.kindVal` and `0` (the kind and name words of the constant records'
layout; nothing reads them). Words `8`, `11` and `12` are not read (the removed `structSort` and
`guards`), and the writer does not write them (its image, `ProjTbl.img`).

**The offsets are names**, as for every record layout (`RecLayout/Caps.lean`): L code writes
`EREC⦃q + ⟪ProjTbl.ctor⟫⦄`, and the compiler evaluates the constant. The kind word at offset 0 stays
`erec_put(q, …)` in L. The environment hands a table out as its address plus one
(`raw_table`, `find_table`; `0` for none): a read through such a handle `tq` is
`EREC⦃tq + ⟪ProjTbl.ctor - 1⟫⦄`.

The namespace is `L.ProjTbl`, not `L.Tbl`: `Tbl` is the twin's hash table (`ConRon.Arena.Tbl`),
open wherever the arena's proofs are.
-/

namespace L.ProjTbl

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

/-- The structure name is not the first word: a decoded table's address plus one (the
environment's handle) does not wrap. -/
theorem structName_pos : 0 < structName.toNat := by simp [structName]

/-- A slice's length word follows its offset word. -/
theorem lpsLen_eq : lpsLen = lpsOff + 1 := by simp [lpsLen, lpsOff]
theorem bodiesLen_eq : bodiesLen = bodiesOff + 1 := by simp [bodiesLen, bodiesOff]
theorem lpsLen_toNat : lpsLen.toNat = lpsOff.toNat + 1 := by simp [lpsLen, lpsOff]
theorem bodiesLen_toNat : bodiesLen.toNat = bodiesOff.toNat + 1 := by simp [bodiesLen, bodiesOff]

/-- **The record's image** (`RecLayout/Img.lean`): what a field-by-field writer stores (the
unused words are not written). -/
def img (kw nm sn lo ll np c nf bo bl : Word) : List (Option Word) :=
  recImg size [(kind, kw), (name, nm), (structName, sn), (lpsOff, lo), (lpsLen, ll), (numParams, np),
    (ctor, c), (numFields, nf), (bodiesOff, bo), (bodiesLen, bl)]

theorem img_length (kw nm sn lo ll np c nf bo bl : Word) : (img kw nm sn lo ll np c nf bo bl).length = size.toNat :=
  recImg_length _ _
theorem img_kind (kw nm sn lo ll np c nf bo bl : Word) :
    (img kw nm sn lo ll np c nf bo bl)[kind.toNat]? = some (some kw) := by
  simp [img, recImg, kind, name, structName, lpsOff, lpsLen, numParams, ctor, numFields, bodiesOff,
    bodiesLen, size, List.replicate]
theorem img_name (kw nm sn lo ll np c nf bo bl : Word) :
    (img kw nm sn lo ll np c nf bo bl)[name.toNat]? = some (some nm) := by
  simp [img, recImg, kind, name, structName, lpsOff, lpsLen, numParams, ctor, numFields, bodiesOff,
    bodiesLen, size, List.replicate]
theorem img_sn (kw nm sn lo ll np c nf bo bl : Word) :
    (img kw nm sn lo ll np c nf bo bl)[structName.toNat]? = some (some sn) := by
  simp [img, recImg, kind, name, structName, lpsOff, lpsLen, numParams, ctor, numFields, bodiesOff,
    bodiesLen, size, List.replicate]
theorem img_lo (kw nm sn lo ll np c nf bo bl : Word) :
    (img kw nm sn lo ll np c nf bo bl)[lpsOff.toNat]? = some (some lo) := by
  simp [img, recImg, kind, name, structName, lpsOff, lpsLen, numParams, ctor, numFields, bodiesOff,
    bodiesLen, size, List.replicate]
theorem img_ll (kw nm sn lo ll np c nf bo bl : Word) :
    (img kw nm sn lo ll np c nf bo bl)[lpsLen.toNat]? = some (some ll) := by
  simp [img, recImg, kind, name, structName, lpsOff, lpsLen, numParams, ctor, numFields, bodiesOff,
    bodiesLen, size, List.replicate]
theorem img_np (kw nm sn lo ll np c nf bo bl : Word) :
    (img kw nm sn lo ll np c nf bo bl)[numParams.toNat]? = some (some np) := by
  simp [img, recImg, kind, name, structName, lpsOff, lpsLen, numParams, ctor, numFields, bodiesOff,
    bodiesLen, size, List.replicate]
theorem img_ctor (kw nm sn lo ll np c nf bo bl : Word) :
    (img kw nm sn lo ll np c nf bo bl)[ctor.toNat]? = some (some c) := by
  simp [img, recImg, kind, name, structName, lpsOff, lpsLen, numParams, ctor, numFields, bodiesOff,
    bodiesLen, size, List.replicate]
theorem img_nf (kw nm sn lo ll np c nf bo bl : Word) :
    (img kw nm sn lo ll np c nf bo bl)[numFields.toNat]? = some (some nf) := by
  simp [img, recImg, kind, name, structName, lpsOff, lpsLen, numParams, ctor, numFields, bodiesOff,
    bodiesLen, size, List.replicate]
theorem img_bo (kw nm sn lo ll np c nf bo bl : Word) :
    (img kw nm sn lo ll np c nf bo bl)[bodiesOff.toNat]? = some (some bo) := by
  simp [img, recImg, kind, name, structName, lpsOff, lpsLen, numParams, ctor, numFields, bodiesOff,
    bodiesLen, size, List.replicate]
theorem img_bl (kw nm sn lo ll np c nf bo bl : Word) :
    (img kw nm sn lo ll np c nf bo bl)[bodiesLen.toNat]? = some (some bl) := by
  simp [img, recImg, kind, name, structName, lpsOff, lpsLen, numParams, ctor, numFields, bodiesOff,
    bodiesLen, size, List.replicate]

end L.ProjTbl
