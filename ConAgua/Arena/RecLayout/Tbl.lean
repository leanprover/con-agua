module

public import ConAgua.Arena.RecLayout.Attr
public import ConAgua.Arena.RecLayout.Img

@[expose] public section

/-!
# The layout of a projection table record (`IProjTable`)

A structure's projection table is a `ProjTbl.size`-word record in the record pool `EREC` (not a
constant: the environment's table component); the decoder is `L.Arena.decTbl`
(`Arena/EnvRec.lean`). The level parameters and the bodies are slices: an offset word and a
length word right after it.

Words `0` and `1` (once the kind and name words of the constant records' layout), `8`, `11` and `12`
(the removed `structSort` and `guards`) are not read, and the writer does not write them (its image,
`ProjTbl.img`).

**The offsets are names**, as for every record layout (`RecLayout/Caps.lean`): L code writes
`EREC⦃q + ⟪ProjTbl.ctor⟫⦄`, and the compiler evaluates the constant. The environment hands a
table out as its address plus one (`raw_table`, `find_table`; `0` for none): a read through such a
handle `tq` is `EREC⦃tq + ⟪ProjTbl.ctor - 1⟫⦄`.

The namespace is `L.ProjTbl`, not `L.Tbl`: `Tbl` is the twin's hash table (`ConRon.Arena.Tbl`),
open wherever the arena's proofs are.
-/

namespace L.ProjTbl

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

/-- **The record's image** (`RecLayout/Img.lean`): what a field-by-field writer stores (the
unused words are not written). -/
def img (sn lo ll np c nf bo bl : Word) : List (Option Word) :=
  recImg size [(structName, sn), (lpsOff, lo), (lpsLen, ll), (numParams, np), (ctor, c),
    (numFields, nf), (bodiesOff, bo), (bodiesLen, bl)]

theorem img_length (sn lo ll np c nf bo bl : Word) : (img sn lo ll np c nf bo bl).length = size.toNat :=
  recImg_length _ _
theorem img_sn (sn lo ll np c nf bo bl : Word) :
    (img sn lo ll np c nf bo bl)[structName.toNat]? = some (some sn) := by
  simp [img, recImg, structName, lpsOff, lpsLen, numParams, ctor, numFields, bodiesOff, bodiesLen,
    size, List.replicate]
theorem img_lo (sn lo ll np c nf bo bl : Word) :
    (img sn lo ll np c nf bo bl)[lpsOff.toNat]? = some (some lo) := by
  simp [img, recImg, structName, lpsOff, lpsLen, numParams, ctor, numFields, bodiesOff, bodiesLen,
    size, List.replicate]
theorem img_ll (sn lo ll np c nf bo bl : Word) :
    (img sn lo ll np c nf bo bl)[lpsLen.toNat]? = some (some ll) := by
  simp [img, recImg, structName, lpsOff, lpsLen, numParams, ctor, numFields, bodiesOff, bodiesLen,
    size, List.replicate]
theorem img_np (sn lo ll np c nf bo bl : Word) :
    (img sn lo ll np c nf bo bl)[numParams.toNat]? = some (some np) := by
  simp [img, recImg, structName, lpsOff, lpsLen, numParams, ctor, numFields, bodiesOff, bodiesLen,
    size, List.replicate]
theorem img_ctor (sn lo ll np c nf bo bl : Word) :
    (img sn lo ll np c nf bo bl)[ctor.toNat]? = some (some c) := by
  simp [img, recImg, structName, lpsOff, lpsLen, numParams, ctor, numFields, bodiesOff, bodiesLen,
    size, List.replicate]
theorem img_nf (sn lo ll np c nf bo bl : Word) :
    (img sn lo ll np c nf bo bl)[numFields.toNat]? = some (some nf) := by
  simp [img, recImg, structName, lpsOff, lpsLen, numParams, ctor, numFields, bodiesOff, bodiesLen,
    size, List.replicate]
theorem img_bo (sn lo ll np c nf bo bl : Word) :
    (img sn lo ll np c nf bo bl)[bodiesOff.toNat]? = some (some bo) := by
  simp [img, recImg, structName, lpsOff, lpsLen, numParams, ctor, numFields, bodiesOff, bodiesLen,
    size, List.replicate]
theorem img_bl (sn lo ll np c nf bo bl : Word) :
    (img sn lo ll np c nf bo bl)[bodiesLen.toNat]? = some (some bl) := by
  simp [img, recImg, structName, lpsOff, lpsLen, numParams, ctor, numFields, bodiesOff, bodiesLen,
    size, List.replicate]

end L.ProjTbl
