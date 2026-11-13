module

public import ConAgua.L.Syntax
public import ConAgua.Arena.RecLayout.Attr
public import ConAgua.Arena.RecLayout.Img

@[expose] public section

/-!
# The layout of a recursor rule record (`IRecRule`)

A recursor's rules are a slice of `Rule.size`-word records in the record pool `EREC` (the
recursor's constant record holds the slice's offset and count); the decoder is
`L.Arena.decRule` (`Arena/EnvRec.lean`), and `decRules` steps through the slice by `Rule.size`.
The fire (`IRecRuleFire`) is a kind word (0 `plain`, 1 `nested`, 2 `levels`) and two slices: the
levels (`levels`, `nested`) and the pins (`nested` only), each an offset word and a length word
right after it.

Words `2`, `9` and `10` are not read (they held the install-computed `ctorParams`, `k` and
`eta`, which con-leche's task #480 removed; the offsets of the rest were kept): the writers put
`0` there.

**The offsets are names**, as for every record layout (`RecLayout/Caps.lean`): L code writes
`EREC⦃q + ⟪Rule.rhs⟫⦄`, and the compiler evaluates the constant. The field at offset 0, `ctor`,
stays `EREC⦃q⦄` / `erec_put(q, x)` in L (`q + ⟪Rule.ctor⟫` would compile to an extra `add`).
-/

namespace L.Rule

/-- `ctor`: the constructor the rule is for (a name handle). Offset 0. -/
@[reducible] def ctor : Word := 0
/-- `nfields`: the constructor's number of fields. -/
@[reducible] def nfields : Word := 1
/-- The fire's kind (0 `plain`, 1 `nested`, 2 `levels`). -/
@[reducible] def fire : Word := 3
/-- The fire's levels, a slice (offset word). -/
@[reducible] def lvlsOff : Word := 4
/-- The fire's levels: the slice's length word. -/
@[reducible] def lvlsLen : Word := 5
/-- The fire's pins (`nested`), a slice (offset word). -/
@[reducible] def pinsOff : Word := 6
/-- The fire's pins: the slice's length word. -/
@[reducible] def pinsLen : Word := 7
/-- `rhs`: the rule's right-hand side (an expression handle). -/
@[reducible] def rhs : Word := 8
/-- The record's size in words (the stride of a rule slice). -/
@[reducible] def size : Word := 11

attribute [rec_unfold] ctor nfields fire lvlsOff lvlsLen pinsOff pinsLen rhs size

/-! ## The layout facts -/

theorem size_le : size.toNat ≤ 64 := by simp [size]
theorem size_pos : 0 < size.toNat := by simp [size]

@[rec_layout] theorem ctor_lt : ctor.toNat < size.toNat := by simp [ctor, size]
@[rec_layout] theorem nfields_lt : nfields.toNat < size.toNat := by simp [nfields, size]
@[rec_layout] theorem fire_lt : fire.toNat < size.toNat := by simp [fire, size]
@[rec_layout] theorem lvlsOff_lt : lvlsOff.toNat < size.toNat := by simp [lvlsOff, size]
@[rec_layout] theorem lvlsLen_lt : lvlsLen.toNat < size.toNat := by simp [lvlsLen, size]
@[rec_layout] theorem pinsOff_lt : pinsOff.toNat < size.toNat := by simp [pinsOff, size]
@[rec_layout] theorem pinsLen_lt : pinsLen.toNat < size.toNat := by simp [pinsLen, size]
@[rec_layout] theorem rhs_lt : rhs.toNat < size.toNat := by simp [rhs, size]

/-- **The fields' order** (the facts `omega` needs to keep two fields' words apart): the scalar
fields first, then each slice's offset word followed by its length word, the right-hand side, the
record's size last. -/
theorem order : ctor.toNat < nfields.toNat ∧ nfields.toNat < fire.toNat ∧
    fire.toNat < lvlsOff.toNat ∧ lvlsLen.toNat = lvlsOff.toNat + 1 ∧
    lvlsLen.toNat < pinsOff.toNat ∧ pinsLen.toNat = pinsOff.toNat + 1 ∧
    pinsLen.toNat < rhs.toNat ∧ rhs.toNat < size.toNat := by
  simp [ctor, nfields, fire, lvlsOff, lvlsLen, pinsOff, pinsLen, rhs, size]

/-- A slice's length word follows its offset word. -/
theorem lvlsLen_eq : lvlsLen = lvlsOff + 1 := by simp [lvlsLen, lvlsOff]
theorem pinsLen_eq : pinsLen = pinsOff + 1 := by simp [pinsLen, pinsOff]
theorem lvlsLen_toNat : lvlsLen.toNat = lvlsOff.toNat + 1 := by simp [lvlsLen, lvlsOff]
theorem pinsLen_toNat : pinsLen.toNat = pinsOff.toNat + 1 := by simp [pinsLen, pinsOff]

/-- **The record's image** (`RecLayout/Img.lean`): what a field-by-field writer stores (the
unused words are not written). -/
def img (c nf fk lo ll po pl x : Word) : List (Option Word) :=
  recImg size [(ctor, c), (nfields, nf), (fire, fk), (lvlsOff, lo), (lvlsLen, ll), (pinsOff, po),
    (pinsLen, pl), (rhs, x)]

theorem img_length (c nf fk lo ll po pl x : Word) : (img c nf fk lo ll po pl x).length = size.toNat :=
  recImg_length _ _
theorem img_ctor (c nf fk lo ll po pl x : Word) :
    (img c nf fk lo ll po pl x)[ctor.toNat]? = some (some c) := by
  simp [img, recImg, ctor, nfields, fire, lvlsOff, lvlsLen, pinsOff, pinsLen, rhs, size, List.replicate]
theorem img_nf (c nf fk lo ll po pl x : Word) :
    (img c nf fk lo ll po pl x)[nfields.toNat]? = some (some nf) := by
  simp [img, recImg, ctor, nfields, fire, lvlsOff, lvlsLen, pinsOff, pinsLen, rhs, size, List.replicate]
theorem img_fk (c nf fk lo ll po pl x : Word) :
    (img c nf fk lo ll po pl x)[fire.toNat]? = some (some fk) := by
  simp [img, recImg, ctor, nfields, fire, lvlsOff, lvlsLen, pinsOff, pinsLen, rhs, size, List.replicate]
theorem img_lo (c nf fk lo ll po pl x : Word) :
    (img c nf fk lo ll po pl x)[lvlsOff.toNat]? = some (some lo) := by
  simp [img, recImg, ctor, nfields, fire, lvlsOff, lvlsLen, pinsOff, pinsLen, rhs, size, List.replicate]
theorem img_ll (c nf fk lo ll po pl x : Word) :
    (img c nf fk lo ll po pl x)[lvlsLen.toNat]? = some (some ll) := by
  simp [img, recImg, ctor, nfields, fire, lvlsOff, lvlsLen, pinsOff, pinsLen, rhs, size, List.replicate]
theorem img_po (c nf fk lo ll po pl x : Word) :
    (img c nf fk lo ll po pl x)[pinsOff.toNat]? = some (some po) := by
  simp [img, recImg, ctor, nfields, fire, lvlsOff, lvlsLen, pinsOff, pinsLen, rhs, size, List.replicate]
theorem img_pl (c nf fk lo ll po pl x : Word) :
    (img c nf fk lo ll po pl x)[pinsLen.toNat]? = some (some pl) := by
  simp [img, recImg, ctor, nfields, fire, lvlsOff, lvlsLen, pinsOff, pinsLen, rhs, size, List.replicate]
theorem img_rhs (c nf fk lo ll po pl x : Word) :
    (img c nf fk lo ll po pl x)[rhs.toNat]? = some (some x) := by
  simp [img, recImg, ctor, nfields, fire, lvlsOff, lvlsLen, pinsOff, pinsLen, rhs, size, List.replicate]

end L.Rule
