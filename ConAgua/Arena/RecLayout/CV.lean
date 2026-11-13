module

public import ConAgua.L.Syntax
public import ConAgua.Arena.RecLayout.Attr

@[expose] public section

/-!
# The layout of a constant value (`IConstantVal`)

A constant value is a record of `CV.size` words (decoder `L.Arena.decCV`, `Arena/EnvRec.lean`):
the name, the universe parameters (a name slice: offset word `lpsOff`, length word `lpsLen` right
after it) and the type. It sits inside every constant record, at `CI.cv` (`RecLayout/CI.lean`),
and the inductive stage and the front keep values of their own (`cv_new`, the front's `DIND`
records). As for every record layout (`RecLayout/Caps.lean`), L code and proofs use these names,
not numbers.

The name is at offset 0, so L reads it as `EREC⦃q⦄` (`q + ⟪CV.name⟫` would compile to an extra
`add`); inside a constant record it is `EREC⦃p + ⟪CI.cv + CV.name⟫⦄`.
-/

namespace L.CV

/-- `name`: the constant's name (a handle; the index key). -/
@[reducible] def name : Word := 0
/-- `levelParams`: the universe parameter names, a name slice (offset word). -/
@[reducible] def lpsOff : Word := 1
/-- `levelParams`: the slice's length word. -/
@[reducible] def lpsLen : Word := 2
/-- `type`: the constant's type (a handle). -/
@[reducible] def type : Word := 3
/-- The record's size in words. -/
@[reducible] def size : Word := 4

/-! ## The layout facts -/

theorem size_le : size.toNat ≤ 64 := by simp [size]

@[rec_layout] theorem name_lt : name.toNat < size.toNat := by simp [name, size]
@[rec_layout] theorem lpsOff_lt : lpsOff.toNat < size.toNat := by simp [lpsOff, size]
@[rec_layout] theorem lpsLen_lt : lpsLen.toNat < size.toNat := by simp [lpsLen, size]
@[rec_layout] theorem type_lt : type.toNat < size.toNat := by simp [type, size]

/-- The slice's length word follows its offset word. -/
theorem lpsLen_eq : lpsLen = lpsOff + 1 := by simp [lpsLen, lpsOff]
theorem lpsLen_toNat : lpsLen.toNat = lpsOff.toNat + 1 := by simp [lpsLen, lpsOff]

theorem size_pos : 0 < size.toNat := by simp [size]

/-- The name is word `q` itself (`decCV` and L read it there). -/
theorem name_toNat : name.toNat = 0 := by simp [name]

@[rec_layout] theorem name_le : name.toNat ≤ 64 := by simp [name]
@[rec_layout] theorem lpsOff_le : lpsOff.toNat ≤ 64 := by simp [lpsOff]
@[rec_layout] theorem lpsLen_le : lpsLen.toNat ≤ 64 := by simp [lpsLen]
@[rec_layout] theorem type_le : type.toNat ≤ 64 := by simp [type]

attribute [rec_unfold] name lpsOff lpsLen type size

end L.CV

namespace L

/-- A sum of two layout offsets (each at most `64`) as a number. -/
theorem layout_add_toNat {a b : Word} (ha : a.toNat ≤ 64) (hb : b.toNat ≤ 64) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt64.toNat_add]; omega

/-- A record's word `q + f` as a number, when the record's words are below `2 ^ 64`. -/
theorem off_add_toNat {q f : Word} {n : Nat} (hf : f.toNat = n) (h : q.toNat + n < 2 ^ 64) :
    (q + f).toNat = q.toNat + n := by
  rw [UInt64.toNat_add, hf]; omega

end L
