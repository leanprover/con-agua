module

public import ConAgua.L.Syntax

@[expose] public section

/-!
# A record's image

A writer that stores a record field by field (`erec_put(q + ⟪R.f⟫, …)`) leaves the words between
the fields as they were. Its model writes the record's *image*: a list of `R.size` entries, the
field's value at each field's offset and `none` (no store) elsewhere (`L.Ind.wrERo`). Each layout
file defines its record's image from its offsets (`CV.img`, …), so the image changes with the
layout and the writers' proofs do not.
-/

namespace L

/-- The image of a record of `size` words with the fields `fs` (offset, value). -/
def recImg (size : Word) (fs : List (Word × Word)) : List (Option Word) :=
  fs.foldl (fun l f => l.set f.1.toNat (some f.2)) (List.replicate size.toNat none)

theorem recImg_length (size : Word) (fs : List (Word × Word)) :
    (recImg size fs).length = size.toNat := by
  unfold recImg
  suffices ∀ (l : List (Option Word)), (fs.foldl (fun l f => l.set f.1.toNat (some f.2)) l).length =
      l.length by simp [this]
  induction fs with
  | nil => intro l; rfl
  | cons f fs ih => intro l; simp [List.foldl_cons, ih]

end L
