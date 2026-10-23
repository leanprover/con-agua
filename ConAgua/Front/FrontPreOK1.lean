import ConAgua.Front.LineRefine

/-!
# The frontend's records, word by word, I: what one line writes to `DECL`/`DLP` (lane `pipeline`)

The checker's later stages read the records of `DECL` with two facts the frontend's refinement
(`StateDR`) does not keep: a one-constant record's handle words `1`, `4`, `5` are below `2 ^ 32`,
an inductive record's block offset (word `2`) and pointer words are nonzero (`L.Checker.RecOK`).
This file and the next two show what one applied line does to `DECL` and `DLP` (`DGrow`): the old
records' words and the pool below its old top stay, and a new record (at most one) has such words.
A name, level or expression line leaves both arrays alone (`DK`, `lineRecW_dk`, `applyExprW_dk`); a
declaration line appends one record of table handles (`applyDeclW_grow`).
-/

open L.Arena
open ConRon.Arena ConRon.Arena.Frontend

namespace L.Front

/-- The number of records of `DECL` (its word `0`). -/
def dcnt (m : Mem) : Nat := ((m.arr64 DECL)[0]?.getD 0).toNat

/-- The top of `DLP` (its word `0`). -/
def dtop (m : Mem) : Nat := ((m.arr64 DLP)[0]?.getD 0).toNat

/-- A record as a line writes it: a one-constant record's handle words are below `2 ^ 32`, an
inductive record's block offset is nonzero. -/
def NewOK (D : Array Word) (x : Nat) : Prop :=
  (dw D x 0 ≠ 6 → (dw D x 1).toNat < 2 ^ 32 ∧ (dw D x 4).toNat < 2 ^ 32 ∧ (dw D x 5).toNat < 2 ^ 32) ∧
  (dw D x 0 = 6 → dw D x 2 ≠ 0)

/-- **What a line does to the records**: the words of the old records and of the pool up to its
old top stay, the new records are `NewOK`. -/
structure DGrow (m m' : Mem) : Prop where
  decl : ∀ j, 0 < j → j < 1 + 8 * dcnt m → (m'.arr64 DECL)[j]? = (m.arr64 DECL)[j]?
  dlp : ∀ j, 0 < j → j ≤ dtop m → (m'.arr64 DLP)[j]? = (m.arr64 DLP)[j]?
  new : ∀ x, dcnt m ≤ x → x < dcnt m' → NewOK (m'.arr64 DECL) x

/-- `DECL` and `DLP` unchanged. -/
def DK (m m' : Mem) : Prop := m'.arr64 DECL = m.arr64 DECL ∧ m'.arr64 DLP = m.arr64 DLP

theorem DK.refl (m : Mem) : DK m m := ⟨rfl, rfl⟩

theorem DK.trans {m₁ m₂ m₃ : Mem} (h₁ : DK m₁ m₂) (h₂ : DK m₂ m₃) : DK m₁ m₃ :=
  ⟨h₂.1.trans h₁.1, h₂.2.trans h₁.2⟩

theorem DK.grow {m m' : Mem} (h : DK m m') : DGrow m m' :=
  ⟨fun j _ _ => by rw [h.1], fun j _ _ => by rw [h.2],
    fun x h1 h2 => by simp only [dcnt, h.1] at h1 h2; omega⟩

theorem DK.ofFrame {A : List ArrId} {C : List Word} {m m' : Mem} (hf : MemFrame A C m m')
    (hd : DECL ∉ A := by tapart) (hq : DLP ∉ A := by tapart) : DK m m' :=
  ⟨hf.1 DECL hd (by decide), hf.1 DLP hq (by decide)⟩

theorem DK.set64 (m : Mem) (b : ArrId) (hd : b ≠ DECL) (hq : b ≠ DLP) (i v : Word) :
    DK m (m.set64 b i v) :=
  ⟨Mem.arr64_set64_ne _ _ _ _ _ (Ne.symm hd), Mem.arr64_set64_ne _ _ _ _ _ (Ne.symm hq)⟩

/-- **A name or level line leaves `DECL`, `DLP` alone.** -/
theorem lineRecW_dk (b : Array UInt8) (m m' : Mem) (pl idx a c d : Word)
    (h : lineRecW b m pl idx a c d = some m') : DK m m' := by
  sorry

/-- **An expression line leaves `DECL`, `DLP` alone.** -/
theorem applyExprW_dk (b : Array UInt8) (m m' : Mem) (pl idx a c d : Word)
    (h : applyExprW b m pl idx a c d = some m') : DK m m' := by
  sorry

/-- **A declaration line appends one record of table handles.** -/
theorem applyDeclW_grow (b : Array UInt8) (m m' : Mem) (st : StateD) (hD : StateDR m st)
    (pl name lps type value hk hn flag : Word)
    (h : applyDeclW b m pl name lps type value hk hn flag = some m') : DGrow m m' := by
  sorry

end L.Front
