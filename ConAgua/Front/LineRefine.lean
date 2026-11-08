module

public import ConAgua.Front.Line
public import ConAgua.Front.UnescapeLink
public import ConAgua.Front.StateDR
public import ConLeche.Frontend.ExportC
public import Std.Tactic.BVDecide.Normalize.Prop
import ConAgua.Scan.LineLink

@[expose] public section

/-!
# The pieces of con-ron's per-line step

`LineStep`: con-leche's scanner reads a record `r` at `i` with `next` the position after it
(`scanLineFwd`), and con-ron's `applyRecord st r` succeeds from the arena state `a₀` with a parse
state `st'` such that the memory after is related to its arena state by `ArenaD` and to `st'` by
`StateDR`. A name or level line's fields applied are that step (`lineRecW_refines`); the
expression and declaration lines' are `ApplyExprRefine.lean`'s and `ApplyDLineRef.lean`'s.
`front_line`'s refinement is `frontLine_ref` (`LineRef.lean`).
-/

open Std.WP
open scoped Lean.Order
open L.Arena
open L.Scan.Member L.Scan.Values L.Scan.Records L.Scan.Line L.Front.Fields
open ConLeche.Frontend hiding StateD RecordVerdict applyLine
open ConAgua.Scan ConAgua.Scan.RecordsLink ConAgua.Scan.LineLink
open ConAgua.Front.FieldsLink
open ConRon.Arena ConRon.Arena.Frontend

namespace L.Front

/-- **One line, as con-ron applies it**: the scanner reads the record `r` at `i` and the next
position `q` (the word `nx`), `applyRecord st r` succeeds from `a₀` with the parse state `st'`, and
the memory `m` is related to the arena state after by `ArenaD` and to `st'` by `StateDR`. -/
def LineStep (b : ByteArray) (i : USize) (nx : Word) (st : StateD) (a₀ : AState) (m : Mem) : Prop :=
  ∃ r q st', scanLineFwd b i = .ok r q ∧ q.toUInt64 = nx ∧ AM.ok (applyRecord st r) a₀ ∧
    AM.res (applyRecord st r) a₀ = .inl st' ∧ ArenaD m (AM.st (applyRecord st r) a₀) ∧ StateDR m st'

/-- The pure arena steps of `applyLine`. -/
theorem applyLine_pure (st : StateD) (a₀ : AState) (r : LineRec)
    (hr : r = .header ∨ r = .blank) :
    AM.ok (applyRecord st r) a₀ ∧ AM.res (applyRecord st r) a₀ = .inl st ∧
      AM.st (applyRecord st r) a₀ = a₀ := by
  sorry

theorem applyLine_name (st : StateD) (a₀ : AState) (i : Nat) (r : NameRec)
    (h : AM.ok (parseNameEntryD st i r) a₀) :
    AM.ok (applyRecord st (.name i r)) a₀ ∧
      AM.res (applyRecord st (.name i r) : AM (StateD ⊕ RecordVerdict)) a₀ = .inl (AM.res (parseNameEntryD st i r) a₀) ∧
      AM.st (applyRecord st (.name i r)) a₀ = AM.st (parseNameEntryD st i r) a₀ := by
  sorry

theorem applyLine_level (st : StateD) (a₀ : AState) (i : Nat) (r : LevelRec)
    (h : AM.ok (parseLevelEntryD st i r) a₀) :
    AM.ok (applyRecord st (.level i r)) a₀ ∧
      AM.res (applyRecord st (.level i r) : AM (StateD ⊕ RecordVerdict)) a₀ = .inl (AM.res (parseLevelEntryD st i r) a₀) ∧
      AM.st (applyRecord st (.level i r)) a₀ = AM.st (parseLevelEntryD st i r) a₀ := by
  sorry

section refine
variable (b : ByteArray) (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63)
include h64 hsize

/-- A name or level line: the fields `f` against the record `r`, applied. -/
theorem lineRecW_refines (m m' : Mem) (_hm : m.arr8 IN = b.data) (a₀ : AState) (st : StateD)
    (hR : ArenaD m a₀) (hD : StateDR m st) (hmode : ModeOK m) (f : Fld) (r : LineRec)
    (hRec : f.pl ≠ 0 → RecR b r f) (h : lineRecW b.data m f.pl f.idx f.a f.c f.d = some m') :
    ∃ st', AM.ok (applyRecord st r) a₀ ∧ AM.res (applyRecord st r) a₀ = .inl st' ∧
      ArenaD m' (AM.st (applyRecord st r) a₀) ∧ StateDR m' st' ∧ ModeOK m' := by
  sorry

omit h64 hsize in
/-- An expression line, as `applyLine` applies it. -/
theorem applyLine_expr (st : StateD) (a₀ : AState) (i : Nat) (r : ExprRec)
    (h : AM.ok (parseExprEntryD st i r) a₀) :
    AM.ok (applyRecord st (.expr i r)) a₀ ∧
      AM.res (applyRecord st (.expr i r) : AM (StateD ⊕ RecordVerdict)) a₀ =
        .inl (AM.res (parseExprEntryD st i r) a₀) ∧
      AM.st (applyRecord st (.expr i r)) a₀ = AM.st (parseExprEntryD st i r) a₀ := by
  sorry

end refine

end L.Front
