module

public import ConAgua.Front.StateDR

@[expose] public section

/-!
# The twin's driver, one line at a time

`finishFrom st b i lineNo`: con-ron's `parseBytes` after `StateD.init`, from position `i`
(`parseBytes_eq`): `feedChunk`'s lines, then `applyFinalLine` on the tail. Its steps: the end of
the input (`finishFrom_end`), a last line without a newline (`finishFrom_last`: the tail
`feedChunk` leaves to `applyFinalLine`, which scans and applies it again, the same record, the
same step), and a line with a next one (`finishFrom_next`). `LineStepI Inv` is one applied line
with the relation `Inv` after; `front_run`'s refinement (`FrontRunRef.lean`) walks these.
-/

open ConLeche ConLeche.Frontend
open ConRon.Arena ConRon.Arena.Frontend
open L.Arena (AM.ok AM.res AM.st AM.run_of_ok)

namespace L.Front


/-- One line, as con-ron applies it, with the relation `Inv` after: the scanner reads the record
`r` at `i` and the next position `q` (the word `nx`), `applyRecord st r` succeeds from `a₀` with the
parse state `st'`, and `Inv m (state after) st'`. -/
def LineStepI (Inv : Mem → AState → StateD → Prop) (b : ByteArray) (i : USize) (nx : Word)
    (st : StateD) (a₀ : AState) (m : Mem) : Prop :=
  ∃ r q st', scanLineFwd b i = .ok r q ∧ q.toUInt64 = nx ∧ AM.ok (applyRecord st r) a₀ ∧
    AM.res (applyRecord st r) a₀ = .inl st' ∧ Inv m (AM.st (applyRecord st r) a₀) st'

/-- `parseBytes` after `StateD.init`: the lines from `i`, then the tail. -/
def finishFrom (st : StateD) (b : ByteArray) (i : USize) (lineNo : Nat) :
    AM (Except (ConRon.Arena.CheckError × Nat) ParseResultD) := do
  match ← feedChunk st b i lineNo with
  | .error e => pure (.error e)
  | .ok (st, lineNo, tail) =>
    if tail < b.usize then
      match ← applyFinalLine st b tail (lineNo + 1) with
      | .error e => pure (.error e)
      | .ok st => pure (.ok (.ofState st))
    else
      pure (.ok (.ofState st))

theorem parseBytes_eq (b : ByteArray) (h : b.size < USize.size) :
    parseBytes b = (StateD.init >>= fun st => finishFrom st b 0 0) := by
  unfold parseBytes finishFrom
  simp only [ge_iff_le, show ¬ USize.size ≤ b.size by omega, ite_false]
  rfl

/-! ## `finishFrom`, one line at a time -/

section steps
variable (st : StateD) (b : ByteArray) (i : USize) (lineNo : Nat) (a : AState)

theorem finishFrom_end (hi : ¬ i < b.usize) :
    (finishFrom st b i lineNo).run a = .ok (.ok (.ofState st), a) := by
  have hi' : ¬ i < USize.ofNat b.size := hi
  unfold finishFrom
  rw [feedChunk, dite_eq_right hi]
  simp [hi']
  rfl

theorem finishFrom_last (r : LineRec) (st' : StateD) (a' : AState) (hi : i < b.usize)
    (hs : scanLineFwd b i = .ok r 0) (hap : (applyRecord st r).run a = .ok (.inl st', a')) :
    (finishFrom st b i lineNo).run a = .ok (.ok (.ofState st'), a') := by
  have hi' : i < USize.ofNat b.size := hi
  unfold finishFrom
  rw [feedChunk, dite_eq_left hi]
  simp [hs, hi', applyFinalLine, hap]
  rfl

theorem finishFrom_next (r : LineRec) (q : USize) (st' : StateD) (a' : AState) (hi : i < b.usize)
    (hs : scanLineFwd b i = .ok r q) (hq : q ≠ 0) (hiq : i < q)
    (hap : (applyRecord st r).run a = .ok (.inl st', a')) :
    (finishFrom st b i lineNo).run a = (finishFrom st' b q (lineNo + 1)).run a' := by
  conv => lhs; unfold finishFrom
  rw [feedChunk, dite_eq_left hi]
  simp [hs, hq, StateT.run_bind, hap, hiq]
  rfl

end steps

end L.Front
