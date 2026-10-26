import ConAgua.Front.Driver
import ConAgua.Scan.RecordsLink
import ConAgua.Arena.Refine
import ConAgua.Front.StateDR
import ConRon.Arena.Frontend.ExportC

/-!
# The driver's model refines con-ron's `parseBytes`

`runW_refines`: if the loop's model accepts (`0`) from position `i` with the parse state `st`
related to the memory, then con-ron's `feedChunk` from `i` followed by `parseBytes`'s last-line
step (`finishFrom`) accepts, and the final memory is related to its final arena and parse states.
The relation `Inv` and the line step are parameters: `LineStepI Inv` is what one applied line
must satisfy (`front_line`'s refinement, `ConAgua.Front.LineRefine`). `runI_refines` adds
`StateD.init` in front: `parseBytes` accepts.

A line that `front_line` applies and whose next position is `0` (no newline before the buffer's
end) is the tail `feedChunk` leaves to `applyFinalLine`, which scans and applies it again: the
same record, the same step.
-/

open ConLeche ConLeche.Frontend
open ConRon.Arena ConRon.Arena.Frontend
open L.Arena (AM.ok AM.res AM.st AM.run_of_ok)

namespace L.Front


/-- One line, as con-ron applies it, with the relation `Inv` after: the scanner reads the record
`r` at `i` and the next position `q` (the word `nx`), `applyLine st r` succeeds from `a₀` with the
parse state `st'`, and `Inv m (state after) st'`. -/
def LineStepI (Inv : Mem → AState → StateD → Prop) (b : ByteArray) (i : USize) (nx : Word)
    (st : StateD) (a₀ : AState) (m : Mem) : Prop :=
  ∃ r q st', scanLineFwd b i = .ok r q ∧ q.toUInt64 = nx ∧ AM.ok (applyLine st r) a₀ ∧
    AM.res (applyLine st r) a₀ = .inl st' ∧ Inv m (AM.st (applyLine st r) a₀) st'

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
    (hs : scanLineFwd b i = .ok r 0) (hap : (applyLine st r).run a = .ok (.inl st', a')) :
    (finishFrom st b i lineNo).run a = .ok (.ok (.ofState st'), a') := by
  have hi' : i < USize.ofNat b.size := hi
  unfold finishFrom
  rw [feedChunk, dite_eq_left hi]
  simp [hs, hi', applyFinalLine, hap]
  rfl

theorem finishFrom_next (r : LineRec) (q : USize) (st' : StateD) (a' : AState) (hi : i < b.usize)
    (hs : scanLineFwd b i = .ok r q) (hq : q ≠ 0) (hiq : i < q)
    (hap : (applyLine st r).run a = .ok (.inl st', a')) :
    (finishFrom st b i lineNo).run a = (finishFrom st' b q (lineNo + 1)).run a' := by
  conv => lhs; unfold finishFrom
  rw [feedChunk, dite_eq_left hi]
  simp [hs, hq, StateT.run_bind, hap, hiq]
  rfl

end steps

/-! ## The loop -/

section loop
variable (Inv : Mem → AState → StateD → Prop) (b : ByteArray)
  (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63)
  (lineW : Mem → Word → Option (Word × Word × Mem))
  (hstep : ∀ (m m' : Mem) (i : USize) (ok nx : Word) (st : StateD) (a : AState), Inv m a st →
    i < b.usize → lineW m i.toUInt64 = some (ok, nx, m') → ok ≠ 0 → LineStepI Inv b i nx st a m')
include h64 hsize hstep

theorem runW_refines : ∀ (d : Nat) (i : USize) (m : Mem) (ln : Word) (st : StateD) (a : AState)
    (lineNo : Nat) (m' : Mem), b.size - i.toNat = d → ln.toNat ≤ i.toNat → Inv m a st →
    runW lineW b.size m i.toUInt64 ln = some (0, m') →
    ∃ st' a', (finishFrom st b i lineNo).run a = .ok (.ok (.ofState st'), a') ∧ Inv m' a' st' := by
  intro d
  refine Nat.strongRecOn d ?_
  intro d ih i m ln st a lineNo m' hd hln hI h
  by_cases hi : i < b.usize
  · have hiW := (ConAgua.Scan.RecordsLink.lt_usize_iff b h64 hsize i).mp hi
    rw [runW_step _ b.size _ _ _ hiW] at h
    cases hl : lineW m i.toUInt64 with
    | none => rw [hl, runK_none] at h; cases h
    | some x =>
    obtain ⟨ok, nx, m₁⟩ := x
    rw [hl] at h
    have hin := ConLeche.Frontend.usizeInBounds b i hi
    have hiv : i.toNat < 2 ^ 63 := by omega
    have hln1 : (ln + 1) ≠ 0 := by
      intro h0
      have := congrArg UInt64.toNat h0
      rw [UInt64.toNat_add] at this
      simp at this
      have := ln.toNat_lt; omega
    by_cases hok : ok = 0
    · rw [runK_fail _ _ _ _ _ _ _ hok] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact absurd h.1 hln1
    obtain ⟨r, q, st', hs, hq, hok', hres, hInv⟩ := hstep m m₁ i ok nx st a hI hi hl hok
    have hrun := AM.run_of_ok _ _ hok'
    rw [hres] at hrun
    by_cases hnx : nx = 0
    · rw [runK_last _ _ _ _ _ _ _ hok hnx] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      have hq0 : q = 0 := by
        apply USize.toNat_inj.mp
        have := congrArg UInt64.toNat (hq.trans hnx)
        simpa [USize.toNat_toUInt64] using this
      subst hq0
      exact ⟨st', _, finishFrom_last st b i lineNo a r st' _ hi hs hrun, hInv⟩
    by_cases hx : i.toUInt64 < nx
    · rw [runK_next _ _ _ _ _ _ _ hok hnx hx] at h
      have hq0 : q ≠ 0 := by
        intro h0; apply hnx; rw [← hq, h0]; rfl
      have hiq : i < q := by
        rw [ConAgua.Scan.lt_toUInt64_iff, hq]; exact hx
      rw [finishFrom_next st b i lineNo a r q st' _ hi hs hq0 hiq hrun]
      have hqi := USize.lt_iff_toNat_lt.mp hiq
      have hqs : q.toNat ≤ b.size ∨ b.size < q.toNat := by omega
      rw [← hq] at h
      refine ih (b.size - q.toNat) ?_ q m₁ (ln + 1) st' _ (lineNo + 1) m' rfl ?_ hInv h
      · omega
      · rw [UInt64.toNat_add]; simp; omega
    · rw [runK_noprog _ _ _ _ _ _ _ hok hnx hx] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact absurd h.1 hln1
  · have hiW : ¬ i.toUInt64 < UInt64.ofNat b.size := fun h' =>
      hi ((ConAgua.Scan.RecordsLink.lt_usize_iff b h64 hsize i).mpr h')
    rw [runW_end _ b.size _ _ _ hiW] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨st, a, finishFrom_end st b i lineNo a hi, hI⟩

/-- **The driver's model refines `parseBytes`**: if `front_init`'s model (refining `StateD.init`
from `Inv₀`) and then the loop's model from `0` accept, `parseBytes b` accepts, with `Inv` of the
final memory and the final arena and parse states. -/
theorem runI_refines (Inv₀ : Mem → AState → Prop) (initW : Mem → Option Mem)
    (hinit : ∀ m m₁ a, Inv₀ m a → initW m = some m₁ →
      ∃ st₀ a₁, StateD.init.run a = .ok (st₀, a₁) ∧ Inv m₁ a₁ st₀)
    (m m' : Mem) (a₀ : AState) (h₀ : Inv₀ m a₀) (h : runI lineW b.size (initW m) = some (0, m')) :
    ∃ st' a', (parseBytes b).run a₀ = .ok (.ok (.ofState st'), a') ∧ Inv m' a' st' := by
  cases hI : initW m with
  | none => rw [hI, runI_none] at h; cases h
  | some m₁ =>
  rw [hI, runI_some] at h
  obtain ⟨st₀, a₁, hrun, hInv⟩ := hinit m m₁ a₀ h₀ hI
  have hz : (0 : USize).toUInt64 = 0 := rfl
  rw [← hz] at h
  obtain ⟨st', a', hf, hI'⟩ := runW_refines Inv b h64 hsize lineW hstep _ 0 m₁ 0 st₀ a₁ 0 m' rfl
    (by simp) hInv h
  refine ⟨st', a', ?_, hI'⟩
  rw [parseBytes_eq b (by rw [show USize.size = 2 ^ 64 by simp [USize.size, h64]]; omega),
    StateT.run_bind, hrun]
  exact hf

end loop

end L.Front
