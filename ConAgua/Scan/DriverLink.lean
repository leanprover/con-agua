module

public import ConAgua.Scan.LineLink
public import ConLeche.Frontend.ExportC

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.deprecated false

/-!
# `scanDriver` against con-leche's `parseBytes`

`parseBytes` scans every line with `scanLineSpec` (which is `scanLineFwd`,
`scanLineSpec_eq_scanLineFwd`) and applies it (`applyLine`); `scanDriver`
(`ConAgua.Scan.LineLink`) only scans. So a successful parse means every line scans
(`scanDriver_of_parseBytes_ok`), and a line that does not scan makes the parse fail at it or at
an earlier line, an earlier failure being one of `applyLine`'s (`parseBytes_error_of_scanDriver`).
-/

namespace ConAgua.Scan.DriverLink
open ConLeche ConLeche.Frontend ConAgua.Scan ConAgua.Scan.LineLink
open L (Word)
open L.Scan.Line (validN)

/-- `parseBytes` after its size guard: the whole buffer fed, then the last line. -/
def finish (b : ByteArray) (r : Except (CheckError × Nat) (StateD × Nat × USize)) :
    Except (CheckError × Nat) ParseResultD := do
  let (st, lineNo, tail) ← r
  if tail < b.usize then
    let st ← applyFinalLine st b tail (lineNo + 1)
    return .ofState st
  else
    return .ofState st

theorem parseBytes_eq (b : ByteArray) (h : b.size < USize.size) :
    parseBytes b = finish b (feedChunk .init b 0 0) := by
  unfold parseBytes finish
  simp only [ge_iff_le, show ¬ USize.size ≤ b.size by omega, if_false]

/-- `scanDriver` is `0` or past the lines already read. -/
theorem scanDriver_ge (b : ByteArray) (i : USize) (ln : Nat) (h : scanDriver b i ln ≠ 0) :
    ln + 1 ≤ scanDriver b i ln := by
  fun_induction scanDriver b i ln <;>
    first | omega | (simp at h; done) | (rename_i ih; have := ih h; omega)

/-- The last line, scanned again by `applyFinalLine`: it fails exactly when the scan does. -/
theorem applyFinalLine_err (st : StateD) (b : ByteArray) (i : USize) (n : Nat) (e : ScanErr)
    (h : scanLineFwd b i = .err e) : ∃ c, applyFinalLine st b i n = .error (c, n) := by
  unfold applyFinalLine
  rw [scanLineSpec_eq_scanLineFwd, h]
  exact ⟨_, rfl⟩

theorem finish_ok_pos (b : ByteArray) (st : StateD) (lineNo : Nat) (i : USize) :
    finish b (.ok (st, lineNo, i)) = if i < b.usize then
      (do let st ← applyFinalLine st b i (lineNo + 1); return .ofState st) else .ok (.ofState st) := by
  rfl

/-- `scanDriver` counts at most one line per byte. -/
theorem scanDriver_le (b : ByteArray) (i : USize) (ln : Nat) :
    scanDriver b i ln ≤ ln + (b.size - i.toNat) + 1 := by
  fun_induction scanDriver b i ln <;>
    first
      | omega
      | (have := usizeInBounds b _ ‹_ < b.usize›; omega)
      | (rename_i hj ih; have := usizeInBounds b _ ‹_ < b.usize›
         have := USize.lt_iff_toNat_lt.mp hj; omega)

/-- A successful parse from `i` means every line from `i` scans. -/
theorem scanDriver_of_finish_ok (b : ByteArray) (st : StateD) (i : USize) (lineNo : Nat)
    (res : ParseResultD) (h : finish b (feedChunk st b i lineNo) = .ok res) :
    scanDriver b i lineNo = 0 := by
  rw [feedChunk] at h
  rw [scanDriver]
  by_cases hi : i < b.usize
  · rw [dif_pos hi] at h ⊢
    rw [scanLineSpec_eq_scanLineFwd] at h
    cases hr : scanLineFwd b i with
    | err e =>
      exfalso
      rw [hr] at h
      simp only at h
      split at h
      · cases h
      · obtain ⟨c, hc⟩ := applyFinalLine_err st b i (lineNo + 1) e hr
        rw [finish_ok_pos, if_pos hi, hc] at h
        cases h
    | ok r j =>
      rw [hr] at h
      simp only at h ⊢
      by_cases hj : j = 0
      · simp [hj]
      · have hj2 : (j == 0) = false := by simpa using hj
        rw [hj2] at h ⊢
        simp only [Bool.false_eq_true, if_false] at h ⊢
        split at h
        · cases h
        · cases h
        · rename_i st' _
          by_cases hij : i < j
          · rw [dif_pos hij] at h ⊢
            exact scanDriver_of_finish_ok b st' j (lineNo + 1) res h
          · rw [dif_neg hij] at h
            cases h
  · rw [dif_neg hi]
termination_by b.size - i.toNat
decreasing_by exact Nat.sub_lt_sub_left (usizeInBounds b i hi) (USize.lt_iff_toNat_lt.mp hij)

/-- A line that does not scan makes the parse from `i` fail, at that line or before. -/
theorem finish_error_of_scanDriver (b : ByteArray) (st : StateD) (i : USize) (lineNo : Nat)
    (h : scanDriver b i lineNo ≠ 0) :
    ∃ c m, finish b (feedChunk st b i lineNo) = .error (c, m) ∧ m ≤ scanDriver b i lineNo := by
  have hge := scanDriver_ge b i lineNo h
  rw [feedChunk]
  rw [scanDriver] at h hge ⊢
  by_cases hi : i < b.usize
  · rw [dif_pos hi] at h hge
    rw [dif_pos hi, dif_pos hi]
    rw [scanLineSpec_eq_scanLineFwd]
    cases hr : scanLineFwd b i with
    | err e =>
      simp only
      split
      · exact ⟨_, _, rfl, Nat.le_refl _⟩
      · obtain ⟨c, hc⟩ := applyFinalLine_err st b i (lineNo + 1) e hr
        rw [finish_ok_pos, if_pos hi, hc]
        exact ⟨c, lineNo + 1, rfl, Nat.le_refl _⟩
    | ok r j =>
      rw [hr] at h hge
      simp only at h hge ⊢
      by_cases hj : j = 0
      · simp [hj] at h
      · have hj2 : (j == 0) = false := by simpa using hj
        rw [hj2] at h hge ⊢
        simp only [Bool.false_eq_true, if_false] at h hge ⊢
        split
        · exact ⟨_, _, rfl, hge⟩
        · exact ⟨_, _, rfl, hge⟩
        · rename_i st' _
          by_cases hij : i < j
          · rw [dif_pos hij] at h
            rw [dif_pos hij, dif_pos hij]
            exact finish_error_of_scanDriver b st' j (lineNo + 1) h
          · rw [dif_neg hij, dif_neg hij]
            exact ⟨_, _, rfl, Nat.le_refl _⟩
  · rw [dif_neg hi] at h; exact absurd rfl h
termination_by b.size - i.toNat
decreasing_by exact Nat.sub_lt_sub_left (usizeInBounds b i hi) (USize.lt_iff_toNat_lt.mp hij)

/-- If con-leche parses the buffer, every line scans: `scanDriver` (and with it the validator,
`validN`, `LineLink.valid_link`) accepts. -/
theorem scanDriver_of_parseBytes_ok (b : ByteArray) (res : ParseResultD)
    (h : parseBytes b = .ok res) : scanDriver b 0 0 = 0 := by
  by_cases hs : b.size < USize.size
  · rw [parseBytes_eq b hs] at h
    exact scanDriver_of_finish_ok b _ 0 0 res h
  · unfold parseBytes at h
    simp only [ge_iff_le, show USize.size ≤ b.size by omega, if_true] at h
    cases h

/-- If `scanDriver` rejects at line `n`, con-leche's parse fails, at line `n` or before (a line
`applyLine` rejects, or the size guard, line `0`). -/
theorem parseBytes_error_of_scanDriver (b : ByteArray) (n : Nat) (h : scanDriver b 0 0 = n)
    (hn : n ≠ 0) : ∃ c m, parseBytes b = .error (c, m) ∧ m ≤ n := by
  by_cases hs : b.size < USize.size
  · rw [parseBytes_eq b hs]
    subst h
    exact finish_error_of_scanDriver b _ 0 0 hn
  · unfold parseBytes
    simp only [ge_iff_le, show USize.size ≤ b.size by omega, if_true]
    exact ⟨_, 0, rfl, Nat.zero_le _⟩

section valid
variable (b : ByteArray) (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63)
include h64 hsize

/-- The validator's model from the start: `scanDriver b 0 0`. -/
theorem validN_zero : validN b.data 0 0 = UInt64.ofNat (scanDriver b 0 0) := by
  have := valid_link b h64 hsize 0 0
  exact this

/-- If con-leche parses the buffer, the validator's model accepts it. -/
theorem validN_of_parseBytes_ok (res : ParseResultD) (h : parseBytes b = .ok res) :
    validN b.data 0 0 = 0 := by
  rw [validN_zero b h64 hsize, scanDriver_of_parseBytes_ok b res h]; rfl

/-- If the validator's model rejects at line `n`, con-leche's parse fails at line `n` or
before. -/
theorem parseBytes_error_of_validN (n : Word) (h : validN b.data 0 0 = n) (hn : n ≠ 0) :
    ∃ c m, parseBytes b = .error (c, m) ∧ m ≤ n.toNat := by
  rw [validN_zero b h64 hsize] at h
  have hd : scanDriver b 0 0 ≠ 0 := by intro h0; rw [h0] at h; exact hn h.symm
  obtain ⟨c, m, hp, hm⟩ := parseBytes_error_of_scanDriver b _ rfl hd
  refine ⟨c, m, hp, ?_⟩
  -- the line count is at most the number of bytes, far below `2 ^ 64`
  have hle := scanDriver_le b 0 0
  rw [← h, UInt64.toNat_ofNat_of_lt' (by have hU : UInt64.size = 2 ^ 64 := rfl; simp at hle; omega)]
  exact hm

end valid

end ConAgua.Scan.DriverLink
