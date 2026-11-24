module

public import ConAgua.Checker.C1Hdr
public import ConAgua.Checker.CmpSeqView
import ConAgua.Arena.FreezeFreshBase
import ConAgua.Arena.FreezeTruncBase

@[expose] public section

/-!
# A thread's switch from header S to header C (lane compare2, H7)

A thread runs its solution calls on `bufMem B r j` (header S, showing `mS`) and then its challenge
calls on `bufMem BC r j` (header C, showing `m9`), on the same region `r`. With both headers of the
same extents (`hext`) and `mS` a frame of `m9` off the stream index's arrays and words (`csA`,
`csC`), the memory after `check_b`'s first block and re-read under header C is the one under
header S with `csA` and the words `csC` of `CTL` replaced by `freshMem m9`'s (`c1Patch`):
`c1_switch`.
-/

namespace L.Checker

open L L.Arena

/-- `c` with the seed words `rrWs` replaced by `d`'s. -/
def c1CtlP (c d : Array Word) : Array Word := c.mapIdx fun i v => if i ∈ rrWs then d.getD i 0 else v

/-- **`X` with the stream index's arrays `csA` and `CTL`'s words `csC` replaced by `C`'s.** -/
def c1Patch (C X : Mem) : Mem :=
  { X with words := fun s => if s ∈ csA then C.arr64 s else if s = CTL then c1CtlP (X.arr64 CTL) (C.arr64 CTL)
      else X.arr64 s }

theorem rrWs_iff (k : Nat) : k ∈ rrWs ↔ k = 128 ∨ (162 ≤ k ∧ k < 174) ∨ k = 224 := by
  simp [rrWs]

theorem csC_iff (x : Word) : x ∈ csC ↔ x.toNat ∈ rrWs := by
  rw [rrWs_iff]
  constructor
  · intro h; have := csC_val h; omega
  · intro h
    have e : x = UInt64.ofNat x.toNat := (UInt64.ofNat_toNat).symm
    rcases h with h | ⟨h1, h2⟩ | h
    · rw [e, h]; decide
    · rw [e]
      have : x.toNat = 162 ∨ x.toNat = 163 ∨ x.toNat = 164 ∨ x.toNat = 165 ∨ x.toNat = 166 ∨ x.toNat = 167 ∨
          x.toNat = 168 ∨ x.toNat = 169 ∨ x.toNat = 170 ∨ x.toNat = 171 ∨ x.toNat = 172 ∨ x.toNat = 173 := by omega
      rcases this with h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> decide
    · rw [e, h]; decide

theorem getD_c1CtlP (c d : Array Word) (k : Nat) :
    (c1CtlP c d).getD k 0 = if k < c.size then (if k ∈ rrWs then d.getD k 0 else c.getD k 0) else 0 := by
  simp only [c1CtlP, Array.getD_eq_getD_getElem?, Array.getElem?_mapIdx]
  by_cases h : k < c.size
  · simp [h]
  · simp [h]

theorem size_c1CtlP (c d : Array Word) : (c1CtlP c d).size = c.size := by simp [c1CtlP]

theorem c1Patch_arr (C X : Mem) (s : TieredArray) : (c1Patch C X).arr64 s =
    if s ∈ csA then C.arr64 s else if s = CTL then c1CtlP (X.arr64 CTL) (C.arr64 CTL) else X.arr64 s := rfl

/-- The re-read keeps `CTL`'s words but the seed's. -/
theorem rereadMem_off (x : Mem) {k : Nat} (hk : k ∉ rrWs) :
    ((rereadMem x).arr64 CTL).getD k 0 = (x.arr64 CTL).getD k 0 := by
  rw [rrWs_iff] at hk
  unfold rereadMem
  split
  · rfl
  rw [getD_set64_same, getD_copy64 (by decide) 12 _ 162 162 (by simp) (by simp), getD_set64_same]
  simp only [L.Mem.size64_set64, show UInt64.toNat 224 = 224 from rfl, show UInt64.toNat 162 = 162 from rfl,
    show UInt64.toNat 128 = 128 from rfl]
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

end L.Checker
