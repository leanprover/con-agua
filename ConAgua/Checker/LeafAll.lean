import ConAgua.Checker.Prog
import ConAgua.Arena.LeafFns

/-!
# The leaves' write set in the checker's program (lane `loopt2`)

`ConAgua/Arena/LeafFns.lean`'s `LeafClosed`, for `checkerProg`: no leaf writes the pin table, the
core's memos or bytes. Per-chunk kernel checks as `LoopAll.lean`.
-/

namespace L.Checker

open L.Arena L.Compiler

/-- The arrays of `leafA`, as a test. -/
def leafPa (a : ArrId) : Bool :=
  decide (a < 388) && a != PINS && a != 49 && a != 50 && a != 52 && a != 53 && a != 54 &&
    a != 151 && a != 152 && a != 153

/-- The `CTL` words of `leafC`, as a test. -/
def leafPc (w : Word) : Bool :=
  decide (w.toNat < 1024) && w.toNat != 48 && w.toNat != 50 && w.toNat != 54 && w.toNat != 56 &&
    w.toNat != 58 && w.toNat != 152 && w.toNat != 154 && w.toNat != 156

theorem leafPa_mem (a : ArrId) (h : leafPa a = true) : a ∈ leafA := by
  simp only [leafPa, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h
  simp [leafA, List.mem_filter, List.mem_range, h]

theorem leafPc_mem (w : Word) (h : leafPc w = true) : w ∈ leafC := by
  simp only [leafPc, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h
  simp only [leafC, List.mem_map, List.mem_filter, List.mem_range]
  refine ⟨w.toNat, ⟨h.1.1.1.1.1.1.1.1, ?_⟩, UInt64.ofNat_toNat⟩
  simp only [decide_eq_true_eq]
  omega

/-- Every function of the checker passes the leaves' per-function check. -/
prog_all checkerProg_leafChk : checkerProg (wsChk CTL leafPa leafPc leafTree)

theorem checkerProg_leafClosed : LeafClosed checkerProg :=
  closedW_of_all leafTree.eq leafPa_mem leafPc_mem checkerProg_leafChk

end L.Checker
