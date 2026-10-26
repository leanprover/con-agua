import ConAgua.Checker.Prog
import ConAgua.Arena.LoopFns
import ConAgua.Compiler.WriteSetSplit

/-!
# The loop's write set in the checker's program (lane `loopt2`)

`ConAgua/Arena/LoopFns.lean`'s `LoopClosed`, for `checkerProg`: every function the loop reaches
writes neither the pin table nor bytes. Per-chunk kernel checks as `LoopCore.lean`.
-/

namespace L.Checker

open L.Arena L.Compiler

/-- `loopFns` as a tree of name codes. -/
names_tree loopAllTree : loopFns

/-- The arrays of `loopA`, as a test. -/
def loopPa (a : ArrId) : Bool := decide (a < 388) && a != PINS

/-- The `CTL` words of `loopC`, as a test. -/
def loopPc (w : Word) : Bool := decide (w.toNat < 1024)

theorem loopPa_mem (a : ArrId) (h : loopPa a = true) : a ∈ loopA := by
  simp only [loopPa, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h
  simp [loopA, List.mem_filter, List.mem_range, h]

theorem loopPc_mem (w : Word) (h : loopPc w = true) : w ∈ loopC := by
  simp only [loopPc, decide_eq_true_eq] at h
  simp only [loopC, List.mem_map, List.mem_range]
  exact ⟨w.toNat, h, UInt64.ofNat_toNat⟩

/-- Every function of the checker passes the loop's per-function check. -/
prog_all checkerProg_loopAllChk : checkerProg (wsChk CTL loopPa loopPc loopAllTree)

theorem checkerProg_loopClosed : LoopClosed checkerProg :=
  closedW_of_all loopAllTree.eq loopPa_mem loopPc_mem checkerProg_loopAllChk

end L.Checker
