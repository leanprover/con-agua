import ConAgua.Checker.IndArmClosed
import ConAgua.Checker.Prog
import ConAgua.Checker.IndArmFns
import ConAgua.Compiler.WriteSetSplit
import ConAgua.Arena.IndRealAbs

/-! The per-function write-set checks of the inductive arm's callees in `checkerProg`
(`Checker/IndArmClosed.lean`), part 3: `maFree`, `mcFree` and the walk memos. -/

namespace L.Checker

open L.Arena L.Ind L.Compiler

/-! ## `maFree`: `check_block_pass`, `check_block_tail` -/

names_tree armMaTree : armMaFns
prog_all checkerProg_armMaChk : checkerProg (wsChk CTL
  (tA fun b => decide (b ≠ MAM)) (tC fun c => decide (c ≠ 202 ∧ c ≠ 203)) armMaTree)

/-! ## `mcFree`: `check_block` -/

names_tree armMcTree : armMcFns
prog_all checkerProg_armMcChk : checkerProg (wsChk CTL
  (tA fun b => decide (b ≠ MCM)) (tC fun c => decide (c ≠ 216 ∧ c ≠ 217)) armMcTree)

/-! ## The walk memos: the `AbsKeep` callees that reach no walk -/

/-- The arrays below 256 apart from the walk memos'. -/
def armAbsA : List ArrId := (List.range 388).filter fun b => memoFreeA [b]
/-- The `CTL` words below 256 apart from the walk memos' epoch words. -/
def armAbsC : List Word := ((List.range 256).filter fun c => memoFreeC [c.toUInt64]).map Nat.toUInt64

theorem armAbsA_free : memoFreeA armAbsA = true := by decide +kernel
theorem armAbsC_free : memoFreeC armAbsC = true := by decide +kernel

names_tree armAbsTree : armAbsFns
prog_all checkerProg_armAbsChk : checkerProg (wsChk CTL
  (tA fun b => memoFreeA [b]) (tC fun c => memoFreeC [c.toUInt64]) armAbsTree)

end L.Checker
