import ConAgua.Checker.IndArmClosed
import ConAgua.Checker.Prog
import ConAgua.Checker.IndArmFns
import ConAgua.Compiler.WriteSetSplit

/-! The per-function write-set checks of the inductive arm's callees in `checkerProg`
(`Checker/IndArmClosed.lean`), part 2: `taFree`, `cidFree`, `rcHbFree`. -/

namespace L.Checker

open L.Arena L.Ind L.Compiler

/-! ## `taFree`: `blockTaCallees` -/

names_tree armTaTree : armTaFns
prog_all checkerProg_armTaChk : checkerProg (wsChk CTL
  (tA fun b => decide (b ≠ TAM)) (tC fun c => decide (c ≠ 212 ∧ c ≠ 213)) armTaTree)

/-! ## `cidFree`: `cidFrameCallees`, `check_basis_decl` -/

names_tree armCidTree : armCidFns
prog_all checkerProg_armCidChk : checkerProg (wsChk CTL
  (tA fun b => decide ((b.arr < 201 ∨ 208 < b.arr) ∧
    b ≠ ABMEMO ∧ b ≠ ILMEMO ∧ b ≠ ILFM ∧ b ≠ Stubs.CRM ∧ b ≠ PINS ∧ b ≠ WSM ∧ b ≠ FLM ∧ b ≠ LSM ∧
    b ≠ LPMEMO ∧ b ≠ LPLMEMO ∧ b ≠ LPLSMEMO))
  (tC fun c => decide ((c < 202 ∨ 219 < c) ∧ c ≠ 48 ∧ c ≠ 50 ∧ c ≠ 52 ∧ c ≠ 158 ∧
    c ≠ 152 ∧ c ≠ 154 ∧ c ≠ 156 ∧ c ≠ 54 ∧ c ≠ 56 ∧ c ≠ 58)) armCidTree)

/-! ## `rcHbFree`: `check_block_tables` -/

names_tree armRcHbTree : armRcHbFns
prog_all checkerProg_armRcHbChk : checkerProg (wsChk CTL
  (tA fun b => decide (b ∉ ([NOM, DPM, RAM, RFM, TAM] : List TieredArray)))
  (tC fun c => decide (c ∉ [204, 206, 208, 210, 212, 213, 218, 219])) armRcHbTree)

end L.Checker
