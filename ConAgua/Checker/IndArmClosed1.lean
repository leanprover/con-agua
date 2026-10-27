import ConAgua.Checker.IndArmClosed
import ConAgua.Checker.Prog
import ConAgua.Checker.IndArmFns
import ConAgua.Compiler.WriteSetSplit

/-! The per-function write-set checks of the inductive arm's callees in `checkerProg`
(`Checker/IndArmClosed.lean`), part 1: `posFree`, `hbFree`, `rcFree`. -/

namespace L.Checker

open L.Arena L.Ind L.Compiler

/-! ## `posFree`: `check_block_pass`' callees and `block_raw_rec` -/

names_tree armPosTree : armPosFns
prog_all checkerProg_armPosChk : checkerProg (wsChk CTL
  (tA fun b => decide (b ∉ [NOM, DPM, RAM, HBM, RFM]))
  (tC fun c => decide (c ∉ [204, 206, 208, 210, 214, 218, 219])) armPosTree)

/-! ## `hbFree`: `tailCallees` -/

names_tree armHbTree : armHbFns
prog_all checkerProg_armHbChk : checkerProg (wsChk CTL
  (tA fun b => decide (b ≠ HBM)) (tC fun c => decide (c ≠ 214)) armHbTree)

/-! ## `rcFree`: `tailRcCallees`, `grcRcCallees`, `cons_block_recs_tf` -/

names_tree armRcTree : armRcFns
prog_all checkerProg_armRcChk : checkerProg (wsChk CTL
  (tA fun b => decide (b ∉ [NOM, DPM, RAM, HBM, RFM, TAM]))
  (tC fun c => decide (c ∉ [204, 206, 208, 210, 212, 213, 214, 218, 219])) armRcTree)

end L.Checker
