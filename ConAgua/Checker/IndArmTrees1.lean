import ConAgua.Checker.IndArmTests
import ConAgua.Checker.IndArmFns
import ConAgua.Layout

/-! The function sets of the inductive arm's write-set checks (`Checker/IndArmClosed.lean`) as
name trees, with their array and `CTL` tests, part 1: `posFree`, `hbFree`, `rcFree`,
`taFree`. Two modules, built in
parallel: the kernel checks of one module run one after another. -/

namespace L.Checker

open L.Arena L.Ind L.Compiler

/-- `posFree`: `check_block_pass`' callees and `block_raw_rec`. -/
names_tree armPosTree : armPosFns
def armPosT : ArmTest := (tA fun b => decide (b ∉ [NOM, DPM, RAM, HBM, RFM]),
  tC fun c => decide (c ∉ [204, 206, 208, 210, 214, 218, 219]), armPosTree)

/-- `hbFree`: `tailCallees`. -/
names_tree armHbTree : armHbFns
def armHbT : ArmTest := (tA fun b => decide (b ≠ HBM), tC fun c => decide (c ≠ 214), armHbTree)

/-- `rcFree`: `tailRcCallees`, `grcRcCallees`, `cons_block_recs_tf`. -/
names_tree armRcTree : armRcFns
def armRcT : ArmTest := (tA fun b => decide (b ∉ [NOM, DPM, RAM, HBM, RFM, TAM]),
  tC fun c => decide (c ∉ [204, 206, 208, 210, 212, 213, 214, 218, 219]), armRcTree)

/-- `taFree`: `blockTaCallees`. -/
names_tree armTaTree : armTaFns
def armTaT : ArmTest := (tA fun b => decide (b ≠ TAM), tC fun c => decide (c ≠ 212 ∧ c ≠ 213), armTaTree)

end L.Checker
