module

public import ConAgua.Checker.IndArmTests
public import ConAgua.Checker.IndArmFns
meta import ConAgua.Checker.IndArmTests
meta import ConAgua.Checker.IndArmFns

@[expose] public section

/-! The function sets of the inductive arm's write-set checks (`Checker/IndArmClosed.lean`) as
name trees, with their array and `CTL` tests, part 1: `posFree`, `hbFree`, `rcFree`,
`taFree`. Two modules, built in
parallel: the kernel checks of one module run one after another. -/

namespace L.Checker

open L.Arena L.Ind L.Compiler

/-- `posFree`: `check_block_pass`' callees and `block_is_rec` (the leaf `struct_used_later`). -/
names_tree armPosTree : armPosFns
names_tree armPosCallTree : armPosFns ++ ["struct_used_later", "has_loose_bvar_in", "has_loose_b_var_b_fast"]
def armPosT : ArmTest := (tA fun b => decide (b ∉ ([NOM, DPM, RAM, HBM, RFM] : List TieredArray)),
  tC fun c => decide (c ∉ [204, 206, 208, 210, 214, 218, 219]), armPosTree, armPosCallTree)

/-- `hbFree`: `tailCallees` (the leaf `struct_used_later`). -/
names_tree armHbTree : armHbFns
names_tree armHbCallTree : armHbFns ++ ["struct_used_later", "has_loose_bvar_in", "has_loose_b_var_b_fast"]
def armHbT : ArmTest :=
  (tA fun b => decide (b ≠ HBM), tC fun c => decide (c ≠ 214), armHbTree, armHbCallTree)

/-- `rcFree`: `tailRcCallees`, `grcRcCallees` (the leaf `struct_used_later`). -/
names_tree armRcTree : armRcFns
names_tree armRcCallTree : armRcFns ++ ["struct_used_later", "has_loose_bvar_in", "has_loose_b_var_b_fast"]
def armRcT : ArmTest := (tA fun b => decide (b ∉ ([NOM, DPM, RAM, HBM, RFM, TAM] : List TieredArray)),
  tC fun c => decide (c ∉ [204, 206, 208, 210, 212, 213, 214, 218, 219]), armRcTree, armRcCallTree)

/-- `taFree`: `blockTaCallees`. -/
names_tree armTaTree : armTaFns
def armTaT : ArmTest :=
  (tA fun b => decide (b ≠ TAM), tC fun c => decide (c ≠ 212 ∧ c ≠ 213), armTaTree, armTaTree)

end L.Checker
