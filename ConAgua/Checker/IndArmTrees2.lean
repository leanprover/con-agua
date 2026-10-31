module

public import ConAgua.Checker.IndArmTests
public import ConAgua.Checker.IndArmFns
public import ConAgua.Arena.IndRealAbs

@[expose] public section

/-! The function sets of the inductive arm's write-set checks (`Checker/IndArmClosed.lean`) as
name trees, with their array and `CTL` tests, part 2: `cidFree`, `rcHbFree`,
`maFree`, `mcFree`, the walk memos. Two modules, built in
parallel: the kernel checks of one module run one after another. -/

namespace L.Checker

open L.Arena L.Ind L.Compiler

/-- `cidFree`: `cidFrameCallees`, `check_basis_decl`. -/
names_tree armCidTree : armCidFns
def armCidT : ArmTest :=
  (tA fun b => decide ((b.arr < 201 ∨ 208 < b.arr) ∧
    b ≠ ABMEMO ∧ b ≠ ILMEMO ∧ b ≠ ILFM ∧ b ≠ Stubs.CRM ∧ b ≠ PINS ∧ b ≠ WSM ∧ b ≠ FLM ∧ b ≠ LSM ∧
    b ≠ LPMEMO ∧ b ≠ LPLMEMO ∧ b ≠ LPLSMEMO),
  tC fun c => decide ((c < 202 ∨ 219 < c) ∧ c ≠ 48 ∧ c ≠ 50 ∧ c ≠ 52 ∧ c ≠ 158 ∧
    c ≠ 152 ∧ c ≠ 154 ∧ c ≠ 156 ∧ c ≠ 54 ∧ c ≠ 56 ∧ c ≠ 58), armCidTree)

/-- `rcHbFree`: `check_block_tables`. -/
names_tree armRcHbTree : armRcHbFns
def armRcHbT : ArmTest := (tA fun b => decide (b ∉ ([NOM, DPM, RAM, RFM, TAM] : List TieredArray)),
  tC fun c => decide (c ∉ [204, 206, 208, 210, 212, 213, 218, 219]), armRcHbTree)

/-- `maFree`: `check_block_pass`, `check_block_tail`. -/
names_tree armMaTree : armMaFns
def armMaT : ArmTest := (tA fun b => decide (b ≠ MAM), tC fun c => decide (c ≠ 202 ∧ c ≠ 203), armMaTree)

/-- `mcFree`: `check_block`. -/
names_tree armMcTree : armMcFns
def armMcT : ArmTest := (tA fun b => decide (b ≠ MCM), tC fun c => decide (c ≠ 216 ∧ c ≠ 217), armMcTree)

/-! The walk memos: the `AbsKeep` callees that reach no walk -/

/-- The checker's word arrays apart from the walk memos'. -/
def armAbsA : List TieredArray := checkerWordArrays.filter fun b => memoFreeA [b]

/-- The `CTL` words below 256 apart from the walk memos' epoch words. -/
def armAbsC : List Word := ((List.range 256).filter fun c => memoFreeC [c.toUInt64]).map Nat.toUInt64

theorem armAbsA_free : memoFreeA armAbsA = true := by decide +kernel
theorem armAbsC_free : memoFreeC armAbsC = true := by decide +kernel

names_tree armAbsTree : armAbsFns
def armAbsT : ArmTest := (tA fun b => memoFreeA [b], tC fun c => memoFreeC [c.toUInt64], armAbsTree)

end L.Checker
