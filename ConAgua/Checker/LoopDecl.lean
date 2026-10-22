import ConAgua.Checker.Prog
import ConAgua.Arena.LoopT
import ConAgua.Compiler.WriteSetSplit

/-!
# The declaration texts' write set in the checker's program (lane `loopt2`)

The declaration loop's program hypotheses (`CvgProg`, `IvProg`, `ArmProg`, `CheckDeclProg`'s
`natText` and `dgClosed`) ask for a step's write set (`stepA`, `stepC`: no `PEND`, `DECL`, `DLP`,
promotion memos, `CTL[130]`, `CTL[140‥147]`, `CTL[150]`, `CTL[151]`) on a call-closed superset of
their function lists (`StepIn`). In the checker's program the texts' open callees (`openFns`: the
core's entry points, the walks, the ROM readers) are real code, so the superset is the texts'
lists, the core's (`stageCoreFns`) and the open callees' own callees (`declExtFns`). Decided by
per-chunk kernel checks as `LoopCore.lean`.
-/

namespace L.Checker

open L.Arena L.Ind L.Compiler
open L.Front (DECL DLP)

/-- The functions the declaration texts reach in the checker's program outside the texts' lists
and `stageCoreFns`: the callees of the walks, the ROM readers and `is_proj_fn_shape`. -/
def declExtFns : List FnName :=
  DECLEXT

/-- The call-closed superset: the texts' lists, their open callees' callees and the core. -/
def declLoopFns : List FnName :=
  cvgFns ++ ivFns ++ armFns ++ natGateFns ++ dgFns ++ declExtFns ++ stageCoreFns

/-- `declLoopFns` as a tree of name codes. -/
names_tree declLoopTree : declLoopFns

/-- The arrays of `stepA`, as a test. -/
def stepPa (a : ArrId) : Bool :=
  decide (a < 256) && a != PEND && a != DECL && a != DLP && (decide (a < 146) || decide (149 < a))

/-- The `CTL` words of `stepC`, as a test. -/
def stepPc (w : Word) : Bool :=
  decide (w.toNat < 1024) && w.toNat != 130 && w.toNat != 150 && w.toNat != 151 &&
    (decide (w.toNat < 140) || decide (147 < w.toNat))

theorem stepPa_mem (a : ArrId) (h : stepPa a = true) : a ∈ stepA := by
  simp only [stepPa, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne,
    ne_eq] at h
  simp [stepA, List.mem_filter, List.mem_range, h]

theorem stepPc_mem (w : Word) (h : stepPc w = true) : w ∈ stepC := by
  simp only [stepPc, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne,
    ne_eq] at h
  simp only [stepC, List.mem_map, List.mem_filter, List.mem_range]
  refine ⟨w.toNat, ⟨h.1.1.1.1, ?_⟩, UInt64.ofNat_toNat⟩
  simp only [decide_eq_true_eq]
  exact ⟨h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- Every function of the checker passes the declaration texts' per-function check. -/
prog_all checkerProg_declChk : checkerProg (wsChk CTL stepPa stepPc declLoopTree)

theorem checkerProg_declClosed : closedA checkerProg stepA stepC declLoopFns = true :=
  closedW_of_all declLoopTree.eq stepPa_mem stepPc_mem checkerProg_declChk

theorem checkerProg_stepIn {fs : List FnName} (h : ∀ f ∈ fs, f ∈ declLoopFns) :
    StepIn checkerProg fs :=
  ⟨_, h, checkerProg_declClosed⟩

theorem checkerProg_cvgIn : StepIn checkerProg cvgFns :=
  checkerProg_stepIn fun _ h => by simp only [declLoopFns, List.mem_append]; tauto

theorem checkerProg_ivIn : StepIn checkerProg ivFns :=
  checkerProg_stepIn fun _ h => by simp only [declLoopFns, List.mem_append]; tauto

theorem checkerProg_armIn : StepIn checkerProg armFns :=
  checkerProg_stepIn fun _ h => by simp only [declLoopFns, List.mem_append]; tauto

theorem checkerProg_natGateIn : StepIn checkerProg natGateFns :=
  checkerProg_stepIn fun _ h => by simp only [declLoopFns, List.mem_append]; tauto

theorem checkerProg_dgIn : StepIn checkerProg dgFns :=
  checkerProg_stepIn fun _ h => by simp only [declLoopFns, List.mem_append]; tauto

end L.Checker
