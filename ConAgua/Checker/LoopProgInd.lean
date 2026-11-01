module

public import ConAgua.Checker.LoopDecl
public import ConAgua.Arena.CheckerT
meta import ConAgua.Checker.LoopDecl
meta import ConAgua.Arena.CheckerT
import all ConAgua.Arena.Abs1
import all ConAgua.Arena.AppStore
import all ConAgua.Arena.ArRange
import all ConAgua.Arena.ArRangeSpec
import all ConAgua.Arena.BVarStore
import all ConAgua.Arena.BvarB
import all ConAgua.Arena.CheckerL
import all ConAgua.Arena.ConsLib
import all ConAgua.Arena.ConsPresize
import all ConAgua.Arena.ConstStore
import all ConAgua.Arena.ConstsResolveF
import all ConAgua.Arena.CoreCaches
import all ConAgua.Arena.CoreLevels
import all ConAgua.Arena.CoreWalks
import all ConAgua.Arena.DeclAndPin
import all ConAgua.Arena.DeclApd
import all ConAgua.Arena.DeclArms
import all ConAgua.Arena.DeclArmsCanon
import all ConAgua.Arena.DeclArmsNat
import all ConAgua.Arena.DeclStep
import all ConAgua.Arena.DefEq
import all ConAgua.Arena.Env
import all ConAgua.Arena.ExprMk
import all ConAgua.Arena.FVarRange
import all ConAgua.Arena.FVarStore
import all ConAgua.Arena.ForallStore
import all ConAgua.Arena.Freeze
import all ConAgua.Arena.HasFvar
import all ConAgua.Arena.ImaxStore
import all ConAgua.Arena.IndIface
import all ConAgua.Arena.IndInstall
import all ConAgua.Arena.IndParts
import all ConAgua.Arena.IndPos
import all ConAgua.Arena.IndPos2
import all ConAgua.Arena.IndSum
import all ConAgua.Arena.Infer
import all ConAgua.Arena.InferFieldSort
import all ConAgua.Arena.Inst1
import all ConAgua.Arena.Inst1Spec
import all ConAgua.Arena.InstLP
import all ConAgua.Arena.InstList
import all ConAgua.Arena.InstListSpec
import all ConAgua.Arena.Knot
import all ConAgua.Arena.LamStore
import all ConAgua.Arena.LetStore
import all ConAgua.Arena.LevelApd
import all ConAgua.Arena.LevelEquiv
import all ConAgua.Arena.LevelHeap
import all ConAgua.Arena.LevelIntern
import all ConAgua.Arena.LevelLeq
import all ConAgua.Arena.LevelSimp
import all ConAgua.Arena.LevelStore
import all ConAgua.Arena.LevelSubst
import all ConAgua.Arena.LevelSubstL
import all ConAgua.Arena.LevelSubstLP
import all ConAgua.Arena.LevelZero
import all ConAgua.Arena.LiftL
import all ConAgua.Arena.LsStore
import all ConAgua.Arena.MaxStore
import all ConAgua.Arena.MemoLib
import all ConAgua.Arena.NAnonStore
import all ConAgua.Arena.NNumStore
import all ConAgua.Arena.NStrStore
import all ConAgua.Arena.NatAdd
import all ConAgua.Arena.NatArms
import all ConAgua.Arena.NatBits
import all ConAgua.Arena.NatCmp
import all ConAgua.Arena.NatDiv
import all ConAgua.Arena.NatGcd
import all ConAgua.Arena.NatMul
import all ConAgua.Arena.NatPow
import all ConAgua.Arena.NatShl
import all ConAgua.Arena.NatShr
import all ConAgua.Arena.NatSub
import all ConAgua.Arena.ParamStore
import all ConAgua.Arena.Pins
import all ConAgua.Arena.Prelude
import all ConAgua.Arena.ProjStore
import all ConAgua.Arena.Promote
import all ConAgua.Arena.PropRead
import all ConAgua.Arena.RecCheck
import all ConAgua.Arena.RecClass
import all ConAgua.Arena.RecGen
import all ConAgua.Arena.Refine
import all ConAgua.Arena.Rom
import all ConAgua.Arena.RomCI
import all ConAgua.Arena.RomExpr
import all ConAgua.Arena.RomItems
import all ConAgua.Arena.RomLevel
import all ConAgua.Arena.RomLevels
import all ConAgua.Arena.RomPins
import all ConAgua.Arena.Scratch
import all ConAgua.Arena.SortStore
import all ConAgua.Arena.Store
import all ConAgua.Arena.StrLit
import all ConAgua.Arena.StripTele
import all ConAgua.Arena.StubInd
import all ConAgua.Arena.StubNames
import all ConAgua.Arena.TeleLift
import all ConAgua.Arena.Walk
import all ConAgua.Arena.WalkLeaves
import all ConAgua.Arena.WalkLift
import all ConAgua.Arena.WalkScope
import all ConAgua.Arena.WhnfCore
import all ConAgua.Arena.WhnfCoreApp
import all ConAgua.Arena.WhnfDelta
import all ConAgua.Arena.WhnfEntry
import all ConAgua.Arena.WhnfIota
import all ConAgua.Arena.WhnfIotaRec
import all ConAgua.Arena.WhnfM2C
import all ConAgua.Arena.WhnfProj
import all ConAgua.Arena.WhnfSpineArgs
import all ConAgua.Arena.WhnfSpineRefine
import all ConAgua.Arena.ZeroStore
import all ConAgua.Checker.Entry
import all ConAgua.Checker.Hoist
import all ConAgua.Checker.Prelude
import all ConAgua.Checker.Presize
import all ConAgua.Front.Apply
import all ConAgua.Front.ApplyDecl
import all ConAgua.Front.ApplyExpr
import all ConAgua.Front.Driver
import all ConAgua.Front.Fields
import all ConAgua.Front.FieldsDecl
import all ConAgua.Front.IdTable
import all ConAgua.Front.IndApply
import all ConAgua.Front.IndFields
import all ConAgua.Front.Line
import all ConAgua.Front.LineRec
import all ConAgua.Front.NatDec
import all ConAgua.Front.Unescape
import all ConAgua.L.Examples
import all ConAgua.Rom.CIRead
import all ConAgua.Rom.PinRead
import all ConAgua.Rom.PinReadSpec
import all ConAgua.Scan.Key
import all ConAgua.Scan.Leaves
import all ConAgua.Scan.Line
import all ConAgua.Scan.Lit
import all ConAgua.Scan.Member
import all ConAgua.Scan.Records
import all ConAgua.Scan.Str
import all ConAgua.Scan.Utf8
import all ConAgua.Scan.Values

@[expose] public section

/-!
# The inductive records' path has a step's write set in the checker's program (lane `loopt3`)

`StepIn checkerProg indFns` (`Arena/CheckerT.lean`'s `LoopCallees.indIn`): the call closure of
`and_pin_ok`, `ind_block_to_erec`, `check_ind_decl` and `check_decl_defn` (1252 functions) writes
only a step's write set (`stepA`, `stepC`). The call-closed superset is `loopFns` (the loop's
closure, `Arena/LoopFns.lean`, generated) without the functions that reach a write of the pending
list, the promotion memos or the declaration index (`loopStepOut`: phase A's fold and its step,
phase B, the pending list's and the promotion's functions). Decided by per-chunk kernel checks as
`LoopDecl.lean`; if `loopFns` gains a function that reaches such a write, the check fails: add it
to `loopStepOut`.
-/

namespace L.Checker

open L.Arena L.Compiler

/-- The functions of `loopFns` that reach a store outside a step's write set (by `checkerProg`'s
call graph): the fold and its step, the pending list, the promotion. -/
def loopStepOut : List FnName :=
  ["caps_parts", "install_decl_step", "install_fold_go", "install_fold_next", "install_step",
   "is_none", "is_some", "pci_ctor", "pci_defn", "pci_ind", "pci_plain",
   "pci_rec", "pe_app", "pe_arm", "pe_at", "pe_clear", "pe_const", "pe_forall", "pe_lam",
   "pe_let", "pe_proj", "pe_put", "pend_push", "pl_arm", "pl_at", "pl_clear", "pl_put", "pls_arm",
   "pls_clear", "pls_put", "pn_arm", "pn_at", "pn_clear", "pn_put", "proj_a", "proj_b",
   "promote_caps", "promote_ci", "promote_ci_list", "promote_clear", "promote_cv", "promote_e",
   "promote_e_list", "promote_fire", "promote_l", "promote_l_list", "promote_l_pool",
   "promote_ls", "promote_n", "promote_n_list", "promote_new", "promote_new_consts",
   "promote_new_tables", "promote_proj_table", "promote_proj_tables",
   "promote_rule", "promote_rules", "promote_slice", "promote_vg", "ps_at"]

/-- The loop's functions with a step's write set: `loopFns` but `loopStepOut` (compared by name
codes, so the kernel compares no `String`s). -/
def loopStepFns : List FnName :=
  let out := loopStepOut.map nameCode
  loopFns.filter fun f => !out.contains (nameCode f)

/-- `loopStepFns` as a tree of name codes. -/
names_tree loopStepTree : loopStepFns

/-- Every function of the checker passes the step's per-function check on `loopStepFns`. -/
prog_all checkerProg_loopStepChk : checkerProg (wsChk CTL stepPa stepPc loopStepTree)

theorem checkerProg_loopStepClosed : closedA checkerProg stepA stepC loopStepFns = true :=
  closedW_of_all loopStepTree.eq stepPa_mem stepPc_mem checkerProg_loopStepChk

theorem indFns_sub : ∀ f ∈ indFns, f ∈ loopStepFns := by
  have h : indFns.all (fun f => (loopStepTree.find (nameCode f)).isSome) = true := by
    decide +kernel
  intro f hf
  have := List.all_eq_true.mp h f hf
  rw [namesTree_spec loopStepTree.eq] at this
  exact of_decide_eq_true this

/-- **The inductive records' path and the definition arm have a step's write set.** -/
theorem checkerProg_indIn : StepIn checkerProg indFns :=
  ⟨_, indFns_sub, checkerProg_loopStepClosed⟩

end L.Checker
