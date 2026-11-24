module

public import ConAgua.Checker.FrontProgAgree
public import ConAgua.Arena.LevelIntern
public import ConAgua.Arena.LevelSubstLP
meta import ConAgua.Checker.FrontProgAgree
meta import ConAgua.Arena.LevelIntern
meta import ConAgua.Arena.LevelSubstLP
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
import all ConAgua.Arena.IotaFrame
import all ConAgua.Arena.IotaRel
import all ConAgua.Arena.JustifyIface
import all ConAgua.Arena.Needs
import all ConAgua.Arena.Justify
import all ConAgua.Arena.JustifySide
import all ConAgua.Checker.CompareEntry
import all ConAgua.Arena.FreezeCmp
import all ConAgua.Checker.CmpSeqEntry
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
import all ConAgua.Arena.NatLeaf
import all ConAgua.Arena.NatArms
import all ConAgua.Arena.NatBits
import all ConAgua.Arena.NatCmp
import all ConAgua.Arena.NatDiv
import all ConAgua.Arena.NatDivKstep
import all ConAgua.Arena.NatDivSubmul
import all ConAgua.Arena.NatDivWord
import all ConAgua.Arena.NatGcd
import all ConAgua.Arena.NatMul
import all ConAgua.Arena.NatPow
import all ConAgua.Arena.NatShl
import all ConAgua.Arena.NatShr
import all ConAgua.Arena.NatSub
import all ConAgua.Arena.ParamStore
import all ConAgua.Arena.Pins
import all ConAgua.Arena.ProjStore
import all ConAgua.Arena.PropRead
import all ConAgua.Arena.RecCheck
import all ConAgua.Arena.RecClass
import all ConAgua.Arena.RecGen
import all ConAgua.Arena.Refine
import all ConAgua.Arena.Rom
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
import all ConAgua.Scan.Key
import all ConAgua.Scan.Leaves
import all ConAgua.Scan.Lit
import all ConAgua.Scan.Member
import all ConAgua.Scan.Records
import all ConAgua.Scan.Str
import all ConAgua.Scan.Utf8
import all ConAgua.Scan.Values
import all ConAgua.Arena.NatSized

@[expose] public section

/-!
# The frontend's refinement at the checker's program (lane `pipeline`)

`checkerProg_front_run`: `front_run` runs in `checkerProg` as in `L.Front.frontAllProg`, so its
refinement there (`frontRun_ref`) holds at the checker's program (`frontRunOK_checker`,
`frontRun_checker_chunks`, `FrontRunRef.lean`).

`checkerProg` does not satisfy `frontRun_ref`'s lookup bundles: it binds no `validate`,
`str_put` or `apply_ind_line` (nothing reachable from `check` calls them; `FrontLookups`,
`IndLineLookups` and the single `str_put` lookup name them). So instead of instantiating the
parametric theorem, the run itself is transferred: the two programs agree on the functions
reachable from `front_run` (`checkerProg_frontAgree`, `FrontProgAgree.lean`), that set is
call-closed in `checkerProg` (`checkerProg_frontClosed`, one kernel check per chunk of functions,
`prog_all`), and the interpreter on a call-closed set reads only its lookups (`exec_agree`), so
`front_run` runs identically in both (`checkerProg_front_run`).
-/

namespace L.Checker

open L L.Compiler

/-! `checkerProg_noSt8`: `Checker/RomProg0.lean`. -/

/-! ## Runs read only the lookups of a call-closed set -/

/-- Every call of the statement is to a function `P` holds of. -/
def _root_.L.Stmt.callsP (P : FnName → Bool) : Stmt → Bool
  | .seq s t => s.callsP P && t.callsP P
  | .ite _ s t => s.callsP P && t.callsP P
  | .while _ s => s.callsP P
  | .call _ f _ => P f
  | _ => true

section agree
variable {p q : Prog} {P : FnName → Bool}
  (hpq : ∀ f, P f = true → p.lookup f = q.lookup f)
  (hcl : ∀ f fd, P f = true → p.lookup f = some fd → fd.body.callsP P = true)
include hpq hcl

theorem invoke_agree {k k' : Stmt → M Sig} (hk : ∀ s, s.callsP P = true → k s = k' s)
    {f : FnName} (hf : P f = true) : invoke p k f = invoke q k' f := by
  funext vs
  unfold invoke lookupFn
  rw [← hpq f hf]
  cases h : p.lookup f with
  | none => rfl
  | some fd =>
    have e : callFn k fd vs = callFn k' fd vs := by
      unfold callFn; rw [hk fd.body (hcl f fd hf h)]
    simp only [pure_bind, e]

theorem step_agree {k k' : Stmt → M Sig} (hk : ∀ s, s.callsP P = true → k s = k' s) :
    ∀ s, s.callsP P = true → step p k s = step q k' s := by
  intro s hs
  induction s with
  | seq s t ihs iht =>
    simp only [Stmt.callsP, Bool.and_eq_true] at hs
    simp only [step]; rw [ihs hs.1, iht hs.2]
  | ite c s t ihs iht =>
    simp only [Stmt.callsP, Bool.and_eq_true] at hs
    simp only [step]; rw [ihs hs.1, iht hs.2]
  | «while» c s ih =>
    have hw := hs
    simp only [Stmt.callsP] at hs
    simp only [step]; rw [ih hs, hk _ hw]
  | «call» xs f args =>
    simp only [Stmt.callsP] at hs
    simp only [step]; rw [invoke_agree hpq hcl hk hs]
  | _ => rfl

theorem exec_agree (n : Nat) : ∀ s, s.callsP P = true → exec p n s = exec q n s := by
  induction n with
  | zero => intro s _; rfl
  | succ n ih => intro s hs; exact step_agree hpq hcl ih s hs

/-- **A call into a call-closed set runs the same in both programs.** -/
theorem invoke_exec_agree (n : Nat) {f : FnName} (hf : P f = true) :
    invoke p (exec p n) f = invoke q (exec q n) f :=
  invoke_agree hpq hcl (exec_agree hpq hcl n) hf

end agree

/-! ## `front_run` in `checkerProg` -/

/-- The functions reachable from `front_run`, as a tree of name codes. -/
names_tree frontTree : frontFns

/-- Membership in `frontFns`, by the tree. -/
def inFront (f : FnName) : Bool := (frontTree.find (nameCode f)).isSome

theorem inFront_iff (f : FnName) : inFront f = true ↔ f ∈ frontFns := by
  rw [inFront, namesTree_spec frontTree.eq f]; exact decide_eq_true_iff

/-- Every function of `frontFns` calls only into `frontFns`, per chunk of functions. -/
prog_all checkerProg_frontClosedAll : checkerProg (fun x => !inFront x.1 || x.2.body.callsP inFront)

theorem checkerProg_frontClosed (f : FnName) (fd : FunDecl) (hf : inFront f = true)
    (h : checkerProg.lookup f = some fd) : fd.body.callsP inFront = true := by
  obtain ⟨l₁, l₂, hp, -⟩ := List.lookup_eq_some_iff.mp h
  have hx := checkerProg_frontClosedAll (f, fd) (hp ▸ List.mem_append_right _ List.mem_cons_self)
  simpa [hf] using hx

/-- **`front_run` runs in `checkerProg` as in `frontAllProg`.** -/
theorem checkerProg_front_run (n : Nat) :
    invoke checkerProg (exec checkerProg n) "front_run" =
      invoke L.Front.frontAllProg (exec L.Front.frontAllProg n) "front_run" :=
  invoke_exec_agree (P := inFront)
    (fun f hf => checkerProg_frontAgree f ((inFront_iff f).1 hf))
    checkerProg_frontClosed n (by decide)

end L.Checker
