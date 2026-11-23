module

public import ConAgua.Checker.Prog
public import ConAgua.Checker.ProgTree
public import ConAgua.Checker.PreludeSim
public import ConAgua.Compiler.WriteSetSplit
public import ConAgua.Compiler.WFSplit
public import ConAgua.Arena.LevelIntern
public import ConAgua.Arena.LevelSubstLP
meta import ConAgua.Checker.Prog
meta import ConAgua.Checker.ProgTree
meta import ConAgua.Checker.PreludeSim
meta import ConAgua.Compiler.WriteSetSplit
meta import ConAgua.Compiler.WFSplit
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
import all ConAgua.Arena.BasisL
import all ConAgua.Arena.IndDeclConsts
import all ConAgua.Arena.IndStream
import all ConAgua.Arena.Prelude
import all ConAgua.Arena.RomCI
import all ConAgua.Rom.PinReadSpec
import all ConAgua.Scan.Line
import all ConAgua.Arena.NatSized
import ConAgua.Compiler.Main

@[expose] public section

/-!
# The checker program has the shape of the prelude simulation (lane `pipeline`)

`checkerProg_preSim : PreSimProg checkerProg preTree (fun f => decide (f ∈ preShared))`, so
`preSim`/`preSim_triple` (`Checker/PreludeSim.lean`) apply to every copy `pre_f` of
`checkerProg`. No kernel check compares `String`s in bulk or sees the whole program:

* the copied and the shared names as literal search trees of name codes (`names_tree`), and
  `preTree`'s membership through `nameTree_find`;
* the bodies by one Bool check per function (`simChk`, `prog_all`, chunks of 32): copied bodies
  store no byte into array `0` and call copied or shared names, shared bodies do not touch array
  `0` and call shared names; numbers compared with GMP, no lookup in the program;
* the copies' bindings by `rfl` on `checkerProg[i]?` at the binding's index, found by evaluation
  (`copy_facts`, one small kernel check per copied name), and the lookups from the program's
  names being distinct (`checkerProg_wf.tree_eq`, `ProgTree.lean`).
-/

namespace L.Checker

open L L.Compiler

/-! ## Name trees -/

theorem NTree.find_of_insert_none {k v : Nat} : ∀ {t : NTree}, t.insert k v = none →
    (t.find k).isSome = true
  | .leaf, h => by simp [NTree.insert] at h
  | .node l k₀ v₀ r, h => by
    simp only [NTree.insert] at h
    by_cases h1 : k < k₀
    · simp only [h1, ite_true, Option.map_eq_none_iff] at h
      simp only [NTree.find, h1, ite_true]
      exact find_of_insert_none h
    · by_cases h3 : k = k₀
      · simp [NTree.find, h3]
      · simp only [h1, h3, ite_false, Option.map_eq_none_iff] at h
        simp only [NTree.find, h1, h3, ite_false]
        exact find_of_insert_none h

theorem nameTree_foldl (g : String) : ∀ (fs : List String) (t : NTree),
    ((fs.foldl (fun t f => (t.insert (nameCode f) 0).getD t) t).find (nameCode g)).isSome =
      ((t.find (nameCode g)).isSome || decide (g ∈ fs))
  | [], t => by simp
  | f :: fs, t => by
    rw [List.foldl_cons, nameTree_foldl g fs]
    have key : ((((t.insert (nameCode f) 0).getD t).find (nameCode g)).isSome) =
        ((t.find (nameCode g)).isSome || decide (g = f)) := by
      cases hi : t.insert (nameCode f) 0 with
      | none =>
        have hf := NTree.find_of_insert_none hi
        by_cases hg : g = f
        · subst hg; simp [hf]
        · simp [hg]
      | some t' =>
        obtain ⟨-, hf⟩ := NTree.find_insert hi
        simp only [Option.getD_some, hf]
        by_cases hg : g = f
        · subst hg; simp
        · have : nameCode g ≠ nameCode f := fun h => hg (nameCode_inj h)
          simp [this, hg]
    rw [key]
    by_cases h1 : g = f <;> by_cases h2 : g ∈ fs <;> simp [h1, h2]

theorem nameTree_find (fs : List String) (g : String) :
    ((nameTree fs).find (nameCode g)).isSome = decide (g ∈ fs) := by
  unfold nameTree
  rw [nameTree_foldl]
  simp [NTree.find]

theorem isCopied_preTree (f : FnName) : isCopied preTree f = decide (f ∈ preNames) :=
  nameTree_find preNames f

/-- `f`'s name code is in `t`. -/
def inT (t : NTree) (f : FnName) : Bool := (t.find (nameCode f)).isSome

/-- The copied functions' names, as a literal tree. -/
names_tree preCT : preNames

/-- The shared functions' names, as a literal tree. -/
names_tree preST : preShared

theorem inT_preCT (f : FnName) : inT preCT f = isCopied preTree f := by
  rw [inT, namesTree_spec preCT.eq, isCopied_preTree]

theorem inT_preST (f : FnName) : inT preST f = decide (f ∈ preShared) := by
  rw [inT, namesTree_spec preST.eq]

/-! ## The bodies, one function at a time -/

/-- One function's check: a copied body stores no byte into array `0` and calls copied or
shared functions; a shared function is not copied, does not touch array `0` and calls shared
functions. -/
def simChk (x : FnName × FunDecl) : Bool :=
  (!inT preCT x.1 ||
    (x.2.body.noSt8In && x.2.body.callsIn (fun g => inT preCT g || inT preST g))) &&
  (!inT preST x.1 || (!inT preCT x.1 && x.2.body.noIn && x.2.body.callsIn (inT preST)))

/-- Every function of `checkerProg` passes `simChk`. -/
prog_all checkerProg_simChk : checkerProg simChk

/-! ## The copies' bindings -/

/-- `f` and its copy `pre_f` are bound, the copy to `preFn preTree` of `f`'s declaration. -/
def CopyAt (f : FnName) : Prop :=
  ∃ fd, (f, fd) ∈ checkerProg ∧ ("pre_" ++ f, preFn preTree fd) ∈ checkerProg

theorem copyAt_of {f : FnName} {fd : FunDecl} {i j : Nat} (hi : checkerProg[i]? = some (f, fd))
    (hj : checkerProg[j]? = some ("pre_" ++ f, preFn preTree fd)) : CopyAt f :=
  ⟨fd, List.mem_of_getElem? hi, List.mem_of_getElem? hj⟩

open Lean Elab Command Meta in
/-- `copy_facts h` declares `h : ∀ f ∈ preNames, CopyAt f`. For each copied name `f` it finds
(by evaluation here) the indices `i` of `f` and `j` of `pre_f` in `checkerProg`, and declares
`h.n<k> : CopyAt f` by `copyAt_of` with `rfl` for `checkerProg[i]?` and `checkerProg[j]?` (one
small kernel check per name; no `String` comparison against the program's names). The main
theorem chains them along `preNames` (no evaluation). -/
elab "copy_facts " n:ident : command =>
  liftTermElabM <| withTheReader Core.Context
      (fun c => { c with maxRecDepth := max c.maxRecDepth 100000 }) do
    let name := (← getCurrNamespace) ++ n.getId
    let elems ← listElems (mkConst ``checkerProg)
    let names ← listElems (mkConst ``preNames)
    let elemTy := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``String) (mkConst ``FunDecl)
    let key (e : Lean.Expr) : Option String :=
      match e.appFn!.appArg! with
      | .lit (.strVal s) => some s
      | _ => none
    let P := mkConst ``CopyAt
    let mut hs : Array Lean.Expr := #[]
    for nm in names do
      let .lit (.strVal f) := nm | throwError "copy_facts: not a string literal: {nm}"
      let some i := elems.findIdx? (key · == some f) | throwError "copy_facts: {f} is not bound"
      let some j := elems.findIdx? (key · == some ("pre_" ++ f))
        | throwError "copy_facts: pre_{f} is not bound"
      let refl (e : Lean.Expr) : MetaM Lean.Expr :=
        mkEqRefl (mkApp2 (mkConst ``Option.some [0]) elemTy e)
      let pf := mkAppN (mkConst ``copyAt_of)
        #[nm, elems[i]!.appArg!, mkNatLit i, mkNatLit j, ← refl elems[i]!, ← refl elems[j]!]
      let hN := name ++ Name.mkSimple s!"n{hs.size}"
      addDecl (thm hN (mkApp P nm) pf [])
      hs := hs.push (mkConst hN)
    let strTy := mkConst ``String
    let mut chain := mkApp2 (mkConst ``forall_mem_nil_of) strTy P
    let mut tl := mkApp (mkConst ``List.nil [0]) strTy
    for e in (List.range names.size).reverse do
      chain := mkAppN (mkConst ``forall_mem_cons_of) #[strTy, P, names[e]!, tl, hs[e]!, chain]
      tl := mkApp3 (mkConst ``List.cons [0]) strTy names[e]! tl
    let ty ← withLocalDeclD `f strTy fun x => do
      mkForallFVars #[x] (← mkArrow (← mkAppM ``Membership.mem #[mkConst ``preNames, x]) (mkApp P x))
    addDecl (thm name ty chain [])

-- Every copied name and its copy are bound as `preFn` says.
copy_facts copyAt_all

/-! ## The shape -/

theorem lookup_of_mem {p : Prog} (hnd : (p.map (·.1)).Nodup) {f : FnName} {fd : FunDecl}
    (hm : (f, fd) ∈ p) : p.lookup f = some fd := by
  induction p with
  | nil => cases hm
  | cons x p ih =>
    obtain ⟨g, gd⟩ := x
    simp only [List.map_cons, List.nodup_cons] at hnd
    rw [List.lookup_cons]
    rcases List.mem_cons.mp hm with h | h
    · cases h; simp
    · have hfg : f ≠ g := fun e => hnd.1 (e ▸ List.mem_map.mpr ⟨_, h, rfl⟩)
      have : (f == g) = false := by simpa using hfg
      rw [this]
      exact ih hnd.2 h

theorem checkerProg_nodup : (checkerProg.map (·.1)).Nodup :=
  (progTree_spec checkerProg_wf.tree_eq).1

/-- **The checker program has the simulation's shape**, the shared functions as a name tree. -/
theorem checkerProg_preSimT : PreSimProg checkerProg preTree (inT preST) where
  defined f hf := by
    rw [isCopied_preTree, decide_eq_true_eq] at hf
    obtain ⟨fd, hm, -⟩ := copyAt_all f hf
    rw [lookup_of_mem checkerProg_nodup hm]; rfl
  copy f fd hf hl := by
    have hc := checkerProg_simChk _ (L.Compiler.mem_of_lookup hl)
    simp only [simChk, inT_preCT, hf, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hc
    rw [isCopied_preTree, decide_eq_true_eq] at hf
    obtain ⟨fd', hm, hm'⟩ := copyAt_all f hf
    rw [lookup_of_mem checkerProg_nodup hm] at hl
    cases hl
    exact ⟨lookup_of_mem checkerProg_nodup hm', hc.1.1, hc.1.2⟩
  shared f fd hs hl := by
    have hc := checkerProg_simChk _ (L.Compiler.mem_of_lookup hl)
    simp only [simChk, hs, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true',
      inT_preCT] at hc
    exact ⟨hc.2.1.1, hc.2.1.2, hc.2.2⟩

/-- **The checker program has the simulation's shape.** -/
theorem checkerProg_preSim : PreSimProg checkerProg preTree (fun f => decide (f ∈ preShared)) := by
  have h : (fun f => decide (f ∈ preShared)) = inT preST := funext fun f => (inT_preST f).symm
  rw [h]; exact checkerProg_preSimT

end L.Checker
