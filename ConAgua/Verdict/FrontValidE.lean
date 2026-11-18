module

public import ConAgua.Front.DeclsPre
public import ConAgua.Front.FrontRun
public import ConAgua.Checker.NoVerdictClosed
public import ConAgua.L.ModelGen
meta import ConAgua.Front.DeclsPre
meta import ConAgua.Front.FrontRun
meta import ConAgua.Checker.NoVerdictClosed
meta import ConAgua.L.ModelGen
import all ConAgua.Arena.AppStore
import all ConAgua.Arena.BVarStore
import all ConAgua.Arena.ConsLib
import all ConAgua.Arena.ConstStore
import all ConAgua.Arena.ExprMk
import all ConAgua.Arena.ForallStore
import all ConAgua.Arena.ImaxStore
import all ConAgua.Arena.IndIface
import all ConAgua.Arena.IndPos
import all ConAgua.Arena.LamStore
import all ConAgua.Arena.LetStore
import all ConAgua.Arena.LevelEquiv
import all ConAgua.Arena.LevelHeap
import all ConAgua.Arena.LevelLeq
import all ConAgua.Arena.LevelSimp
import all ConAgua.Arena.LevelStore
import all ConAgua.Arena.LevelSubst
import all ConAgua.Arena.LsStore
import all ConAgua.Arena.MaxStore
import all ConAgua.Arena.MemoLib
import all ConAgua.Arena.NAnonStore
import all ConAgua.Arena.NNumStore
import all ConAgua.Arena.NStrStore
import all ConAgua.Arena.ParamStore
import all ConAgua.Arena.ProjStore
import all ConAgua.Arena.SortStore
import all ConAgua.Arena.Store
import all ConAgua.Arena.ZeroStore
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
import all ConAgua.Arena.NatAdd
import all ConAgua.Arena.NatLeaf
import all ConAgua.Arena.NatMul
import all ConAgua.Front.Unescape
import all ConAgua.L.Examples
import all ConAgua.Scan.Key
import all ConAgua.Scan.Leaves
import all ConAgua.Scan.Line
import all ConAgua.Scan.Lit
import all ConAgua.Scan.Member
import all ConAgua.Scan.Records
import all ConAgua.Scan.Str
import all ConAgua.Scan.Utf8
import all ConAgua.Scan.Values
import ConAgua.Arena.TwinStep

@[expose] public section
/-!
# The front's error arms' assumptions at the driver's program

`apply_ind`'s error arms (`applyInd_ref`, `FrontPreOK2.lean`) assume `ApplyIndG`: the twin facts
`XV` (`validate_ref`'s), which every state of the driver has (`xOfTwin`), and the no-verdict
closure of `frontAllProg` (`frontAllProg_nv`).
-/

open ConRon.Arena ConRon.Arena.Frontend L.Arena
open ConLeche.Frontend (IndCtorRec IndTypeRec IndRecRec)
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Front.Ind

/-! ## The twin facts the messages need -/

theorem readName_run (a : AState) (h : NIdx) (x : ConLeche.Name) (hd : denoteN a.store.ns h = some x) :
    (readName h).run a = .ok (x, a) := by
  simp [readName, StateT.run_bind, StateT.run_get, hd]; rfl

/-- The handles of the parse state's name table read back (`StateDRel`). -/
theorem names_read_of_twin {a : AState} {st : StateD} (hT : L.Front.TwinOK a st) :
    ∀ i h, st.names.get? i = some h → ∃ x, (readName h).run a = .ok (x, a) := by
  intro i h hg
  obtain ⟨-, -, -, -, sc, hrel⟩ := hT
  have := hrel.names i
  rw [hg] at this
  cases hs : sc.names.get? i with
  | none => rw [hs] at this; exact this.elim
  | some n =>
    rw [hs] at this
    exact ⟨n, readName_run a h n this⟩

theorem namesReadR_of_twin {a : AState} {st : StateD} (hT : L.Front.TwinOK a st) (D : Array IDeclaration) :
    NamesReadR (st.pre D) a := by
  intro i h hr
  unfold StateD.name at hr
  cases hg : (st.pre D).names.get? i with
  | none => rw [hg] at hr; cases hr
  | some h' =>
    rw [hg] at hr; cases hr
    exact names_read_of_twin hT i h hg

theorem viewReadR_of_ok {a : AState} (hok : ConRon.Bridge.StateOK a) : ViewReadR a := by
  intro h T s hv
  have hv' : a.store.ns.view h = some (.str T s) := by
    unfold viewN at hv
    cases hw : a.store.ns.view h with
    | none => simp [StateT.run_bind, StateT.run_get, hw] at hv; cases hv
    | some w => simp [StateT.run_bind, StateT.run_get, hw] at hv; cases hv; rfl
  obtain ⟨rk, hrk⟩ := ConRon.Bridge.Frontend.nsWF_of_StateOK hok
  have hc := hrk.childOK h _ hv' T (by simp [NNodeView.children])
  obtain ⟨x, hx⟩ := L.Arena.denoteN_of_viewW hrk _ T (Nat.lt_succ_self _) hc.1
  exact ⟨x, readName_run a T x hx⟩

theorem xOfTwin : ∀ (D : Array IDeclaration) (a : AState) (st : StateD), L.Front.TwinOK a st →
    XV (st.pre D) a := fun D _a _st hT =>
  ⟨fun i h hg => names_read_of_twin hT i h hg, namesReadR_of_twin hT D, viewReadR_of_ok hT.1⟩

prog_all frontAllProg_nvChk : frontAllProg (L.nvChk L.Checker.nvTree)

/-- **The functions outside the verdict closure claim nothing in `frontAllProg`** either (the
unified models' lifted callees). -/
theorem frontAllProg_nv : closedNV frontAllProg L.Checker.nvFns = true :=
  closedNV_of_all L.Checker.nvTree.eq frontAllProg_nvChk

end L.Front.Ind
