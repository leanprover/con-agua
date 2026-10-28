import ConAgua.Front.FrontPreOK
import ConAgua.Checker.NoVerdictClosed
import ConAgua.Final.TwinVerdict
import ConAgua.L.ModelGen
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
  obtain ⟨x, hx⟩ := ConRon.Bridge.denoteN_of_view ⟨rk, ConRon.Arena.NWFAt'.of_wf hrk⟩ hc.1
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
