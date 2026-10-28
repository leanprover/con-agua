import ConAgua.Front.IndApplyRefine9
import ConAgua.Verdict.FrontRunE
import ConAgua.L.ModelGen
/-!
# `validate_ind_d`'s error half at the driver's program

`validate_ref`'s error half (`IndApplyRefine9.lean`) read from a failing run: `ValidateClaim`
(`FrontRunE.lean`) at `frontAllProg`, at the twin facts `XV` every state of the driver has
(`xOfTwin`).
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

/-- **`validate_ind_d`'s claim at `frontAllProg`** (`ValidateClaim`, at the twin facts `XV`). -/
theorem validateClaim_frontAll : ValidateClaim frontAllProg XV :=
  fun _ n m _ _ to tn co cn ro rn _ _ _ _ hR hD hok hT hF hIFR hX hc =>
    RefC.run_err (validate_specE frontAllProg frontAllProg_indApply n ⟨m, Locals.init []⟩ to tn co cn ro rn)
      (fun _ h0 h => absurd h0 h) frontAllProg_nv hX (validate_ref hR hD hok hT hF hIFR frontAllProg n) hc

end L.Front.Ind
