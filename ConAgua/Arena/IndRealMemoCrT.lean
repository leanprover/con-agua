module

import ConAgua.Arena.IndRealMemoCr
public import ConAgua.Arena.StageTLift
import ConAgua.Arena.DeclNatCv
import ConAgua.Arena.FVarRangeRefine
import ConAgua.Arena.IndReal
import ConAgua.Arena.TwinStep
public import ConAgua.Arena.ConstsResolveFRefine2
public import ConAgua.Arena.IndRealCrF

@[expose] public section

/-!
# `consts_resolve_ffast` under `StageT` (lane `indproofs4`, helper `wkt`)

`IndRealMemoCr.lean`'s `crfF_ok` lifted to `StageT`. The walk reads the twin state only (its run
leaves the state as it was: `constsResolveFFast_keepsSt`, lane `tails`' proof with the state kept),
and the L side writes its memo table only (`crfF_frame`: array 155, `CTL[158]`, `CTL[159]`), away
from the core's memos and the pins, so `TwinOK` and the pin flag are framed. The walk's own memo
(`CrMemo`, `AbsOK`'s part) is not in `StageT` and is threaded: the caller supplies it, it holds
after. Replaced the stub contract `IndStubsT.constsResolveFFastT_spec` (deleted): the callers' models call `crfF`
and carry `CrMemo` (see the note there).
-/


open ConRon.Arena

namespace L.Stubs

open L.Arena L.Ind

section rel
variable {p : Prog} (hp : CrfProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
include hp

/-- **`consts_resolve_ffast` refines `constsResolveFFast` and keeps the twin state**: lane `tails`'
`constsResolveFFast_ref` with the state after the run named (it is the state before). -/
theorem constsResolveFFast_keepsSt (e : Word) (he : H e) (a₀ : AState) :
    CallRef p "consts_resolve_ffast" [vis, e] (fun m a => StageR vis fe m a ∧ CrOK m ∧ a = a₀)
      (constsResolveFFast fe (decI e))
      (fun m m' a r x => KeepPost vis fe decW0B m m' a r x ∧ CrOK m' ∧ a = a₀) := by
  sorry

end rel

end L.Stubs

namespace L.Ind

open L.Arena

/-! ## `CrMemo` is lane `tails`' `CrOK` -/

theorem CrMemo.crOK {m : Mem} (h : CrMemo m) : L.Stubs.CrOK m := h

theorem _root_.L.Stubs.CrOK.crMemo {m : Mem} (h : L.Stubs.CrOK m) : CrMemo m := h

/-- `AbsOK` holds `CrMemo`. -/
theorem AbsOK.crMemo {m : Mem} (h : AbsOK m) : CrMemo m := h.cr

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **A program's call of `consts_resolve_ffast` is the model's** (`realCall p`'s reading). -/
theorem crfF_of_callW {p : Prog} (hp : CrfF p) {n : Nat} {args r : List Word} {m m' : Mem}
    (h : callW p n "consts_resolve_ffast" args m = some (r, m')) :
    crfF m args = some (r, m') :=
  callF_of_callW (by rw [← callW_agree crfP_closed (hp.agree crfPFns) n (by decide)]; exact h)
-/

/- ronsync2 stage 2: commented out (statement at the old twin/L)
/-- **`consts_resolve_ffast` under `StageT`**, the walk's memo threaded (`crfF_ok` lifted). -/
theorem crfF_okT (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (e : Word) (he : H e) :
    RelW crfF [vis, e] (fun m a => StageT dn vis fe m a ∧ CrMemo m) (constsResolveFFast fe (decI e))
      (fun m m' a r x => KeepPostT dn vis fe decW0B m m' a r x ∧ CrMemo m') := by
  intro m m' a r h ⟨hT, hCr⟩
  have hf := crfF_frame h
  obtain ⟨x, a', hrun, ⟨hS', hg, hd⟩, hCr', ha'⟩ := relW_callF (P := crfP)
    (L.Stubs.constsResolveFFast_keepsSt crfP_prog (dn := dn) (vis := vis) (fe := fe) e he a).refAM
    m m' a r h ⟨hT.stage, hCr, rfl⟩
  subst ha'
  exact ⟨x, _, hrun, ⟨⟨hS', hT.twin.frame hf (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide), by rw [pinW_frame hf (by decide)]; exact hT.flag⟩, hg, hd⟩, hCr'⟩
-/

end L.Ind
