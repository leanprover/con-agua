import ConAgua.Arena.IndRealMemoCr
import ConAgua.Arena.StageTLift
import ConAgua.Arena.DeclNatCv

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
    CallRef p "consts_resolve_ffast" [vis, e] (fun m a => StageR dn vis fe m a ∧ CrOK m ∧ a = a₀)
      (constsResolveFFast fe (decI e))
      (fun m m' a r x => KeepPost dn vis fe decW0B m m' a r x ∧ CrOK m' ∧ a = a₀) := by
  refine CallRef.of_succ fun k m a r m' ⟨hS, ⟨memo0, hM0⟩, ha⟩ hc => ?_
  have hW := callW_model (M := fun mm => crffW p k mm vis e) (crff_spec p hp k · vis e) hc
  unfold crffW at hW
  obtain ⟨rc, mc, h1, hW⟩ := ntBW_some hW
  obtain ⟨s', hmc, -, hw, hclr⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (memoClearG_spec crSch p "crm_clear" hp.clear k _) h1
  simp only at hw hclr
  subst hmc
  rw [hclr] at hW
  obtain ⟨rg, mg, h2, hW⟩ := ntBW_some hW
  rw [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨rfl, rfl⟩ := hW
  have hfc : CrFrame m (mclearG crSch m) :=
    (mclearG_frame crSch m).mono (by simp) (by simp)
  have hSc := (StageR.crf hS hfc).1
  have hMc : CrR (mclearG crSch m) ∅ := memoRV_clear crSch crSch_wf bmKey CrV m memo0 hM0 hw
  obtain ⟨b, memo', hr, hM', hF, hres⟩ := crf_refines hp k _ _ a ∅ _ e rg hSc hMc he h2
  rw [coreWalkFuel_toNat] at hr
  obtain ⟨hS', hG⟩ := StageR.crf hS (hfc.trans hF)
  refine ⟨b, a, ?_, ⟨⟨hS', hG, ?_, ?_⟩, ⟨memo', hM'⟩, ha⟩⟩
  · simp only [constsResolveFFast, StateT.run_bind, ← decE_eq, hr, except_ok_bind]; rfl
  · simp only [List.headD_cons, hres]; cases b <;> rfl
  · simp only [List.headD_cons, hres]; cases b <;> decide

end rel

end L.Stubs

namespace L.Ind

open L.Arena

/-! ## `CrMemo` is lane `tails`' `CrOK` -/

theorem CrMemo.crOK {m : Mem} (h : CrMemo m) : L.Stubs.CrOK m := h

theorem _root_.L.Stubs.CrOK.crMemo {m : Mem} (h : L.Stubs.CrOK m) : CrMemo m := h

/-- `AbsOK` holds `CrMemo`. -/
theorem AbsOK.crMemo {m : Mem} (h : AbsOK m) : CrMemo m := h.2.2.1

/-- **A program's call of `consts_resolve_ffast` is the model's** (`realCall p`'s reading). -/
theorem crfF_of_callW {p : Prog} (hp : CrfF p) {n : Nat} {args r : List Word} {m m' : Mem}
    (h : callW p n "consts_resolve_ffast" args m = some (r, m')) :
    crfF m args = some (r, m') :=
  callF_of_callW (by rw [← callW_agree crfP_closed (hp.agree crfPFns) n (by decide)]; exact h)

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

end L.Ind
