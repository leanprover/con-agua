import ConAgua.Arena.IndRealCrF
import ConAgua.Arena.ConstsResolveFRefine2

/-!
# `consts_resolve_ffast` under the stage relation and the walk memos (lane `indproofs4`, helper `memo`)

Lane `tails`' `constsResolveFFast_refines` (`ConstsResolveFRefine2.lean`) at the model's program
`crfP` (`IndRealCrF.lean`): under `StageR ∧ CrOK` (`CrOK`: the memo table `CRM` related to some
memo, `AbsOK`'s part `CrMemo`) a returning run is the twin's `constsResolveFFast`, with
`KeepPost ∧ CrOK` after; the other walk memos are framed (`crfF_frame`: array 155, `CTL[158]`,
`CTL[159]` only).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem crfP_prog : L.Stubs.CrfProg crfP := by
  constructor <;> exact (ProgHas.refl crfP).get _

/-- **`consts_resolve_ffast` refines `constsResolveFFast` under the stage relation and the walk
memos** (replaces `IndStubs.constsResolveFFast_spec` at the inductive stage's uses); the memos are
well formed after. -/
theorem crfF_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (e : Word) (he : H e) :
    RelW crfF [vis, e] (fun m a => StageR dn vis fe m a ∧ AbsOK m) (constsResolveFFast fe (decI e))
      (fun m m' a r x => KeepPost dn vis fe decW0B m m' a r x ∧ AbsOK m') := by
  intro m m' a r h ⟨hS, hAb, hI1, hCr, hIl, hWk⟩
  have hfr := crfF_frame h
  obtain ⟨x, a', hrun, hK, hCr'⟩ := relW_callF (P := crfP)
    (L.Stubs.constsResolveFFast_refines crfP_prog (dn := dn) (vis := vis) (fe := fe) e he) m m' a r h
    ⟨hS, hCr⟩
  exact ⟨x, a', hrun, hK, hAb.frame hfr (by decide) (by decide), hI1.frame hfr (by decide) (by decide),
    hCr', hIl.frame hfr (by decide) (by decide),
    hWk.frame hfr (by decide) (by decide) (by decide) (by decide) (by decide)⟩

end L.Ind
