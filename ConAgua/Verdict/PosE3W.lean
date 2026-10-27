import ConAgua.Verdict.PosE
import ConAgua.Verdict.PosE3Cm
import ConAgua.Arena.IndPosSpec.P2sfW
import ConAgua.Checker.NoVerdictTree

/-!
# `nest_ctors_walk`'s error claim step (lane `verdicts-b`, helper `ia2`, fork `kn2b`)

`walkOKC_step`'s proof (`PosWalk.lean`) on the error model `nwE`: the fields' error is the block's
`FieldsOKE` at `n`; `whnf_walk_fuel` and `close_telescope` claim nothing.
-/


open ConRon.Arena
open ConRon.Bridge.Inductives (PStep dCtx dProg dState dCtx_ext dProg_ext dState_ext kindOf RPos)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- A twin run that fails whenever another (of another type, from another state) does. -/
theorem ErrClaim.of_run' {α β : Type} {T : AM α} {T' : AM β} {a a' : AState} {e : Err}
    (h' : ErrClaim T' a' e) (h : ∀ ce, T'.run a' = Except.error ce → T.run a = Except.error ce) :
    ErrClaim T a e := fun hk => by
  obtain ⟨ce, hce, hc⟩ := h' hk
  exact ⟨ce, h ce hce, hc⟩

section steps
variable {p : Prog} (L : NbLook p) (hnv : closedNV p _root_.L.Checker.nvFns = true)
  (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) {env : ConLeche.Env}

include L hnv in
theorem walkOKE_step (n : Nat) (ihE : NbOKE p dn vis fe env n) : WalkOKE p dn vis fe env (n + 1) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hFieldsE⟩ := ihE
  intro m a ctx root fu po pl hi nF crest ns c prog NS ctxP progP crestP nsP hC hW hcr hns hP hA
    hc hctx hprog hcrP hnsP hwc e he β K
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  replace he := triple_of_callE_err (nwE_spec p L.pwalk (n + 1) ⟨m, Locals.init []⟩ vis ctx root fu po pl hi nF
    crest ns) he (Err.code_ne_of_cls hk0)
  simp only at he
  have hS := hC.stage
  have hF : ∀ (fu' : Word) (m1 : Mem) (a1 : AState), StageC dn vis fe env m1 a1 → IWGrow m m1 → PosMR m1 →
      AbsOK m1 → PStep a a1 → nwE.j1 p n vis ctx po pl hi nF crest ns fu' m1 = .error e →
      ErrClaim (ConRon.Arena.nestFields V fe c fu'.toNat prog hi.toNat nF.toNat 0 (decI crest) NS [] []) a1 e := by
    intro fu' m1 a1 hC1 hg1 hP1 hA1 p1 h
    simp only [nwE.j1] at h
    cases c1 : callE p n "nest_fields" [vis, ctx, fu', po, pl, hi, nF, 0, crest, ns, 0, 0, 0, 0] m1 with
    | error e1 =>
      rw [c1, nwE.k_nest_fields.none] at h; cases h
      have := hFieldsE m1 a1 ctx fu' po pl hi nF 0 crest ns 0 0 0 0 c prog NS [] [] ctxP progP crestP nsP []
        hC1 (hW.grow hg1) hcr
        (hns.grow hg1 (Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1)) (KlB.nil _ _) (by simp)
        (by simp [decHL, hslice?]) (by simp) hP1 hA1 hc (dCtx_ext _ p1.ext _ _ hctx) (dProg_ext p1.ext _ _ hprog)
        (ConRon.Bridge.denote_ext hcrP p1.ext) (dState_ext p1.ext _ _ hnsP) rfl (by simpa using hwc) _ c1
      simpa using this
    | ok q1 =>
      obtain ⟨rf, mf⟩ := q1
      rw [c1, nwE.k_nest_fields.arm1] at h
      cases c2 : callE p n "close_telescope" [rf.tail.tail.headD 0, rf.tail.tail.tail.headD 0, hi,
          rf.tail.tail.tail.tail.headD 0] mf with
      | error e2 =>
        rw [c2, nwE.k_close_telescope.none] at h; cases h
        exact ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) c2
      | ok q2 => obtain ⟨rc, mc⟩ := q2; rw [c2, nwE.k_close_telescope.arm1] at h; cases h
  by_cases hr : root ≠ 0
  · rw [nwE.arm1 p n m vis ctx root fu po pl hi nF crest ns hr] at he
    have hdec : decide (root ≠ 0) = true := by simpa using hr
    cases c1 : callE p n "whnf_walk_fuel" [crest] m with
    | error e1 =>
      rw [c1, nwE.k_whnf_walk_fuel.none] at he; cases he
      exact ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) c1
    | ok q1 =>
    obtain ⟨rw, m1⟩ := q1
    rw [c1, nwE.k_whnf_walk_fuel.arm1] at he
    obtain ⟨s1, hs1, -, hw⟩ := triple_of_callW (whnfWalkFuel_spec' p L n ⟨m, Locals.init []⟩ crest)
      (callW_of_callE c1)
    simp only at hw
    rw [hs1] at hw
    cases n with
    | zero => simp [wfWf] at hw
    | succ n' =>
    cases n' with
    | zero => simp [wfWf] at hw
    | succ n'' =>
    simp only [wfWf] at hw
    rcases hw' : wfW n'' m crest with _ | ⟨wf, m1'⟩ <;> rw [hw'] at hw; · simp at hw
    simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hw
    obtain ⟨hwr, rfl⟩ := hw
    obtain ⟨mp, hmp⟩ := hP.dp
    obtain ⟨d, hrunw, hwd, hM1, hS1, hg1, hf1⟩ := wfW_ok n'' dn fe vis m m1' a crest wf mp hw' hS hcr hmp
    have hA1 := wfW_afr hw' hA
    have h1 := hF (rw.headD 0) m1' a (hC.of_pstep hS1 hA1 (PStep.refl hC.check.state)) hg1
      (hP.setDp hf1 ⟨∅, hM1⟩) hA1 (PStep.refl hC.check.state) he
    rw [← hwr, hwd] at h1
    refine ErrClaim.of_run' h1 fun ce hce => ?_
    rw [← decE_eq] at hce
    simp only [walkK, hdec, dite_true, StateT.run_bind, ← decE_eq, hrunw, except_ok_bind, hce]
    rfl
  · have h0 : root = 0 := by simpa using hr
    rw [nwE.arm2 p n m vis ctx root fu po pl hi nF crest ns h0] at he
    have hdec : decide (root ≠ 0) = false := by simpa using hr
    simp only [walkK, hdec]
    exact ErrClaim.bind_left (hF fu m a hC (IWGrow.refl _) hP hA (PStep.refl hC.check.state) he)

end steps

end L.Ind
