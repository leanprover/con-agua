import ConAgua.Arena.IndT.PosFields
import ConAgua.Arena.IndPosSpec.NestCrest
import ConAgua.Arena.IndPosSpec.P2sfW
import ConAgua.Arena.IndRealAbsPos

/-!
# `nest_ctors_walk` refines `walkT`, both outcomes

`walkRef_step` walks the unified model `nwE` (`Verdict/PosE3Cm`) against `walkT` (`walkK` without
its continuation): the root frame's fuel (`whnfWalkFuel`, the state unchanged), the fields (the
block's `FieldsRef` at `n`, con-ron's `nestFields_spec` on the run for the walked telescope's
denotations), the telescope closed (`closeTelescope_spec`); `whnf_walk_fuel` and `close_telescope`
are outside the verdict closure.
-/


open ConRon.Arena
open ConRon.Bridge.Inductives (PStep dCtx dProg dState dCtx_ext dProg_ext dState_ext kindOf)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section steps
variable {p : Prog} (L : NbLook p) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
  {env : ConLeche.Env} (henv : ConLeche.EnvWF env)

include L henv in
theorem walkRef_step (n : Nat) (ih : NbRef p dn vis fe env n) : WalkRef p dn vis fe env (n + 1) := by
  have R := L.ct.cr.rx
  intro m a ctx root fu po pl hi nF crest ns c prog NS ctxP progP crestP nsP hC hW hcr hns hP hA
    hc hctx hprog hcrP hnsP hwc
  have hS := hC.stage
  -- the fields walked, at the input-derived fuel or the given one
  have hF : ∀ (fu' : Word) (m1 : Mem) (a1 : AState), StageC dn vis fe env m1 a1 → IWGrow m m1 → PosMR m1 →
      AbsOK m1 → PStep a a1 →
      RefE (NbG p) (nwE.j1 p n vis ctx po pl hi nF crest ns fu' m1)
        (walkT V fe c fu'.toNat prog false hi.toNat nF.toNat (decI crest) NS) a1
        (fun v x a' => WalkPost dn vis fe env a m hi nF v.1 v.2 x a') := by
    intro fu' m1 a1 hC1 hg1 hP1 hA1 p1
    have hS1 := hC1.stage
    have hctx1 := dCtx_ext _ p1.ext _ _ hctx
    have hprog1 := dProg_ext p1.ext _ _ hprog
    have hcr1 := ConRon.Bridge.denote_ext hcrP p1.ext
    have hns1 := dState_ext p1.ext _ _ hnsP
    have hR1 := ih.fields m1 a1 ctx fu' po pl hi nF 0 crest ns 0 0 0 0 c prog NS [] [] ctxP progP crestP nsP []
      hC1 (hW.grow hg1) hcr (hns.grow hg1 (Nat.lt_of_le_of_lt hS.iw.iw hS.iw.iwSize)) (KlB.nil _ _) (by simp)
      (by simp [decHL, hslice?]) (by simp) hP1 hA1 hc hctx1 hprog1 hcr1 hns1 rfl (by simpa using hwc)
    simp only [UInt64.toNat_zero] at hR1
    have hs1 := nfE_spec p L.pfields n ⟨m1, Locals.init []⟩ vis ctx fu' po pl hi nF 0 crest ns 0 0 0 0
    unfold walkT walkK
    simp only [Bool.false_eq_true, dite_false, nwE.j1]
    rcases c1 : callE p n "nest_fields" [vis, ctx, fu', po, pl, hi, nF, 0, crest, ns, 0, 0, 0, 0] m1 with e1 | ⟨rf, m2⟩
    · rw [nwE.k_nest_fields.none]
      exact RefE.bind_left fun hG => RefE.run_err hs1 True.intro hG hR1 c1
    rw [nwE.k_nest_fields.arm1]
    obtain ⟨s2, hs2, -, ⟨ks, nds, cur, ns2⟩, a2, hrun, hpost⟩ := RefE.run_ok hs1 hR1 c1
    rw [hs2] at hpost
    obtain ⟨hC2, hg2, hK, hKb, hD, hDb, hcH, hcd, hns2, hl1, hl2, hov, hP2, hA2, c2⟩ := hpost
    dsimp only at hC2 hg2 hK hKb hD hDb hcH hcd hns2 hl1 hl2 hov hP2 hA2 c2
    have hS2 := hC2.stage
    have c1 := p1.toCore hC.check
    obtain ⟨-, vf, ⟨-, hnds, hcur, hnsP2, hwnds, hwcur⟩, -⟩ := ConRon.Bridge.Inductives.nestFields_spec
      (ConRon.Bridge.Inductives.nestPos_spec coreSpecV henv hc fu'.toNat) prog progP hi.toNat
      (.invalid "nested positivity") nF.toNat 0 (decI crest) crestP NS nsP [] [] [] (by simpa using hwc)
      a1 a2 _ hC1.check ⟨hctx1, hprog1, hcr1, hns1, rfl⟩ hrun
    simp only [List.nil_append] at hnds
    refine RefE.bind_right hrun ?_
    rcases c2' : callE p n "close_telescope" [rf.tail.tail.headD 0, rf.tail.tail.tail.headD 0, hi,
        rf.tail.tail.tail.tail.headD 0] m2 with e2 | ⟨rc, m3⟩
    · rw [nwE.k_close_telescope.none]
      exact fun hG => ErrClaim.of_callE_nv hG.nv (_root_.L.Checker.nv_mem (by decide +kernel)) c2'
    rw [nwE.k_close_telescope.arm1]
    obtain ⟨s3, hs3, -, hcl⟩ := triple_of_callW (closeTelescope_spec p R.hk.hd R.hk.forF R.hk.forP R.hk.forI
      R.hk.forM L.hcl L.ab n ⟨m2, Locals.init []⟩ _ _ _ _) (callW_of_callE c2')
    simp only at hcl
    rw [hs3] at hcl
    have htop2 : iwTop m2 < 2 ^ 64 := Nat.lt_of_le_of_lt hS2.iw.iw hS2.iw.iwSize
    have hdl : (rf.tail.tail.tail.headD 0).toNat = nds.length := (decHL_length _ hD).symm
    have hib : hi.toNat + (rf.tail.tail.tail.headD 0).toNat < 2 ^ 64 := by
      rw [hdl, hl2]
      simp only [UInt64.toNat_zero, Nat.add_zero, List.length_nil, Nat.zero_add] at hov ⊢
      rcases hov with h0 | h0
      · rw [h0]; simpa using hi.toNat_lt
      · omega
    obtain ⟨cl, a3, hrun3, hS3, hg3, ⟨hclH, hcld⟩, hA3⟩ := closeW_ok n dn fe vis m2 m3 a2 _ _ hi _ nds rc hcl hS2
      hcH hD (by omega) hDb hib hA2
    rw [hcd] at hrun3
    obtain ⟨p3, hclP⟩ := ConRon.Bridge.Inductives.closeTelescope_spec nds vf.2.1 hi.toNat cur vf.2.2.1
      a2 a3 cl hC2.check.state ⟨hnds, hcur⟩ hrun3
    refine RefE.bind_right hrun3 (RefE.ret rfl ⟨hC2.of_pstep hS3 hA3 p3, hg1.trans (hg2.trans hg3), hK.grow hg3,
      by simp only [List.headD_cons, List.tail_cons]; have := hg3.1; omega, by simpa using hl1, hcH, hcd, hclH,
      hcld, hns2.grow hg3 htop2,
      hP2.fr (closeW_mfr _ _ _ _ _ _ _ _ hcl), hA3, (c1.trans c2).trans (p3.toCore hC2.check),
      vf.2.1, vf.2.2.1, vf.2.2.2, ConRon.Bridge.denoteEList_ext p3.ext _ _ hnds,
      ConRon.Bridge.denote_ext hcur p3.ext, dState_ext p3.ext _ _ hnsP2, hclP,
      fun i nd hi' => by simpa using hwnds i nd hi', by simpa using hwcur⟩)
  by_cases hr : root ≠ 0
  · rw [nwE.arm1 p n m vis ctx root fu po pl hi nF crest ns hr]
    have hdec : decide (root ≠ 0) = true := by simpa using hr
    rcases c1 : callE p n "whnf_walk_fuel" [crest] m with e1 | ⟨rw, m1⟩
    · rw [nwE.k_whnf_walk_fuel.none]
      exact fun hG => ErrClaim.of_callE_nv hG.nv (_root_.L.Checker.nv_mem (by decide +kernel)) c1
    rw [nwE.k_whnf_walk_fuel.arm1]
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
      (hP.setDp hf1 ⟨∅, hM1⟩) hA1 (PStep.refl hC.check.state)
    rw [← hwr, hwd] at h1
    rw [← hwr]
    refine RefE.of_run_eq ?_ h1
    rw [hdec]
    simp only [walkT, walkK, dite_true, Bool.false_eq_true, dite_false, StateT.run_bind, ← decE_eq, hrunw,
      except_ok_bind]
  · have h0 : root = 0 := by simpa using hr
    rw [nwE.arm2 p n m vis ctx root fu po pl hi nF crest ns h0]
    have hdec : decide (root ≠ 0) = false := by simpa using hr
    rw [hdec]
    exact hF fu m a hC (IWGrow.refl _) hP hA (PStep.refl hC.check.state)

end steps

end L.Ind
