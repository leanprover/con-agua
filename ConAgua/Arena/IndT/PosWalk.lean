import ConAgua.Arena.IndT.PosFields
import ConAgua.Arena.IndPosSpec.NestCrest
import ConAgua.Arena.IndPosSpec.P2sfW
import ConAgua.Arena.IndRealAbsPos

/-!
# `nest_ctors_walk` under `StageC` (lane `indstaget`, helper `indstaget-pos`)

`walkOK_step`'s proof (`IndPosSpec/Pos2DecHLSplit`) with the twin side of con-ron's `nestCtors_spec` (its field
walk): the root frame's fuel (`whnfWalkFuel`, the state unchanged), the fields (the block's
`FieldsOKC` at `n`, con-ron's `nestFields_spec` on the run for the walked telescope's
denotations), the telescope closed (`closeTelescope_spec`).
-/


open ConRon.Arena
open ConRon.Bridge.Inductives (PStep dCtx dProg dState dCtx_ext dProg_ext dState_ext kindOf)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section steps
variable (p : Prog) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) {env : ConLeche.Env}
  (henv : ConLeche.EnvWF env)

include henv in
theorem walkOKC_step (n : Nat) (ih : NbOKC p dn vis fe env n) : WalkOKC p dn vis fe env (n + 1) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hFields⟩ := ih
  intro m m' a ctx root fu po pl hi nF crest ns c prog NS r ctxP progP crestP nsP h hC hW hcr hns hP hA
    hc hctx hprog hcrP hnsP hwc
  have hS := hC.stage
  rw [nbWalkW_succ] at h
  -- the fields walked, at the input-derived fuel or the given one
  have hF : ∀ (fu' : Word) (m1 : Mem) (a1 : AState), StageC dn vis fe env m1 a1 → IWGrow m m1 → PosMR m1 →
      AbsOK m1 → PStep a a1 →
      nbWalkK2 n hi (nbFieldsW (realCall p) n m1 vis ctx fu' po pl hi nF 0 crest ns 0 0 0 0) = some (r, m') →
      ∃ ks nds cur ns2 closed a',
        (∀ {β : Type} (K : List NestFieldKind → List EIdx → EIdx → NestState → EIdx → AM β),
          (do let (ks, nds, cur, ns2) ← nestFields V fe c fu'.toNat prog hi.toNat nF.toNat 0 (decI crest) NS [] []
              let closed ← ConRon.Arena.closeTelescope nds hi.toNat cur
              K ks nds cur ns2 closed).run a1 = (K ks nds cur ns2 closed).run a') ∧
        StageC dn vis fe env m' a' ∧ IWGrow m1 m' ∧ KlB m' (r.headD 0).toNat (r.tail.headD 0).toNat ks ∧
        (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' ∧ ks.length = nF.toNat ∧
        H (r.tail.tail.headD 0) ∧ decI (r.tail.tail.headD 0) = cur ∧
        H (r.tail.tail.tail.headD 0) ∧ decI (r.tail.tail.tail.headD 0) = closed ∧
        NSB m' (r.tail.tail.tail.tail.headD 0) ns2 ∧ PosMR m' ∧ AbsOK m' ∧
        ConRon.Bridge.CoreStep V env fe a a' ∧
        ∃ ndsP curP nsP2, Frontend.denoteEList a'.store nds = some ndsP ∧ denoteE a'.store cur = some curP ∧
          dState a'.store ns2 = some nsP2 ∧
          denoteE a'.store closed = some (ConLeche.closeTelescope ndsP hi.toNat curP) ∧
          (∀ (i : Nat) (nd : ConLeche.Expr), ndsP[i]? = some nd → ConLeche.Expr.WScoped (hi.toNat + i) nd) ∧
          ConLeche.Expr.WScoped (hi.toNat + ndsP.length) curP := by
    intro fu' m1 a1 hC1 hg1 hP1 hA1 p1 h
    have hS1 := hC1.stage
    have htop1 : iwTop m1 < 2 ^ 64 := Nat.lt_of_le_of_lt hS1.2.1 hS1.2.2.2.1
    rcases hf : nbFieldsW (realCall p) n m1 vis ctx fu' po pl hi nF 0 crest ns 0 0 0 0 with _ | ⟨rf, m2⟩ <;> rw [hf] at h; · simp [nbWalkK2] at h
    rw [nbWalkK2_some] at h
    have hctx1 := dCtx_ext _ p1.ext _ _ hctx
    have hprog1 := dProg_ext p1.ext _ _ hprog
    have hcr1 := ConRon.Bridge.denote_ext hcrP p1.ext
    have hns1 := dState_ext p1.ext _ _ hnsP
    obtain ⟨x, a2, hrun, hC2, hg2, hK, hKb, hD, hDb, hcH, hcd, hns2, hl1, hl2, hov, hP2, hA2, c2⟩ :=
      hFields m1 m2 a1 ctx fu' po pl hi nF 0 crest ns 0 0 0 0 c prog NS [] [] rf ctxP progP crestP nsP []
        hf hC1 (hW.grow hg1) hcr
        (hns.grow hg1 (Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1)) (KlB.nil _ _) (by simp)
        (by simp [decHL, hslice?]) (by simp) hP1 hA1 hc hctx1 hprog1 hcr1 hns1 rfl (by simpa using hwc)
    have hS2 := hC2.stage
    have c1 := p1.toCore hC.check
    obtain ⟨-, vf, ⟨-, hnds, hcur, hnsP2, hwnds, hwcur⟩, -⟩ := ConRon.Bridge.Inductives.nestFields_spec
      (ConRon.Bridge.Inductives.nestPos_spec coreSpecV henv hc fu'.toNat) prog progP hi.toNat
      (.invalid "nested positivity") nF.toNat 0 (decI crest) crestP NS nsP [] [] [] (by simpa using hwc)
      a1 a2 x hC1.check ⟨hctx1, hprog1, hcr1, hns1, rfl⟩ (by simp only [UInt64.toNat_zero] at hrun; exact hrun)
    simp only [List.nil_append] at hnds
    rcases hcl : closeW n m2 (rf.tail.tail.headD 0) (rf.tail.tail.tail.headD 0) hi (rf.tail.tail.tail.tail.headD 0) with _ | ⟨rc, m3⟩ <;> rw [hcl] at h; · simp [nbWalkK3] at h
    rw [nbWalkK3_some] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    simp only [List.headD_cons, List.tail_cons]
    have htop2 : iwTop m2 < 2 ^ 64 := Nat.lt_of_le_of_lt hS2.2.1 hS2.2.2.2.1
    have hdl : (rf.tail.tail.tail.headD 0).toNat = x.2.1.length := (decHL_length _ hD).symm
    have hib : hi.toNat + (rf.tail.tail.tail.headD 0).toNat < 2 ^ 64 := by
      rw [hdl, hl2]
      simp only [UInt64.toNat_zero, Nat.add_zero, List.length_nil, Nat.zero_add] at hov ⊢
      rcases hov with h0 | h0
      · rw [h0]; simpa using hi.toNat_lt
      · omega
    obtain ⟨cl, a3, hrun3, hS3, hg3, ⟨hclH, hcld⟩, hA3⟩ := closeW_ok n dn fe vis m2 m3 a2 _ _ hi _ x.2.1 rc hcl hS2
      hcH hD (by omega) hDb hib hA2
    rw [hcd] at hrun3
    obtain ⟨p3, hclP⟩ := ConRon.Bridge.Inductives.closeTelescope_spec x.2.1 vf.2.1 hi.toNat x.2.2.1 vf.2.2.1
      a2 a3 cl hC2.check.state ⟨hnds, hcur⟩ hrun3
    refine ⟨x.1, x.2.1, x.2.2.1, x.2.2.2, cl, a3, fun K => ?_, hC2.of_pstep hS3 hA3 p3, hg2.trans hg3, hK.grow hg3,
      by have := hg3.1; omega, by simpa using hl1, hcH, hcd, hclH, hcld, hns2.grow hg3 htop2,
      hP2.fr (closeW_mfr _ _ _ _ _ _ _ _ hcl), hA3, (c1.trans c2).trans (p3.toCore hC2.check),
      vf.2.1, vf.2.2.1, vf.2.2.2, ConRon.Bridge.denoteEList_ext p3.ext _ _ hnds,
      ConRon.Bridge.denote_ext hcur p3.ext, dState_ext p3.ext _ _ hnsP2, hclP,
      fun i nd hi' => by simpa using hwnds i nd hi', by simpa using hwcur⟩
    simp only [UInt64.toNat_zero] at hrun
    simp only [StateT.run_bind, hrun, except_ok_bind, hrun3]
  by_cases hr : root ≠ 0
  · rw [ite_eq_left hr] at h
    have hdec : decide (root ≠ 0) = true := by simpa using hr
    cases n with
    | zero => simp [wfWf, nbWalkK1] at h
    | succ n' =>
    cases n' with
    | zero => simp [wfWf, nbWalkK1] at h
    | succ n'' =>
    simp only [wfWf] at h
    rcases hw : wfW n'' m crest with _ | ⟨wf, m1⟩ <;> rw [hw] at h; · simp [nbWalkK1] at h
    simp only [nbWalkK1_some, List.headD_cons] at h
    obtain ⟨mp, hmp⟩ := hP.dp
    obtain ⟨d, hrunw, hwd, hM1, hS1, hg1, hf1⟩ := wfW_ok n'' dn fe vis m m1 a crest wf mp hw hS hcr hmp
    have hA1 := wfW_afr hw hA
    obtain ⟨ks, nds, cur, ns2, closed, a', hK, rest⟩ := hF wf m1 a
      (hC.of_pstep hS1 hA1 (PStep.refl hC.check.state)) hg1 (hP.setDp hf1 ⟨∅, hM1⟩) hA1
      (PStep.refl hC.check.state) h
    refine ⟨ks, nds, cur, ns2, closed, a', fun K => ?_, rest.1, hg1.trans rest.2.1, rest.2.2⟩
    simp only [← hK K, hwd, walkK, hdec, dite_true, StateT.run_bind, ← decE_eq, hrunw, except_ok_bind]
  · rw [ite_eq_right hr] at h
    have hdec : decide (root ≠ 0) = false := by simpa using hr
    obtain ⟨ks, nds, cur, ns2, closed, a', hK, rest⟩ := hF fu m a hC (IWGrow.refl _) hP hA
      (PStep.refl hC.check.state) h
    refine ⟨ks, nds, cur, ns2, closed, a', fun K => ?_, rest⟩
    simp only [← hK K, walkK, hdec]
    rfl

end steps

end L.Ind
