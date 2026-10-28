import ConAgua.Arena.IndT.Lift
import ConAgua.Verdict.PosE
import ConAgua.Arena.IndT.PosDefs
import ConAgua.Arena.IndPosSpec.GgW2
import ConAgua.Arena.IndPosSpec.Pos2DecHLSplit
import ConAgua.Arena.IndRealAbsPos
import ConAgua.Arena.IndPosSpec.Snoc

/-!
# `nest_cont_key` under `StageC` (lane `indstaget`, helper `indstaget-pos`)

`keyOK_step`'s proof (`IndPosSpec/Pos2DecHLSplit`) with the twin side of con-ron's `nestContKey_spec`: the
parameters' closedness (`closedAll_spec`), then a cache hit or a new frame (the block's `NewOKC`
at `n`).
-/


open ConRon.Arena
open ConRon.Bridge.Inductives (PStep dCtx dProg dState dCtx_ext dProg_ext dState_ext kindOf)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section steps
variable (p : Prog) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) {env : ConLeche.Env}

/-- **`nest_cont_key` refines `nestContKey`, both outcomes**, at L fuel `n + 1`: the key, not in
progress, the parameters' closedness, then a cache hit or a new frame (the block's `NewRef` at `n`). -/
theorem keyRef_step (L : NbLook p) (n : Nat) (ih : NbRef p dn vis fe env n) : KeyRef p dn vis fe env (n + 1) := by
  intro m a ctx fu po pl kb nn us dO dL nPc cty ns c prog ds NS ctxP progP nP usP dsP ctyP nsP hC hW hnn hus
    hds hdsb hcty hns hP hA hc hctx hprog hnP husP hdsP hctyP hnsP hwds hni
  have R := L.ct.cr.rx
  have hS := hC.stage
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  rw [nckE.arm1]
  -- the key
  cases h1 : callE p n "rec4" [nn, us, dO, dL] m with
  | error e1 =>
    rw [nckE.k_rec4.none]
    exact fun hG => ErrClaim.of_callE_nv hG.nv (_root_.L.Checker.nv_mem (by decide +kernel)) h1
  | ok q =>
  obtain ⟨rk, m1⟩ := q
  obtain ⟨s1, hs1, -, hk⟩ := triple_of_callW (posRec4_specW p R.ha R.h4 n ⟨m, Locals.init []⟩ nn us dO dL)
    (callW_of_callE h1)
  simp only at hk
  rw [hs1] at hk
  rw [nckE.k_rec4.eq_2]
  obtain ⟨hS1, hg1, hkq, ht1, hget1⟩ := posRecW_stage hk hS (by simp)
  simp only [List.length_cons, List.length_nil] at ht1
  have hK : DecB (fun m => decNK m (rk.headD 0).toNat) m1 ⟨decI nn, decI us, ds⟩ :=
    pos2_key_rec hnn hus (by omega) hget1 (hds.grow (OMono.decHL _ _) hg1)
  have htop1 : iwTop m1 < 2 ^ 64 := Nat.lt_of_le_of_lt hS1.2.1 hS1.2.2.2.1
  obtain ⟨hp6, hk0', ha0, -⟩ := nsb_words hns htop
  -- not in progress
  cases h2 : callE p n "nest_keys_contains" [rdW (m1.arr64 IW) (ns + 2), rdW (m1.arr64 IW) (ns + 3), rk.headD 0] m1 with
  | error e2 =>
    rw [nckE.k_nest_keys_contains.none]
    exact fun hG => ErrClaim.of_callE_nv hG.nv (_root_.L.Checker.nv_mem (by decide +kernel)) h2
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  obtain ⟨s2, hs2, -, hm2, hW2⟩ := triple_of_callW (nestKeysContains_spec p L.nag.hq L.nag.he L.nag.hkc n
    ⟨m1, Locals.init []⟩ _ _ _) (callW_of_callE h2)
  simp only at hm2 hW2
  rw [hs2] at hm2
  rw [pos2_ns_rd hg1 hp6 htop 2 (by decide), pos2_ns_rd hg1 hp6 htop 3 (by decide)] at hW2
  have hb1 := nkcW_ok (rk.headD 0) _ n m1 _ _ _ NS.active hW2 (ha0.grow hg1) hK htop1
  by_cases hb1n : r2.headD 0 ≠ 0
  · rw [nckE.k_nest_keys_contains.abort1 p n vis ctx fu po pl kb nn us dO dL nPc cty ns (rk.headD 0) r2 m2 hb1n]
    have hact : NS.active.contains ⟨decI nn, decI us, ds⟩ = true := by
      cases e : NS.active.contains ⟨decI nn, decI us, ds⟩ with
      | true => rfl
      | false => rw [e] at hb1; exact absurd (by simpa using hb1) hb1n
    refine fun _ => ?_
    simp only [nestContKey.eq_def, hact, ite_true]
    exact ErrClaim.fail _ _ (by decide)
  obtain rfl := hm2.symm
  rw [nckE.k_nest_keys_contains.arm1 p n vis ctx fu po pl kb nn us dO dL nPc cty ns (rk.headD 0) r2 m1
    (by simpa using hb1n)]
  have hact : NS.active.contains ⟨decI nn, decI us, ds⟩ = false := by
    cases e : NS.active.contains ⟨decI nn, decI us, ds⟩ with
    | false => rfl
    | true =>
      have h0 : r2.headD 0 = 0 := by simpa using hb1n
      rw [e, h0] at hb1; exact absurd hb1 (by decide)
  -- closed?
  cases h3 : callE p n "nest_ds_closed" [ctx, dO, dL] m1 with
  | error e3 =>
    rw [nckE.k_nest_ds_closed.none]
    exact fun hG => ErrClaim.of_callE_nv hG.nv (_root_.L.Checker.nv_mem (by decide +kernel)) h3
  | ok q3 =>
  obtain ⟨r3, m3⟩ := q3
  obtain ⟨s3, hs3, -, hW3⟩ := triple_of_callW (dc_spec' p L.dc.hf L.dc.hh L.dc.hg L.dc.hp n
    ⟨m1, Locals.init []⟩ ctx dO dL) (callW_of_callE h3)
  simp only at hW3
  rw [hs3] at hW3
  cases n with
  | zero => simp [dcWf] at hW3
  | succ n' =>
  have hhi0 : c.hiAt 0 < 2 ^ 64 := by have := hW.hb; simp only [NestCtx.hiAt] at this ⊢; omega
  obtain ⟨bc, a2, hrun2, hS2, hg2, hr2⟩ := dcWf_ok dn fe vis (n' + 1) m1 m3 a ctx dO dL c ds [r3.headD 0] hW3 hS1
    (hW.grow hg1).u.dec (hW.grow hg1).u.inn hhi0 ((hds.grow (OMono.decHL _ _) hg1).get (OMono.decHL _ _))
    (fun j hj => by have := hg1.1; omega)
  have hg12 := hg1.trans hg2
  have hP2 : PosMR m3 := (hP.fr (posRecW_mfr hk)).fr (dcWf_mfr hW3)
  have hA2 : AbsOK m3 := dcWf_afr hW3 (posRecW_afr hk hA)
  have hrun2' : (ds.allM fun x => do
      let b ← fvarB coreWalkFuel x
      pure (decide (b ≤ c.hiAt 0))).run a = .ok (bc, a2) := hrun2
  obtain ⟨p2, -⟩ := ConRon.Bridge.Inductives.closedAll_spec (c.hiAt 0) ds dsP a a2 bc hC.check.state hdsP hrun2'
  have hC2 : StageC dn vis fe env m3 a2 := hC.of_pstep hS2 hA2 p2
  have c2 := p2.toCore hC.check
  simp only [nestContKey.eq_def, hact, Bool.false_eq_true, ite_false]
  refine RefE.bind_right hrun2' ?_
  -- the frame, when not cached
  have hnew : RefE (NbG p) (nckE.j1 p (n' + 1) vis ctx fu po pl kb nn us dO dL nPc cty ns m3)
      (nestContNew V fe c fu.toNat prog kb.toNat (decI nn) (decI us) ds nPc.toNat (decI cty) NS) a2
      (fun v x a' => KindPost dn vis fe env a m v.1 v.2 x a') := by
    have hR := ih.new m3 a2 ctx fu po pl kb nn us dO dL nPc cty ns c prog ds NS ctxP progP nP usP dsP ctyP nsP hC2
      (hW.grow hg12) hnn hus (hds.grow (OMono.decHL _ _) hg12) (by have := hg12.1; omega) hcty
      (hns.grow hg12 htop) hP2 hA2 hc (dCtx_ext _ p2.ext _ _ hctx) (dProg_ext p2.ext _ _ hprog)
      (ConRon.Bridge.denoteN_ext hnP p2.ext) (ConRon.Bridge.denoteLs_ext husP p2.ext)
      (ConRon.Bridge.denoteEList_ext p2.ext _ _ hdsP) (ConRon.Bridge.denote_ext hctyP p2.ext)
      (dState_ext p2.ext _ _ hnsP) hwds hni
    have hsp := nnewE_specU p L.pnew (n' + 1) ⟨m3, Locals.init []⟩ vis ctx fu po pl kb nn us dO dL nPc cty ns
    simp only [nckE.j1]
    cases h5 : callE p (n' + 1) "nest_cont_new" [vis, ctx, fu, po, pl, kb, nn, us, dO, dL, nPc, cty, ns] m3 with
    | error e5 =>
      rw [nckE.k_nest_cont_new.none]
      exact fun hG => RefE.run_err hsp True.intro hG hR h5
    | ok q5 =>
      obtain ⟨r5, m5⟩ := q5
      rw [nckE.k_nest_cont_new.arm1]
      obtain ⟨s5, hs5, -, x, a', hrun, hpost⟩ := RefE.run_ok hsp hR h5
      dsimp only at hpost
      rw [hs5] at hpost
      exact RefE.ret hrun ⟨hpost.stage, hg12.trans hpost.grow, by simpa using hpost.kind,
        by simpa using hpost.ns, hpost.pos, hpost.abs, c2.trans hpost.core⟩
  by_cases hr3 : r3.headD 0 ≠ 0
  · rw [nckE.k_nest_ds_closed.arm1 p (n' + 1) vis ctx fu po pl kb nn us dO dL nPc cty ns (rk.headD 0) r3 m3 hr3]
    have hbc : bc = true := by cases bc <;> simp_all
    subst hbc
    cases h4 : callE p (n' + 1) "nest_keys_contains"
        [rdW (m3.arr64 IW) ns, rdW (m3.arr64 IW) (ns + 1), rk.headD 0] m3 with
    | error e4 =>
      rw [nckE.k_nest_keys_contains_2.none]
      exact fun hG => ErrClaim.of_callE_nv hG.nv (_root_.L.Checker.nv_mem (by decide +kernel)) h4
    | ok q4 =>
    obtain ⟨r4, m4⟩ := q4
    obtain ⟨s4, hs4, -, hm4, hW4⟩ := triple_of_callW (nestKeysContains_spec p L.nag.hq L.nag.he L.nag.hkc (n' + 1)
      ⟨m3, Locals.init []⟩ _ _ _) (callW_of_callE h4)
    simp only at hm4 hW4
    rw [hs4] at hm4
    obtain rfl := hm4.symm
    rw [pos2_rd_grow hg12 (by omega), pos2_ns_rd hg12 hp6 htop 1 (by decide)] at hW4
    have hb2 := nkcW_ok (rk.headD 0) _ (n' + 1) m3 _ _ _ NS.keys.toList hW4 (hk0'.grow hg12)
      (hK.grow (decNK_mono _) hg2) (Nat.lt_of_le_of_lt hS2.2.1 hS2.2.2.2.1)
    by_cases hb2n : r4.headD 0 ≠ 0
    · rw [nckE.k_nest_keys_contains_2.arm1 p (n' + 1) vis ctx fu po pl kb nn us dO dL nPc cty ns r4 m3 hb2n]
      have hin : NS.keys.contains ⟨decI nn, decI us, ds⟩ = true := by
        rw [← Array.contains_toList]
        cases e : NS.keys.toList.contains ⟨decI nn, decI us, ds⟩ with
        | true => rfl
        | false => rw [e] at hb2; exact absurd hb2 (by simpa using hb2n)
      refine RefE.ite_pos (by simp [hin]) (RefE.ret rfl ⟨hC2, hg12, ?_, by simpa using hns.grow hg12 htop, hP2, hA2,
        c2⟩)
      have := decNFK_nestedW kb
      by_cases hkb : kb = 0 <;> simp_all [nestedW]
    · have h0 : r4.headD 0 = 0 := by simpa using hb2n
      rw [nckE.k_nest_keys_contains_2.arm2 p (n' + 1) vis ctx fu po pl kb nn us dO dL nPc cty ns r4 m3 h0]
      have hout : NS.keys.contains ⟨decI nn, decI us, ds⟩ = false := by
        rw [← Array.contains_toList]
        cases e : NS.keys.toList.contains ⟨decI nn, decI us, ds⟩ with
        | false => rfl
        | true => rw [e, h0] at hb2; exact absurd hb2 (by decide)
      exact RefE.ite_neg (by simp [hout]) hnew
  · have h0 : r3.headD 0 = 0 := by simpa using hr3
    rw [nckE.k_nest_ds_closed.arm2 p (n' + 1) vis ctx fu po pl kb nn us dO dL nPc cty ns (rk.headD 0) r3 m3 h0]
    have hbc : bc = false := by cases bc <;> simp_all
    subst hbc
    exact RefE.ite_neg (by simp) hnew

end steps

end L.Ind
