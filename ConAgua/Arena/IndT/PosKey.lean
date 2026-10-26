import ConAgua.Arena.IndT.PosNew

/-!
# `nest_cont_key` under `StageC` (lane `indstaget`, helper `indstaget-pos`)

`keyOK_step`'s proof (`IndPos2SpecS`) with the twin side of con-ron's `nestContKey_spec`: the
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

theorem keyOKC_step (n : Nat) (ih : NbOKC p dn vis fe env n) : KeyOKC p dn vis fe env (n + 1) := by
  obtain ⟨-, -, -, -, -, hNew, -, -, -, -, -⟩ := ih
  intro m m' a ctx fu po pl kb nn us dO dL nPc cty ns c prog ds NS r ctxP progP nP usP dsP ctyP nsP h hC hW hnn hus
    hds hdsb hcty hns hP hA hc hctx hprog hnP husP hdsP hctyP hnsP hwds hni
  have hS := hC.stage
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  have hhi0 : c.hiAt 0 < 2 ^ 64 := by have := hW.hb; simp only [NestCtx.hiAt] at this ⊢; omega
  rw [nbKeyW_succ] at h
  rcases hk : posRecW m [nn, us, dO, dL] with _ | ⟨key, m1⟩ <;> rw [hk] at h; · simp [nbKeyK1] at h
  rw [nbKeyK1_some] at h
  obtain ⟨hS1, hg1, hkq, ht1, hget1⟩ := posRecW_stage hk hS (by simp)
  simp only [List.length_cons, List.length_nil] at ht1
  have hK : DecB (fun m => decNK m key.toNat) m1 ⟨decI nn, decI us, ds⟩ :=
    pos2_key_rec hnn hus (by omega) hget1 (hds.grow (OMono.decHL _ _) hg1)
  have htop1 : iwTop m1 < 2 ^ 64 := Nat.lt_of_le_of_lt hS1.2.1 hS1.2.2.2.1
  obtain ⟨hp6, hk0, ha0, -⟩ := nsb_words hns htop
  rw [pos2_ns_rd hg1 hp6 htop 2 (by decide), pos2_ns_rd hg1 hp6 htop 3 (by decide)] at h
  -- not in progress
  rcases hc1 : nkcW n m1 (rdW (m.arr64 IW) (ns + 2)) (rdW (m.arr64 IW) (ns + 3)) key with _ | b1 <;> rw [hc1] at h; · cases h
  simp only at h
  have hb1 := nkcW_ok key _ n m1 _ _ b1 NS.active hc1 (ha0.grow hg1) hK htop1
  by_cases hb1n : b1 ≠ 0
  · rw [ite_eq_left hb1n] at h; cases h
  rw [ite_eq_right hb1n] at h
  have hact : NS.active.contains ⟨decI nn, decI us, ds⟩ = false := by
    cases e : NS.active.contains ⟨decI nn, decI us, ds⟩ with
    | false => rfl
    | true => rw [e] at hb1; simp at hb1n; rw [hb1n] at hb1; exact absurd hb1 (by decide)
  -- closed?
  cases n with
  | zero => simp [dcWf, nbKeyK2] at h
  | succ n' =>
  rcases hdc : dcWf (n' + 1) m1 ctx dO dL with _ | ⟨r2, m2⟩ <;> rw [hdc] at h; · simp [nbKeyK2] at h
  rw [nbKeyK2_some] at h
  obtain ⟨bc, a2, hrun2, hS2, hg2, hr2⟩ := dcWf_ok dn fe vis (n' + 1) m1 m2 a ctx dO dL c ds r2 hdc hS1
    (hW.grow hg1).u.dec (hW.grow hg1).u.inn hhi0 ((hds.grow (OMono.decHL _ _) hg1).get (OMono.decHL _ _))
    (fun j hj => by have := hg1.1; omega)
  have hg12 := hg1.trans hg2
  have hP2 : PosMR m2 := (hP.fr (posRecW_mfr hk)).fr (dcWf_mfr hdc)
  have hA2 : AbsOK m2 := dcWf_afr hdc (posRecW_afr hk hA)
  have hrun2' : (ds.allM fun x => do
      let b ← fvarB coreWalkFuel x
      pure (decide (b ≤ c.hiAt 0))).run a = .ok (bc, a2) := hrun2
  obtain ⟨p2, -⟩ := ConRon.Bridge.Inductives.closedAll_spec (c.hiAt 0) ds dsP a a2 bc hC.check.state hdsP hrun2'
  have hC2 : StageC dn vis fe env m2 a2 := hC.of_pstep hS2 hA2 p2
  have c2 := p2.toCore hC.check
  -- the frame, when not cached
  have hnew : ∀ (rr : List Word) (mm : Mem),
      nbAppK6 (nbNewW (realCall p) (n' + 1) m2 vis ctx fu po pl kb nn us dO dL nPc cty ns) = some (rr, mm) →
      ∃ x a', (nestContNew V fe c fu.toNat prog kb.toNat (decI nn) (decI us) ds nPc.toNat (decI cty) NS).run a2 =
          .ok (x, a') ∧ StageC dn vis fe env mm a' ∧ IWGrow m2 mm ∧ decNFK (rr.headD 0) = some x.1 ∧
        NSB mm (rr.tail.headD 0) x.2 ∧ PosMR mm ∧ AbsOK mm ∧ ConRon.Bridge.CoreStep V env fe a a' := by
    intro rr mm hh
    rcases hn : nbNewW (realCall p) (n' + 1) m2 vis ctx fu po pl kb nn us dO dL nPc cty ns with _ | ⟨r3, m3⟩ <;> rw [hn] at hh; · simp [nbAppK6] at hh
    rw [nbAppK6_some] at hh
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hh)
    obtain ⟨x, a', hrun, hC3, hg3, hk3, hns3, hP3, hA3, c3⟩ := hNew m2 m3 a2 ctx fu po pl kb nn us dO dL nPc cty ns c
      prog ds NS r3 ctxP progP nP usP dsP ctyP nsP hn hC2 (hW.grow hg12) hnn hus (hds.grow (OMono.decHL _ _) hg12)
      (by have := hg12.1; omega) hcty (hns.grow hg12 htop) hP2 hA2 hc (dCtx_ext _ p2.ext _ _ hctx)
      (dProg_ext p2.ext _ _ hprog) (ConRon.Bridge.denoteN_ext hnP p2.ext) (ConRon.Bridge.denoteLs_ext husP p2.ext)
      (ConRon.Bridge.denoteEList_ext p2.ext _ _ hdsP) (ConRon.Bridge.denote_ext hctyP p2.ext)
      (dState_ext p2.ext _ _ hnsP) hwds hni
    exact ⟨x, a', hrun, hC3, hg3, by simpa using hk3, by simpa using hns3, hP3, hA3, c2.trans c3⟩
  have htwin : (nestContKey V fe c fu.toNat prog kb.toNat (decI nn) (decI us) ds nPc.toNat (decI cty) NS).run a =
      (if bc && NS.keys.contains ⟨decI nn, decI us, ds⟩ then pure (NestFieldKind.nested (kb.toNat != 0), NS)
       else nestContNew V fe c fu.toNat prog kb.toNat (decI nn) (decI us) ds nPc.toNat (decI cty) NS).run a2 := by
    simp only [ConRon.Arena.nestContKey.eq_def, hact, Bool.false_eq_true, ite_false, StateT.run_bind, hrun2', except_ok_bind]
  by_cases hr2n : r2.headD 0 ≠ 0
  · rw [ite_eq_left hr2n] at h
    have hbc : bc = true := by cases bc <;> simp_all
    subst hbc
    rw [pos2_rd_grow hg12 (by omega), pos2_ns_rd hg12 hp6 htop 1 (by decide)] at h
    rcases hc2 : nkcW (n' + 1) m2 (rdW (m.arr64 IW) ns) (rdW (m.arr64 IW) (ns + 1)) key with _ | b2 <;> rw [hc2] at h; · cases h
    simp only at h
    have hb2 := nkcW_ok key _ (n' + 1) m2 _ _ b2 NS.keys.toList hc2 (hk0.grow hg12) (hK.grow (decNK_mono _) hg2)
      (Nat.lt_of_le_of_lt hS2.2.1 hS2.2.2.2.1)
    by_cases hb2n : b2 ≠ 0
    · rw [ite_eq_left hb2n] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have hin : NS.keys.contains ⟨decI nn, decI us, ds⟩ = true := by
        rw [← Array.contains_toList]
        cases e : NS.keys.toList.contains ⟨decI nn, decI us, ds⟩ with
        | true => rfl
        | false => rw [e] at hb2; exact absurd hb2 (by simpa using hb2n)
      refine ⟨(NestFieldKind.nested (kb.toNat != 0), NS), a2, by rw [htwin]; simp [hin]; rfl, hC2, hg12,
        by simpa using decNFK_nestedW kb, by simpa using hns.grow hg12 htop, hP2, hA2, c2⟩
    · rw [ite_eq_right hb2n] at h
      have hout : NS.keys.contains ⟨decI nn, decI us, ds⟩ = false := by
        rw [← Array.contains_toList]
        cases e : NS.keys.toList.contains ⟨decI nn, decI us, ds⟩ with
        | false => rfl
        | true => rw [e] at hb2; simp at hb2n hb2; rw [hb2n] at hb2; exact absurd hb2 (by decide)
      obtain ⟨x, a', hrun, rest⟩ := hnew r m' h
      exact ⟨x, a', by rw [htwin]; simpa [hout] using hrun, rest.1, hg12.trans rest.2.1, rest.2.2⟩
  · rw [ite_eq_right hr2n] at h
    have hbc : bc = false := by cases bc <;> simp_all
    subst hbc
    obtain ⟨x, a', hrun, rest⟩ := hnew r m' h
    exact ⟨x, a', by rw [htwin]; simpa using hrun, rest.1, hg12.trans rest.2.1, rest.2.2⟩

end steps

end L.Ind
