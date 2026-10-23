import ConAgua.Arena.IndT.PosKey

/-!
# `nest_cont` under `StageC` (lane `indstaget`, helper `indstaget-pos`)

`contOK_step`'s proof (`IndPos2SpecS`) with the twin side of con-ron's `nestCont_spec`: the
container (`nestContainer_spec`), the parameters' locality (`paramsLocal_spec`; the index checks
and `Quot`'s pin leave the state), the instantiation's former (`nestInstType_spec`), the
instantiation met (the block's `KeyOKC` at `n`).
-/

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

open ConRon.Arena
open ConRon.Bridge.Inductives (PStep dCtx dProg dState dCtx_ext dProg_ext dState_ext kindOf)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section steps
variable (p : Prog) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) {env : ConLeche.Env}

theorem contOKC_step (n : Nat) (hk : n + 1 ≤ coreWalkFuel) (ih : NbOKC p dn vis fe env n) :
    ContOKC p dn vis fe env (n + 1) := by
  obtain ⟨-, -, -, -, hKey, -, -, -, -, -, -⟩ := ih
  intro m m' a ctx fu po pl kb nn us aO aL ns c prog args NS r ctxP progP nP usP argsP nsP dep h hC hW hnn hus
    hargs hab hns hP hA hc hctx hprog hnP husP hargsP hnsP hwargs
  have hS := hC.stage
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  obtain ⟨-, -, hfind, -, -, -⟩ := ConRon.Bridge.Inductives.dCtx_fields hctx
  have hhpP : c.hiAt prog.length = ctxP.hiAt progP.length := by
    rw [ConRon.Bridge.Inductives.hiAt_eq hctx, ConRon.Bridge.Inductives.dProg_length hprog]
  rw [nbContW_succ] at h
  cases n with
  | zero => simp [ntWf, nbContK1] at h
  | succ n' =>
  simp only [ntWf] at h
  cases hnt : ntW n' m vis nn with
  | none => rw [hnt] at h; simp [nbContK1] at h
  | some pr =>
  obtain ⟨r1, m1⟩ := pr
  rw [hnt, nbContK1_some] at h
  obtain ⟨xc, a1, hrun1, hS1, hg1, hnc⟩ := ntW_ok dn fe vis nn hnn n' m m1 a r1 hnt hS
  obtain ⟨p1, -⟩ := ConRon.Bridge.Inductives.nestContainer_spec ctxP hfind (decI nn) nP a a1 xc hC.check.state
    ⟨hC.check.ienv.toS, hnP⟩ hrun1
  cases xc with
  | none => simp only [NcOut] at hnc; rw [if_pos hnc] at h; cases h
  | some pc =>
  obtain ⟨nPc, ctors⟩ := pc
  obtain ⟨hnc0, hnc1, -, -, -⟩ := hnc
  rw [if_neg (by rw [hnc0]; decide)] at h
  have hal := decHL_length m hargs
  by_cases hlt : aL < r1.tail.headD 0
  · rw [if_pos hlt] at h; cases h
  rw [if_neg hlt] at h
  have hle : nPc ≤ args.length := by
    have : ¬ aL.toNat < (r1.tail.headD 0).toNat := fun e => hlt (UInt64.lt_iff_toNat_lt.mpr e)
    omega
  generalize hPw : r1.tail.headD 0 = nPcW at h hnc1
  have htop1 : iwTop m1 < 2 ^ 64 := Nat.lt_of_le_of_lt hS1.2.1 hS1.2.2.2.1
  have hW1 := hW.grow hg1
  have hhp : (nhiW m1 ctx pl).toNat = c.hiAt prog.length := hW1.hi htop1
  have hargs1 : decHL m1 aO.toNat aL.toNat = some args := by
    rw [decHL_agree (RdS.of_grow hg1) (fun j hj => by omega)]; exact hargs
  obtain ⟨hds, hidx⟩ := pos2_decHL_split hargs1 (show nPcW.toNat ≤ aL.toNat by omega)
  have hab1 : aO.toNat + aL.toNat ≤ iwTop m1 := by have := hg1.1; omega
  have hPle : nPcW.toNat ≤ aL.toNat := by omega
  have hiO : (aO + nPcW).toNat = aO.toNat + nPcW.toNat := word_add_toNat (by omega)
  have hiL : (aL - nPcW).toNat = aL.toNat - nPcW.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega))]
  -- the checks
  cases hcc : p2ccW (n' + 1) m1 ctx (nhiW m1 ctx pl) nn aO nPcW (aO + nPcW) (aL - nPcW) with
  | none => rw [hcc] at h; simp [nbContK2] at h
  | some pr2 =>
  obtain ⟨r2, m2⟩ := pr2
  rw [hcc, nbContK2_some] at h
  obtain ⟨-, q, a2, hrun2a, hrun2q, hq, hrun2c, -, hS2, hg2, hP2⟩ := p2ccW_ok dn vis fe (by omega) hcc hS1 hW1.u hds
    (fun j hj => by omega) (by rw [hiO, hiL]; exact hidx) (fun j hj => by rw [hiO, hiL] at *; omega) hnn
    (hP.fr (ntWf_mfr (k := n' + 1) (by simpa [ntWf] using hnt)))
  have hA2 : AbsOK m2 := p2ccW_afr hcc (ntWf_afr (k := n' + 1) (by simpa [ntWf] using hnt) hA)
  have hargsT1 := ConRon.Bridge.Inductives.denoteEList_take
    (ConRon.Bridge.denoteEList_ext p1.ext _ _ hargsP) nPcW.toNat
  obtain ⟨p2, hpc⟩ := ConRon.Bridge.Inductives.paramsLocal_spec (nhiW m1 ctx pl).toNat _ _ a1 a2 true p1.ok
    hargsT1 hrun2c
  simp only [ConRon.Bridge.Inductives.RV] at hpc
  have hdsT : ∀ d ∈ List.take nPcW.toNat argsP, ConLeche.Expr.WScoped (ctxP.hiAt progP.length) d := by
    intro d hd
    have h1 := List.all_eq_true.mp hpc.symm d hd
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h1
    rw [← hhpP, ← hhp]
    exact ConLeche.WScoped.of_fvarsBelow (hwargs d (List.mem_of_mem_take hd)) (ConLeche.Expr.fvarB_le h1.2)
  have p12 := p1.trans p2
  have c2 := p12.toCore hC.check
  -- the instantiation's former
  cases hk4 : posRecW m2 [nn, us, aO, nPcW] with
  | none => rw [hk4] at h; simp [nbContK3] at h
  | some pr3 =>
  obtain ⟨key, m3⟩ := pr3
  rw [hk4, nbContK3_some] at h
  obtain ⟨hS3, hg3, hkq, ht3, hget3⟩ := posRecW_stage hk4 hS2 (by simp)
  simp only [List.length_cons, List.length_nil] at ht3
  have hg13 := hg1.trans (hg2.trans hg3)
  have hab3 : aO.toNat + aL.toNat ≤ iwTop m3 := by have := (hg2.trans hg3).1; omega
  have htop3 : iwTop m3 < 2 ^ 64 := Nat.lt_of_le_of_lt hS3.2.1 hS3.2.2.2.1
  have hdsB : DecB (fun m => (decHL m aO.toNat nPcW.toNat : Option (List EIdx))) m3 (args.take nPcW.toNat) :=
    decHL_decB (by rw [decHL_agree (RdS.of_grow (hg2.trans hg3)) (fun j hj => by omega)]; exact hds)
      (by have := (hg2.trans hg3).1; omega)
  have hK : DecB (fun m => decNK m key.toNat) m3 ⟨decI nn, decI us, args.take nPcW.toNat⟩ :=
    pos2_key_rec hnn hus (by omega) hget3 hdsB
  obtain ⟨hKd, hKin⟩ := pos2_nk_in hK
  simp only [nitWf] at h
  cases hni : nitW n' m3 vis ctx (nhiW m1 ctx pl) key with
  | none => rw [hni] at h; simp [nbContK4] at h
  | some pr4 =>
  obtain ⟨r4, m4⟩ := pr4
  rw [hni, nbContK4_some] at h
  have hksl : NKSl m3 key := by
    unfold NKSl
    rw [pos2_rd_get (by simpa using hget3 2 (by simp)) (by simp; omega),
      pos2_rd_get (by simpa using hget3 3 (by simp)) (by simp; omega)]
    have := (hg2.trans hg3).1; omega
  obtain ⟨xi, a4, hrun4, hS4, hg4, hni0, hctyH, hctyd, hP4⟩ := nitW_ok n' dn fe vis ctx (nhiW m1 ctx pl)
    (c.hiAt prog.length) hhp c m3 m4 a2 key _ r4 hni hS3 ((hW1.grow (hg2.trans hg3)).u) hKd hKin hksl
    (hP2.fr (posRecW_mfr hk4))
  have hA4 : AbsOK m4 := nitW_afr hni (posRecW_afr hk4 hA2)
  have hx02 := p12.ext
  obtain ⟨c4, niP, ⟨-, hni2, hni3⟩, -⟩ := ConRon.Bridge.Inductives.nestInstType_spec hc c (c.hiAt prog.length)
    ⟨decI nn, decI us, args.take nPcW.toNat⟩ ⟨nP, usP, argsP.take nPcW.toNat⟩ a2 a4 xi c2.ok
    ⟨dCtx_ext _ hx02 _ _ hctx, by simp [ConRon.Bridge.Inductives.dKey, ConRon.Bridge.denoteN_ext hnP hx02,
      ConRon.Bridge.denoteLs_ext husP hx02,
      ConRon.Bridge.Inductives.denoteEList_take (ConRon.Bridge.denoteEList_ext hx02 _ _ hargsP) nPcW.toNat]⟩
    hrun4
  have c24 := c2.trans c4
  have hx04 := c24.ext
  have hC4 : StageC dn vis fe env m4 a4 := hC.of_cstep hS4 hA4 c24
  by_cases hne : aL ≠ nPcW + r4.headD 0
  · rw [if_pos hne] at h; cases h
  rw [if_neg hne] at h
  have heq : args.length = nPc + xi.1 := by
    have := (pos2_len_eq (nI := r4.headD 0) (show nPcW.toNat ≤ aL.toNat by omega)).mp (by simpa using hne)
    omega
  -- the instantiation met
  cases hky : nbKeyW (realCall p) (n' + 1) m4 vis ctx fu po pl kb nn us aO nPcW nPcW (r4.tail.headD 0) ns with
  | none => rw [hky] at h; simp [nbAppK6] at h
  | some pr5 =>
  obtain ⟨r5, m5⟩ := pr5
  rw [hky, nbAppK6_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hg14 := hg13.trans hg4
  obtain ⟨x, a', hrun5, hC5, hg5, hk5, hns5, hP5, hA5, c5⟩ := hKey m4 m5 a4 ctx fu po pl kb nn us aO nPcW nPcW
    (r4.tail.headD 0) ns c prog (args.take nPcW.toNat) NS r5 ctxP progP nP usP (argsP.take nPcW.toNat) niP.2 nsP
    hky hC4 (hW.grow hg14) hnn hus (hdsB.grow (OMono.decHL _ _) hg4) (by have := hg14.1; omega) hctyH
    (hns.grow hg14 htop) hP4 hA4 hc (dCtx_ext _ hx04 _ _ hctx) (dProg_ext hx04 _ _ hprog)
    (ConRon.Bridge.denoteN_ext hnP hx04) (ConRon.Bridge.denoteLs_ext husP hx04)
    (ConRon.Bridge.Inductives.denoteEList_take (ConRon.Bridge.denoteEList_ext hx04 _ _ hargsP) nPcW.toNat)
    (by rw [hctyd]; exact hni2) (dState_ext hx04 _ _ hnsP) hdsT hni3
  refine ⟨x, a', ?_, hC5, hg14.trans hg5, by simpa using hk5, by simpa using hns5, hP5, hA5, c24.trans c5⟩
  rw [hnc1] at hrun2a hrun2c hrun4 hrun5
  rw [hhp] at hrun2a hrun2c
  rw [hctyd] at hrun5
  have hpc' : ((args.take nPc).allM fun x => do
      let bb ← bvarB coreWalkFuel x
      if bb != 0 then pure false
      else do
        let fb ← fvarB coreWalkFuel x
        pure (decide (fb ≤ c.hiAt prog.length))).run a1 = .ok (true, a2) := hrun2c
  have hlt' : ¬ args.length < nPc := by omega
  rw [ConRon.Arena.nestCont.eq_def]
  simp only [StateT.run_bind, hrun1, except_ok_bind, hlt', ite_false, hrun2a, Bool.false_eq_true, hrun2q, hq,
    hpc', Bool.not_true, hrun4]
  simp only [heq, bne_self_eq_false, Bool.false_eq_true, ite_false]
  exact hrun5

end steps

end L.Ind
