import ConAgua.Verdict.PosE1L
import ConAgua.Verdict.PosNty

/-!
# `nest_cont` under `StageC` (lane `indstaget`, helper `indstaget-pos`)

`contOK_step`'s proof (`IndPosSpec/Pos2DecHLSplit`) with the twin side of con-ron's `nestCont_spec`: the
container (`nestContainer_spec`), the parameters' locality (`paramsLocal_spec`; the index checks
and `Quot`'s pin leave the state), the instantiation's former (`nestInstType_spec`), the
instantiation met (the block's `KeyOKC` at `n`).
-/


open ConRon.Arena
open ConRon.Bridge.Inductives (PStep dCtx dProg dState dCtx_ext dProg_ext dState_ext kindOf)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section steps
variable (p : Prog) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) {env : ConLeche.Env}

theorem contOKC_step (hL : NbLook p) (hIlpf : IlpfF p) (hcl : CoreStageClosed p) (hLC : LvlCacheProg p) (n : Nat) (ih : NbOKC p dn vis fe env n) : ContOKC p dn vis fe env (n + 1) := by
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
  rcases hnt : ntW n' m vis nn with _ | ⟨r1, m1⟩ <;> rw [hnt] at h; · simp [nbContK1] at h
  rw [nbContK1_some] at h
  obtain ⟨xc, a1, hrun1, hS1, hg1, hnc⟩ := ntW_ok dn fe vis nn hnn n' m m1 a r1 hnt hS
  obtain ⟨p1, -⟩ := ConRon.Bridge.Inductives.nestContainer_spec ctxP hfind (decI nn) nP a a1 xc hC.check.state
    ⟨hC.check.ienv.toS, hnP⟩ hrun1
  cases xc with
  | none => simp only [NcOut] at hnc; rw [ite_eq_left hnc] at h; cases h
  | some pc =>
  obtain ⟨nPc, ctors⟩ := pc
  obtain ⟨hnc0, hnc1, -, -, -⟩ := hnc
  rw [ite_eq_right (by rw [hnc0]; decide)] at h
  have hal := decHL_length m hargs
  by_cases hlt : aL < r1.tail.headD 0
  · rw [ite_eq_left hlt] at h; cases h
  rw [ite_eq_right hlt] at h
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
  rcases hcc : nccR (realCall p) (n' + 1) m1 ctx (nhiW m1 ctx pl) nn aO nPcW (aO + nPcW) (aL - nPcW) with _ | ⟨r2, m2⟩ <;> rw [hcc] at h; · simp [nbContK2] at h
  rw [nbContK2_some] at h
  obtain ⟨s2, hs2, -, -, a2, -, hR2⟩ := RefE.run_okW (nccE_spec p hL (n' + 1) ⟨m1, Locals.init []⟩ _ _ _ _ _ _ _)
    (ncc_ref (dO := aO) (dL := nPcW) (iO := aO + nPcW) (iL := aL - nPcW) dn vis fe hS1 hW1.u hds (fun j hj => by dsimp only; omega) (by rw [hiO, hiL]; exact hidx)
      (fun j hj => by dsimp only; rw [hiO, hiL] at *; omega) hnn (hP.fr (ntWf_mfr (k := n' + 1) (by simpa [ntWf] using hnt)))) hcc
  rw [hs2] at hR2; dsimp only at hR2
  obtain ⟨hrun2a, ⟨q, hrun2q, hq⟩, hrun2c, hS2, hg2, hP2, hA2⟩ := hR2
  replace hA2 : AbsOK m2 := hA2 (ntWf_afr (k := n' + 1) (by simpa [ntWf] using hnt) hA)
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
  rcases hk4 : posRecW m2 [nn, us, aO, nPcW] with _ | ⟨key, m3⟩ <;> rw [hk4] at h; · simp [nbContK3] at h
  rw [nbContK3_some] at h
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
  rcases hni : nitW (realCall p) n' m3 vis ctx (nhiW m1 ctx pl) key with _ | ⟨r4, m4⟩ <;> rw [hni] at h; · simp [nbContK4] at h
  rw [nbContK4_some] at h
  have hksl : NKSl m3 key := by
    unfold NKSl
    rw [pos2_rd_get (by simpa using hget3 2 (by simp)) (by simp; omega),
      pos2_rd_get (by simpa using hget3 3 (by simp)) (by simp; omega)]
    have := (hg2.trans hg3).1; omega
  have hA3 : AbsOK m3 := posRecW_afr hk4 hA2
  have hC3 : StageC dn vis fe env m3 a2 := hC.of_pstep hS3 hA3 p12
  have hx02 := p12.ext
  have hkey2 : ConRon.Bridge.Inductives.dKey a2.store ⟨decI nn, decI us, args.take nPcW.toNat⟩ =
      some ⟨nP, usP, argsP.take nPcW.toNat⟩ := by
    simp [ConRon.Bridge.Inductives.dKey, ConRon.Bridge.denoteN_ext hnP hx02,
      ConRon.Bridge.denoteLs_ext husP hx02,
      ConRon.Bridge.Inductives.denoteEList_take (ConRon.Bridge.denoteEList_ext hx02 _ _ hargsP) nPcW.toNat]
  obtain ⟨xi, a4, hrun4, hS4, hg4, hni0, hctyH, hctyd, hP4, -, hA4⟩ := nitW_ok n' dn fe vis ctx (nhiW m1 ctx pl)
    (c.hiAt prog.length) hhp c m3 m4 a2 key _ r4 (realCall p) (nty_ok hL.nit.ty (IlpRd.realC hIlpf hC3)) _
    (nitLe_realC hcl hLC n' _ _ key c _ hC3 hA3 (dCtx_ext _ hx02 _ _ hctx) hkey2) hni hS3
    ((hW1.grow (hg2.trans hg3)).u) hKd hKin hksl (hP2.fr (posRecW_mfr hk4))
  obtain ⟨c4, niP, ⟨-, hni2, hni3⟩, -⟩ := ConRon.Bridge.Inductives.nestInstType_spec hc c (c.hiAt prog.length)
    ⟨decI nn, decI us, args.take nPcW.toNat⟩ ⟨nP, usP, argsP.take nPcW.toNat⟩ a2 a4 xi c2.ok
    ⟨dCtx_ext _ hx02 _ _ hctx, hkey2⟩ hrun4
  have c24 := c2.trans c4
  have hx04 := c24.ext
  have hC4 : StageC dn vis fe env m4 a4 := hC.of_cstep hS4 hA4 c24
  by_cases hne : aL ≠ nPcW + r4.headD 0
  · rw [ite_eq_left hne] at h; cases h
  rw [ite_eq_right hne] at h
  have heq : args.length = nPc + xi.1 := by
    have := (pos2_len_eq (nI := r4.headD 0) (show nPcW.toNat ≤ aL.toNat by omega)).mp (by simpa using hne)
    omega
  -- the instantiation met
  rcases hky : nbKeyW (realCall p) (n' + 1) m4 vis ctx fu po pl kb nn us aO nPcW nPcW (r4.tail.headD 0) ns with _ | ⟨r5, m5⟩ <;> rw [hky] at h; · simp [nbAppK6] at h
  rw [nbAppK6_some] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
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
