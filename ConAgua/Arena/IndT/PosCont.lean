import ConAgua.Arena.IndT.PosDefs
import ConAgua.Arena.IndT.PosNit
import ConAgua.Arena.IndT.RecGen19
import ConAgua.Arena.IndPosSpec.Pos2DecHLSplit

/-!
# `nest_cont` under `StageC` (lane `indstaget`, helper `indstaget-pos`)

`contOK_step`'s proof (`IndPos2SpecS`) with the twin side of con-ron's `nestCont_spec`: the
container (`nestContainer_spec`), the parameters' locality (`paramsLocal_spec`; the index checks
and `Quot`'s pin leave the state), the instantiation's former (`nestInstType_spec`), the
instantiation met (the block's `KeyOKC` at `n`).
-/


open ConRon.Arena
open ConRon.Bridge.Inductives (PStep dCtx dProg dState dCtx_ext dProg_ext dState_ext kindOf)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- `cpW_ok` with no exec-fuel bound (its walks run at `CWF`: `bvbW_stageW`'s first case). -/
theorem cpW_okW (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis hp : Word) (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (dO dL : Word) (ds : List EIdx) (r : List Word),
    cpW n m hp dO dL = some (r, m') → StageR dn vis fe m a →
    decHL m dO.toNat dL.toNat = some ds → (∀ j < dL.toNat, dO.toNat + j < iwTop m) →
    ∃ b a', (ds.allM (pcF hp.toNat)).run a = .ok (b, a') ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧
      r.headD 0 = (if b then 1 else 0) := by
  induction n with
  | zero => intro m m' a dO dL ds r h; simp [cpW] at h
  | succ n ih =>
    intro m m' a dO dL ds r h hS hds hin
    by_cases hl0 : dL = 0
    · rw [cpW_nil (h := hl0)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      subst hl0
      have : ds = [] := by simpa [decHL, hslice?] using hds.symm
      subst this
      exact ⟨true, a, rfl, hS, IWGrow.refl _, rfl⟩
    rw [cpW_cons (h := hl0)] at h
    have hl : dL.toNat ≠ 0 := fun e => hl0 (UInt64.toNat_inj.mp (by simpa using e))
    obtain ⟨l', hl'⟩ : ∃ l', dL.toNat = l' + 1 := ⟨dL.toNat - 1, by omega⟩
    have hds' := hds
    simp only [decHL, hl', hslice?_succ, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hds'
    obtain ⟨x, hx, xs, hxs, rfl⟩ := hds'
    obtain ⟨hxH, hxd⟩ := rd_iwH0E (m := m) (o := dO) (k := IdxKind.expr) (by simpa [iwH, iwA] using hx)
    have hdO1 : (dO + 1).toNat = dO.toNat + 1 :=
      word_add_toNat (show dO.toNat + 1 < 2 ^ 64 by have := hin 0 (by omega); have := hS.2.1; have := hS.2.2.2.1; omega)
    have hl1 : (dL - 1).toNat = l' := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
    rw [List.allM_cons]
    rcases hb : bvbW n m (rdW (m.arr64 IW) dO) CWF with _ | ⟨bb, m1⟩ <;> rw [hb] at h; · simp [cpK1] at h
    obtain ⟨a1, hrun1, hS1, hg1, -⟩ := bvbW_stageW dn vis fe hS n coreWalkFuel CWF (.inl (Nat.le_of_eq CWF_eq)) _ bb hxH hb
    rw [decE_eq, hxd] at hrun1
    by_cases hbb : bb ≠ 0
    · rw [cpK1_b (h := hbb)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      refine ⟨false, a1, ?_, hS1, hg1, rfl⟩
      have : (bb.toNat != 0) = true := by
        simp only [bne_iff_ne, ne_eq]; intro h0; exact hbb (UInt64.toNat_inj.mp (by simpa using h0))
      simp only [pcF, StateT.run_bind, hrun1, except_ok_bind, this, ite_true]
      rfl
    rw [cpK1_ok (h := hbb)] at h
    have hbb0 : (bb.toNat != 0) = false := by simp at hbb; simp [hbb]
    have hrd1 : rdW (m1.arr64 IW) dO = rdW (m.arr64 IW) dO := by
      simp only [rdW]; rw [hg1.2.2.1 _ (by simpa using hin 0 (by omega))]
    rw [hrd1] at h
    rcases hst : fvbF m1 [CWF, rdW (m.arr64 IW) dO] with _ | ⟨r2, m2⟩ <;> rw [hst] at h; · simp [cpK2] at h
    obtain ⟨k, a2, hrun2, hS2, hg2, hk⟩ := fvbF_ok dn vis fe CWF _ hxH _ _ a1 r2 hst hS1
    rw [CWF_eq, hxd] at hrun2
    simp only [decW0Nat] at hk
    by_cases hc : hp < r2.headD 0
    · rw [cpK2_out (h := hc)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have hgt : ¬ k ≤ hp.toNat := by have := UInt64.lt_iff_toNat_lt.mp hc; omega
      refine ⟨false, a2, ?_, hS2, hg1.trans hg2, rfl⟩
      simp only [pcF, StateT.run_bind, hrun1, except_ok_bind, hbb0, Bool.false_eq_true, ite_false,
        hrun2, hgt, decide_false]
      rfl
    rw [cpK2_in (h := hc)] at h
    have hle : k ≤ hp.toNat := by
      have : ¬ hp.toNat < (r2.headD 0).toNat := fun e => hc (UInt64.lt_iff_toNat_lt.mpr e)
      omega
    have hg12 := hg1.trans hg2
    obtain ⟨b, a', hrun, hS', hg', hr⟩ := ih m2 m' a2 (dO + 1) (dL - 1) xs r h hS2
      (by rw [hdO1, hl1, ← hxs, decHL]; exact decHL_agree (RdS.of_grow hg12) (fun j hj => by
            have := hin (j + 1) (by omega); simp only [decHL] at *; omega))
      (fun j hj => by rw [hdO1, hl1] at *; have := hin (j + 1) (by omega); have := hg12.1; omega)
    refine ⟨b, a', ?_, hS', hg12.trans hg', hr⟩
    simp only [pcF, StateT.run_bind, hrun1, except_ok_bind, hbb0, Bool.false_eq_true, ite_false,
      hrun2, hle, decide_true]
    exact hrun

/-- `p2ccW_ok` with no exec-fuel bound. -/
theorem p2ccW_okW (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    {k : Nat} {m m' : Mem} {a : AState} {ctx hp nn dO dL iO iL : Word}
    {c : NestCtx} {ds idx : List EIdx} {r : List Word}
    (h : p2ccW k m ctx hp nn dO dL iO iL = some (r, m')) (hS : StageR dn vis fe m a)
    (hU : UCtx dn vis fe m ctx c) (hds : decHL m dO.toNat dL.toNat = some ds)
    (hdsb : ∀ j < dL.toNat, dO.toNat + j < iwTop m) (hidx : decHL m iO.toNat iL.toNat = some idx)
    (hidxb : ∀ j < iL.toNat, iO.toNat + j < iwTop m) (hnH : H nn) (hP : PosMR m) :
    ∃ a1 q a2, (idx.anyM (fun x => ConRon.Arena.nestOcc c.names c.nP hp.toNat x)).run a = .ok (false, a) ∧
      pinQuot.run a = .ok (q, a) ∧ (decI nn == q) = false ∧
      (ds.allM (pcF hp.toNat)).run a = .ok (true, a2) ∧ a1 = a ∧ StageR dn vis fe m' a2 ∧ IWGrow m m' ∧
      PosMR m' := by
  cases k with
  | zero => simp [p2ccW] at h
  | succ k =>
  simp only [p2ccW] at h
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  obtain ⟨hn, -, -, -, hnP, -⟩ := ctx_fields hU.dec hU.inn htop
  have hne := ctx_names_end hU.dec hU.inn hU.sl htop
  rcases hoa : noaW k m (rdW (m.arr64 IW) ctx) (rdW (m.arr64 IW) (ctx + 1)) (rdW (m.arr64 IW) (ctx + 4)) hp iO iL with _ | ⟨r1, m1⟩ <;> rw [hoa] at h; · simp [p2ccK1] at h
  rw [p2ccK1_eq] at h
  obtain ⟨b, hrunoa, hS1, hg1, hr1, hP1⟩ := noaW_ok dn fe vis _ _ _ _ c.names k m m1 a _ _ idx r1 hoa hS
    hn hne hidx hidxb hP
  rw [hnP] at hrunoa
  cases b with
  | true => rw [ite_eq_left (by rw [hr1]; decide)] at h; cases h
  | false =>
  rw [ite_eq_right (by rw [hr1]; decide)] at h
  rcases hq : pos2PinW m1 47 with _ | ⟨rq, m2⟩ <;> rw [hq] at h; · cases h
  simp only at h
  obtain ⟨hm2, hqH, hqrun⟩ := pos2PinW_ok hq hS1.1.pins
  subst m2
  by_cases hnq : nn = rq.headD 0
  · rw [ite_eq_left hnq] at h; cases h
  rw [ite_eq_right hnq] at h
  rcases hcp : cpW k m1 hp dO dL with _ | ⟨r3, m3⟩ <;> rw [hcp] at h; · simp [p2ccK2] at h
  obtain ⟨b3, a3, hrun3, hS3, hg3, hr3⟩ := cpW_okW dn fe vis hp k m1 m3 a dO dL ds r3 hcp hS1
    (by rw [decHL_agree (RdS.of_grow hg1) (fun j hj => hdsb j hj)]; exact hds)
    (fun j hj => by have := hdsb j hj; have := hg1.1; omega)
  cases b3 with
  | false => rw [p2ccK2_z (h := by rw [hr3]; rfl)] at h; cases h
  | true =>
  rw [p2ccK2_nz (h := by rw [hr3]; decide)] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  have hpq : pinQuot = pinAt 47 := rfl
  refine ⟨a, decI (rq.headD 0), a3, hrunoa, by rw [hpq]; simpa using hqrun, ?_, hrun3, rfl, hS3, hg1.trans hg3,
    hP1.fr (cpW_mfr _ _ _ _ _ _ _ hcp)⟩
  rw [decI_beq' _ _ hnH hqH]; simpa using hnq

section steps
variable (p : Prog) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) {env : ConLeche.Env}

theorem contOKC_step (hIlpf : IlpfF p) (hcl : CoreStageClosed p) (hLC : LvlCacheProg p) (n : Nat) (ih : NbOKC p dn vis fe env n) : ContOKC p dn vis fe env (n + 1) := by
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
  rcases hcc : p2ccW (n' + 1) m1 ctx (nhiW m1 ctx pl) nn aO nPcW (aO + nPcW) (aL - nPcW) with _ | ⟨r2, m2⟩ <;> rw [hcc] at h; · simp [nbContK2] at h
  rw [nbContK2_some] at h
  obtain ⟨-, q, a2, hrun2a, hrun2q, hq, hrun2c, -, hS2, hg2, hP2⟩ := p2ccW_okW dn vis fe hcc hS1 hW1.u hds
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
    (c.hiAt prog.length) hhp c m3 m4 a2 key _ r4 (realCall p) (IlpRd.realC hIlpf hC3) (IlpFr.real hIlpf) _
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
