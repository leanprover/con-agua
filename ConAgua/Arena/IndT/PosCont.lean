module

public import ConAgua.Verdict.PosE
import ConAgua.Arena.IndPosSpec.Pos2DecHLSplit
import ConAgua.Arena.IndPosSpec.Snoc
import ConAgua.Verdict.PosE1L
import ConAgua.Verdict.PosE1N
public import ConAgua.Verdict.PosFt
import ConAgua.Arena.IndT.PosFields
import ConAgua.Arena.IndPosSpec.NestCrest
import ConAgua.Arena.IndRealAbsPos
import ConAgua.Arena.RefWalk
import ConAgua.Checker.NoVerdictTree
import ConRon.Bridge.Inductives.PosWalks
public import ConAgua.Arena.IndRealIlpL
import ConLeche.Verify.Cached.Erase
import ConAgua.Arena.IndPosSpec.CfW

@[expose] public section

/-!
# `nest_cont` under `StageC` (lane `indstaget`, helper `indstaget-pos`)

`contRef_step`: `nest_cont` refines `nestCont`, both outcomes (`ncE`, unified): the
container (`nestContainer_spec`), the parameters' locality (`paramsLocal_spec`; the index checks
and `Quot`'s pin leave the state), the instantiation's former (`nestInstType_spec`), the
instantiation met (the block's `KeyRef` at `n`); the instantiation by `nit_ref` (both halves
through the run).
-/


open ConRon.Arena
open ConRon.Bridge.Inductives (PStep dCtx dProg dState dCtx_ext dProg_ext dState_ext kindOf)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section steps
variable (p : Prog) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) {env : ConLeche.Env}

theorem contRef_step (L : NbLook p) (hq : KnotStageProg p) (hIlpf : IlpfF p) (hLC : LvlCacheProg p)
    (hF : FtProg p) (henv : ConLeche.EnvWF env) (n : Nat) (hn : n ≤ 2 ^ 62)
    (ih : NbRef p dn vis fe env n) : ContRef p dn vis fe env (n + 1) := by
  intro m a ctx fu po pl kb nn us aO aL ns c prog args NS ctxP progP nP usP argsP nsP dep hC hW hnn hus
    hargs hab hns hP hA hc hctx hprog hnP husP hargsP hnsP hwargs
  have hcl := hq.closed
  rw [ncE.arm1]
  have R := L.ct.cr.rx
  have hS := hC.stage
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.iw.iw hS.iw.iwSize
  obtain ⟨-, -, hfind, -, -, -⟩ := ConRon.Bridge.Inductives.dCtx_fields hctx
  have hhpP : c.hiAt prog.length = ctxP.hiAt progP.length := by
    rw [ConRon.Bridge.Inductives.hiAt_eq hctx, ConRon.Bridge.Inductives.dProg_length hprog]
  -- the container
  cases h1 : callE p n "nest_container" [vis, nn] m with
  | error e1 =>
    rw [ncE.k_nest_container.eq_1]
    exact fun hG => ErrClaim.of_callE_nv hG.nv (_root_.L.Checker.nv_mem (by decide +kernel)) h1
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  obtain ⟨s1, hs1, -, hnt⟩ := triple_of_callW (nt_spec' p L.nt n ⟨m, Locals.init []⟩ vis nn) (callW_of_callE h1)
  dsimp only at hnt
  rw [hs1] at hnt
  cases n with
  | zero => simp [ntWf] at hnt
  | succ n' =>
  simp only [ntWf] at hnt
  obtain ⟨xc, a1, hrun1, hS1, hg1, hnc⟩ := ntW_ok fe vis nn hnn n' m m1 a r1 hnt hS
  obtain ⟨p1, -⟩ := ConRon.Bridge.Inductives.nestContainer_spec ctxP hfind (decI nn) nP a a1 xc hC.check.state
    ⟨hC.check.ienv.toS, hnP⟩ hrun1
  rw [ConRon.Arena.nestCont.eq_def]
  refine RefE.bind_right hrun1 ?_
  cases xc with
  | none =>
    simp only [NcOut] at hnc
    rw [ncE.k_nest_container.abort1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hnc]
    exact fun _ => ErrClaim.fail _ _ (by decide)
  | some pc =>
  obtain ⟨nPc, ctors⟩ := pc
  obtain ⟨hnc0, hnc1, -, -, -⟩ := hnc
  rw [ncE.k_nest_container.arm1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by rw [hnc0]; decide)]
  dsimp only
  have hal := decHL_length m hargs
  -- `nest_ctx_hi_at`
  cases h2 : callE p (n' + 1) "nest_ctx_hi_at" [ctx, pl] m1 with
  | error e2 =>
    rw [ncE.k_nest_ctx_hi_at.eq_1]
    exact fun hG => ErrClaim.of_callE_nv hG.nv (_root_.L.Checker.nv_mem (by decide +kernel)) h2
  | ok q2 =>
  obtain ⟨rh, mh⟩ := q2
  obtain ⟨s2, hs2, -, hmh, hrh⟩ := triple_of_callW (nestCtxHiAt_specE p R.hi (n' + 1) ⟨m1, Locals.init []⟩ ctx pl)
    (callW_of_callE h2)
  dsimp only at hmh hrh
  rw [hs2] at hmh
  rw [hmh]
  rw [ncE.k_nest_ctx_hi_at.eq_2]
  refine RefE.split (fun hlt => by have := UInt64.lt_iff_toNat_lt.mp hlt; omega)
    (fun _ => UInt64.lt_iff_toNat_lt.mpr (by omega)) (fun _ _ _ => ErrClaim.fail _ _ (by decide))
    fun hlt _ => ?_
  rw [hrh]
  generalize hPw : r1.tail.headD 0 = nPcW at hnc1 ⊢
  subst hnc1
  have htop1 : iwTop m1 < 2 ^ 64 := Nat.lt_of_le_of_lt hS1.iw.iw hS1.iw.iwSize
  have hW1 := hW.grow hg1
  have hhp : (nhiW m1 ctx pl).toNat = c.hiAt prog.length := hW1.hi htop1
  have hargs1 : decHL m1 aO.toNat aL.toNat = some args := by
    rw [decHL_agree (RdS.of_grow hg1) (fun j hj => by omega)]; exact hargs
  obtain ⟨hds, hidx⟩ := pos2_decHL_split hargs1 (show nPcW.toNat ≤ aL.toNat by omega)
  have hPle : nPcW.toNat ≤ aL.toNat := by omega
  have hab1 : aO.toNat + aL.toNat ≤ iwTop m1 := by have := hg1.iw; omega
  have hiO : (aO + nPcW).toNat = aO.toNat + nPcW.toNat := word_add_toNat (by omega)
  have hiL : (aL - nPcW).toNat = aL.toNat - nPcW.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega))]
  have hP1 : PosMR m1 := hP.fr (ntWf_mfr (k := n' + 1) (by simpa [ntWf] using hnt))
  rw [← hhp]
  -- the checks
  have hs := nccE_spec p L (n' + 1) ⟨m1, Locals.init []⟩ ctx (nhiW m1 ctx pl) nn aO nPcW (aO + nPcW) (aL - nPcW)
  have hR := ncc_ref (p := p) (k := n' + 1) (hp := nhiW m1 ctx pl) (dO := aO) (dL := nPcW) (iO := aO + nPcW) (iL := aL - nPcW) dn vis fe hS1 hW1.u hds
    (fun j hj => by omega) (by rw [hiO, hiL]; exact hidx)
    (fun j hj => by rw [hiO, hiL] at *; omega) hnn hP1
  cases h3 : callE p (n' + 1) "nest_cont_checks" [ctx, nhiW m1 ctx pl, nn, aO, nPcW, aO + nPcW, aL - nPcW] m1 with
  | error e3 =>
    rw [ncE.k_nest_cont_checks.eq_1]
    refine fun hG => ErrClaim.congr (T' := nccT c (nhiW m1 ctx pl).toNat (decI nn) (args.take nPcW.toNat)
      (args.drop nPcW.toNat) _) rfl ?_
    rw [nccT_eq]
    exact ErrClaim.bind_left (RefE.run_err hs hG.nv hG.nv hR h3)
  | ok q3 =>
  obtain ⟨r2, m2⟩ := q3
  rw [ncE.k_nest_cont_checks.arm1]
  obtain ⟨s2, hs2, -, -, a2, -, hR2⟩ := RefE.run_ok hs hR h3
  rw [hs2] at hR2; dsimp only at hR2
  obtain ⟨hrun2a, ⟨q, hrun2q, hqq⟩, hrun2c, hS2, hg2, hP2, hA2⟩ := hR2
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
  refine RefE.bind_right hrun2a (RefE.ite_neg (by simp) ?_)
  refine RefE.bind_right hrun2q (RefE.ite_neg (by simp [hqq]) ?_)
  refine RefE.bind_right hrun2c (RefE.ite_neg (by simp) ?_)
  -- the instantiation's former
  cases h4 : callE p (n' + 1) "rec4" [nn, us, aO, nPcW] m2 with
  | error e4 =>
    rw [ncE.k_rec4.eq_1]
    exact fun hG => ErrClaim.of_callE_nv hG.nv (_root_.L.Checker.nv_mem (by decide +kernel)) h4
  | ok q4 =>
  obtain ⟨rk, m3⟩ := q4
  obtain ⟨s4, hs4, -, hk4⟩ := triple_of_callW (posRec4_specW p R.ha R.h4 (n' + 1) ⟨m2, Locals.init []⟩ nn us aO nPcW)
    (callW_of_callE h4)
  dsimp only at hk4
  rw [hs4] at hk4
  rw [ncE.k_rec4.arm1]
  generalize rk.headD 0 = key at hk4 ⊢
  obtain ⟨hS3, hg3, hkq, ht3, hget3⟩ := posRecW_stage hk4 hS2 (by simp)
  simp only [List.length_cons, List.length_nil] at ht3
  have hg13 := hg1.trans (hg2.trans hg3)
  have hab3 : aO.toNat + aL.toNat ≤ iwTop m3 := by have := (hg2.trans hg3).iw; omega
  have htop3 : iwTop m3 < 2 ^ 64 := Nat.lt_of_le_of_lt hS3.iw.iw hS3.iw.iwSize
  have hdsB : DecB (fun m => (decHL m aO.toNat nPcW.toNat : Option (List EIdx))) m3 (args.take nPcW.toNat) :=
    decHL_decB (by rw [decHL_agree (RdS.of_grow (hg2.trans hg3)) (fun j hj => by omega)]; exact hds)
      (by have := (hg2.trans hg3).iw; omega)
  have hK : DecB (fun m => decNK m key.toNat) m3 ⟨decI nn, decI us, args.take nPcW.toNat⟩ :=
    pos2_key_rec hnn hus (by omega) hget3 hdsB
  obtain ⟨hKd, hKin⟩ := pos2_nk_in hK
  have hksl : NKSl m3 key := by
    unfold NKSl
    rw [pos2_rd_get (by simpa using hget3 2 (by simp)) (by simp; omega),
      pos2_rd_get (by simpa using hget3 3 (by simp)) (by simp; omega)]
    have := (hg2.trans hg3).iw; omega
  have hA3 : AbsOK m3 := posRecW_afr hk4 hA2
  have hC3 : StageC dn vis fe env m3 a2 := hC.of_pstep hS3 hA3 p12
  have hx02 := p12.ext
  have hkey2 : ConRon.Bridge.Inductives.dKey a2.store ⟨decI nn, decI us, args.take nPcW.toNat⟩ =
      some ⟨nP, usP, argsP.take nPcW.toNat⟩ := by
    simp [ConRon.Bridge.Inductives.dKey, ConRon.Bridge.denoteN_ext hnP hx02,
      ConRon.Bridge.denoteLs_ext husP hx02,
      ConRon.Bridge.Inductives.denoteEList_take (ConRon.Bridge.denoteEList_ext hx02 _ _ hargsP) nPcW.toNat]
  have hP3 : PosMR m3 := hP2.fr (posRecW_mfr hk4)
  have hsN := nitE_spec p L.nit (n' + 1) ⟨m3, Locals.init []⟩ vis ctx (nhiW m1 ctx pl) key
  have hN := nit_ref L.nit hcl hIlpf hLC hq hF henv (n' + 1) (by omega) (hi := nhiW m1 ctx pl) hC3 hA3 rfl ((hW1.grow (hg2.trans hg3)).u) hKd hKin hksl hP3
    (dCtx_ext _ hx02 _ _ hctx) hkey2
  cases h5 : callE p (n' + 1) "nest_inst_type" [vis, ctx, nhiW m1 ctx pl, key] m3 with
  | error e5 =>
    rw [ncE.k_nest_inst_type.eq_1]
    exact fun hG => ErrClaim.bind_left (RefE.run_err hsN hG.nv ⟨hG.nv, hG.whnf⟩ hN h5)
  | ok q5 =>
  obtain ⟨r4, m4⟩ := q5
  obtain ⟨s5, hs5, -, xi, a4, hrun4, hS4, hg4, hni0, hctyH, hctyd, hP4, hA4⟩ := RefE.run_ok hsN hN h5
  dsimp only at hS4 hg4 hni0 hctyH hctyd hP4 hA4
  rw [hs5] at hS4 hg4 hP4 hA4
  obtain ⟨c4, niP, ⟨-, hni2, hni3⟩, -⟩ := ConRon.Bridge.Inductives.nestInstType_spec coreSpecV henv hc c (nhiW m1 ctx pl).toNat
    ⟨decI nn, decI us, args.take nPcW.toNat⟩ ⟨nP, usP, argsP.take nPcW.toNat⟩ a2 a4 xi c2.ok
    ⟨dCtx_ext _ hx02 _ _ hctx, hkey2⟩ hrun4
  have c24 := c2.trans c4
  have hx04 := c24.ext
  have hC4 : StageC dn vis fe env m4 a4 := hC.of_cstep hS4 hA4 c24
  refine RefE.bind_right hrun4 ?_
  have hlen := pos2_len_eq (nI := r4.headD 0) (show nPcW.toNat ≤ aL.toNat by omega)
  rw [ncE.k_nest_inst_type.eq_2]
  refine RefE.split (fun hne => by grind) (fun hne => by grind) (fun _ _ _ => ErrClaim.fail _ _ (by decide))
    fun hne _ => ?_
  -- the instantiation met
  have hg14 := hg13.trans hg4
  have hs6 := nckE_spec p L.pkey (n' + 1) ⟨m4, Locals.init []⟩ vis ctx fu po pl kb nn us aO nPcW nPcW
    (r4.tail.headD 0) ns
  have hR6 := ih.key m4 a4 ctx fu po pl kb nn us aO nPcW nPcW (r4.tail.headD 0) ns c prog (args.take nPcW.toNat) NS
    ctxP progP nP usP (argsP.take nPcW.toNat) niP.2 nsP
    hC4 (hW.grow hg14) hnn hus (hdsB.grow (OMono.decHL _ _) hg4) (by have := hg14.iw; omega) hctyH
    (hns.grow hg14 htop) hP4 hA4 hc (dCtx_ext _ hx04 _ _ hctx) (dProg_ext hx04 _ _ hprog)
    (ConRon.Bridge.denoteN_ext hnP hx04) (ConRon.Bridge.denoteLs_ext husP hx04)
    (ConRon.Bridge.Inductives.denoteEList_take (ConRon.Bridge.denoteEList_ext hx04 _ _ hargsP) nPcW.toNat)
    (by rw [hctyd]; exact hni2) (dState_ext hx04 _ _ hnsP) hdsT hni3
  rw [hctyd] at hR6
  cases h6 : callE p (n' + 1) "nest_cont_key" [vis, ctx, fu, po, pl, kb, nn, us, aO, nPcW, nPcW, r4.tail.headD 0,
      ns] m4 with
  | error e6 =>
    rw [ncE.k_nest_cont_key.eq_1]
    exact fun hG => RefE.run_err hs6 True.intro hG hR6 h6
  | ok q6 =>
  obtain ⟨r6, m6⟩ := q6
  rw [ncE.k_nest_cont_key.eq_2]
  obtain ⟨s6, hs6', -, x, a', hrun5, hQ5⟩ := RefE.run_ok hs6 hR6 h6
  rw [hs6'] at hQ5
  obtain ⟨hC5, hg5, hk5, hns5, hP5, hA5, c5⟩ := hQ5
  exact RefE.ret hrun5 ⟨hC5, hg14.trans hg5, by simpa using hk5, by simpa using hns5, hP5, hA5, c24.trans c5⟩

end steps

end L.Ind
