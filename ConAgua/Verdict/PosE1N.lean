import ConAgua.Arena.IndPosSpec.NtyW
import ConAgua.Arena.IndPosSpec.Grow
import ConAgua.Verdict.PosNty
import ConAgua.Arena.IlpRdReal
import ConAgua.Arena.IndRealAbsPos
/-!
# `nest_inst_type`: one refinement for both outcomes

`nit_ref` on the unified model `nitE` (`PosE1M.lean`): `nest_inst_type_ty` by `nty_ref`, `pi_binders`,
`e_view` and `nest_occ_any` lifted, the level comparison by `lef_ref` (its error assumption
`NVAt p "lvl_eq_c"` from the no-verdict closure).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (dCtx dKey)

namespace L.Ind
open L.Arena

theorem nvAt_of {p : Prog} (hnv : closedNV p _root_.L.Checker.nvFns = true) {f : FnName}
    (hf : f ∈ _root_.L.Checker.nvFns) : NVAt p f :=
  fun n args m _ h => callE_nv hnv hf n args m h

theorem ErrClaim.of_run_eq' {α : Type} {T T' : AM α} {a a' : AState} {e : Err}
    (h : T.run a = T'.run a') (h' : ErrClaim T' a' e) : ErrClaim T a e := fun hk => by
  obtain ⟨ce, hce, hc⟩ := h' hk
  exact ⟨ce, h ▸ hce, hc⟩

/-- What `nest_inst_type` gives besides the twin's result `x` (from `m`): the stage, the growth, the
count of binders at `r[0]`, the container's type at `r[1]`, the frames, `AbsOK`. -/
structure NitPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m : Mem) (r : List Word)
    (m' : Mem) (x : Nat × EIdx) (a' : AState) : Prop where
  stage : StageR dn vis fe m' a'
  grow : IWGrow m m'
  count : (r.headD 0).toNat = x.1
  hty : H (r.tail.headD 0)
  dec : decI (r.tail.headD 0) = x.2
  pos : PosMR m'
  abs : AbsOK m'

/-- **`nest_inst_type` refines `nestInstType`, both outcomes**, under `StageC`: `nest_inst_type_ty`
(`nty_ref`), `pi_binders`, `e_view` and `nest_occ_any` (lifted), the level comparison (`lef_ref`,
under `StageC` with the context's and key's denotations). -/
theorem nit_ref {p : Prog} (L : NitLook p) (hcl : CoreStageClosed p) (hIlpf : IlpfF p) (hLC : LvlCacheProg p)
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env} (k : Nat) {m : Mem}
    {a : AState} {ctx hi key : Word} {HI : Nat} {c : NestCtx} {kk : NestKey} {ctxP : ConLeche.NestCtx}
    {keyP : ConLeche.NestKey} (hC : StageC dn vis fe env m a) (hA : AbsOK m) (hHI : hi.toNat = HI)
    (hU : UCtx dn vis fe m ctx c) (hk : decNK m key.toNat = some kk) (hkin : NKIn m key.toNat (· < iwTop m))
    (hksl : NKSl m key) (hP : PosMR m) (hctx : dCtx a.store env.find? c = some ctxP)
    (hkey : dKey a.store kk = some keyP) :
    RefE (closedNV p _root_.L.Checker.nvFns = true) (nitE p k m vis ctx hi key)
      (ConRon.Arena.nestInstType fe c HI kk) a (fun v x a' => NitPost dn vis fe m v.1 v.2 x a') := by
  cases k with
  | zero => rw [nitE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  | succ k =>
  have hS := hC.stage
  rw [nitE.arm1]
  have hTy := nty_ref L.ty k (IlpRd.realC hIlpf hC) hS hk hkin hksl
  rcases h1 : ntyE p k m vis key with e1 | ⟨w1, m1⟩ <;> rw [h1] at hTy
  · rw [nitE.k_nest_inst_type_ty.none]; exact fun hnv => ErrClaim.nestInstType (hTy hnv)
  rw [nitE.k_nest_inst_type_ty.arm1]
  obtain ⟨ty, a5, -, ⟨cv, caps, q, a3, a4, tl, hfind, hvl, hrun3, hrun4, hrun5⟩, hS1, hg1, htyH, htyd, hA1, hM1⟩ :=
    hTy
  dsimp only at hS1 hg1 htyH htyd hA1 hM1
  -- the twin up to `instPisWith`
  rw [ConRon.Arena.nestInstType.eq_1]
  refine RefE.bind_right (v := cv) (a₁ := a) (by rw [hfind]; rfl) ?_
  refine RefE.bind_right (v := some cv.levelParams.length) (a₁ := a) (by rw [viewLsLen_run, hvl]) ?_
  refine RefE.ite_neg (by simp) ?_
  refine RefE.bind_right hrun3 ?_
  refine RefE.bind_right hrun4 ?_
  refine RefE.bind_right hrun5 ?_
  dsimp only
  -- `pi_binders`
  rcases hpb : piBW k m1 CWF w1 with _ | ⟨rs, m2⟩
  · rw [liftE_none, nitE.k_pi_binders.none]; exact RefE.of_cls0 rfl
  rw [liftE_some]
  obtain ⟨bs, e', hrunpb, hdecbs, hresH, hresd, hS2, hg2, hbsb⟩ := piBW_cwf hpb hS1 htyH
  have hrunpb' : (ConRon.Arena.piBinders coreWalkFuel ty).run a5 = .ok ((bs, e'), a5) := htyd ▸ hrunpb
  refine RefE.bind_right hrunpb' ?_
  dsimp only
  have hg2' : rs.tail.tail.headD 0 = rs.getD 2 0 := by rcases rs with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl
  have hg1' : rs.tail.headD 0 = rs.getD 1 0 := by rcases rs with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl
  -- `e_view`
  by_cases hv0 : eViewW m2 (rs.getD 2 0) = []
  · rw [nitE.k_pi_binders.arm1 _ _ _ _ _ _ _ (by rw [hg2']; exact hv0)]; exact RefE.of_cls0 rfl
  obtain ⟨v, hview, hvr⟩ := eViewW_ok m2 a5 hS2.check.arena.base (rs.getD 2 0) hv0
  have hview' : (view e').run a5 = .ok (v, a5) := view_run _ _ _ (hresd ▸ hview)
  refine RefE.bind_right hview' ?_
  by_cases hv2 : (eViewW m2 (rs.getD 2 0)).headD 0 ≠ 2
  · rw [nitE.k_pi_binders.abort1 _ _ _ _ _ _ _ (by rw [hg2']; exact hv0) (by rw [hg2']; exact hv2)]
    cases v with
    | sort u => exact absurd hvr.1 hv2
    | _ => exact fun _ => ErrClaim.fail _ _ (by decide)
  have hv2' : (eViewW m2 (rs.getD 2 0)).headD 0 = 2 := by simpa using hv2
  rw [nitE.k_pi_binders.arm2 _ _ _ _ _ _ _ (by rw [hg2']; exact hv0) (by rw [hg2']; exact hv2'), hg2', hg1']
  obtain ⟨u, rfl, huH, hud⟩ : ∃ u, v = .sort u ∧ ((eViewW m2 (rs.getD 2 0)).getD 1 0).toNat < 2 ^ 32 ∧
      decI ((eViewW m2 (rs.getD 2 0)).getD 1 0) = u := by
    cases v <;> simp only [ViewR] at hvr <;> (try (rw [hv2'] at hvr; simp at hvr))
    · exact ⟨_, rfl, hvr.1, hvr.2⟩
  dsimp only
  -- `nest_occ_any` over the binders
  have hg12 := hg1.trans hg2
  have hU2 := hU.grow hg12
  have htop2 : iwTop m2 < 2 ^ 64 := Nat.lt_of_le_of_lt hS2.2.1 hS2.2.2.2.1
  obtain ⟨hn2, -, -, -, hnP2, -⟩ := ctx_fields hU2.dec hU2.inn htop2
  have hne2 := ctx_names_end hU2.dec hU2.inn hU2.sl htop2
  rcases hoa : noaW k m2 (rdW (m2.arr64 IW) ctx) (rdW (m2.arr64 IW) (ctx + 1)) (rdW (m2.arr64 IW) (ctx + 4)) hi
      (rs.headD 0) (rs.getD 1 0) with _ | ⟨r3, m3⟩
  · rw [liftE_none, nitE.k_nest_occ_any.none]; exact RefE.of_cls0 rfl
  rw [liftE_some]
  obtain ⟨b, hrunoa, hS3, hg3, hr3, hP3⟩ := noaW_ok dn fe vis _ _ _ _ c.names k m2 m3 a5 _ _ bs _ hoa hS2
    hn2 hne2 hdecbs (fun j hj => by omega) ((hP.fr hM1).fr (piBW_mfr _ _ _ _ _ _ hpb))
  rw [hnP2, hHI] at hrunoa
  refine RefE.bind_right hrunoa ?_
  cases b with
  | true =>
    rw [nitE.k_nest_occ_any.abort1 _ _ _ _ _ _ _ _ (by rw [hr3]; decide)]
    exact fun _ => ErrClaim.ite_pos rfl (ErrClaim.fail _ _ (by decide))
  | false =>
  rw [nitE.k_nest_occ_any.arm1 _ _ _ _ _ _ _ _ (by rw [hr3]; rfl)]
  refine RefE.ite_neg (by simp) ?_
  -- the stage at the comparison
  have hok := hC.check
  obtain ⟨hcn, hlv, hds⟩ := ConRon.Bridge.Inductives.dKey_inv hkey
  obtain ⟨namesP, lpsP, paramsP, sortP, -, -, -, -, hsort, -⟩ := ConRon.Bridge.Inductives.dCtx_inv hctx
  obtain ⟨ci, hci, -⟩ := ConRon.Bridge.Inductives.find_some_rel hok.ienv hcn hfind
  obtain ⟨cvP, capsP, hcvP, -, -⟩ := ConRon.Bridge.Inductives.denoteCI_indInfo_inv hci
  obtain ⟨-, hlpsC, htyC⟩ := ConRon.Bridge.denoteCV_inv hcvP
  obtain ⟨hs3', -⟩ := ConRon.Bridge.Inductives.stripPis_pstep hok.state htyC hrun3
  subst hs3'
  obtain ⟨c4, htl⟩ := ConRon.Bridge.Inductives.instLPFast_cstep hok hlpsC hlv htyC hrun4
  obtain ⟨p5, ho2⟩ := ConRon.Bridge.Inductives.instPisWith_spec kk.ds keyP.ds tl _ a4 a5 (some ty)
    c4.ok.state ⟨ConRon.Bridge.denoteEList_ext c4.ext _ _ hds, htl⟩ hrun5
  have c5 := c4.trans (p5.toCore c4.ok)
  obtain ⟨tyP, -, htyP⟩ := ho2
  obtain ⟨-, -, hpb2⟩ := ConRon.Bridge.Inductives.piBinders_spec _ ty tyP a5 a5 (bs, e') c5.ok.state htyP hrunpb'
  obtain ⟨-, hv5⟩ := ConRon.Bridge.view_run hview'
  obtain ⟨sP, -, hsL⟩ := ConRon.Bridge.denote_sort_inv c5.ok.state.wf hv5 hpb2
  have hA3 : AbsOK m3 := noaW_afr _ _ _ _ _ _ _ _ _ _ hoa (piBW_afr _ _ _ _ _ _ hpb (hA1 hA))
  have hC3 : StageC dn vis fe env m3 a5 := hC.of_check hS3 hA3 c5.ok c5.ext
  have hU3 := hU2.grow hg3
  have htop3 : iwTop m3 < 2 ^ 64 := Nat.lt_of_le_of_lt hS3.2.1 hS3.2.2.2.1
  obtain ⟨-, -, -, -, -, -, -, hsH, hsd, -⟩ := ctx_fields hU3.dec hU3.inn htop3
  have hdv : denoteL a5.store.ls (decI (rdW (m3.arr64 IW) (ctx + 9))) = some sortP := by
    rw [hsd]; exact ConRon.Bridge.denoteL_ext hsort c5.ext
  have huH' : H ((eViewW m2 (rs.getD 2 0)).tail.headD 0) := by rw [← getD1_eq]; exact huH
  have hud' : decI ((eViewW m2 (rs.getD 2 0)).tail.headD 0) = u := by rw [← getD1_eq]; exact hud
  rw [← hud'] at hsL
  rw [← hud', ← hsd]
  -- `lvl_eq_fueled`
  have hRL := lef_ref hcl hLC k hC3.stageT huH' hsH hsL hdv
  rcases h5 : lefE p k m3 ((eViewW m2 (rs.getD 2 0)).tail.headD 0) (rdW (m3.arr64 IW) (ctx + 9)) with
    e5 | ⟨w4, m4⟩ <;> rw [h5] at hRL
  · rw [nitE.k_lvl_eq_fueled.none, lefT_bind]
    exact RefE.bind_left fun hnv => hRL (nvAt_of hnv (_root_.L.Checker.nv_mem (by decide +kernel)))
  obtain ⟨b', a6, -, hRp⟩ := hRL
  dsimp only at hRp
  refine RefE.bind_right hRp.run ?_
  cases b' with
  | false =>
    rw [nitE.k_lvl_eq_fueled.abort1 _ _ _ _ _ (by rw [hRp.res]; rfl)]
    exact fun _ => ErrClaim.bind_right (v := false) (a₁ := a6) rfl
      (ErrClaim.ite_neg (by simp) (ErrClaim.fail _ _ (by decide)))
  | true =>
    rw [nitE.k_lvl_eq_fueled.arm1 _ _ _ _ _ (by rw [hRp.res]; decide)]
    obtain ⟨hC4, hA4, -⟩ := hRp.stageC env hC3 hA3
    refine RefE.bind_right (v := true) (a₁ := a6) rfl (RefE.ite_pos (by simp) (RefE.ret rfl ?_))
    exact ⟨hC4.stage, (hg12.trans hg3).trans hRp.grow, (decHL_length _ hdecbs).symm, htyH, htyd,
      hP3.fr hRp.mfr, hA4⟩

end L.Ind
