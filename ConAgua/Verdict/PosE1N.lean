module

import ConRon.Bridge.Inductives.FieldTele
import ConRon.Bridge.Inductives.PosWalks
import ConAgua.Arena.IndPosSpec.NtyW
import ConAgua.Arena.IndPosSpec.Grow
import ConAgua.Verdict.PosNty
import ConAgua.Arena.IlpRdReal
import ConAgua.Arena.IndRealAbsPos
import ConAgua.Arena.IndPosSpec.FgW
import ConAgua.Arena.IndT.Lift
import ConAgua.Arena.RefWalk
import ConAgua.Checker.NoVerdictTree
import ConRon.Bridge.Inductives.Positivity
import ConRon.Bridge.Specs
public import ConAgua.Arena.IndPosSpec.BvbWMfr
public import ConAgua.Arena.IndPosSpec.NkFields
public import ConAgua.Arena.IndRealIlpL
public import ConAgua.Verdict.PosE1M

@[expose] public section
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

/-- What `nest_inst_type` gives besides the twin's result `x` (from `m`): the stage, the growth, the
count of binders at `r[0]`, the container's type at `r[1]`, the frames, `AbsOK`. -/
structure NitPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m : Mem) (r : List Word)
    (m' : Mem) (x : Nat × EIdx) (a' : AState) : Prop where
  stage : StageR vis fe m' a'
  grow : IWGrow m m'
  count : (r.headD 0).toNat = x.1
  hty : H (r.tail.headD 0)
  dec : decI (r.tail.headD 0) = x.2
  pos : PosMR m'
  abs : AbsOK m'

/- ronsync2 stage 2: commented out (statement at the old twin/L)
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
  -- `nest_inst_type_ty`: the twin up to `instPisWith`
  change RefE _ _ (ntyT fe kk _) _ _
  rw [ntyT_eq]
  refine RefE.bindE (fun _ => rfl) id (nty_ref L.ty k (IlpRd.realC hIlpf hC) hS hk hkin hksl)
    fun ⟨w1, m1⟩ ty a5 _ ⟨⟨cv, caps, q, a3, a4, tl, hfind, hvl, hrun3, hrun4, hrun5⟩, hS1, hg1, htyH, htyd,
      hA1, hM1⟩ => ?_
  dsimp only [nitE.k_nest_inst_type_ty]
  -- `pi_binders`
  refine RefE.bindLift (fun _ => rfl) fun rs m2 hpb => ?_
  obtain ⟨bs, e', hrunpb, hdecbs, hresH, hresd, hS2, hg2, hbsb⟩ := piBW_cwf hpb hS1 htyH
  have hrunpb' : (ConRon.Arena.piBinders coreWalkFuel ty).run a5 = .ok ((bs, e'), a5) := htyd ▸ hrunpb
  refine ⟨_, _, hrunpb', ?_⟩
  have hg2' : rs.tail.tail.headD 0 = rs.getD 2 0 := by rcases rs with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl
  have hg1' : rs.tail.headD 0 = rs.getD 1 0 := by rcases rs with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl
  dsimp only [nitE.k_pi_binders]
  rw [hg2', hg1']
  -- `e_view`
  refine RefE.abort0 (by rfl) fun hv0 => ?_
  obtain ⟨v, hview, hvr⟩ := eViewW_ok m2 a5 hS2.check.arena.base (rs.getD 2 0) hv0
  have hview' : (view e').run a5 = .ok (v, a5) := view_run _ _ _ (hresd ▸ hview)
  refine RefE.bind_right hview' ?_
  by_cases hv2 : (eViewW m2 (rs.getD 2 0)).headD 0 ≠ 2
  · refine RefE.abortAt hv2 ?_
    cases v with
    | sort u => exact absurd hvr.1 hv2
    | _ => exact fun _ => ErrClaim.fail _ _ (by decide)
  refine RefE.pass hv2 ?_
  have hv2' : (eViewW m2 (rs.getD 2 0)).headD 0 = 2 := by simpa using hv2
  obtain ⟨u, rfl, huH, hud⟩ : ∃ u, v = .sort u ∧ ((eViewW m2 (rs.getD 2 0)).getD 1 0).toNat < 2 ^ 32 ∧
      decI ((eViewW m2 (rs.getD 2 0)).getD 1 0) = u := by
    cases v <;> simp only [ViewR] at hvr <;> (try (rw [hv2'] at hvr; simp at hvr))
    · exact ⟨_, rfl, hvr.1, hvr.2⟩
  dsimp only
  -- `nest_occ_any` over the binders
  have hg12 := hg1.trans hg2
  have hU2 := hU.grow hg12
  have htop2 : iwTop m2 < 2 ^ 64 := Nat.lt_of_le_of_lt hS2.iw.iw hS2.iw.iwSize
  obtain ⟨hn2, -, -, -, hnP2, -⟩ := ctx_fields hU2.dec hU2.inn htop2
  have hne2 := ctx_names_end hU2.dec hU2.inn hU2.sl htop2
  refine RefE.bindLift (fun _ => rfl) fun r3 m3 hoa => ?_
  obtain ⟨b, hrunoa, hS3, hg3, hr3, hP3⟩ := noaW_ok dn fe vis _ _ _ _ c.names k m2 m3 a5 _ _ bs _ hoa hS2
    hn2 hne2 hdecbs (fun j hj => by omega) ((hP.fr hM1).fr (piBW_mfr _ _ _ _ _ _ hpb))
  rw [hnP2, hHI] at hrunoa
  refine ⟨_, _, hrunoa, ?_⟩
  dsimp only [nitE.k_nest_occ_any]
  refine RefE.guardThen (by decide) (fun h => by cases b; exact absurd hr3 h; rfl)
    (fun hb => by subst hb; rw [hr3]; decide) fun _ _ => ?_
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
  have htop3 : iwTop m3 < 2 ^ 64 := Nat.lt_of_le_of_lt hS3.iw.iw hS3.iw.iwSize
  obtain ⟨-, -, -, -, -, -, -, hsH, hsd, -⟩ := ctx_fields hU3.dec hU3.inn htop3
  have hdv : denoteL a5.store.ls (decI (rdW (m3.arr64 IW) (ctx + 9))) = some sortP := by
    rw [hsd]; exact ConRon.Bridge.denoteL_ext hsort c5.ext
  have huH' : H ((eViewW m2 (rs.getD 2 0)).tail.headD 0) := by rw [← getD1_eq]; exact huH
  have hud' : decI ((eViewW m2 (rs.getD 2 0)).tail.headD 0) = u := by rw [← getD1_eq]; exact hud
  rw [← hud'] at hsL
  rw [← hud', ← hsd]
  -- `lvl_eq_fueled`
  rw [lefT_bind]
  refine RefE.bindE (fun _ => rfl) (fun hnv => nvAt_of hnv (_root_.L.Checker.nv_mem (by decide +kernel)))
    (lef_ref hcl hLC k hC3.stageT huH' hsH hsL hdv) fun ⟨w4, m4⟩ b' a6 _ hRp => ?_
  dsimp only [nitE.k_lvl_eq_fueled]
  have hres := hRp.res
  refine RefE.guardIf (by decide) (fun h => by cases b'; rfl; exact absurd (hres.symm.trans h) (by decide))
    (fun hb => by subst hb; exact hres) fun _ _ => ?_
  obtain ⟨hC4, hA4, -⟩ := hRp.stageC env hC3 hA3
  exact RefE.ret rfl ⟨hC4.stage, (hg12.trans hg3).trans hRp.grow, (decHL_length _ hdecbs).symm, htyH, htyd,
    hP3.fr hRp.mfr, hA4⟩
-/

end L.Ind
