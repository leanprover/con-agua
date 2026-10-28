import ConAgua.Verdict.PosNty
import ConAgua.Verdict.DeclValE
import ConAgua.Verdict.PosE
import ConAgua.Arena.IlpRdReal
import ConAgua.Arena.IndPosSpec.NitW
import ConAgua.Arena.IndT.Install2
/-!
# `nest_inst_type`: error claim (lane `verdicts-b`, helper `ia2`, fork `kn1`)

`nitE_all`: `NitE` (`PosE.lean`), `nitW_ok`'s proof with `nitLe_realC`'s twin side; the level
comparison's decline by `lvlEqFueled_errT`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind
open L.Arena

theorem nvAt_of {p : Prog} (hnv : closedNV p _root_.L.Checker.nvFns = true) {f : FnName}
    (hf : f ∈ _root_.L.Checker.nvFns) : NVAt p f :=
  fun n args m _ h => callE_nv hnv hf n args m h

theorem ErrClaim.of_run_eq' {α : Type} {T T' : AM α} {a a' : AState} {e : Err}
    (h : T.run a = T'.run a') (h' : ErrClaim T' a' e) : ErrClaim T a e := fun hk => by
  obtain ⟨ce, hce, hc⟩ := h' hk
  exact ⟨ce, h ▸ hce, hc⟩

/-- **`nest_inst_type`'s error claim** (`NitE`). -/
theorem nitE_all {p : Prog} (L : NbLook p) (hq : KnotStageProg p) (hIlpf : IlpfF p) (hLC : LvlCacheProg p)
    (hnv : closedNV p _root_.L.Checker.nvFns = true) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (env : ConLeche.Env) : NitE p dn vis fe env := by
  intro k m a ctx hi key HI c kk ctxP keyP hC hA hHI hU hk hkin hksl hP hctx hkey er he
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hl := L.nit
  replace he := triple_of_callE_err (nitE_spec p hl.hp k ⟨m, Locals.init []⟩ vis ctx hi key) he
    (Err.code_ne_of_cls hk0)
  dsimp only at he
  have hS := hC.stage
  cases k with
  | zero => rw [nitE.eq_1] at he; cases he; exact absurd rfl hk0
  | succ k =>
  rw [nitE.arm1] at he
  have hTy := nty_ref hl.ty k (IlpRd.realC hIlpf hC) hS hk hkin hksl
  cases h1 : callE p k "nest_inst_type_ty" [vis, key] m with
  | error e1 =>
    rw [h1, nitE.k_nest_inst_type_ty.eq_1] at he; cases he
    exact ErrClaim.nestInstType (RefE.run_err (ntyE_spec p hl.ty k ⟨m, Locals.init []⟩ vis key) hnv hnv hTy h1)
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, nitE.k_nest_inst_type_ty.arm1] at he
  obtain ⟨s1, hs1, -, ty, a5, -, ⟨⟨cv, caps, q, a3, a4, tl, hfind, hvl, hrun3, hrun4, hrun5⟩, hS1, hg1, htyH, htyd,
    hA1, hM1⟩⟩ := RefE.run_ok (ntyE_spec p hl.ty k ⟨m, Locals.init []⟩ vis key) hTy h1
  rw [hs1] at hS1 hg1 hA1 hM1
  -- the twin up to `instPisWith`
  rw [ConRon.Arena.nestInstType.eq_1]
  refine ErrClaim.bind_right (v := cv) (a₁ := a) (by rw [hfind]; rfl) ?_
  refine ErrClaim.bind_right (v := some cv.levelParams.length) (a₁ := a) (by rw [viewLsLen_run, hvl]) ?_
  refine ErrClaim.ite_neg (by simp) ?_
  refine ErrClaim.bind_right hrun3 ?_
  refine ErrClaim.bind_right hrun4 ?_
  refine ErrClaim.bind_right hrun5 ?_
  dsimp only
  -- `pi_binders`
  cases h2 : callE p k "pi_binders" [CWF, r1.headD 0] m1 with
  | error e2 =>
    rw [h2, nitE.k_pi_binders.eq_1] at he; cases he
    exact ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) h2
  | ok q2 =>
  obtain ⟨rs, m2⟩ := q2
  rw [h2, nitE.k_pi_binders.arm1] at he
  obtain ⟨s2, hs2, -, hpb, hrs⟩ := triple_of_callW
    (piBinders_spec p hl.ty.ha hl.hc2 hl.ty.hv hl.hs hl.hpb k ⟨m1, Locals.init []⟩ CWF _) (callW_of_callE h2)
  dsimp only at hpb
  rw [hs2] at hpb
  obtain ⟨bs, e', hrunpb, hdecbs, hresH, hresd, hS2, hg2, hbsb⟩ := piBW_cwf hpb hS1 htyH
  have hrunpb' : (ConRon.Arena.piBinders coreWalkFuel ty).run a5 = .ok ((bs, e'), a5) := htyd ▸ hrunpb
  refine ErrClaim.bind_right hrunpb' ?_
  dsimp only
  have hg2' : rs.tail.tail.headD 0 = rs.getD 2 0 := by rw [hrs]; rfl
  have hg1' : rs.tail.headD 0 = rs.getD 1 0 := by rw [hrs]; rfl
  rw [hg2', hg1'] at he
  -- `e_view`
  cases h3 : callE p k "e_view" [rs.getD 2 0] m2 with
  | error e3 =>
    rw [h3, nitE.k_e_view.eq_1] at he; cases he
    exact ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) h3
  | ok q3 =>
  obtain ⟨rv, m2'⟩ := q3
  obtain ⟨s3, hs3, hm3, hv0, hrv⟩ := triple_of_callW (eView_spec p hl.ty.hv k ⟨m2, Locals.init []⟩ _)
    (callW_of_callE h3)
  have hm2' : m2' = m2 := by rw [← hs3, hm3]
  dsimp only at hrv
  subst hm2' hrv
  rw [h3] at he
  obtain ⟨v, hview, hvr⟩ := eViewW_ok m2' a5 hS2.1.arena.1 (rs.getD 2 0) hv0
  have hview' : (view e').run a5 = .ok (v, a5) := view_run _ _ _ (hresd ▸ hview)
  refine ErrClaim.bind_right hview' ?_
  by_cases hv2 : (eViewW m2' (rs.getD 2 0)).headD 0 ≠ 2
  · rw [nitE.k_e_view.abort1 _ _ _ _ _ _ _ _ _ hv2] at he; cases he
    cases v with
    | sort u => exact absurd hvr.1 hv2
    | _ => exact ErrClaim.fail _ _ (by decide)
  have hv2' : (eViewW m2' (rs.getD 2 0)).headD 0 = 2 := by simpa using hv2
  rw [nitE.k_e_view.arm1 _ _ _ _ _ _ _ _ _ hv2'] at he
  obtain ⟨u, rfl, huH, hud⟩ : ∃ u, v = .sort u ∧ ((eViewW m2' (rs.getD 2 0)).getD 1 0).toNat < 2 ^ 32 ∧
      decI ((eViewW m2' (rs.getD 2 0)).getD 1 0) = u := by
    cases v <;> simp only [ViewR] at hvr <;> (try (rw [hv2'] at hvr; simp at hvr))
    · exact ⟨_, rfl, hvr.1, hvr.2⟩
  dsimp only
  -- `nest_occ_any` over the binders
  have hg12 := hg1.trans hg2
  have hU2 := hU.grow hg12
  have htop2 : iwTop m2' < 2 ^ 64 := Nat.lt_of_le_of_lt hS2.2.1 hS2.2.2.2.1
  obtain ⟨hn2, -, -, -, hnP2, -⟩ := ctx_fields hU2.dec hU2.inn htop2
  have hne2 := ctx_names_end hU2.dec hU2.inn hU2.sl htop2
  cases h4 : callE p k "nest_occ_any" [rdW (m2'.arr64 IW) ctx, rdW (m2'.arr64 IW) (ctx + 1),
      rdW (m2'.arr64 IW) (ctx + 4), hi, rs.headD 0, rs.getD 1 0] m2' with
  | error e4 =>
    rw [h4, nitE.k_nest_occ_any.eq_1] at he; cases he
    exact ErrClaim.of_callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) h4
  | ok q4 =>
  obtain ⟨r3, m3⟩ := q4
  obtain ⟨s4, hs4, -, hoa⟩ := triple_of_callW (nestOccAny_spec p hl.no hl.hoa k ⟨m2', Locals.init []⟩ _ _ _ _ _ _)
    (callW_of_callE h4)
  dsimp only at hoa
  rw [hs4] at hoa
  rw [h4] at he
  obtain ⟨b, hrunoa, hS3, hg3, hr3, hP3⟩ := noaW_ok dn fe vis _ _ _ _ c.names k m2' m3 a5 _ _ bs _ hoa hS2
    hn2 hne2 hdecbs (fun j hj => by omega)
    ((hP.fr hM1).fr (piBW_mfr _ _ _ _ _ _ hpb))
  simp only [List.headD_cons] at hr3
  rw [hnP2, hHI] at hrunoa
  refine ErrClaim.bind_right hrunoa ?_
  cases b with
  | true =>
    rw [nitE.k_nest_occ_any.abort1 _ _ _ _ _ _ _ _ (by rw [hr3]; decide)] at he; cases he
    exact ErrClaim.ite_pos rfl (ErrClaim.fail _ _ (by decide))
  | false =>
  rw [nitE.k_nest_occ_any.arm1 _ _ _ _ _ _ _ _ (by rw [hr3]; rfl)] at he
  refine ErrClaim.ite_neg (by simp) ?_
  -- the stage at the comparison (`nitLe_realC`'s twin side)
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
  have huH' : H ((eViewW m2' (rs.getD 2 0)).tail.headD 0) := by rw [← getD1_eq]; exact huH
  have hud' : decI ((eViewW m2' (rs.getD 2 0)).tail.headD 0) = u := by rw [← getD1_eq]; exact hud
  rw [← hud'] at hsL
  rw [← hud', ← hsd]
  -- `lvl_eq_fueled`
  cases h5 : callE p k "lvl_eq_fueled" [(eViewW m2' (rs.getD 2 0)).tail.headD 0, rdW (m3.arr64 IW) (ctx + 9)] m3 with
  | error e5 =>
    rw [h5, nitE.k_lvl_eq_fueled.eq_1] at he; cases he
    exact lvlEqFueled_errT hq hLC hl.hlf (nvAt_of hnv (_root_.L.Checker.nv_mem (by decide +kernel))) _ hC3.stageT huH' hsH _ _ hsL hdv h5
  | ok q5 =>
  obtain ⟨r4, m4⟩ := q5
  rw [h5] at he
  obtain ⟨s5, hs5, -, hle⟩ := triple_of_callW
    (lvlEqFueled_specC p hl.hlf (realCall p) (realCall_spec p) k ⟨m3, Locals.init []⟩ _ _) (callW_of_callE h5)
  dsimp only at hle
  rw [hs5] at hle
  obtain ⟨b', a6, hrunle, -, -, -, -, hr4⟩ := lveC_okC hq.closed hLC hle hC3 hA3 huH' hsH hsL hdv
  refine ErrClaim.bind_right hrunle ?_
  cases b' with
  | true => rw [nitE.k_lvl_eq_fueled.arm1 _ _ _ _ _ (by rw [hr4]; decide)] at he; cases he
  | false =>
    rw [nitE.k_lvl_eq_fueled.abort1 _ _ _ _ _ (by rw [hr4]; rfl)] at he; cases he
    exact ErrClaim.bind_right (v := false) (a₁ := a6) rfl (ErrClaim.ite_neg (by simp) (ErrClaim.fail _ _ (by decide)))

end L.Ind
