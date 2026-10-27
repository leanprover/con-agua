import ConAgua.Arena.IndT.Lift
import ConAgua.Arena.IndT.PosDefs
import ConAgua.Arena.IndPosSpec.GgW2
import ConAgua.Arena.IndPosSpec.NestCrest
import ConAgua.Arena.IndPosSpec.Pos2DecHLSplit
import ConAgua.Arena.IndRealAbsPos

/-!
# `nest_pos_app` under `StageC` (lane `indstaget`, helper `indstaget-pos`)

`appOK_step`'s proof (`IndPosSpec/Pos2DecHLSplit`) with the twin side of con-ron's `nestPos_succ` (its head
case): the reduct's arguments and head (no state change), a hole (`pfK`: `nestOcc_spec`,
`nestArity_spec`) or a container (the block's `ContOKC` at `n`).
-/


open ConRon.Arena
open ConRon.Bridge.Inductives (PStep dCtx dProg dState dCtx_ext dProg_ext dState_ext kindOf)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- A hole application's checks (`pfK`) are a pure step. -/
theorem pfK_pstep {fe : IFEnv} {env : ConLeche.Env} {c : NestCtx} {prog : List NestHole} {kb hi i : Nat}
    {args : List EIdx} {x : NestFieldKind} {a a' : AState} {ctxP : ConLeche.NestCtx}
    {progP : List ConLeche.NestHole} {argsP : List ConLeche.Expr}
    (h : ∀ {β : Type} (K : NestFieldKind → AM β), (pfK fe c prog kb hi i args K).run a = (K x).run a')
    (hok : ConRon.Bridge.CheckOK V env fe a) (hctx : dCtx a.store env.find? c = some ctxP)
    (hprog : dProg a.store prog = some progP) (hargs : Frontend.denoteEList a.store args = some argsP) :
    PStep a a' := by
  obtain ⟨hcn, -, hfind, -, -, -⟩ := ConRon.Bridge.Inductives.dCtx_fields hctx
  have h2 : (pfK fe c prog kb hi i args (fun k => (pure k : AM NestFieldKind))) a = .ok (x, a') := h _
  unfold pfK at h2
  have hrel := ConRon.Bridge.Inductives.nestHoleAt_rel hctx hprog i
  rcases hh : ConRon.Arena.nestHoleAt c prog i with _ | hole; · rw [hh] at h2; exact absurd h2 (fun hc => ConRon.Bridge.AM.fail_ok hc)
  rw [hh] at h2 hrel
  obtain ⟨hP, -, hdh⟩ := hrel
  simp only at h2
  obtain ⟨b, s1, h3, h4⟩ := ConRon.Bridge.AM.bind_ok h2
  obtain ⟨p1, -⟩ := ConRon.Bridge.Inductives.anyM_E_pstep
    (fun st => Frontend.denoteNList st.ns c.names = some ctxP.names)
    (fun hx h => ConRon.Bridge.denoteNListE_ext hx _ _ h)
    (fun e eP s₀ s' b hok' hq hd hrun' =>
      ConRon.Bridge.Inductives.nestOcc_spec c.names ctxP.names c.nP hi e eP s₀ s' b hok' ⟨hq, hd⟩ hrun')
    args argsP a s1 b hok.state hcn hargs h3
  cases b with
  | true =>
    simp only [↓reduceIte] at h4; exact absurd h4 (fun hc => ConRon.Bridge.AM.fail_ok hc)
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h4
  obtain ⟨ar, s2, h5, h6⟩ := ConRon.Bridge.AM.bind_ok h4
  simp only [ConRon.Bridge.Inductives.dHole, Option.map_eq_some_iff] at hdh
  obtain ⟨kP, hkP, -⟩ := hdh
  obtain ⟨hkc, -, -⟩ := ConRon.Bridge.Inductives.dKey_inv hkP
  obtain ⟨p2, -⟩ := ConRon.Bridge.Inductives.nestArity_spec ctxP hfind hole.key.cname kP.cname s1 s2 ar p1.ok
    ⟨hok.ienv.toS.mono p1.ext, ConRon.Bridge.denoteN_ext hkc p1.ext⟩ h5
  split at h6
  · obtain ⟨-, rfl⟩ := ConRon.Bridge.AM.pure_ok h6; exact p1.trans p2
  · exact absurd h6 (fun hc => ConRon.Bridge.AM.fail_ok hc)

section steps
variable (p : Prog) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) {env : ConLeche.Env}

theorem appOKC_step (n : Nat) (ih : NbOKC p dn vis fe env n) : AppOKC p dn vis fe env (n + 1) := by
  obtain ⟨-, -, -, hCont, -, -, -, -, -, -, -⟩ := ih
  intro m m' a ctx fu po pl kb hi w ns c prog NS r ctxP progP wP nsP dep h hC hW hhi hw hns hP hA hc hctx hprog
    hwP hnsP hww
  have hS := hC.stage
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  rw [nbAppW_succ] at h
  rcases hga : gaaF m [CWF, w] with _ | ⟨ra, m1⟩ <;> rw [hga] at h; · simp [nbAppK1] at h
  rw [nbAppK1_some] at h
  obtain ⟨args, a1, hrun1, hS1, hg1, hargs, hargsb⟩ := gaaF_ok dn vis fe CWF w hw m m1 a ra hga hS
  rw [CWF_eq] at hrun1
  obtain ⟨ha1, hargsP⟩ := ConRon.Bridge.Inductives.getAppArgs_run hC.check.state hwP hrun1
  subst ha1
  have e0 : ra.getD 0 0 = ra.headD 0 := by cases ra <;> rfl
  rw [e0, getD1_eq] at hargs hargsb
  rcases hgf : gafF m1 [CWF, w] with _ | ⟨rh, m2⟩ <;> rw [hgf] at h; · simp [nbAppK2] at h
  rw [nbAppK2_some] at h
  obtain ⟨hd, a2, hrun2, hS2, hg2, hhdH, hhdd⟩ := gafF_ok dn vis fe CWF w hw m1 m2 a1 rh hgf hS1
  rw [CWF_eq] at hrun2
  obtain ⟨ha2, hhdP⟩ := ConRon.Bridge.Inductives.getAppFn_run hC.check.state hwP hrun2
  subst ha2
  have hg12 := hg1.trans hg2
  have hP2 : PosMR m2 := (hP.fr (MFr.ofGaaF hga)).fr (MFr.ofGafF hgf)
  have hA2 : AbsOK m2 := gafF_afr hgf (gaaF_afr hga hA)
  have hS2' := hS2
  have hC2 : StageC dn vis fe env m2 a2 := hC.of_pstep hS2' hA2 (PStep.refl hC.check.state)
  by_cases hev : eViewW m2 (rh.headD 0) = []
  · rw [ite_eq_left hev] at h; cases h
  rw [ite_eq_right hev] at h
  obtain ⟨v, hview, hvr⟩ := eViewW_ok m2 a2 hS2.1.arena.1 (rh.headD 0) hev
  have hvrun : (view hd).run a2 = .ok (v, a2) := by rw [← hhdd, ← decE_eq]; exact view_run _ _ _ hview
  have hargs2 : decHL m2 (ra.headD 0).toNat (ra.tail.headD 0).toNat = some args := by
    rw [decHL_agree (RdS.of_grow hg2) (fun j hj => by omega)]; exact hargs
  by_cases h1 : (eViewW m2 (rh.headD 0)).headD 0 = 1
  · rw [ite_eq_left h1] at h
    -- a hole
    obtain ⟨i, ty, rfl⟩ : ∃ i ty, v = .fvar i ty := by
      cases v <;> simp only [ViewR] at hvr <;> (try (rw [h1] at hvr; simp at hvr)) <;> exact ⟨_, _, rfl⟩
    obtain ⟨-, hi1, -, -⟩ := hvr
    rw [getD1_eq] at hi1
    rcases hpf : pfW n m2 vis ctx po pl kb hi ((eViewW m2 (rh.headD 0)).tail.headD 0) (ra.headD 0) (ra.tail.headD 0) with _ | ⟨rp, m3⟩ <;> rw [hpf] at h; · simp [nbAppK4] at h
    rw [nbAppK4_some] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have hhi0 : c.hiAt 0 < 2 ^ 64 := by have := hW.hb; simp only [NestCtx.hiAt] at this ⊢; omega
    obtain ⟨k, a3, hK, hS3, hg3, hk, hP3⟩ := pfW_ok dn vis fe hpf hS2' (hW.grow hg12).u (hW.grow hg12).hs hhi0 hargs2
      (by have := hg2.1; omega) hP2
    have hA3 : AbsOK m3 := pfW_afr hpf hA2
    have p3 : PStep a2 a3 := pfK_pstep hK hC.check hctx hprog hargsP
    refine ⟨(k, decI w, NS), a3, ?_, hC.of_pstep hS3 hA3 p3, hg12.trans hg3, by simpa using hk, rfl,
      by simpa using (hns.grow (hg12.trans hg3) htop), hP3, hA3, p3.toCore hC.check⟩
    rw [hi1] at hK
    simp only [posAppT, StateT.run_bind, hrun1, except_ok_bind, hrun2, hvrun]
    rw [hK]; rfl
  rw [ite_eq_right h1] at h
  have h3 : (eViewW m2 (rh.headD 0)).headD 0 = 3 := by
    by_cases h3 : (eViewW m2 (rh.headD 0)).headD 0 = 3
    · exact h3
    · rw [ite_eq_right h3] at h; cases h
  rw [ite_eq_left h3] at h
  -- a constant: a container
  obtain ⟨nn, us, rfl⟩ : ∃ nn us, v = .const nn us := by
    cases v <;> simp only [ViewR] at hvr <;> (try (rw [h3] at hvr; simp at hvr)) <;> exact ⟨_, _, rfl⟩
  obtain ⟨-, hnH, hnd, husH, husd⟩ := hvr
  rw [getD1_eq] at hnH hnd
  rw [pos2_getD2] at husH husd
  obtain ⟨nm, ls, -, hnmP, hlsP⟩ := ConRon.Bridge.denote_const_inv hC.check.state.wf
    (by rw [← hhdd, ← decE_eq]; exact hview) hhdP
  have htop2 : iwTop m2 < 2 ^ 64 := Nat.lt_of_le_of_lt hS2.2.1 hS2.2.2.2.1
  obtain ⟨hn2, hnb2, -, -, -, -⟩ := ctx_fields (hW.grow hg12).u.dec (hW.grow hg12).u.inn htop2
  have hne2 := ctx_names_end (hW.grow hg12).u.dec (hW.grow hg12).u.inn (hW.grow hg12).u.sl htop2
  obtain ⟨ws, hws, hwsd, hwsH⟩ := slR_of_decHL m2 _ _ _ hn2 (by omega)
  simp only [UInt64.ofNat_toNat] at hws
  rcases hco : containsW n m2 (rdW (m2.arr64 IW) ctx) (rdW (m2.arr64 IW) (ctx + 1))
      ((eViewW m2 (rh.headD 0)).tail.headD 0) with _ | o; · rw [hco] at h; simp [nbAppK5] at h
  rw [hco, nbAppK5_some] at h
  have ho := containsW_ok n m2 _ _ _ o ws hws hco
  by_cases hon : o ≠ 0
  · rw [ite_eq_left hon] at h; cases h
  rw [ite_eq_right hon] at h
  have hnotin : c.names.contains nn = false := by
    rw [hwsd, ← hnd, pos2_contains_map ws hwsH _ hnH]
    cases e : ws.contains ((eViewW m2 (rh.headD 0)).tail.headD 0) with
    | false => rfl
    | true => rw [e] at ho; simp at hon; rw [hon] at ho; exact absurd ho (by decide)
  rcases hct : nbContW (realCall p) n m2 vis ctx fu po pl kb ((eViewW m2 (rh.headD 0)).tail.headD 0)
      ((eViewW m2 (rh.headD 0)).tail.tail.headD 0) (ra.headD 0) (ra.tail.headD 0) ns with _ | ⟨rc, m4⟩; · rw [hct] at h; simp [nbAppK6] at h
  rw [hct, nbAppK6_some] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨x, a4, hrun4, hC4, hg4, hk4, hns4, hP4, hA4, c4⟩ := hCont m2 m4 a2 ctx fu po pl kb _ _ _ _ ns c prog args NS
    rc ctxP progP nm ls wP.getAppArgs nsP dep hct hC2 (hW.grow hg12) hnH husH hargs2 (by have := hg2.1; omega)
    (hns.grow hg12 htop) hP2 hA2 hc hctx hprog (by rw [hnd]; exact hnmP) (by rw [husd]; exact hlsP) hargsP hnsP
    (ConLeche.Expr.WScoped.getAppArgs hww)
  rw [hnd, husd] at hrun4
  refine ⟨(x.1, decI w, x.2), a4, ?_, hC4, hg12.trans hg4, by simpa using hk4, rfl, by simpa using hns4, hP4, hA4,
    c4⟩
  
  simp only [posAppT, StateT.run_bind, hrun1, except_ok_bind, hrun2, hvrun, hnotin, Bool.false_eq_true, ite_false,
    hrun4]
  rfl

end steps

end L.Ind
