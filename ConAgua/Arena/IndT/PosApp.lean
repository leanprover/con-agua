import ConAgua.Verdict.PosE1L
import ConAgua.Arena.IndPosSpec.Pos2DecHLSplit
import ConAgua.Arena.IndPosSpec.Snoc
import ConAgua.Verdict.PosE

/-!
# `nest_pos_app` under `StageC` (lane `indstaget`, helper `indstaget-pos`)

`appRef_step`: `nest_pos_app` refines `posAppT` (con-ron's `nestPos_succ`, its head case), both
outcomes (`npaE`, unified): the reduct's arguments and head (no state change), a hole (`pfv_ref`
on `pfK`) or a container (the block's `ContRef` at `n`).
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

theorem appRef_step (L : NbLook p) (n : Nat) (ih : NbRef p dn vis fe env n) : AppRef p dn vis fe env (n + 1) := by
  intro m a ctx fu po pl kb hi w ns c prog NS ctxP progP wP nsP dep hC hW hhi hw hns hP hA hc hctx hprog
    hwP hnsP hww
  have hS := hC.stage
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  rw [npaE.arm1]
  -- the arguments
  cases h1 : callE p n "get_app_args_f" [CWF, w] m with
  | error e1 =>
    rw [npaE.k_get_app_args_f.eq_1]
    exact fun hG => ErrClaim.of_callE_nv hG.nv (_root_.L.Checker.nv_mem (by decide +kernel)) h1
  | ok q1 =>
  obtain ⟨ra, m1⟩ := q1
  obtain ⟨s1, hs1, -, hga⟩ := triple_of_callW (gaaF_spec p L.nt.ad n ⟨m, Locals.init []⟩ _) (callW_of_callE h1)
  dsimp only at hga
  rw [hs1] at hga
  rw [npaE.k_get_app_args_f.arm1]
  obtain ⟨args, a1, hrun1, hS1, hg1, hargs, hargsb⟩ := gaaF_ok dn vis fe CWF w hw m m1 a ra hga hS
  rw [CWF_eq] at hrun1
  obtain ⟨ha1, hargsP⟩ := ConRon.Bridge.Inductives.getAppArgs_run hC.check.state hwP hrun1
  subst ha1
  have e0 : ra.getD 0 0 = ra.headD 0 := by cases ra <;> rfl
  rw [e0, getD1_eq] at hargs hargsb
  unfold posAppT
  refine RefE.bind_right hrun1 ?_
  -- the head
  cases h2 : callE p n "get_app_fn_f" [CWF, w] m1 with
  | error e2 =>
    rw [npaE.k_get_app_fn_f.eq_1]
    exact fun hG => ErrClaim.of_callE_nv hG.nv (_root_.L.Checker.nv_mem (by decide +kernel)) h2
  | ok q2 =>
  obtain ⟨rh, m2⟩ := q2
  obtain ⟨s2, hs2, -, hgf⟩ := triple_of_callW (gafF_spec p L.nt.ad n ⟨m1, Locals.init []⟩ _) (callW_of_callE h2)
  dsimp only at hgf
  rw [hs2] at hgf
  rw [npaE.k_get_app_fn_f.arm1]
  obtain ⟨hd, a2, hrun2, hS2, hg2, hhdH, hhdd⟩ := gafF_ok dn vis fe CWF w hw m1 m2 a1 rh hgf hS1
  rw [CWF_eq] at hrun2
  obtain ⟨ha2, hhdP⟩ := ConRon.Bridge.Inductives.getAppFn_run hC.check.state hwP hrun2
  subst ha2
  refine RefE.bind_right hrun2 ?_
  have hg12 := hg1.trans hg2
  have hP2 : PosMR m2 := (hP.fr (MFr.ofGaaF hga)).fr (MFr.ofGafF hgf)
  have hA2 : AbsOK m2 := gafF_afr hgf (gaaF_afr hga hA)
  have hC2 : StageC dn vis fe env m2 a2 := hC.of_pstep hS2 hA2 (PStep.refl hC.check.state)
  -- the view
  cases h3 : callE p n "e_view" [rh.headD 0] m2 with
  | error e3 =>
    rw [npaE.k_e_view.eq_1]
    exact fun hG => ErrClaim.of_callE_nv hG.nv (_root_.L.Checker.nv_mem (by decide +kernel)) h3
  | ok q3 =>
  obtain ⟨rv, m3⟩ := q3
  obtain ⟨s3, hs3, hm3, hev, hrv⟩ := triple_of_callW (eView_spec p L.ct.cr.rx.hl.hv n ⟨m2, Locals.init []⟩ _)
    (callW_of_callE h3)
  have hm3' : m3 = m2 := by rw [← hs3, hm3]
  dsimp only at hrv
  rw [npaE.k_e_view.eq_2, hm3', hrv]
  rw [hrv] at hev
  obtain ⟨v, hview, hvr⟩ := eViewW_ok m2 a2 hS2.check.arena.base (rh.headD 0) hev
  have hvrun : (view hd).run a2 = .ok (v, a2) := by rw [← hhdd, ← decE_eq]; exact view_run _ _ _ hview
  refine RefE.bind_right hvrun ?_
  have hargs2 : decHL m2 (ra.headD 0).toNat (ra.tail.headD 0).toNat = some args := by
    rw [decHL_agree (RdS.of_grow hg2) (fun j hj => by omega)]; exact hargs
  by_cases h1v : (eViewW m2 (rh.headD 0)).headD 0 = 1
  · -- a hole
    rw [ite_eq_left h1v]
    obtain ⟨i, ty, rfl⟩ : ∃ i ty, v = .fvar i ty := by
      cases v <;> simp only [ViewR] at hvr <;> (try (rw [h1v] at hvr; simp at hvr)) <;> exact ⟨_, _, rfl⟩
    obtain ⟨-, hi1, -, -⟩ := hvr
    rw [getD1_eq] at hi1
    dsimp only
    rw [← hi1, pfK_eq]
    have hhi0 : c.hiAt 0 < 2 ^ 64 := by have := hW.hb; simp only [NestCtx.hiAt] at this ⊢; omega
    have hab2 : (ra.headD 0).toNat + (ra.tail.headD 0).toNat ≤ iwTop m2 := by have := hg2.1; omega
    have hs := pfvE_spec p L.pf n ⟨m2, Locals.init []⟩ vis ctx po pl kb hi ((eViewW m2 (rh.headD 0)).tail.headD 0)
      (ra.headD 0) (ra.tail.headD 0)
    have hR := pfv_ref (p := p) (k := n) (kb := kb) (hi := hi) (i := (eViewW m2 (rh.headD 0)).tail.headD 0) dn vis fe hS2 (hW.grow hg12).u (hW.grow hg12).hs hhi0 hargs2 hab2 hP2
    cases h4 : callE p n "nest_pos_fvar" [vis, ctx, po, pl, kb, hi, (eViewW m2 (rh.headD 0)).tail.headD 0,
        ra.headD 0, ra.tail.headD 0] m2 with
    | error e4 =>
      rw [npaE.k_nest_pos_fvar.eq_1]
      exact RefE.bind_left fun hG => RefE.run_err hs hG.nv hG.nv hR h4
    | ok q4 =>
    obtain ⟨rp, m4⟩ := q4
    rw [npaE.k_nest_pos_fvar.eq_2]
    obtain ⟨s4, hs4, -, k, a3, hrun3, ⟨hS3, hg3, hk, hP3, hA3⟩⟩ := RefE.run_ok hs hR h4
    rw [hs4] at hS3 hg3 hP3 hA3
    replace hA3 : AbsOK m4 := hA3 hA2
    have hK := fun {β : Type} (K : NestFieldKind → AM β) => pfK_run hrun3 K
    rw [hi1] at hK
    have p3 : PStep a2 a3 := pfK_pstep hK hC.check hctx hprog hargsP
    refine RefE.bind_right hrun3 (RefE.ret rfl ⟨hC.of_pstep hS3 hA3 p3, hg12.trans hg3, by simpa using hk, rfl,
      by simpa using (hns.grow (hg12.trans hg3) htop), hP3, hA3, p3.toCore hC.check⟩)
  rw [ite_eq_right h1v]
  by_cases h3v : (eViewW m2 (rh.headD 0)).headD 0 = 3
  · -- a constant: a container
    rw [ite_eq_left h3v]
    obtain ⟨nn, us, rfl⟩ : ∃ nn us, v = .const nn us := by
      cases v <;> simp only [ViewR] at hvr <;> (try (rw [h3v] at hvr; simp at hvr)) <;> exact ⟨_, _, rfl⟩
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
    cases h4 : callE p n "sl_contains" [rdW (m2.arr64 IW) ctx, rdW (m2.arr64 IW) (ctx + 1),
        (eViewW m2 (rh.headD 0)).tail.headD 0] m2 with
    | error e4 =>
      rw [npaE.k_sl_contains.eq_1]
      exact fun hG => ErrClaim.of_callE_nv hG.nv (_root_.L.Checker.nv_mem (by decide +kernel)) h4
    | ok q4 =>
    obtain ⟨ro, m4⟩ := q4
    obtain ⟨s4, hs4, -, hm4, hco⟩ := triple_of_callW (slContains_spec p L.nit.no.hc n ⟨m2, Locals.init []⟩ _ _ _)
      (callW_of_callE h4)
    dsimp only at hm4 hco
    have hm4' : m4 = m2 := by rw [← hs4, hm4]
    rw [hm4']
    have ho := containsW_ok n m2 _ _ _ _ ws hws hco
    dsimp only
    by_cases hon : ro.headD 0 ≠ 0
    · rw [npaE.k_sl_contains.abort1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hon]
      have hin : c.names.contains nn = true := by
        rw [hwsd, ← hnd, contains_map_decI _ hnH ws hwsH]
        cases e : ws.contains ((eViewW m2 (rh.headD 0)).tail.headD 0) with
        | true => rfl
        | false => rw [e] at ho; simp only [Bool.false_eq_true, ite_false] at ho; exact absurd ho hon
      exact RefE.ite_pos hin fun _ => ErrClaim.fail _ _ (by decide)
    have hnotin : c.names.contains nn = false := by
      rw [hwsd, ← hnd, contains_map_decI _ hnH ws hwsH]
      cases e : ws.contains ((eViewW m2 (rh.headD 0)).tail.headD 0) with
      | false => rfl
      | true =>
        rw [e] at ho; simp only [ite_true] at ho
        have := Decidable.of_not_not hon; rw [ho] at this; exact absurd this (by decide)
    rw [npaE.k_sl_contains.arm1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by simpa using hon)]
    refine RefE.ite_neg (by rw [hnotin]; simp) ?_
    have hs := ncE_spec p L.pcont n ⟨m2, Locals.init []⟩ vis ctx fu po pl kb ((eViewW m2 (rh.headD 0)).tail.headD 0)
      ((eViewW m2 (rh.headD 0)).tail.tail.headD 0) (ra.headD 0) (ra.tail.headD 0) ns
    have hR := ih.cont m2 a2 ctx fu po pl kb _ _ _ _ ns c prog args NS ctxP progP nm ls wP.getAppArgs nsP dep hC2
      (hW.grow hg12) hnH husH hargs2 (by have := hg2.1; omega) (hns.grow hg12 htop) hP2 hA2 hc hctx hprog
      (by rw [hnd]; exact hnmP) (by rw [husd]; exact hlsP) hargsP hnsP (ConLeche.Expr.WScoped.getAppArgs hww)
    rw [hnd, husd] at hR
    cases h5 : callE p n "nest_cont" [vis, ctx, fu, po, pl, kb, (eViewW m2 (rh.headD 0)).tail.headD 0,
        (eViewW m2 (rh.headD 0)).tail.tail.headD 0, ra.headD 0, ra.tail.headD 0, ns] m2 with
    | error e5 =>
      rw [npaE.k_nest_cont.eq_1]
      exact RefE.bind_left fun hG => RefE.run_err hs True.intro hG hR h5
    | ok q5 =>
    obtain ⟨rc, m5⟩ := q5
    rw [npaE.k_nest_cont.eq_2]
    obtain ⟨s5, hs5, -, x, a4, hrun4, hQ4⟩ := RefE.run_ok hs hR h5
    rw [hs5] at hQ4
    obtain ⟨hC4, hg4, hk4, hns4, hP4, hA4, c4⟩ := hQ4
    exact RefE.bind_right hrun4 (RefE.ret rfl ⟨hC4, hg12.trans hg4, by simpa using hk4, rfl, by simpa using hns4,
      hP4, hA4, c4⟩)
  rw [ite_eq_right h3v]
  cases v with
  | fvar i ty => exact absurd hvr.1 h1v
  | const nn us => exact absurd hvr.1 h3v
  | _ => exact fun _ => ErrClaim.fail _ _ (by decide)

end steps

end L.Ind
