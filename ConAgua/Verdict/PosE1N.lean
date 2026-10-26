import ConAgua.Verdict.PosE1M
import ConAgua.Verdict.DeclValE

/-!
# `nest_inst_type_ty`, `nest_inst_type`: error claims (lane `verdicts-b`, helper `ia2`, fork `kn1`)

`ntyE_claim`: a failing `nest_inst_type_ty` (its model `ntyE`) claims the twin's `nestInstType`
fails (the steps before `piBinders` are `nest_inst_type_ty`'s; `ntyW_ok`'s proof on the error model).
`nitE_all`: `NitE` (`PosE.lean`), `nitW_ok`'s proof with `nitLe_realC`'s twin side; the level
comparison's decline by `lvlEqFueled_errT`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind
open L.Arena

theorem ntyE_claim {p : Prog} (hl : NtyLook p) (hIlpf : IlpfF p)
    (hnv : closedNV p _root_.L.Checker.nvFns = true)
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env}
    (k : Nat) {m : Mem} {a : AState} {key : Word} {kk : NestKey} (c : NestCtx) (HI : Nat)
    (hC : StageC dn vis fe env m a) (hk : decNK m key.toNat = some kk)
    (hkin : NKIn m key.toNat (· < iwTop m)) (hksl : NKSl m key) {e : Err}
    (he : ntyE p (k + 1) m vis key = .error e) :
    ErrClaim (ConRon.Arena.nestInstType fe c HI kk) a e := by
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hS := hC.stage
  have hE := hS.1.env
  have hR := hS.1.arena.1
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  have hEb : erTop m ≤ (m.arr64 EREC).size := hS.2.2.1
  have hEs : (m.arr64 EREC).size < 2 ^ 64 := hS.2.2.2.2.1
  obtain ⟨hcH, hcd, hlH, hld, hds, hdsb, hk4⟩ := nk_fields hk hkin htop
  rw [ntyE.arm1] at he
  cases h1 : callE p k "env_find" [rdW (m.arr64 IW) key, vis] m with
  | error e1 =>
    rw [h1, ntyE.k_env_find.none] at he; cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h1
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  obtain ⟨s1, hs1, -, hef⟩ := triple_of_callW (envFind_specW p hl.hx hl.hg hl.hf k ⟨m, Locals.init []⟩ _ vis)
    (callW_of_callE h1)
  dsimp only at hef
  rw [hs1] at hef
  have hm1 := envFindW_mem hef
  subst hm1
  rw [h1] at he
  by_cases hf0 : r1.headD 0 = 0
  · rw [ntyE.k_env_find.abort1 _ _ _ _ _ hf0] at he; cases he; exact absurd rfl hk0
  obtain ⟨-, hfind, ci, hci⟩ := envFindW_hit hef hE hcH hf0
  rw [hci] at hfind
  by_cases h3 : rdW (m1.arr64 EREC) (r1.tail.headD 0) ≠ 3
  · rw [ntyE.k_env_find.abort2 _ _ _ _ _ hf0 h3] at he; cases he; exact absurd rfl hk0
  rw [ntyE.k_env_find.arm1 _ _ _ _ _ hf0 (by simpa using h3)] at he
  generalize r1.tail.headD 0 = q at he hfind hci h3
  have hciq := decCI_idx hci
  have hszE := erecP_size_le m1
  have hk3 : nat? (erecP m1) q.toNat = some 3 := by
    have : (erecP m1)[q.toNat]? = (m1.arr64 EREC)[q.toNat]? := erecP_getE (by omega)
    simp only [nat?, this]
    have hb : q.toNat < (m1.arr64 EREC).size := by omega
    have : rdW (m1.arr64 EREC) q = 3 := by simpa using h3
    simp [rdW, hb] at this ⊢; rw [this]; rfl
  obtain ⟨cv, caps, rfl, hcaps⟩ := decCI_kind3 hci hk3
  have hb16 := decCI_indInfo_bound hci
  have hcv : decCV (erecP m1) (q.toNat + 1) = some cv := by
    simp only [decCI, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at hci
    obtain ⟨kd, hkd, hci⟩ := hci
    rw [hk3] at hkd; cases hkd
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at hci
    obtain ⟨cv', h1, _, _, h2⟩ := hci
    cases h2; exact h1
  have e1 : (q + 1).toNat = q.toNat + 1 := word_add_toNat (by simp; omega)
  have e12 : (q + 1 + 2).toNat = q.toNat + 1 + 1 + 1 := by
    rw [word_add_toNat (by rw [e1]; simp; omega), e1]; rfl
  have e13 : (q + 1 + 3).toNat = q.toNat + 1 + 3 := by
    rw [word_add_toNat (by rw [e1]; simp; omega), e1]; rfl
  obtain ⟨-, hlps, hty⟩ := decCV_some hcv
  obtain ⟨wt, hwt, hwtH, hwtd⟩ := hd?_some hty
  have hrdt : rdW (m1.arr64 EREC) (q + 1 + 3) = wt := by simp [rdW, e13, erecP_get hwt]
  simp only [hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hlps
  obtain ⟨lo, hlo, ll, hll, hsl⟩ := hlps
  have hlen : (rdW (m1.arr64 EREC) (q + 1 + 2)).toNat = cv.levelParams.length := by
    rw [erecP_rdN hll e12]; simpa using (mapM_opt_length _ _ _ hsl).symm
  -- the twin's container
  rw [ConRon.Arena.nestInstType.eq_1]
  refine ErrClaim.bind_right (v := cv) (a₁ := a) (by rw [← hcd, hfind]; rfl) ?_
  -- `view_ls_len`
  cases h2 : callE p k "view_ls_len" [rdW (m1.arr64 IW) (key + 1)] m1 with
  | error e2 =>
    rw [h2, ntyE.k_view_ls_len.none] at he; cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h2
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  obtain ⟨s2, hs2, -, hm2, hln0, hr2⟩ := triple_of_callW (viewLsLen_specE p hl.hls hl.hvl k ⟨m1, Locals.init []⟩ _)
    (callW_of_callE h2)
  simp only at hm2
  rw [hs2] at hm2
  subst hr2
  rw [h2, hm2] at he
  rcases lsNodeW_cases m1 (rdW (m1.arr64 IW) (key + 1)) with hln | ⟨o', l', hln⟩
  · exact absurd hln hln0
  have hvl := lsNodeW_viewLen hR hlH hln
  rw [hld] at hvl
  refine ErrClaim.bind_right (v := some l'.toNat) (a₁ := a) (by simp [ConRon.Arena.viewLsLen, hvl]; rfl) ?_
  simp only [hln, List.tail_cons, List.headD_cons] at he
  by_cases hneq : l' ≠ rdW (m1.arr64 EREC) (q + 1 + 2)
  · rw [ntyE.k_view_ls_len.abort1 _ _ _ _ _ _ (by simpa using hneq)] at he
    cases he
    refine ErrClaim.ite_pos ?_ (ErrClaim.fail _ _ (by decide))
    have : l'.toNat ≠ cv.levelParams.length := by
      rw [← hlen]; intro h; exact hneq (UInt64.toNat_inj.mp h)
    simpa using this
  have hneq' : l' = rdW (m1.arr64 EREC) (q + 1 + 2) := by simpa using hneq
  rw [ntyE.k_view_ls_len.arm1 _ _ _ _ _ _ (by simpa using hneq')] at he
  have hl'eq : l'.toNat = cv.levelParams.length := by rw [← hlen, hneq']
  refine ErrClaim.ite_neg (by simp [hl'eq]) ?_
  rw [hrdt] at he
  -- `strip_pis`
  cases h3c : callE p k "strip_pis" [rdW (m1.arr64 IW) (key + 3), wt] m1 with
  | error e3 =>
    rw [h3c, ntyE.k_strip_pis.none] at he; cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h3c
  | ok q3 =>
  obtain ⟨r3, m3⟩ := q3
  obtain ⟨s3, hs3, -, hst⟩ := triple_of_callW (stripPis_specF p hl.hst k ⟨m1, Locals.init []⟩ _ _)
    (callW_of_callE h3c)
  dsimp only at hst
  rw [hs3] at hst
  rw [h3c] at he
  obtain ⟨x3, a3, hrun3, hS3, hg3, hx3⟩ := stripF_pis_ok dn vis fe _ wt hwtH m1 m3 a r3 hst hS
  have ha3 : a3 = a := stripPis_st _ _ _ _ _ hrun3
  subst a3
  have hdsl := decHL_length m1 hds
  rw [← hdsl, ← hwtd] at hrun3
  refine ErrClaim.bind_right hrun3 ?_
  cases x3 with
  | none =>
    have : r3.headD 0 = 0 := hx3
    rw [ntyE.k_strip_pis.abort1 _ _ _ _ _ _ this] at he; cases he
    exact ErrClaim.fail _ _ (by decide)
  | some q3 =>
  rw [ntyE.k_strip_pis.arm1 _ _ _ _ _ _ (by rw [hx3.1]; decide)] at he
  -- `cv_lps`
  have hcv3 : decCVp m3 (q + 1).toNat = some cv := by
    rw [e1]; exact (erecP_ext m3).decCV ((GrowX.of_grow (q := 0) (n := 0) hg3).erecP.decCV hcv)
  cases h4c : callE p k "cv_lps" [q + 1] m3 with
  | error e4 =>
    rw [h4c, ntyE.k_cv_lps.none] at he; cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h4c
  | ok q4 =>
  obtain ⟨r4, m4⟩ := q4
  obtain ⟨s4, hs4, -, hlp⟩ := triple_of_callW (cvLps_spec p hl.ha hl.hc hl.he hl.hcv k ⟨m3, Locals.init []⟩ _)
    (callW_of_callE h4c)
  dsimp only at hlp
  rw [hs4] at hlp
  rw [h4c, ntyE.k_cv_lps.arm1] at he
  obtain ⟨hS4, hg4, hE4, hdec4, -⟩ := pos2_cvLpsW_stage hlp hS3 hcv3 (by rw [e1]; have := hg3.2.1; omega)
  have hg34 := hg3.trans hg4
  have hlv4 : rdW (m4.arr64 IW) (key + 1) = rdW (m1.arr64 IW) (key + 1) := by
    have e : (key + 1).toNat = key.toNat + 1 := word_add_toNat (by simp; omega)
    simp only [rdW, e]; rw [hg34.2.2.1 _ (by omega)]
  have hwt4 : rdW (m4.arr64 EREC) (q + 1 + 3) = wt := by
    rw [hE4]
    have : (m3.arr64 EREC)[(q + 1 + 3).toNat]? = (m1.arr64 EREC)[(q + 1 + 3).toNat]? := by
      rw [e13]; exact hg3.2.2.2 _ (by omega)
    simp only [rdW, this]; exact hrdt
  rw [hlv4, hwt4] at he
  -- `inst_lp_fast`
  cases h5c : callE p k "inst_lp_fast" [CWF, r4.headD 0, r4.tail.headD 0, rdW (m1.arr64 IW) (key + 1), wt] m4 with
  | error e5 =>
    rw [h5c, ntyE.k_inst_lp_fast.none] at he; cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h5c
  | ok q5 =>
  obtain ⟨r5, m5⟩ := q5
  rw [h5c, ntyE.k_inst_lp_fast.arm1] at he
  obtain ⟨tl, a4, hrun4, ⟨hS5, hg5, htlH, htld⟩, -, hA5⟩ :=
    IlpRd.realC hIlpf hC k CWF _ _ _ _ cv.levelParams m4 m5 a r5 hlH hwtH
      ⟨rfl, (stripF_frame hst).trans (erToIwW_iwFr hlp)⟩ hS4 hdec4 (callW_of_callE h5c)
  rw [CWF_eq, hld, ← hwtd] at hrun4
  refine ErrClaim.bind_right hrun4 ?_
  have hg35 := hg34.trans hg5
  have hrd2 : rdW (m5.arr64 IW) (key + 2) = rdW (m1.arr64 IW) (key + 2) := by
    have e : (key + 2).toNat = key.toNat + 2 := word_add_toNat (by simp; omega)
    simp only [rdW, e]; rw [hg35.2.2.1 _ (by omega)]
  have hrd3 : rdW (m5.arr64 IW) (key + 3) = rdW (m1.arr64 IW) (key + 3) := by
    have e : (key + 3).toNat = key.toNat + 3 := word_add_toNat (by simp; omega)
    simp only [rdW, e]; rw [hg35.2.2.1 _ (by omega)]
  rw [hrd2, hrd3] at he
  -- `inst_pis_with`
  cases h6c : callE p k "inst_pis_with" [rdW (m1.arr64 IW) (key + 2), rdW (m1.arr64 IW) (key + 3), r5.headD 0] m5 with
  | error e6 =>
    rw [h6c, ntyE.k_inst_pis_with.none] at he; cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h6c
  | ok q6 =>
  obtain ⟨r6, m6⟩ := q6
  obtain ⟨s6, hs6, -, hiw⟩ := triple_of_callW (instPisWith_spec p hl.hv hl.hip hl.hi1 k ⟨m5, Locals.init []⟩ _ _ _)
    (callW_of_callE h6c)
  dsimp only at hiw
  rw [hs6] at hiw
  rw [h6c] at he
  obtain ⟨x6, a5, hrun5, hS6, hg6, hx6⟩ := instW_ok k dn fe vis m5 m6 a4 _ _ _ kk.ds r6 hiw hS5 htlH
    (by rw [decHL_agree (RdS.of_grow hg35) (fun j hj => hdsb j hj)]; exact hds) (by unfold NKSl at hksl; omega)
    (by have := hg35.1; exact Nat.le_trans hksl this)
  rw [htld] at hrun5
  refine ErrClaim.bind_right hrun5 ?_
  cases x6 with
  | none =>
    have : r6.headD 0 = 0 := hx6
    rw [ntyE.k_inst_pis_with.abort1 _ _ _ this] at he; cases he
    exact ErrClaim.fail _ _ (by decide)
  | some ty =>
    rw [ntyE.k_inst_pis_with.arm1 _ _ _ (by rw [hx6.1]; decide)] at he; cases he


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
  cases h1 : callE p k "nest_inst_type_ty" [vis, key] m with
  | error e1 =>
    rw [h1, nitE.k_nest_inst_type_ty.eq_1] at he; cases he
    have h1' := triple_of_callE_err (ntyE_spec p hl.ty.hp k ⟨m, Locals.init []⟩ vis key) h1
      (Err.code_ne_of_cls hk0)
    dsimp only at h1'
    cases k with
    | zero => rw [ntyE.eq_1] at h1'; cases h1'; exact absurd rfl hk0
    | succ k => exact ntyE_claim hl.ty hIlpf hnv k c HI hC hk hkin hksl h1'
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1, nitE.k_nest_inst_type_ty.arm1] at he
  obtain ⟨s1, hs1, -, hty⟩ := triple_of_callW
    (nestInstTypeTy_spec' p hl.ty (realCall p) (realCall_spec p) k ⟨m, Locals.init []⟩ vis key) (callW_of_callE h1)
  dsimp only at hty
  rw [hs1] at hty
  cases k with
  | zero => simp [ntyWf] at hty
  | succ k =>
  simp only [ntyWf] at hty
  obtain ⟨cv, caps, a3, q, a4, tl, a5, ty, hfind, hvl, hrun3, hrun4, hrun5, hS1, hg1, htyH, htyd, hA1⟩ :=
    ntyW_ok k dn fe vis m m1 a key kk _ (realCall p) (IlpRd.realC hIlpf hC) hty hS hk hkin hksl
  simp only [List.headD_cons] at htyH htyd
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
  cases h2 : callE p (k + 1) "pi_binders" [CWF, r1.headD 0] m1 with
  | error e2 =>
    rw [h2, nitE.k_pi_binders.eq_1] at he; cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h2
  | ok q2 =>
  obtain ⟨rs, m2⟩ := q2
  rw [h2, nitE.k_pi_binders.arm1] at he
  obtain ⟨s2, hs2, -, hpb, hrs⟩ := triple_of_callW
    (piBinders_spec p hl.ty.ha hl.hc2 hl.ty.hv hl.hs hl.hpb (k + 1) ⟨m1, Locals.init []⟩ CWF _) (callW_of_callE h2)
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
  cases h3 : callE p (k + 1) "e_view" [rs.getD 2 0] m2 with
  | error e3 =>
    rw [h3, nitE.k_e_view.eq_1] at he; cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h3
  | ok q3 =>
  obtain ⟨rv, m2'⟩ := q3
  obtain ⟨s3, hs3, hm3, hv0, hrv⟩ := triple_of_callW (eView_spec p hl.ty.hv (k + 1) ⟨m2, Locals.init []⟩ _)
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
  cases h4 : callE p (k + 1) "nest_occ_any" [rdW (m2'.arr64 IW) ctx, rdW (m2'.arr64 IW) (ctx + 1),
      rdW (m2'.arr64 IW) (ctx + 4), hi, rs.headD 0, rs.getD 1 0] m2' with
  | error e4 =>
    rw [h4, nitE.k_nest_occ_any.eq_1] at he; cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h4
  | ok q4 =>
  obtain ⟨r3, m3⟩ := q4
  obtain ⟨s4, hs4, -, hoa⟩ := triple_of_callW (nestOccAny_spec p hl.no hl.hoa (k + 1) ⟨m2', Locals.init []⟩ _ _ _ _ _ _)
    (callW_of_callE h4)
  dsimp only at hoa
  rw [hs4] at hoa
  rw [h4] at he
  obtain ⟨b, hrunoa, hS3, hg3, hr3, hP3⟩ := noaW_ok dn fe vis _ _ _ _ c.names (k + 1) m2' m3 a5 _ _ bs _ hoa hS2
    hn2 hne2 hdecbs (fun j hj => by omega)
    ((hP.fr (ntyW_mfr (IlpFr.real hIlpf) hty)).fr (piBW_mfr _ _ _ _ _ _ hpb))
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
  cases h5 : callE p (k + 1) "lvl_eq_fueled" [(eViewW m2' (rs.getD 2 0)).tail.headD 0, rdW (m3.arr64 IW) (ctx + 9)] m3 with
  | error e5 =>
    rw [h5, nitE.k_lvl_eq_fueled.eq_1] at he; cases he
    exact lvlEqFueled_errT hq hLC hl.hlf (nvAt_of hnv (by decide +kernel)) _ hC3.stageT huH' hsH _ _ hsL hdv h5
  | ok q5 =>
  obtain ⟨r4, m4⟩ := q5
  rw [h5] at he
  obtain ⟨s5, hs5, -, hle⟩ := triple_of_callW
    (lvlEqFueled_specC p hl.hlf (realCall p) (realCall_spec p) (k + 1) ⟨m3, Locals.init []⟩ _ _) (callW_of_callE h5)
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
