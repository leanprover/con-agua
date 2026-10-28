import ConAgua.Arena.IlpRd
import ConAgua.Verdict.PosE1M

/-!
# `nest_inst_type_ty`: one model and one refinement for both outcomes

`ntyE` (`l_model … unified`, `PosE1M.lean`): its callees outside the verdict closure through their
`Option` models (`view_ls_len` and `inst_lp_fast` through their runs). `nty_ref` refines `ntyT`,
the twin's `nestInstType` up to the instantiated type, for both outcomes. Its ok half is
`nest_inst_type`'s refinement `nitW_ok` (whose hand model reads `nest_inst_type_ty` through its
run, `ntyR`), its error half `nest_inst_type`'s error claim (`nitE_all`, `PosE1N.lean`).
-/

noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind
open L.Arena

/-- `ntyT` with its continuation split off. -/
theorem ntyT_eq {β : Type} (fe : IFEnv) (key : NestKey) (K : EIdx → AM β) :
    ntyT fe key K = ntyT fe key pure >>= K := by
  unfold ntyT
  simp only [bind_assoc]
  congr 1; funext cv
  congr 1; funext o
  split
  · funext s; rfl
  · split
    · funext s; rfl
    · simp only [bind_assoc]
      congr 1; funext q
      split
      · funext s; rfl
      · simp only [bind_assoc]
        congr 1; funext tl
        congr 1; funext t
        split
        · funext s; rfl
        · simp

/-- `nestInstType` is `ntyT` with a continuation. -/
theorem nestInstType_ntyT (fe : IFEnv) (c : NestCtx) (hi : Nat) (key : NestKey) :
    ∃ K, ConRon.Arena.nestInstType fe c hi key = ntyT fe key K := ⟨_, rfl⟩

/-- A failing `ntyT` fails `nestInstType`. -/
theorem ErrClaim.nestInstType {fe : IFEnv} {c : NestCtx} {hi : Nat} {key : NestKey} {a : AState}
    {e : Err} (h : ErrClaim (ntyT fe key pure) a e) :
    ErrClaim (ConRon.Arena.nestInstType fe c hi key) a e := by
  obtain ⟨K, hK⟩ := nestInstType_ntyT fe c hi key
  rw [hK, ntyT_eq]; exact ErrClaim.bind_left h

/-- **`nest_inst_type_ty` refines `ntyT`, both outcomes**: the container (`env_find`), the level
count (`view_ls_len`), `strip_pis`, `cv_lps`, `inst_lp_fast` (its contract `hI`), `inst_pis_with`. -/
theorem nty_ref {p : Prog} (hl : NtyLook p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} (k : Nat) {m : Mem} {a : AState} {key : Word} {kk : NestKey}
    (hI : IlpRd (realCall p) dn vis fe (IlpBase m a)) (hS : StageR dn vis fe m a)
    (hk : decNK m key.toNat = some kk) (hkin : NKIn m key.toNat (· < iwTop m)) (hksl : NKSl m key) :
    RefE (closedNV p _root_.L.Checker.nvFns = true) (ntyE p k m vis key) (ntyT fe kk pure) a
      (fun v ty a' => NtyPost dn vis fe kk m a v.1 v.2 ty a') := by
  cases k with
  | zero => rw [ntyE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ k =>
  have hE := hS.1.env
  have hR := hS.1.arena.1
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  have hEb : erTop m ≤ (m.arr64 EREC).size := hS.2.2.1
  have hEs : (m.arr64 EREC).size < 2 ^ 64 := hS.2.2.2.2.1
  obtain ⟨hcH, hcd, hlH, hld, hds, hdsb, hk4⟩ := nk_fields hk hkin htop
  rw [ntyE.arm1]
  rcases hef : envFindW m (rdW (m.arr64 IW) key) vis with _ | ⟨r1, m1⟩
  · rw [liftE_none, ntyE.k_env_find.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  have hm1 := envFindW_mem hef
  subst hm1
  by_cases hf0 : r1.headD 0 = 0
  · rw [ntyE.k_env_find.abort1 _ _ _ _ _ hf0]; exact RefE.of_cls0 rfl
  obtain ⟨-, hfind, ci, hci⟩ := envFindW_hit hef hE hcH hf0
  rw [hci] at hfind
  by_cases h3 : rdW (m1.arr64 EREC) (r1.tail.headD 0) ≠ 3
  · rw [ntyE.k_env_find.abort2 _ _ _ _ _ hf0 h3]; exact RefE.of_cls0 rfl
  rw [ntyE.k_env_find.arm1 _ _ _ _ _ hf0 (by simpa using h3)]
  generalize r1.tail.headD 0 = q at hfind hci h3 ⊢
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
  unfold ntyT
  refine RefE.bind_right (v := cv) (a₁ := a) (by rw [← hcd, hfind]; rfl) ?_
  -- `view_ls_len`
  rcases h2 : callW p k "view_ls_len" [rdW (m1.arr64 IW) (key + 1)] m1 with _ | ⟨r2, m2⟩
  · rw [liftE_none, ntyE.k_view_ls_len.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨s2, hs2, -, hm2, hln0, hr2⟩ := triple_of_callW (viewLsLen_specE p hl.hls hl.hvl k ⟨m1, Locals.init []⟩ _) h2
  simp only at hm2
  rw [hs2] at hm2
  subst hr2
  rw [hm2]
  rcases lsNodeW_cases m1 (rdW (m1.arr64 IW) (key + 1)) with hln | ⟨o', l', hln⟩
  · exact absurd hln hln0
  have hvl := lsNodeW_viewLen hR hlH hln
  rw [hld] at hvl
  refine RefE.bind_right (v := some l'.toNat) (a₁ := a) (by simp [ConRon.Arena.viewLsLen, hvl]; rfl) ?_
  simp only [hln, List.tail_cons, List.headD_cons]
  by_cases hneq : l' ≠ rdW (m1.arr64 EREC) (q + 1 + 2)
  · rw [ntyE.k_view_ls_len.abort1 _ _ _ _ _ _ (by simpa using hneq)]
    refine RefE.ite_pos ?_ (fun _ => ErrClaim.fail _ _ (by decide))
    have : l'.toNat ≠ cv.levelParams.length := by
      rw [← hlen]; intro h; exact hneq (UInt64.toNat_inj.mp h)
    simpa using this
  have hneq' : l' = rdW (m1.arr64 EREC) (q + 1 + 2) := by simpa using hneq
  rw [ntyE.k_view_ls_len.arm1 _ _ _ _ _ _ (by simpa using hneq')]
  have hl'eq : l'.toNat = cv.levelParams.length := by rw [← hlen, hneq']
  refine RefE.ite_neg (by simp [hl'eq]) ?_
  rw [hrdt]
  -- `strip_pis`
  rcases hst : stripF 6 m1 [rdW (m1.arr64 IW) (key + 3), wt] with _ | ⟨r3, m3⟩
  · rw [liftE_none, ntyE.k_strip_pis.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨x3, a3, hrun3, hS3, hg3, hx3⟩ := stripF_pis_ok dn vis fe _ wt hwtH m1 m3 a r3 hst hS
  have ha3 : a3 = a := stripPis_st _ _ _ _ _ hrun3
  subst a3
  have hdsl := decHL_length m1 hds
  rw [← hdsl, ← hwtd] at hrun3
  refine RefE.bind_right hrun3 ?_
  cases x3 with
  | none =>
    have : r3.headD 0 = 0 := hx3
    rw [ntyE.k_strip_pis.abort1 _ _ _ _ _ _ this]
    exact fun _ => ErrClaim.fail _ _ (by decide)
  | some q3 =>
  rw [ntyE.k_strip_pis.arm1 _ _ _ _ _ _ (by rw [hx3.1]; decide)]
  -- `cv_lps`
  have hcv3 : decCVp m3 (q + 1).toNat = some cv := by
    rw [e1]; exact (erecP_ext m3).decCV ((GrowX.of_grow (q := 0) (n := 0) hg3).erecP.decCV hcv)
  rcases hlp : cvLpsW k m3 (q + 1) with _ | ⟨r4, m4⟩
  · rw [liftE_none, ntyE.k_cv_lps.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, ntyE.k_cv_lps.arm1]
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
  rw [hlv4, hwt4]
  -- `inst_lp_fast`
  rcases hil : callW p k "inst_lp_fast" [CWF, r4.headD 0, r4.tail.headD 0, rdW (m1.arr64 IW) (key + 1), wt] m4
    with _ | ⟨r5, m5⟩
  · rw [liftE_none, ntyE.k_inst_lp_fast.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, ntyE.k_inst_lp_fast.arm1]
  obtain ⟨tl, a4, hrun4, ⟨hS5, hg5, htlH, htld⟩, ⟨_, _, hfA, hfC, hf5⟩, hA5⟩ :=
    hI k CWF _ _ _ _ cv.levelParams m4 m5 a r5 hlH hwtH ⟨rfl, (stripF_frame hst).trans (erToIwW_iwFr hlp)⟩ hS4
      hdec4 hil
  rw [CWF_eq, hld, ← hwtd] at hrun4
  refine RefE.bind_right hrun4 ?_
  have hg35 := hg34.trans hg5
  have hrd2 : rdW (m5.arr64 IW) (key + 2) = rdW (m1.arr64 IW) (key + 2) := by
    have e : (key + 2).toNat = key.toNat + 2 := word_add_toNat (by simp; omega)
    simp only [rdW, e]; rw [hg35.2.2.1 _ (by omega)]
  have hrd3 : rdW (m5.arr64 IW) (key + 3) = rdW (m1.arr64 IW) (key + 3) := by
    have e : (key + 3).toNat = key.toNat + 3 := word_add_toNat (by simp; omega)
    simp only [rdW, e]; rw [hg35.2.2.1 _ (by omega)]
  rw [hrd2, hrd3]
  -- `inst_pis_with`
  rcases hiw : instW k m5 (rdW (m1.arr64 IW) (key + 2)) (rdW (m1.arr64 IW) (key + 3)) (r5.headD 0) with _ | ⟨r6, m6⟩
  · rw [liftE_none, ntyE.k_inst_pis_with.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨x6, a5, hrun5, hS6, hg6, hx6⟩ := instW_ok k dn fe vis m5 m6 a4 _ _ _ kk.ds r6 hiw hS5 htlH
    (by rw [decHL_agree (RdS.of_grow hg35) (fun j hj => hdsb j hj)]; exact hds) (by unfold NKSl at hksl; omega)
    (by have := hg35.1; exact Nat.le_trans hksl this)
  rw [htld] at hrun5
  refine RefE.bind_right hrun5 ?_
  cases x6 with
  | none =>
    have : r6.headD 0 = 0 := hx6
    rw [ntyE.k_inst_pis_with.abort1 _ _ _ this]
    exact fun _ => ErrClaim.fail _ _ (by decide)
  | some ty =>
  obtain ⟨hx61, hx6H, hx6d⟩ := hx6
  rw [ntyE.k_inst_pis_with.arm1 _ _ _ (by rw [hx61]; decide)]
  exact RefE.ret rfl ⟨⟨cv, caps, q3, a, a4, tl, by rw [← hcd]; exact hfind, by rw [hvl, hl'eq], hrun3, hrun4, hrun5⟩, hS6,
    hg35.trans hg6, hx6H, hx6d,
    (AFr.iw (stripF_frame hst)).trans ((AFr.iw (erToIwW_iwFr hlp)).trans (hA5.trans (instW_afr _ _ _ _ _ _ _ hiw))),
    (((MFr.of_iw (stripF_frame hst)).trans (posmemo_cvLpsW_mfr hlp)).trans (MFr.of_frame hf5 hfA hfC)).trans
      (instW_mfr _ _ _ _ _ _ _ hiw)⟩

/-- `nest_inst_type_ty`'s ok half at the real calls (`nest_inst_type`'s refinement `nitW_ok`). -/
theorem nty_ok {p : Prog} (hl : NtyLook p) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {k : Nat} {m : Mem} {a : AState} {key : Word} (hI : IlpRd (realCall p) dn vis fe (IlpBase m a)) :
    NtyOk (realCall p) dn vis fe k m a key := by
  intro kk r1 m1 hS hk hkin hksl h
  obtain ⟨s1, rfl, -, ty, a', -, hpost⟩ :=
    RefE.run_okW (ntyE_spec p hl k ⟨m, Locals.init []⟩ vis key) (nty_ref hl k hI hS hk hkin hksl) h
  exact ⟨ty, a', hpost⟩

end L.Ind

end
