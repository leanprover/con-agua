import ConAgua.Verdict.WhnfModels3E
import ConAgua.Verdict.WhnfAppE
/-!
# `iota_rec_at`'s verdict claims, the top (lane `verdicts-b`, helper `k2`)

`iota_rec_at` and `iota_rec_c` have no verdict site of their own: their claims are
`iota_rec_major`'s (`IotaRecMajorE`), propagated (`iotaRecAtE_of`: `IotaRecAtE`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

theorem whnfIotaE_nv : ∀ f ∈ ["iota_rec_head", "env_find", "ls_node", "peel_pis", "intern_bvar",
    "get_app_fn", "find_rule", "get_app_args", "rule_rhs_at", "mk_app_n", "mk_app_n_from",
    "rec_fire_levels", "iota_case3", "lvls_eq_c", "const_ty_at", "rec_rule_k", "is_ctor_app",
    "is_str_lit", "erec_push", "rec_fire_args", "stack_cover"], f ∈ L.Checker.nvFns :=
  _root_.L.Checker.nv_sub (by decide +kernel)

/-- `iota_rec_major`'s error claim at fuel `N + 1` (the premises of `iotaRecMajor_refines'`). -/
def IotaRecMajorE (p : Prog) : Prop :=
  ∀ (N : Nat), KnotUpTo p N → KnotUpToE p N → ∀ (F : Nat), N ≤ F → N ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d c us recP so sn : Word) (cv : IConstantVal) (rules : List IRecRule)
    (xs : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 → HW c → HW us →
    decCV (s₀.mem.arr64 EREC) (recP.toNat + 1) = some cv →
    decRules (s₀.mem.arr64 EREC) (rdW (s₀.mem.arr64 EREC) (recP + 7)).toNat
      (rdW (s₀.mem.arr64 EREC) (recP + 8)).toNat = some rules →
    (∃ cr mI rP, fe.find? cr = some (.recInfo cv mI rP rules)) →
    SpineR s₀.mem so sn xs → so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat →
    (rdW (s₀.mem.arr64 EREC) (recP + 5)).toNat + 1 = sn.toNat →
    CoreSpecE p (N + 1) "iota_rec_major" [mode, vis, d, c, us, recP, so, sn]
      (iotaRecMajorT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI c) (decI us)
        cv (rdW (s₀.mem.arr64 EREC) (recP + 5)).toNat (rdW (s₀.mem.arr64 EREC) (recP + 6)).toNat rules
        xs.toList) s₀ a₀

theorem cT_err_major (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (c : NIdx)
    (us : LsIdx) (sargs : Array EIdx) (n : Nat) (a : AState) (cv : IConstantVal) (mI rP : Nat)
    (rules : List IRecRule) (usl : Nat) (pe : Option EIdx)
    (hf : fe.find? c = some (.recInfo cv mI rP rules)) (hn : n = mI + 1)
    (hl : a.store.lss.viewLen us = some usl) (hp : (peelPis (mI + 1) cv.type).run a = .ok (pe, a))
    (hc : (takeEidx sargs n).toList.length = mI + 1 ∧ usl = cv.levelParams.length ∧
      pe.isSome = true) (ce : CheckError)
    (hm : (iotaRecMajorT mode r fe depth c us cv mI rP rules (takeEidx sargs n).toList).run a =
      .error ce) :
    (iotaRecCT mode r fe depth c us sargs n).run a = .error ce := by
  subst hn
  simp only [iotaRecCT, hf, ne_eq, not_true_eq_false, ↓reduceIte, StateT.run_bind,
    viewLsLen_run, hl, except_ok_bind, hp]
  rw [ite_eq_left hc]; exact hm

section iotaTop
variable (p : Prog) (hp : IotaRecProg' p) (hnv : closedNV p L.Checker.nvFns = true)
  (hM : IotaRecMajorE p)

include hp hnv hM in
/-- **`iota_rec_c`'s verdicts** are `iota_rec_major`'s. -/
theorem iotaRecC_refinesE :
    ∀ (n : Nat), KnotUpTo p n → KnotUpToE p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d c us so sn : Word) (xs : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 → HW c → HW us →
    SpineR s₀.mem so sn xs → so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat →
    CoreSpecE p (n + 1) "iota_rec_c" [mode, vis, d, c, us, so, sn]
      (iotaRecCT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI c) (decI us) xs
        xs.size) s₀ a₀ := by
  intro n hk hkE F hnF hn62 s₀ a₀ dn vis fe MM eb mode d c us so sn xs hS hm4 hebm hcw hus hsa hsat
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (irCE_spec p hp.recC (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d c us so sn) hc0 (Err.code_ne_of_cls hk0)
  simp only [irCE] at hW
  have herec := hS.erec
  have hsz : xs.size = sn.toNat := hsa.size
  cases c1 : callE p n "env_find" [c, vis] s₀.mem with
  | error e1 =>
    rw [c1, irCE.k_env_find.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfIotaE_nv "env_find" (by simp)) c1
  | ok q =>
  obtain ⟨re, m1⟩ := q
  rw [c1] at hW
  simp only [irCE.k_env_find] at hW
  obtain ⟨hm1, -, hfsome⟩ := irEnvFind p hp.toIotaProg' n dn s₀.mem vis fe hS.env c hcw re m1
    (callW_of_callE c1)
  subst m1
  by_cases f0 : re.headD 0 = 0
  · rw [ite_eq_left f0] at hW; cases hW
  rw [ite_eq_right f0] at hW
  obtain ⟨ci, hfind, hci⟩ := hfsome f0
  by_cases k5 : rdW (s₀.mem.arr64 EREC) (re.tail.headD 0) ≠ 5
  · rw [ite_eq_left k5] at hW; cases hW
  rw [ite_eq_right k5] at hW
  obtain ⟨cv, rules, rfl, hcv, hrules⟩ := (decCI_rec_rd herec hci).1 (Classical.not_not.mp k5)
  generalize hE0 : s₀.mem.arr64 EREC = E at *
  generalize hrecP : re.tail.headD 0 = recP at *
  by_cases s0 : sn = 0
  · rw [ite_eq_left s0] at hW; cases hW
  rw [ite_eq_right s0] at hW
  have hsn1 : (sn - 1).toNat = sn.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ (by
      have : sn.toNat ≠ 0 := fun h => s0 (UInt64.toNat_inj.mp (by simpa using h))
      rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
  have hsnp : sn.toNat ≠ 0 := fun h => s0 (UInt64.toNat_inj.mp (by simpa using h))
  by_cases a1 : sn - 1 ≠ rdW E (recP + 5)
  · rw [ite_eq_left a1] at hW; cases hW
  rw [ite_eq_right a1] at hW
  have hn : xs.size = (rdW E (recP + 5)).toNat + 1 := by
    have := congrArg UInt64.toNat (Classical.not_not.mp a1); rw [hsn1] at this; omega
  obtain ⟨-, hname, hlps, hlen, htyw, htype⟩ := decCV_rd1 herec hcv
  cases c2 : callE p n "ls_node" [us] s₀.mem with
  | error e2 =>
    rw [c2, irCE.k_ls_node.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfIotaE_nv "ls_node" (by simp)) c2
  | ok q =>
  obtain ⟨rl, m2⟩ := q
  rw [c2] at hW
  simp only [irCE.k_ls_node] at hW
  obtain ⟨t2, ht2, hs2, hne2, hr2⟩ := triple_of_callE
    (lsNode_spec p hp.lvl.lsnode n ⟨s₀.mem, Locals.init []⟩ us) c2
  have hm2 : m2 = s₀.mem := by rw [← ht2, hs2]
  subst hm2
  obtain ⟨o, l, hol⟩ : ∃ o l, rl = [o, l] := by
    rcases lsNodeW_cases s₀.mem us with h | ⟨o, l, h⟩
    · rw [hr2] at hne2; exact absurd h hne2
    · exact ⟨o, l, by rw [hr2]; exact h⟩
  have hvl := lsNodeW_viewLen hS.arena.1 hus (by rw [← hr2, hol])
  subst hol
  rw [hE0] at hW
  cases c3 : callE p n "peel_pis" [sn, rdW E (recP + 4)] s₀.mem with
  | error e3 =>
    rw [c3, irCE.k_peel_pis.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfIotaE_nv "peel_pis" (by simp)) c3
  | ok q =>
  obtain ⟨rp, m3⟩ := q
  rw [c3] at hW
  simp only [irCE.k_peel_pis] at hW
  obtain ⟨t3, ht3, hm3, -, -, hrunP⟩ := triple_of_callE
    (peelPis_refines' p hp.spine.peel n ⟨s₀.mem, Locals.init []⟩ a₀ hS.arena.1 sn _ htyw) c3
  have hm3' : s₀.mem = m3 := hm3.symm.trans ht3
  subst hm3'
  rw [hE0] at hW
  have hrunP' : (peelPis ((rdW E (recP + 5)).toNat + 1) cv.type).run a₀ =
      .ok (decOpt (rp.headD 0) (rp.tail.headD 0), a₀) := by
    rw [htype, ← hn, hsz]; exact hrunP
  have htk : (takeEidx xs xs.size).toList.length = (rdW E (recP + 5)).toNat + 1 := by
    rw [takeEidx_size]; simp [hn]
  by_cases u1 : [o, l].tail.headD 0 ≠ rdW E (recP + 3)
  · rw [ite_eq_left u1] at hW; cases hW
  rw [ite_eq_right u1] at hW
  by_cases p0 : rp.headD 0 = 0
  · rw [ite_eq_left p0] at hW; cases hW
  rw [ite_eq_right p0] at hW
  have hW' := err_of_k (by intro q e; simp [irCE.k_iota_rec_major]) (fun _ => rfl) hW
  cases n with
  | zero => exact ErrClaim.of_callE_zeroW hW'
  | succ N =>
  have hma := hM N (hk.mono (by omega)) (hkE.mono (by omega)) F (by omega) (by omega)
    ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe MM eb mode d c us recP so sn cv rules xs hS
    hm4 hebm hcw hus
  simp only [hE0] at hma
  refine ErrClaim.of_run_err (fun ce h' => cT_err_major _ _ _ _ _ _ _ _ a₀ _ _ _ _ _ _
    hfind hn hvl hrunP' ⟨htk, by
      rw [hlen]; have := Classical.not_not.mp u1; simp only [List.tail_cons, List.headD_cons] at this
      rw [this], by unfold decOpt; rw [ite_eq_right p0]; rfl⟩ ce (by rw [takeEidx_size]; exact h'))
    (CoreSpecE.of_callE (hma hcv hrules ⟨_, _, _, hfind⟩ hsa hsat (by omega)) hW')

theorem at_err_c (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (hd : EIdx)
    (sargs : Array EIdx) (n : Nat) (a : AState) (c : NIdx) (us : LsIdx)
    (ht : hd.tag = ETag.const) (hv : a.store.viewConst hd = some (c, us)) (ce : CheckError)
    (h : (iotaRecCT mode r fe depth c us sargs n).run a = .error ce) :
    (iotaRecAt mode r fe depth hd sargs n).run a = .error ce := by
  have hvr : (viewConst hd).run a = .ok (some (c, us), a) := by
    show Except.ok (a.store.viewConst hd, a) = _; rw [hv]
  rw [iotaRecAt_eq]
  simp only [ht, beq_self_eq_true, ↓reduceIte, StateT.run_bind, hvr, except_ok_bind, h]

include hp hnv hM in
/-- **`IotaRecAtE`**: `iota_rec_at`'s verdicts are `iota_rec_c`'s. -/
theorem iotaRecAtE_of : IotaRecAtE p := by
  intro n hk hkE F s₀ a₀ dn vis fe M eb mode d hd so sn xs hnF hn62 hpre hhd hsa hsat
  have hS := hpre.rel
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (irAtE_spec p hp.iotaRecAt (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d hd so sn) hc0 (Err.code_ne_of_cls hk0)
  simp only [irAtE] at hW
  cases c1 : callE p n "iota_rec_head" [hd] s₀.mem with
  | error e1 =>
    rw [c1, irAtE.k_iota_rec_head.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfIotaE_nv "iota_rec_head" (by simp)) c1
  | ok q =>
  obtain ⟨rv, m1⟩ := q
  rw [c1] at hW
  simp only [irAtE.k_iota_rec_head] at hW
  obtain ⟨hm1, -, hyes⟩ := irCallW_head p hp.head n s₀.mem a₀ hS.arena.1 hd hhd rv m1
    (callW_of_callE c1)
  subst m1
  by_cases v0 : rv.headD 0 = 0
  · rw [ite_eq_left v0] at hW; cases hW
  rw [ite_eq_right v0] at hW
  obtain ⟨htag, hview, hcw, husw⟩ := hyes v0
  have hvc := L.Ind.EStore.viewConst_of_view _ _ htag _ _ hview
  have hW' := err_of_k (by intro q e; simp [irAtE.k_iota_rec_c]) (fun _ => rfl) hW
  cases n with
  | zero => exact ErrClaim.of_callE_zeroW hW'
  | succ N =>
  exact ErrClaim.of_run_err (fun ce h' => at_err_c _ _ _ _ _ _ _ a₀ _ _ htag hvc ce h')
    (CoreSpecE.of_callE (iotaRecC_refinesE p hp hnv hM N (hk.mono (by omega)) (hkE.mono (by omega)) F
      (by omega) (by omega) ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe M eb mode d _ _ so sn xs hS
      hpre.mode4 hpre.eb_mode hcw husw hsa hsat) hW')

end iotaTop

/-! ## `iota_rec_major` -/

/-- `prepare_major`'s error claim at fuel `N + 1` (the premises of `prepareMajor_refines'`). -/
def PrepareMajorE (p : Prog) : Prop :=
  ∀ (N : Nat), KnotUpTo p N → KnotUpToE p N → ∀ (F : Nat), N ≤ F → N ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d rec ro rc major : Word) (rules : List IRecRule),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 → HW major →
    decRules (s₀.mem.arr64 EREC) ro.toNat rc.toNat = some rules →
    CoreSpecE p (N + 1) "prepare_major" [mode, vis, d, rec, ro, rc, major]
      (prepareMajor (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI rec) rules
        (decE major)) s₀ a₀

/-- `iota_rec_fire`'s error claim at fuel `N + 1` (the premises of `iotaRecFire_refines'`). -/
def IotaRecFireE (p : Prog) : Prop :=
  ∀ (N : Nat), KnotUpTo p N → KnotUpToE p N → ∀ (F : Nat), N ≤ F → N ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d c us recP so usj ctorP rl major sn : Word) (lps : List NIdx)
    (rule : IRecRule) (cvj : IConstantVal) (np nf : Nat) (args : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 → HW c → HW us → HW usj →
    HW major →
    hslice? (s₀.mem.arr64 EREC) (rdW (s₀.mem.arr64 EREC) (recP + 2)).toNat
      (rdW (s₀.mem.arr64 EREC) (recP + 3)).toNat = some lps →
    decRule (s₀.mem.arr64 EREC) rl.toNat = some rule →
    decCI (s₀.mem.arr64 EREC) dn ctorP.toNat = some (.ctorInfo cvj np nf) →
    FireEnv fe lps rule cvj →
    SpineR s₀.mem so sn args → so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat →
    (rdW (s₀.mem.arr64 EREC) (recP + 5)).toNat + 1 = sn.toNat →
    CoreSpecE p (N + 1) "iota_rec_fire" [mode, vis, d, c, us, recP, so, usj, ctorP, rl, major]
      (iotaRecFireT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI c)
        (rdW (s₀.mem.arr64 EREC) (recP + 5)).toNat (rdW (s₀.mem.arr64 EREC) (recP + 6)).toNat lps
        (decI us) args.toList (decE major) (decI usj) cvj rule) s₀ a₀

section majorRunE
variable (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (c : NIdx)
  (us : LsIdx) (cv : IConstantVal) (mI rP : Nat) (rules : List IRecRule) (args : List EIdx)

theorem majorT_err_pm (a a0 : AState) (b0 : EIdx)
    (h0 : (internE (.bvar 0)).run a = .ok (b0, a0)) (ce : CheckError)
    (h1 : (prepareMajor mode r fe depth c rules (args.getD mI b0)).run a0 = .error ce) :
    (iotaRecMajorT mode r fe depth c us cv mI rP rules args).run a = .error ce := by
  simp only [iotaRecMajorT, StateT.run_bind, h0, except_ok_bind, h1]; rfl

theorem majorT_err_fire (a a0 a1 : AState) (b0 major hh : EIdx) (cj : NIdx) (usj : LsIdx)
    (cvj : IConstantVal) (np nf : Nat) (rl : IRecRule)
    (h0 : (internE (.bvar 0)).run a = .ok (b0, a0))
    (h1 : (prepareMajor mode r fe depth c rules (args.getD mI b0)).run a0 = .ok (major, a1))
    (h2 : (getAppFn coreWalkFuel major).run a1 = .ok (hh, a1)) (ht : hh.tag = ETag.const)
    (hv : a1.store.view hh = some (.const cj usj)) (hf : fe.find? cj = some (.ctorInfo cvj np nf))
    (hr : findRule rules cj = some rl) (ce : CheckError)
    (h3 : (iotaRecFireT mode r fe depth c mI rP cv.levelParams us args major usj cvj rl).run a1 =
      .error ce) :
    (iotaRecMajorT mode r fe depth c us cv mI rP rules args).run a = .error ce := by
  simp only [iotaRecMajorT, StateT.run_bind, h0, except_ok_bind, h1, h2, ht, beq_self_eq_true,
    ↓reduceIte, view_run_of _ _ _ hv, hf, hr, h3]

end majorRunE

section major
variable (p : Prog) (hp : IotaRecProg' p) (hc : IotaCallees p) (hw : WhnfCallees p)
  (hsup : ∀ fe : IFEnv, SupKeep fe) (hmtc : MajorToCtorOK p) (hEK : ErecKeptKnot p)
  (hnv : closedNV p L.Checker.nvFns = true) (hPM : PrepareMajorE p) (hF : IotaRecFireE p)

include hp hc hw hsup hmtc hEK hnv hPM hF in
/-- **`IotaRecMajorE`**: `iota_rec_major`'s verdicts are `prepare_major`'s and `iota_rec_fire`'s. -/
theorem iotaRecMajorE_of : IotaRecMajorE p := by
  intro n hk hkE F hnF hn62 s₀ a₀ dn vis fe MM eb mode d c us recP so sn cv rules xs hS hm4 hebm hcw hus
    hcv hrules hrecF hsa hsat hmI
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (irMajorE_spec p hp.major (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d c us recP so sn) hc0 (Err.code_ne_of_cls hk0)
  simp only [irMajorE] at hW
  have hspn := hS.spn
  have herec := hS.erec
  obtain ⟨-, -, hlps, -, -, -⟩ := decCV_rd1 herec hcv
  generalize hE0 : s₀.mem.arr64 EREC = E at *
  cases c0 : callE p n "intern_bvar" [0] s₀.mem with
  | error e0 =>
    rw [c0, irMajorE.k_intern_bvar.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfIotaE_nv "intern_bvar" (by simp)) c0
  | ok q =>
  obtain ⟨rb, m1⟩ := q
  rw [c0] at hW
  simp only [irMajorE.k_intern_bvar] at hW
  obtain ⟨hrun0, hS1, hSt1, e1, hspn1⟩ := irCallW_internBVar p hp n hS 0 rb m1 (callW_of_callE c0)
  rw [e1, hE0, hspn1] at hW
  have hmIl : (rdW E (recP + 5)).toNat < sn.toNat := by omega
  have hmw : so + rdW E (recP + 5) = so + (rdW E (recP + 5)).toNat.toUInt64 := by
    rw [toUInt64_toNat_self]
  have hmaj : HW (rdW (s₀.mem.arr64 SPN) (so + rdW E (recP + 5))) := by
    have := hsa.lt _ hmIl; unfold HW; rw [hmw]; exact this
  have hgetD : xs.toList.getD (rdW E (recP + 5)).toNat (decE (rb.headD 0)) =
      decE (rdW (s₀.mem.arr64 SPN) (so + rdW E (recP + 5))) := by
    have hsz := hsa.size
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [hsz]; exact hmIl),
      Option.getD_some]
    have := hsa.get _ (by rw [hsz]; exact hmIl)
    simp only [Array.getElem_toList]
    rw [this, hmw]; rfl
  cases c1 : callE p n "prepare_major" [mode, vis, d, c, rdW E (recP + 7), rdW E (recP + 8),
      rdW (s₀.mem.arr64 SPN) (so + rdW E (recP + 5))] m1 with
  | error e1' =>
    rw [c1, irMajorE.k_prepare_major.none] at hW; cases hW
    cases n with
    | zero => exact ErrClaim.of_callE_zeroW c1
    | succ N =>
    exact ErrClaim.of_run_err (fun ce h' => majorT_err_pm (h0 := hrun0) (ce := ce)
        (h1 := by rw [hgetD]; exact h') ..)
      (CoreSpecE.of_callE (hPM N (hk.mono (by omega)) (hkE.mono (by omega)) F (by omega) (by omega)
        ⟨m1, Locals.init []⟩ _ dn vis fe MM eb mode d c (rdW E (recP + 7)) (rdW E (recP + 8))
        (rdW (s₀.mem.arr64 SPN) (so + rdW E (recP + 5))) rules hS1 hm4 hebm hmaj
        (by show decRules (m1.arr64 EREC) _ _ = _; rw [e1, hE0]; exact hrules)) c1)
  | ok q =>
  obtain ⟨rm, m2⟩ := q
  rw [c1] at hW
  simp only [irMajorE.k_prepare_major] at hW
  cases n with
  | zero =>
    obtain ⟨e', he', -⟩ := callE_zero p "intern_bvar" [0] s₀.mem
    rw [c0] at he'; cases he'
  | succ N =>
  have hpm := prepareMajor_refines' p hp.toIotaProg4 hc hw hsup hmtc hEK N (hk.mono (by omega)) F
    (by omega) (by omega) ⟨m1, Locals.init []⟩ _ dn vis fe MM eb mode d c (rdW E (recP + 7))
    (rdW E (recP + 8)) (rdW (s₀.mem.arr64 SPN) (so + rdW E (recP + 5))) rules hS1 hm4 hebm hmaj
  obtain ⟨hrun1, ⟨M2, hS2, hK2, hSt2⟩, hr1⟩ := CoreSpec.run (hpm (by
    show decRules (m1.arr64 EREC) _ _ = _; rw [e1, hE0]; exact hrules)) (callW_of_callE c1)
  simp only [decH] at hrun1
  have e2 : m2.arr64 EREC = E := by rw [hEK _ _ _ _ _ _ (by simp) (callW_of_callE c1), e1, hE0]
  cases c2 : callE p (N + 1) "get_app_fn" [rm.headD 0] m2 with
  | error e2' =>
    rw [c2, irMajorE.k_get_app_fn.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfIotaE_nv "get_app_fn" (by simp)) c2
  | ok q =>
  obtain ⟨rh, m3⟩ := q
  rw [c2] at hW
  simp only [irMajorE.k_get_app_fn] at hW
  obtain ⟨t2, ht2, hm3, -, hhw, hrun2⟩ := triple_of_callE
    (getAppFn_refines' p hp.spine.fn (N + 1) ⟨m2, Locals.init []⟩ _ hS2.arena.1 (rm.headD 0) hr1) c2
  have hm3' : m2 = m3 := hm3.symm.trans ht2
  subst hm3'
  cases c3 : callE p (N + 1) "iota_rec_head" [rh.headD 0] m2 with
  | error e3 =>
    rw [c3, irMajorE.k_iota_rec_head.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfIotaE_nv "iota_rec_head" (by simp)) c3
  | ok q =>
  obtain ⟨rv, m4⟩ := q
  rw [c3] at hW
  simp only [irMajorE.k_iota_rec_head] at hW
  obtain ⟨hm4, -, hyes⟩ := irCallW_head p hp.head (N + 1) m2 _ hS2.arena.1 _ hhw rv m4
    (callW_of_callE c3)
  subst m4
  have hSt12 := hSt1.trans hSt2
  by_cases v0 : rv.headD 0 = 0
  · rw [ite_eq_left v0] at hW; cases hW
  rw [ite_eq_right v0] at hW
  obtain ⟨htag, hview, hcjw, husjw⟩ := hyes v0
  cases c4 : callE p (N + 1) "env_find" [rv.tail.headD 0, vis] m2 with
  | error e4 =>
    rw [c4, irMajorE.k_env_find.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfIotaE_nv "env_find" (by simp)) c4
  | ok q =>
  obtain ⟨re, m5⟩ := q
  rw [c4] at hW
  simp only [irMajorE.k_env_find] at hW
  obtain ⟨hm5, -, hfsome⟩ := irEnvFind p hp.toIotaProg' (N + 1) dn m2 vis fe hS2.env _ hcjw re m5
    (callW_of_callE c4)
  subst m5
  rw [e2] at hW
  by_cases f0 : re.headD 0 = 0
  · rw [ite_eq_left f0] at hW; cases hW
  rw [ite_eq_right f0] at hW
  obtain ⟨ci, hfind, hci⟩ := hfsome f0
  rw [e2] at hci
  by_cases k4 : rdW E (re.tail.headD 0) ≠ 4
  · rw [ite_eq_left k4] at hW; cases hW
  rw [ite_eq_right k4] at hW
  obtain ⟨cvj, np, nf, rfl, -⟩ := decCI_ctor_rd hci (Classical.not_not.mp k4)
  have hEsz : (m2.arr64 EREC).size < 2 ^ 64 := by rw [e2]; omega
  have hrules2 : decRules (m2.arr64 EREC) (rdW E (recP + 7)).toNat (rdW E (recP + 8)).toNat =
      some rules := by rw [e2]; exact hrules
  cases c5 : callE p (N + 1) "find_rule" [rdW E (recP + 7), rdW E (recP + 8), rv.tail.headD 0] m2 with
  | error e5 =>
    rw [c5, irMajorE.k_find_rule.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfIotaE_nv "find_rule" (by simp)) c5
  | ok q =>
  obtain ⟨rr, m6⟩ := q
  rw [c5] at hW
  simp only [irMajorE.k_find_rule] at hW
  obtain ⟨t5, ht5, hm6, -, hfr⟩ := triple_of_callE
    (findRule_refines p hp.findRule (N + 1) ⟨m2, Locals.init []⟩ _ _ _ rules hcjw hEsz hrules2) c5
  have hm6' : m2 = m6 := hm6.symm.trans ht5
  subst hm6'
  by_cases g0 : rr.headD 0 = 0
  · rw [ite_eq_left g0] at hW; cases hW
  rw [ite_eq_right g0] at hW
  obtain ⟨rule, hdr⟩ := findRule_found p hp.findRule (N + 1) m2 _ _ _ rules hEsz hrules2 rr m2
    (callW_of_callE c5) g0
  rw [e2] at hdr
  have hfrs : findRule rules (decI (rv.tail.headD 0)) = some rule := by
    rw [hfr]; simp only [decRuleAt, g0, ↓reduceIte, e2, hdr]
  obtain ⟨hmem, -⟩ := findRule_mem _ _ _ hfrs
  have hW' := err_of_k (by intro q e; simp [irMajorE.k_iota_rec_fire]) (fun _ => rfl) hW
  have hfi := hF N (hk.mono (by omega)) (hkE.mono (by omega)) F (by omega)
    (by omega) ⟨m2, Locals.init []⟩ _ dn vis fe M2 eb mode d c us recP so (rv.tail.tail.headD 0)
    (re.tail.headD 0) (rr.tail.headD 0) (rm.headD 0) sn cv.levelParams rule cvj np nf xs hS2 hm4 hebm
    hcw hus husjw hr1
  simp only [e2] at hfi
  have hfe : FireEnv fe cv.levelParams rule cvj := by
    obtain ⟨cr, mI, rP, hfr⟩ := hrecF
    exact ⟨⟨cr, cv, mI, rP, rules, hfr, rfl, hmem⟩, ⟨_, np, nf, hfind⟩⟩
  exact ErrClaim.of_run_err (fun ce h' => majorT_err_fire (h0 := hrun0)
      (h1 := by rw [hgetD]; exact hrun1) (h2 := hrun2) (ht := htag) (hv := hview) (hf := hfind)
      (hr := hfrs) (ce := ce) (h3 := h') ..)
    (CoreSpecE.of_callE (hfi hlps hdr hci hfe (hsa.keep hSt12.size hSt12.below hsat hspn)
      (by rw [hSt12.1]; exact hsat) hmI) hW')

end major

end L.Arena
