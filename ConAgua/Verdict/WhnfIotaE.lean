import ConAgua.Verdict.WhnfModels3E
import ConAgua.Verdict.WhnfAppE
import ConAgua.Arena.DefEqKnot

/-!
# `iota_rec_at`'s verdict claims, the top (lane `verdicts-b`, helper `k2`)

`iota_rec_at` and `iota_rec_c` have no verdict site of their own: their claims are
`iota_rec_major`'s (`IotaRecMajorE`), propagated (`iotaRecAtE_of`: `IotaRecAtE`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace L.Arena

theorem whnfIotaE_nv : ∀ f ∈ ["iota_rec_head", "env_find", "ls_node", "peel_pis", "intern_bvar",
    "get_app_fn", "find_rule", "get_app_args", "rule_rhs_at", "mk_app_n", "mk_app_n_from",
    "rec_fire_levels", "iota_case3", "lvls_eq_c", "const_ty_at", "rec_rule_k", "is_ctor_app",
    "is_str_lit", "erec_push", "rec_fire_args", "stack_cover"], f ∈ L.Checker.nvFns := by
  decide +kernel

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
  rw [if_pos hc]; exact hm

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
  · rw [if_pos f0] at hW; cases hW
  rw [if_neg f0] at hW
  obtain ⟨ci, hfind, hci⟩ := hfsome f0
  by_cases k5 : rdW (s₀.mem.arr64 EREC) (re.tail.headD 0) ≠ 5
  · rw [if_pos k5] at hW; cases hW
  rw [if_neg k5] at hW
  obtain ⟨cv, rules, rfl, hcv, hrules⟩ := (decCI_rec_rd herec hci).1 (Classical.not_not.mp k5)
  generalize hE0 : s₀.mem.arr64 EREC = E at *
  generalize hrecP : re.tail.headD 0 = recP at *
  by_cases s0 : sn = 0
  · rw [if_pos s0] at hW; cases hW
  rw [if_neg s0] at hW
  have hsn1 : (sn - 1).toNat = sn.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ (by
      have : sn.toNat ≠ 0 := fun h => s0 (UInt64.toNat_inj.mp (by simpa using h))
      rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
  have hsnp : sn.toNat ≠ 0 := fun h => s0 (UInt64.toNat_inj.mp (by simpa using h))
  by_cases a1 : sn - 1 ≠ rdW E (recP + 5)
  · rw [if_pos a1] at hW; cases hW
  rw [if_neg a1] at hW
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
  · rw [if_pos u1] at hW; cases hW
  rw [if_neg u1] at hW
  by_cases p0 : rp.headD 0 = 0
  · rw [if_pos p0] at hW; cases hW
  rw [if_neg p0] at hW
  have hW' := err_of_k (by intro q e; simp [irCE.k_iota_rec_major]) (fun _ => rfl) hW
  cases n with
  | zero => exact ErrClaim.of_callE_zero hW'
  | succ N =>
  have hma := hM N (hk.mono (by omega)) (hkE.mono (by omega)) F (by omega) (by omega)
    ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe MM eb mode d c us recP so sn cv rules xs hS
    hm4 hebm hcw hus
  simp only [hE0] at hma
  refine ErrClaim.of_run_err (fun ce h' => cT_err_major _ _ _ _ _ _ _ _ a₀ _ _ _ _ _ _
    hfind hn hvl hrunP' ⟨htk, by
      rw [hlen]; have := Classical.not_not.mp u1; simp only [List.tail_cons, List.headD_cons] at this
      rw [this], by unfold decOpt; rw [if_neg p0]; rfl⟩ ce (by rw [takeEidx_size]; exact h'))
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
  · rw [if_pos v0] at hW; cases hW
  rw [if_neg v0] at hW
  obtain ⟨htag, hview, hcw, husw⟩ := hyes v0
  have hvc := L.Ind.EStore.viewConst_of_view _ _ htag _ _ hview
  have hW' := err_of_k (by intro q e; simp [irAtE.k_iota_rec_c]) (fun _ => rfl) hW
  cases n with
  | zero => exact ErrClaim.of_callE_zero hW'
  | succ N =>
  exact ErrClaim.of_run_err (fun ce h' => at_err_c _ _ _ _ _ _ _ a₀ _ _ htag hvc ce h')
    (CoreSpecE.of_callE (iotaRecC_refinesE p hp hnv hM N (hk.mono (by omega)) (hkE.mono (by omega)) F
      (by omega) (by omega) ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe M eb mode d _ _ so sn xs hS
      hpre.mode4 hpre.eb_mode hcw husw hsa hsat) hW')

end iotaTop

end L.Arena
