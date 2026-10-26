import ConAgua.Verdict.WhnfUnitE
import ConAgua.Arena.DefEqStuckCert

/-!
# `struct_eta_cert` and its pieces: error claims (lane `verdicts-b`, helper `k2`)

Their verdicts are the `infer_io`, `whnf` slots', `defeq_lst`'s (a hypothesis, `DefeqLstE`, from the
`defeq` family) and the level comparison's out-of-fuel decline (`struct_eta_cert_tail`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false

namespace L.Arena

/-- `defeq_lst`'s error claim at fuel `n + 1` (the premises of `DefeqLstOK`). -/
def DefeqLstE (p : Prog) : Prop :=
  ∀ (n : Nat), KnotUpTo p n → KnotUpToE p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
  ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d ao an bo bn : Word) (xs ys : Array EIdx),
    SlotPre s₀ a₀ dn vis fe M eb mode → SpineR s₀.mem ao an xs → SpineR s₀.mem bo bn ys →
    ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat → bo.toNat + bn.toNat ≤ (spTop s₀.mem).toNat →
    CoreSpecE p (n + 1) "defeq_lst" [mode, vis, d, ao, an, bo, bn]
      (defEqList (coreKnot (decMode mode) fe id F) fe d.toNat xs.toList ys.toList) s₀ a₀

theorem whnfSetE_nv : ∀ f ∈ ["get_app_fn", "env_find", "get_app_args", "ls_node", "reserved_contains_w",
    "lvls_eq_c", "eta_projs", "eta_ctor_shape", "ind_caps", "er_slice_eq", "tower_slots_all"], f ∈ L.Checker.nvFns := by
  decide +kernel

/-! ## `struct_eta_cert_tail` -/

section tailErr
variable (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (b : EIdx) (us : LsIdx) (T : NIdx)
  (us' : LsIdx) (ep nf : Nat) (aargs targs : List EIdx)

theorem setTail_fail (a a₁ : AState) (h1 : (lvlsEq? us us').run a = .ok (none, a₁)) :
    (setTailT r fe depth b us T us' ep nf aargs targs).run a =
      (ConRon.Arena.fail (.notImplemented "resource limit: fuel exhausted: level comparison") :
        AM Bool).run a₁ := by
  simp only [setTailT, StateT.run_bind, h1, except_ok_bind, liftFueled]
  rfl

theorem setTail_err1 (a a₁ : AState) (h1 : (lvlsEq? us us').run a = .ok (some true, a₁)) (ce : CheckError)
    (h2 : (defEqList r fe depth (aargs.take ep) targs).run a₁ = .error ce) :
    (setTailT r fe depth b us T us' ep nf aargs targs).run a = .error ce := by
  simp only [setTailT, StateT.run_bind, h1, except_ok_bind, liftFueled_run_some, ↓reduceIte, h2]; rfl

theorem setTail_err2 (a a₁ a₂ a₃ : AState) (projs : List EIdx)
    (h1 : (lvlsEq? us us').run a = .ok (some true, a₁))
    (h2 : (defEqList r fe depth (aargs.take ep) targs).run a₁ = .ok (true, a₂))
    (h3 : (etaProjs T b nf).run a₂ = .ok (projs, a₃)) (ce : CheckError)
    (h4 : (defEqList r fe depth (aargs.drop ep) projs).run a₃ = .error ce) :
    (setTailT r fe depth b us T us' ep nf aargs targs).run a = .error ce := by
  simp only [setTailT, StateT.run_bind, h1, except_ok_bind, liftFueled_run_some, ↓reduceIte, h2, h3, h4]

end tailErr

section goErr
variable (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (b : EIdx) (c : NIdx) (us : LsIdx)
  (cvc : IConstantVal) (T : NIdx) (us' : LsIdx) (cvT : IConstantVal) (caps : IIndCaps)
  (aargs targs : List EIdx)

theorem setGo_err {m : Mem} {a : AState} (hP : PinsFull m a.pins) (uslen : Nat)
    (hv : a.store.lss.viewLen us' = some uslen)
    (hcond : caps.eta = true ∧ caps.etaCtor = c ∧
      a.pins.reserved.contains T = false ∧ a.pins.reserved.contains c = false ∧
      targs.length = caps.etaParams ∧
      uslen = cvT.levelParams.length ∧
      cvc.levelParams = cvT.levelParams ∧ towerSlotsAll fe T caps.etaFields = true) (ce : CheckError)
    (h : (setTailT r fe depth b us T us' caps.etaParams caps.etaFields aargs targs).run a = .error ce) :
    (setGoT r fe depth b c us cvc T us' cvT caps aargs targs).run a = .error ce := by
  rw [setGoT_run r fe depth b c us cvc T us' cvT caps aargs targs hP uslen hv]
  simp only [StateT.run_bind]
  show (setGoK r fe depth b c us cvc T us' cvT caps aargs targs a.pins.reserved uslen
    (towerSlotsAll fe T caps.etaFields)).run a = _
  unfold setGoK
  rw [if_pos hcond]; exact h

end goErr

section certErr
variable (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (a b : EIdx)

theorem setCert_err_io (s s₁ : AState) (h1 : (etaCtorShape fe a).run s = .ok (true, s₁)) (ce : CheckError)
    (h : (r.inferIO depth b).run s₁ = .error ce) :
    (structEtaCert r fe depth a b).run s = .error ce := by
  simp only [structEtaCert, StateT.run_bind, h1, except_ok_bind, ↓reduceIte, h]; rfl

theorem setCert_err_whnf (s s₁ s₂ : AState) (tb : EIdx) (h1 : (etaCtorShape fe a).run s = .ok (true, s₁))
    (h2 : (r.inferIO depth b).run s₁ = .ok (tb, s₂)) (ce : CheckError)
    (h : (r.whnf depth tb).run s₂ = .error ce) :
    (structEtaCert r fe depth a b).run s = .error ce := by
  simp only [structEtaCert, StateT.run_bind, h1, except_ok_bind, ↓reduceIte, h2, h]; rfl

theorem setCert_err_with (s s₁ s₂ s₃ : AState) (tb wtb : EIdx)
    (h1 : (etaCtorShape fe a).run s = .ok (true, s₁))
    (h2 : (r.inferIO depth b).run s₁ = .ok (tb, s₂)) (h3 : (r.whnf depth tb).run s₂ = .ok (wtb, s₃))
    (ce : CheckError) (h : (structEtaCertWith r fe depth a b wtb).run s₃ = .error ce) :
    (structEtaCert r fe depth a b).run s = .error ce := by
  simp only [structEtaCert, StateT.run_bind, h1, except_ok_bind, ↓reduceIte, h2, h3, h]

end certErr

section set
variable (p : Prog) (hq : StuckProg p) (hi : IotaProg' p) (hc : StuckCallees p)
  (hnv : closedNV p L.Checker.nvFns = true) (hDL : DefeqLstE p)

include hq hi hc hnv hDL in
/-- **`struct_eta_cert_tail`'s verdicts**: the level comparison's out-of-fuel decline and
`defeq_lst`'s. -/
theorem setTail_refinesE (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) (F : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d b us T us2 ao an to tn ep nf : Word) (aargs targs : Array EIdx) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hb : HW b) (hus : HW us)
    (hT : HW T) (hus2 : HW us2) (hdus : ∃ lu, denoteLs a₀.store.lss (decI us) = some lu)
    (hdus2 : ∃ lv, denoteLs a₀.store.lss (decI us2) = some lv) (ha : SpineR s₀.mem ao an aargs)
    (ht : SpineR s₀.mem to tn targs)
    (hat : ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat)
    (htt : to.toNat + tn.toNat ≤ (spTop s₀.mem).toNat) :
    CoreSpecE p (n + 1) "struct_eta_cert_tail" [mode, vis, d, b, us, T, us2, ao, an, to, tn, ep, nf]
      (setTailT (coreKnot (decMode mode) fe id F) fe d.toNat (decE b) (decI us) (decI T) (decI us2)
        ep.toNat nf.toNat aargs.toList targs.toList) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (sectE_spec p hq.setTail (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d b us T us2 ao an to tn ep nf) hc0 (Err.code_ne_of_cls hk0)
  simp only [sectE] at hW
  have hspn := hs.rel.spn
  cases c1 : callE p n "lvls_eq_c" [us, us2] s₀.mem with
  | error e1 =>
    rw [c1, sectE.k_lvls_eq_c.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfSetE_nv "lvls_eq_c" (by simp)) c1
  | ok q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [c1] at hW
  simp only [sectE.k_lvls_eq_c] at hW
  obtain ⟨hrun1, ⟨M₁, hS₁, -, hst₁⟩, -⟩ := CoreSpec.run
    (hc.lvlsEqC n ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe M eb us us2 hs.rel hus hus2 hdus hdus2)
    (callW_of_callE c1)
  by_cases h0 : r₁.headD 0 = 0
  · rw [if_pos h0] at hW; cases hW
    have hdo : decO (r₁.headD 0) = none := by rw [h0]; rfl
    rw [hdo] at hrun1
    refine ErrClaim.of_run_eq' (setTail_fail _ _ _ _ _ _ _ _ _ _ _ a₀ _ hrun1) ?_
    exact ErrClaim.fail _ _ rfl
  rw [if_neg h0] at hW
  by_cases h1 : r₁.headD 0 = 1
  · rw [if_pos h1] at hW; cases hW
  rw [if_neg h1] at hW
  have hdo : decO (r₁.headD 0) = some true := by unfold decO; rw [if_neg h0, if_neg h1]
  rw [hdo] at hrun1
  obtain ⟨tk, htk⟩ : ∃ tk, tk = (if an < ep then an else ep) := ⟨_, rfl⟩
  have hW1 : sectE.j1 p n mode vis d b T ao an to tn nf tk m₁ = .error er := by
    rw [htk]; split <;> simpa [*] using hW
  clear hW
  simp only [sectE.j1] at hW1
  have hmin : tk.toNat ≤ an.toNat := htk ▸ min_le_an an ep
  have hlen : aargs.toList.length = an.toNat := by simpa using ha.size
  have hsp₁ : SpineR m₁ ao an aargs := ha.keep hst₁.size hst₁.below hat hspn
  have htp₁ : SpineR m₁ to tn targs := ht.keep hst₁.size hst₁.below htt hspn
  have htop₁ : spTop m₁ = spTop s₀.mem := hst₁.1
  have hspn₁ : (m₁.arr64 SPN).size < 2 ^ 63 := hS₁.spn
  have htake := hsp₁.take tk hmin
  have etake : ((aargs.toList.take tk.toNat).toArray).toList = aargs.toList.take ep.toNat := by
    rw [htk]; exact take_min_eq _ _ _ hlen
  cases n with
  | zero =>
    obtain ⟨e', he', -⟩ := callE_zero p "defeq_lst" [mode, vis, d, ao, tk, to, tn] m₁
    rw [he', sectE.k_defeq_lst.none] at hW1; cases hW1; exact ErrClaim.of_callE_zero he'
  | succ N =>
  cases c2 : callE p (N + 1) "defeq_lst" [mode, vis, d, ao, tk, to, tn] m₁ with
  | error e2 =>
    rw [c2, sectE.k_defeq_lst.none] at hW1; cases hW1
    have h := CoreSpecE.of_callE (hDL N (hk.mono (Nat.le_succ N)) (hkE.mono (Nat.le_succ N)) F (by omega)
      (by omega) ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode d ao tk to tn _ targs
      ⟨hS₁, hs.mode4, hs.eb_mode⟩ htake htp₁ (by rw [htop₁]; omega) (by rw [htop₁]; exact htt)) c2
    rw [etake] at h
    exact ErrClaim.of_run_err (fun ce h' => setTail_err1 (b := _) (T := _) (nf := _) (h1 := hrun1) (ce := ce)
      (h2 := h')) h
  | ok q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [c2] at hW1
  simp only [sectE.k_defeq_lst] at hW1
  have h₂ := CoreSpec.of_callW (defeqLst_at p hc (N + 1) hk F hF hn ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb
    mode d ao tk to tn _ targs ⟨hS₁, hs.mode4, hs.eb_mode⟩ htake htp₁
    (by rw [htop₁]; omega) (by rw [htop₁]; exact htt)) (callW_of_callE c2)
  rw [etake] at h₂
  obtain ⟨hok2, ⟨M₂, hS₂, -, hst₂⟩, hres2, -⟩ := h₂
  have hrun2 := AM.run_of_ok _ _ hok2
  rw [hres2] at hrun2
  by_cases h20 : r₂.headD 0 = 0
  · rw [if_pos h20] at hW1; cases hW1
  rw [if_neg h20] at hW1
  rw [decBool_true_of h20] at hrun2
  cases c3 : callE p (N + 1) "eta_projs" [T, b, nf] m₂ with
  | error e3 =>
    rw [c3, sectE.k_eta_projs.none] at hW1; cases hW1
    exact ErrClaim.of_callE_nv hnv (whnfSetE_nv "eta_projs" (by simp)) c3
  | ok q =>
  obtain ⟨r₃, m₃⟩ := q
  rw [c3] at hW1
  simp only [sectE.k_eta_projs] at hW1
  obtain ⟨h₃, hr30, hr31, htop₃, hroom₃, hsp₃⟩ := etaProjs_callW hi hS₂ hT hb (callW_of_callE c3)
  obtain ⟨hok3, ⟨M₃, hS₃, -, hst₃⟩, -, -⟩ := h₃
  have hrun3 := AM.run_of_ok _ _ hok3
  have hW' := err_of_k (by intro q e; simp [sectE.k_defeq_lst_2]) (fun _ => rfl) hW1
  have hspn₂ : (m₂.arr64 SPN).size < 2 ^ 63 := hS₂.spn
  have htop₂ : spTop m₂ = spTop s₀.mem := hst₂.1.trans htop₁
  have hdrop := hsp₁.drop tk hmin hspn₁
  have e1 : (ao + tk).toNat = ao.toNat + tk.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by have := hsp₁.bound; omega)
  have e2 : (an - tk).toNat = an.toNat - tk.toNat :=
    UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hmin)
  have hsum : (ao + tk).toNat + (an - tk).toNat = ao.toNat + an.toNat := by rw [e1, e2]; omega
  have hle3 : (spTop s₀.mem).toNat ≤ (spTop m₃).toNat := htop₂ ▸ hst₃.1
  have hdrop₃ : SpineR m₃ (ao + tk) (an - tk) (aargs.toList.drop tk.toNat).toArray :=
    (hdrop.keep hst₂.size hst₂.below (by rw [hsum, htop₁]; exact hat) hspn₁).keep hst₃.size hst₃.below
      (by rw [hsum, htop₂]; exact hat) hspn₂
  have hb₃ : (ao + tk).toNat + (an - tk).toNat ≤ (spTop m₃).toNat := by rw [hsum]; omega
  have hp₃ : (r₃.headD 0).toNat + (r₃.tail.headD 0).toNat ≤ (spTop m₃).toNat := by
    rw [hr30, hr31, htop₃, UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]; exact Nat.le_refl _
  have h := CoreSpecE.of_callE (hDL N (hk.mono (Nat.le_succ N)) (hkE.mono (Nat.le_succ N)) F (by omega)
    (by omega) ⟨m₃, Locals.init []⟩ _ dn vis fe M₃ eb mode d (ao + tk) (an - tk) (r₃.headD 0)
    (r₃.tail.headD 0) _ _ ⟨hS₃, hs.mode4, hs.eb_mode⟩ hdrop₃ hsp₃ hb₃ hp₃) hW'
  rw [show ((aargs.toList.drop tk.toNat).toArray).toList = aargs.toList.drop ep.toNat by
    rw [htk]; exact drop_min_eq _ _ _ hlen, List.toList_toArray] at h
  exact ErrClaim.of_run_err (fun ce h' => setTail_err2 (h1 := hrun1) (h2 := hrun2) (h3 := hrun3) (ce := ce)
    (h4 := h')) h

set_option maxHeartbeats 800000 in
include hq hi hc hnv hDL in
/-- **`struct_eta_cert_go`'s verdicts** are `struct_eta_cert_tail`'s. -/
theorem setGo_refinesE (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) (F : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d b us c pc T q us2 ao an to tn : Word) (aargs targs : Array EIdx)
    (cvc : IConstantVal) (np nf : Nat) (cvT : IConstantVal) (caps : IIndCaps) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hb : HW b) (hus : HW us)
    (hcw : HW c) (hT : HW T) (hus2 : HW us2)
    (hvus : ∃ x c', a₀.store.view x = some (.const c' (decI us)))
    (hvus2 : ∃ x c', a₀.store.view x = some (.const c' (decI us2)))
    (hcvc : decCI (erecP s₀.mem) dn pc.toNat = some (.ctorInfo cvc np nf))
    (hcvT : decCI (erecP s₀.mem) dn q.toNat = some (.indInfo cvT caps))
    (ha : SpineR s₀.mem ao an aargs) (ht : SpineR s₀.mem to tn targs)
    (hat : ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat)
    (htt : to.toNat + tn.toNat ≤ (spTop s₀.mem).toNat) :
    CoreSpecE p (n + 1) "struct_eta_cert_go" [mode, vis, d, b, us, c, pc, T, q, us2, ao, an, to, tn]
      (setGoT (coreKnot (decMode mode) fe id F) fe d.toNat (decE b) (decI c) (decI us) cvc (decI T)
        (decI us2) cvT caps aargs.toList targs.toList) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (secgE_spec p hq.setGo (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d b us c pc T q us2 ao an to tn) hc0 (Err.code_ne_of_cls hk0)
  simp only [secgE] at hW
  have hS := hs.rel
  have hspn := hS.spn
  have hIR := decCI_indCaps hcvT (erecP_ext _) hS.erec
  have hCL := decCI_ctorLp hcvc (erecP_ext _) hS.erec
  cases c1 : callE p n "er_slice_eq" [rdW (s₀.mem.arr64 EREC) (pc + 2), rdW (s₀.mem.arr64 EREC) (pc + 3),
      rdW (s₀.mem.arr64 EREC) (q + 2), rdW (s₀.mem.arr64 EREC) (q + 3)] s₀.mem with
  | error e1 =>
    rw [c1, secgE.k_er_slice_eq.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfSetE_nv "er_slice_eq" (by simp)) c1
  | ok q₁ =>
  obtain ⟨r₁, m₁⟩ := q₁
  rw [c1] at hW
  simp only [secgE.k_er_slice_eq] at hW
  cases n with
  | zero =>
    obtain ⟨e', he', -⟩ := callE_zero p "er_slice_eq" [rdW (s₀.mem.arr64 EREC) (pc + 2),
      rdW (s₀.mem.arr64 EREC) (pc + 3), rdW (s₀.mem.arr64 EREC) (q + 2), rdW (s₀.mem.arr64 EREC) (q + 3)]
      s₀.mem
    rw [he'] at c1; cases c1
  | succ n' =>
  obtain ⟨t₁, ht₁, hm₁, -, hr₁, -⟩ := triple_of_callE (s₀ := ⟨s₀.mem, Locals.init []⟩)
    (erSliceEq_refines p hq.ers n' ⟨s₀.mem, Locals.init []⟩ _ _ _ _ cvc.levelParams cvT.levelParams
      hS.erec hCL hIR.lp) c1
  have em₁ : m₁ = s₀.mem := by rw [← ht₁]; exact hm₁
  subst em₁
  cases c2 : callE p (n' + 1) "reserved_contains_w" [T] s₀.mem with
  | error e2 =>
    rw [c2, secgE.k_reserved_contains_w.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfSetE_nv "reserved_contains_w" (by simp)) c2
  | ok q₂ =>
  obtain ⟨r₂, m₂⟩ := q₂
  rw [c2] at hW
  simp only [secgE.k_reserved_contains_w] at hW
  obtain ⟨hA₂, hr₂⟩ := reservedContains_callW hc hS hT (callW_of_callE c2)
  obtain ⟨M₂, hS₂, -, hst₂⟩ := hA₂
  cases c3 : callE p (n' + 1) "reserved_contains_w" [c] m₂ with
  | error e3 =>
    rw [c3, secgE.k_reserved_contains_w_2.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfSetE_nv "reserved_contains_w" (by simp)) c3
  | ok q₃ =>
  obtain ⟨r₃, m₃⟩ := q₃
  rw [c3] at hW
  simp only [secgE.k_reserved_contains_w_2] at hW
  obtain ⟨hA₃, hr₃⟩ := reservedContains_callW hc hS₂ hcw (callW_of_callE c3)
  obtain ⟨M₃, hS₃, -, hst₃⟩ := hA₃
  cases c4 : callE p (n' + 1) "ls_node" [us2] m₃ with
  | error e4 =>
    rw [c4, secgE.k_ls_node.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfSetE_nv "ls_node" (by simp)) c4
  | ok q₄ =>
  obtain ⟨r₄, m₄⟩ := q₄
  rw [c4] at hW
  simp only [secgE.k_ls_node] at hW
  obtain ⟨t₄, ht₄, ht₄s, hne, hr₄⟩ := triple_of_callE (s₀ := ⟨m₃, Locals.init []⟩)
    (lsNode_spec p hq.leaf.core.lsn (n' + 1) ⟨m₃, Locals.init []⟩ us2) c4
  have em₄ : m₄ = m₃ := by rw [← ht₄, ht₄s]
  subst em₄
  rw [hr₄] at hne
  have hvl := defeq_lsNodeW_viewLen hS₃.arena.1 hus2 hne
  rw [← hr₄] at hvl
  cases c5 : callE p (n' + 1) "tower_slots_all" [vis, T, rdW (s₀.mem.arr64 EREC) (q + 8)] m₄ with
  | error e5 =>
    rw [c5, secgE.k_tower_slots_all.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfSetE_nv "tower_slots_all" (by simp)) c5
  | ok q₅ =>
  obtain ⟨r₅, m₅⟩ := q₅
  rw [c5] at hW
  simp only [secgE.k_tower_slots_all] at hW
  have h₅ := CoreSpec.of_callW (hc.towerSlots (n' + 1) ⟨m₄, Locals.init []⟩ a₀ dn vis fe M₃ eb T _ hS₃
    hT) (callW_of_callE c5)
  rw [← hIR.etaFields] at h₅
  obtain ⟨-, ⟨M₅, hS₅, -, hst₅⟩, hres5, -⟩ := h₅
  have hts : towerSlotsAll fe (decI T) caps.etaFields = decBool r₅ := hres5
  have hlenT : targs.toList.length = tn.toNat := by simpa using ht.size
  have hlpT : cvT.levelParams.length = (rdW (s₀.mem.arr64 EREC) (q + 3)).toNat := hslice?_length hIR.lp
  have hiff : (caps.eta = true ∧ caps.etaCtor = decI c ∧
      a₀.pins.reserved.contains (decI T) = false ∧ a₀.pins.reserved.contains (decI c) = false ∧
      targs.toList.length = caps.etaParams ∧
      (r₄.tail.headD 0).toNat = cvT.levelParams.length ∧
      cvc.levelParams = cvT.levelParams ∧ decBool r₅ = true) ↔
      sgOK s₀.mem c q tn (r₁.headD 0) (r₂.headD 0) (r₃.headD 0) (r₄.tail.headD 0) r₅ := by
    unfold sgOK
    rw [hIR.eta, hIR.etaCtor, ← hr₂, ← hr₃, hlenT, hIR.etaParams, hlpT]
    have e2 : decI (rdW (s₀.mem.arr64 EREC) (q + 6)) = (decI c : NIdx) ↔
        rdW (s₀.mem.arr64 EREC) (q + 6) = c :=
      ⟨fun h => decI_inj hIR.etaCtor_hw hcw h, fun h => by rw [h]⟩
    have e7 : cvc.levelParams = cvT.levelParams ↔ r₁.headD 0 ≠ 0 := by
      have h1 : decBool r₁ = decide (cvc.levelParams = cvT.levelParams) := hr₁
      unfold decBool at h1
      by_cases he : cvc.levelParams = cvT.levelParams
      · simp only [he, decide_true, bne_iff_ne, ne_eq] at h1; exact ⟨fun _ => h1, fun _ => he⟩
      · simp only [he, decide_false, bne_eq_false_iff_eq] at h1
        exact ⟨fun h => absurd h he, fun h => absurd h1 h⟩
    rw [e2, e7]
    simp only [decBool, bne_iff_ne, ne_eq, Bool.not_eq_true', bne_eq_false_iff_eq,
      UInt64.toNat_inj]
  by_cases hok : sgOK s₀.mem c q tn (r₁.headD 0) (r₂.headD 0) (r₃.headD 0) (r₄.tail.headD 0) r₅
  · have hcond := hiff.mpr hok
    obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8⟩ := hok
    subst o5
    simp only [o1, o2, o3, o4, o6, o7, o8, ne_eq, not_true_eq_false, not_false_eq_true,
      ↓reduceIte] at hW
    rw [← hts] at hcond
    have hW' := err_of_k (by intro q e; simp [secgE.k_struct_eta_cert_tail]) (fun _ => rfl) hW
    have hk₅ := hst₂.trans (hst₃.trans hst₅)
    have htop : spTop m₅ = spTop s₀.mem := hk₅.1
    have h := CoreSpecE.of_callE (setTail_refinesE p hq hi hc hnv hDL n' (hk.mono (by omega))
      (hkE.mono (by omega)) F ⟨m₅, Locals.init []⟩ a₀ dn vis fe M₅ eb mode d b us T us2 ao an to _
      (rdW (s₀.mem.arr64 EREC) (q + 7)) (rdW (s₀.mem.arr64 EREC) (q + 8)) aargs targs (by omega) (by omega)
      ⟨hS₅, hs.mode4, hs.eb_mode⟩ hb hus hT hus2
      (by obtain ⟨x, c', hx⟩ := hvus
          exact (hc.den _ _ _ _ _ _ _ hS₅).constLs _ _ _ (constLs_after_tower hx))
      (by obtain ⟨x, c', hx⟩ := hvus2
          exact (hc.den _ _ _ _ _ _ _ hS₅).constLs _ _ _ (constLs_after_tower hx))
      (ha.keep hk₅.size hk₅.below hat hspn)
      (ht.keep hk₅.size hk₅.below htt hspn) (by rw [htop]; exact hat) (by rw [htop]; exact htt)) hW'
    rw [← hIR.etaParams, ← hIR.etaFields] at h
    exact ErrClaim.of_run_err (fun ce h' => setGo_err _ fe _ _ _ _ cvc _ _ cvT caps _ _ hS.pins _ hvl
      hcond ce h') h
  · unfold sgOK at hok
    by_cases o1 : rdW (s₀.mem.arr64 EREC) (q + 5) = 0
    · rw [if_pos o1] at hW; cases hW
    rw [if_neg o1] at hW
    by_cases o2 : rdW (s₀.mem.arr64 EREC) (q + 6) ≠ c
    · rw [if_pos o2] at hW; cases hW
    rw [if_neg o2] at hW
    by_cases o3 : r₂.headD 0 ≠ 0
    · rw [if_pos o3] at hW; cases hW
    rw [if_neg o3] at hW
    by_cases o4 : r₃.headD 0 ≠ 0
    · rw [if_pos o4] at hW; cases hW
    rw [if_neg o4] at hW
    by_cases o5 : tn ≠ rdW (s₀.mem.arr64 EREC) (q + 7)
    · rw [if_pos o5] at hW; cases hW
    rw [if_neg o5] at hW
    by_cases o6 : r₄.tail.headD 0 ≠ rdW (s₀.mem.arr64 EREC) (q + 3)
    · rw [if_pos o6] at hW; cases hW
    rw [if_neg o6] at hW
    by_cases o7 : r₁.headD 0 = 0
    · rw [if_pos o7] at hW; cases hW
    rw [if_neg o7] at hW
    by_cases o8 : r₅.headD 0 = 0
    · rw [if_pos o8] at hW; cases hW
    exact absurd ⟨o1, by simpa using o2, by simpa using o3, by simpa using o4, by simpa using o5,
      by simpa using o6, o7, o8⟩ hok

set_option maxHeartbeats 800000 in
include hq hi hc hnv hDL in
/-- **`struct_eta_cert_wtb`'s verdicts** are `struct_eta_cert_go`'s. -/
theorem setWtb_refinesE (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) (F : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d b us c pc ao an wtb : Word) (aargs : Array EIdx) (cvc : IConstantVal) (np nf : Nat)
    (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hb : HW b)
    (hus : HW us) (hcw : HW c) (hwtb : HW wtb)
    (hvus : ∃ x c', a₀.store.view x = some (.const c' (decI us)))
    (hcvc : decCI (erecP s₀.mem) dn pc.toNat = some (.ctorInfo cvc np nf))
    (ha : SpineR s₀.mem ao an aargs) (hat : ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat) :
    CoreSpecE p (n + 1) "struct_eta_cert_wtb" [mode, vis, d, b, us, c, pc, ao, an, wtb]
      (setWtbT (coreKnot (decMode mode) fe id F) fe d.toNat (decE b) (decI c) (decI us) cvc
        aargs.toList (decE wtb)) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (secwtbE_spec p hq.setWtb (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d b us c pc ao an wtb) hc0 (Err.code_ne_of_cls hk0)
  simp only [secwtbE] at hW
  have hS := hs.rel
  have hR := hS.arena.1
  cases c1 : callE p n "get_app_fn" [wtb] s₀.mem with
  | error e1 =>
    rw [c1, secwtbE.k_get_app_fn.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfSetE_nv "get_app_fn" (by simp)) c1
  | ok q₁ =>
  obtain ⟨r₁, m₁⟩ := q₁
  rw [c1] at hW
  simp only [secwtbE.k_get_app_fn] at hW
  obtain ⟨rfl, hh, hgaf⟩ := getAppFn_callW (a := a₀) hq.leaf hR hwtb (callW_of_callE c1)
  generalize r₁.headD 0 = h at hh hgaf hW
  by_cases h3 : h >>> 28 ≠ 3
  · rw [if_pos h3] at hW; cases hW
  rw [if_neg h3] at hW
  have h3' : h >>> 28 = 3 := by simpa using h3
  by_cases hsc : tierW h ≠ 0 ∧ rdW (s₀.mem.arr64 CTL) 1 = 0
  · rw [if_pos hsc] at hW; cases hW; exact absurd rfl hk0
  rw [if_neg hsc] at hW
  by_cases hcc : tcnt s₀.mem CONST (tierW h) ≤ idxW h
  · rw [if_pos hcc] at hW; cases hW; exact absurd rfl hk0
  rw [if_neg hcc] at hW
  have hvo : viewOK s₀.mem h CONST := ⟨hsc, by simpa using hcc⟩
  obtain ⟨hv, hnw, huw⟩ := L.Ind.view_const_f s₀.mem a₀ hR h hh hvo h3'
  have hct : ((decE h).tag == ETag.const) = true := by rw [tag_beq_const _ hh]; simp [h3']
  generalize tfld s₀.mem CONST (tierW h) (idxW h) 0 = k at hnw hW hv
  generalize tfld s₀.mem CONST (tierW h) (idxW h) 1 = us2 at huw hW hv
  cases c2 : callE p n "env_find" [k, vis] s₀.mem with
  | error e2 =>
    rw [c2, secwtbE.k_env_find.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfSetE_nv "env_find" (by simp)) c2
  | ok q₂ =>
  obtain ⟨r₂, m₂⟩ := q₂
  rw [c2] at hW
  simp only [secwtbE.k_env_find] at hW
  obtain ⟨rfl, hfind, hfound⟩ := envFind_callW hq.leaf.core hS.env hnw (callW_of_callE c2)
  by_cases h0 : r₂.headD 0 = 0
  · rw [if_pos h0] at hW; cases hW
  rw [if_neg h0] at hW
  obtain ⟨ci, hci⟩ := hfound h0
  have hfind' := find_of_found hfind h0 hci
  have hind := decCI_indK hci (erecP_ext _) hS.erec
  by_cases h4 : rdW (s₀.mem.arr64 EREC) (r₂.tail.headD 0) ≠ 3
  · rw [if_pos h4] at hW; cases hW
  rw [if_neg h4] at hW
  have h4' : rdW (s₀.mem.arr64 EREC) (r₂.tail.headD 0) = 3 := by simpa using h4
  obtain ⟨cvT, caps, hci_eq⟩ := hind.1 h4'
  rw [hci_eq] at hci
  cases c3 : callE p n "get_app_args" [wtb] s₀.mem with
  | error e3 =>
    rw [c3, secwtbE.k_get_app_args.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfSetE_nv "get_app_args" (by simp)) c3
  | ok q₃ =>
  obtain ⟨r₃, m₃⟩ := q₃
  rw [c3] at hW
  simp only [secwtbE.k_get_app_args] at hW
  obtain ⟨hf3, hg3, hr30, htop3, targs, hargs, hsp⟩ := getAppArgs_callW hq.leaf.core.spine hS hwtb
    (callW_of_callE c3)
  have hS₃ := hS.frame_stk hf3 (by simp) (by simp)
  have hep : erecP m₃ = erecP s₀.mem := erecP_frame hf3 (by simp [EREC, SPN]) (by simp)
  have hspn := hS.spn
  have hb3 := hsp.bound
  have hsz3 : (m₃.arr64 SPN).size < 2 ^ 63 := hg3.size ▸ hspn
  have htt : (r₃.headD 0).toNat + (r₃.tail.headD 0).toNat ≤ (spTop m₃).toNat := by
    have e := addW_toNat (x := r₃.headD 0) (y := r₃.tail.headD 0) (by omega)
    rw [htop3, ← hr30]; omega
  have hW' := err_of_k (by intro q e; simp [secwtbE.k_struct_eta_cert_go]) (fun _ => rfl) hW
  have hrunW := setWtbT_ind (coreKnot (decMode mode) fe id F) fe d.toNat (decE b) (decI c) (decI us) cvc
    aargs.toList _ a₀ _ hgaf _ _ hct hv cvT caps (by rw [hfind', hci_eq]) targs hargs
  cases n with
  | zero => exact ErrClaim.of_callE_zero hW'
  | succ n' =>
  have h := CoreSpecE.of_callE (setGo_refinesE p hq hi hc hnv hDL n' (hk.mono (by omega))
    (hkE.mono (by omega)) F ⟨m₃, Locals.init []⟩ a₀ dn vis fe M eb mode d
      b us c pc k (r₂.tail.headD 0) us2 ao an (r₃.headD 0) (r₃.tail.headD 0) aargs targs.toArray
      cvc np nf cvT caps (by omega) (by omega) ⟨hS₃, hs.mode4, hs.eb_mode⟩ hb hus hcw hnw huw
      hvus ⟨_, _, hv⟩ (by rw [hep]; exact hcvc) (by rw [hep]; exact hci) (ha.grew hg3 hat hspn) hsp
      (Nat.le_trans hat (UInt64.le_iff_toNat_le.mp hg3.1)) htt) hW'
  simp only [List.toList_toArray] at h
  exact ErrClaim.of_run_err (fun ce h' => by rw [hrunW]; exact h') h

set_option maxHeartbeats 800000 in
include hq hi hc hnv hDL in
/-- **`struct_eta_cert_with`'s verdicts** are `struct_eta_cert_wtb`'s. -/
theorem setWith_refinesE (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) (F : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a b wtb : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) (hwtb : HW wtb) :
    CoreSpecE p (n + 1) "struct_eta_cert_with" [mode, vis, d, a, b, wtb]
      (structEtaCertWith (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b) (decE wtb))
      s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (secwE_spec p hq.setWith (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d a b wtb) hc0 (Err.code_ne_of_cls hk0)
  simp only [secwE] at hW
  have hS := hs.rel
  have hR := hS.arena.1
  cases c1 : callE p n "get_app_fn" [a] s₀.mem with
  | error e1 =>
    rw [c1, secwE.k_get_app_fn.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfSetE_nv "get_app_fn" (by simp)) c1
  | ok q₁ =>
  obtain ⟨r₁, m₁⟩ := q₁
  rw [c1] at hW
  simp only [secwE.k_get_app_fn] at hW
  obtain ⟨rfl, hh, hgaf⟩ := getAppFn_callW (a := a₀) hq.leaf hR ha (callW_of_callE c1)
  generalize r₁.headD 0 = h at hh hgaf hW
  by_cases h3 : h >>> 28 ≠ 3
  · rw [if_pos h3] at hW; cases hW
  rw [if_neg h3] at hW
  have h3' : h >>> 28 = 3 := by simpa using h3
  by_cases hsc : tierW h ≠ 0 ∧ rdW (s₀.mem.arr64 CTL) 1 = 0
  · rw [if_pos hsc] at hW; cases hW; exact absurd rfl hk0
  rw [if_neg hsc] at hW
  by_cases hcc : tcnt s₀.mem CONST (tierW h) ≤ idxW h
  · rw [if_pos hcc] at hW; cases hW; exact absurd rfl hk0
  rw [if_neg hcc] at hW
  have hvo : viewOK s₀.mem h CONST := ⟨hsc, by simpa using hcc⟩
  obtain ⟨hv, hnw, huw⟩ := L.Ind.view_const_f s₀.mem a₀ hR h hh hvo h3'
  have hct : ((decE h).tag == ETag.const) = true := by rw [tag_beq_const _ hh]; simp [h3']
  generalize tfld s₀.mem CONST (tierW h) (idxW h) 0 = k at hnw hW hv
  generalize tfld s₀.mem CONST (tierW h) (idxW h) 1 = us at huw hW hv
  cases c2 : callE p n "env_find" [k, vis] s₀.mem with
  | error e2 =>
    rw [c2, secwE.k_env_find.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfSetE_nv "env_find" (by simp)) c2
  | ok q₂ =>
  obtain ⟨r₂, m₂⟩ := q₂
  rw [c2] at hW
  simp only [secwE.k_env_find] at hW
  obtain ⟨rfl, hfind, hfound⟩ := envFind_callW hq.leaf.core hS.env hnw (callW_of_callE c2)
  by_cases h0 : r₂.headD 0 = 0
  · rw [if_pos h0] at hW; cases hW
  rw [if_neg h0] at hW
  obtain ⟨ci, hci⟩ := hfound h0
  have hfind' := find_of_found hfind h0 hci
  have hctor := decCI_ctorF hci (erecP_ext _) hS.erec
  by_cases h4 : rdW (s₀.mem.arr64 EREC) (r₂.tail.headD 0) ≠ 4
  · rw [if_pos h4] at hW; cases hW
  rw [if_neg h4] at hW
  have h4' : rdW (s₀.mem.arr64 EREC) (r₂.tail.headD 0) = 4 := by simpa using h4
  obtain ⟨cvc, hci_eq⟩ := hctor.1 h4'
  rw [hci_eq] at hci
  cases c3 : callE p n "get_app_args" [a] s₀.mem with
  | error e3 =>
    rw [c3, secwE.k_get_app_args.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfSetE_nv "get_app_args" (by simp)) c3
  | ok q₃ =>
  obtain ⟨r₃, m₃⟩ := q₃
  rw [c3] at hW
  simp only [secwE.k_get_app_args] at hW
  obtain ⟨hf3, hg3, hr30, htop3, aargs, hargs, hsp⟩ := getAppArgs_callW hq.leaf.core.spine hS ha
    (callW_of_callE c3)
  have hS₃ := hS.frame_stk hf3 (by simp) (by simp)
  have hep : erecP m₃ = erecP s₀.mem := erecP_frame hf3 (by simp [EREC, SPN]) (by simp)
  have herec : m₃.arr64 EREC = s₀.mem.arr64 EREC := hf3.1 EREC (by simp [EREC, SPN]) (by decide)
  have hrunW := setWith_ctor (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b) (decE wtb) a₀
    _ hgaf _ _ hct hv cvc _ _ (by rw [hfind', hci_eq]) aargs hargs
  have hlen : aargs.length = (r₃.tail.headD 0).toNat := by simpa using hsp.size
  simp only [herec] at hW
  have hspn := hS.spn
  have hsz3 : (m₃.arr64 SPN).size < 2 ^ 63 := hg3.size ▸ hspn
  by_cases hcnt : ¬ r₃.tail.headD 0 < rdW (s₀.mem.arr64 EREC) (r₂.tail.headD 0 + 6) ∧
      r₃.tail.headD 0 - rdW (s₀.mem.arr64 EREC) (r₂.tail.headD 0 + 6) =
        rdW (s₀.mem.arr64 EREC) (r₂.tail.headD 0 + 5)
  · rw [if_neg (by rintro (h | h); exact hcnt.1 h; exact h hcnt.2)] at hW
    rw [if_pos (by rw [hlen]; exact (count_iff _ _ _).mpr hcnt)] at hrunW
    have hW' := err_of_k (by intro q e; simp [secwE.k_struct_eta_cert_wtb]) (fun _ => rfl) hW
    cases n with
    | zero => exact ErrClaim.of_callE_zero hW'
    | succ n' =>
    have h := CoreSpecE.of_callE (setWtb_refinesE p hq hi hc hnv hDL n' (hk.mono (by omega))
      (hkE.mono (by omega)) F ⟨m₃, Locals.init []⟩ a₀ dn vis fe M eb mode d b us k (r₂.tail.headD 0)
      (r₃.headD 0) (r₃.tail.headD 0) wtb aargs.toArray cvc _ _ (by omega) (by omega)
      ⟨hS₃, hs.mode4, hs.eb_mode⟩ hb huw hnw hwtb ⟨_, _, hv⟩ (by rw [hep]; exact hci) hsp (by
        have e := addW_toNat (x := r₃.headD 0) (y := r₃.tail.headD 0) (by have := hsp.bound; omega)
        rw [htop3, ← hr30]; omega)) hW'
    simp only [List.toList_toArray] at h
    exact ErrClaim.of_run_err (fun ce h' => by rw [hrunW]; exact h') h
  · have hc' : r₃.tail.headD 0 < rdW (s₀.mem.arr64 EREC) (r₂.tail.headD 0 + 6) ∨
        r₃.tail.headD 0 - rdW (s₀.mem.arr64 EREC) (r₂.tail.headD 0 + 6) ≠
          rdW (s₀.mem.arr64 EREC) (r₂.tail.headD 0 + 5) := by
      by_cases h1 : r₃.tail.headD 0 < rdW (s₀.mem.arr64 EREC) (r₂.tail.headD 0 + 6)
      · exact Or.inl h1
      · exact Or.inr (fun e => hcnt ⟨h1, e⟩)
    rw [if_pos hc'] at hW; cases hW

include hq hi hc hnv hDL in
/-- **`struct_eta_cert`'s verdicts** are the `infer_io`, `whnf` slots' and `struct_eta_cert_with`'s. -/
theorem setCert_refinesE (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) (F : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a b : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) :
    CoreSpecE p (n + 1) "struct_eta_cert" [mode, vis, d, a, b]
      (structEtaCert (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (secE_spec p hq.setCert (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d a b) hc0 (Err.code_ne_of_cls hk0)
  simp only [secE] at hW
  cases c1 : callE p n "eta_ctor_shape" [vis, a] s₀.mem with
  | error e1 =>
    rw [c1, secE.k_eta_ctor_shape.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfSetE_nv "eta_ctor_shape" (by simp)) c1
  | ok q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [c1] at hW
  simp only [secE.k_eta_ctor_shape] at hW
  obtain ⟨hok1, ⟨M₁, hS₁, -, -⟩, hres1, -⟩ := CoreSpec.of_callW
    (etaCtorShape_at p hq n ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe M eb a hs.rel ha) (callW_of_callE c1)
  have hrun1 := AM.run_of_ok _ _ hok1
  rw [hres1] at hrun1
  by_cases h0 : r₁.headD 0 = 0
  · rw [if_pos h0] at hW; cases hW
  rw [if_neg h0] at hW
  rw [decBool_true_of h0] at hrun1
  cases c2 : callE p n "infer_io" [mode, vis, d, b] m₁ with
  | error e2 =>
    rw [c2, secE.k_infer_io.none] at hW; cases hW
    exact ErrClaim.of_run_err (fun ce h' => setCert_err_io (h1 := hrun1) (ce := ce) (h := h'))
      (CoreSpecE.of_callE ((hkE n (Nat.le_refl _)).inferIO F ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode d b
        hF hn ⟨hS₁, hs.mode4, hs.eb_mode⟩ hb) c2)
  | ok q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [c2] at hW
  simp only [secE.k_infer_io] at hW
  obtain ⟨hok2, ⟨M₂, hS₂, -, -⟩, hres2, hr2⟩ := CoreSpec.of_callW ((hk n (Nat.le_refl _)).inferIO F
    ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode d b hF hn ⟨hS₁, hs.mode4, hs.eb_mode⟩ hb) (callW_of_callE c2)
  have hrun2 := AM.run_of_ok _ _ hok2
  rw [hres2] at hrun2
  cases c3 : callE p n "whnf" [mode, vis, d, r₂.headD 0] m₂ with
  | error e3 =>
    rw [c3, secE.k_whnf.none] at hW; cases hW
    exact ErrClaim.of_run_err (fun ce h' => setCert_err_whnf (h1 := hrun1) (h2 := hrun2) (ce := ce) (h := h'))
      (CoreSpecE.of_callE ((hkE n (Nat.le_refl _)).whnf F ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode d
        (r₂.headD 0) hF hn ⟨hS₂, hs.mode4, hs.eb_mode⟩ hr2) c3)
  | ok q =>
  obtain ⟨r₃, m₃⟩ := q
  rw [c3] at hW
  simp only [secE.k_whnf] at hW
  obtain ⟨hok3, ⟨M₃, hS₃, -, -⟩, hres3, hh3⟩ := CoreSpec.of_callW ((hk n (Nat.le_refl _)).whnf F
    ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode d (r₂.headD 0) hF hn ⟨hS₂, hs.mode4, hs.eb_mode⟩ hr2)
    (callW_of_callE c3)
  have hrun3 := AM.run_of_ok _ _ hok3
  rw [hres3] at hrun3
  have hW' := err_of_k (by intro q e; simp [secE.k_struct_eta_cert_with]) (fun _ => rfl) hW
  cases n with
  | zero => exact ErrClaim.of_callE_zero hW'
  | succ N =>
  exact ErrClaim.of_run_err (fun ce h' => setCert_err_with (h1 := hrun1) (h2 := hrun2) (h3 := hrun3) (ce := ce)
      (h := h'))
    (CoreSpecE.of_callE (setWith_refinesE p hq hi hc hnv hDL N (hk.mono (Nat.le_succ N))
      (hkE.mono (Nat.le_succ N)) F ⟨m₃, Locals.init []⟩ _ dn vis fe M₃ eb mode d a b (r₃.headD 0) (by omega)
      (by omega) ⟨hS₃, hs.mode4, hs.eb_mode⟩ ha hb hh3) hW')

end set

end L.Arena
