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
    "lvls_eq_c", "eta_projs", "eta_ctor_shape", "ind_caps"], f ∈ L.Checker.nvFns := by
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

end set

end L.Arena
