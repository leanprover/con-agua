import ConAgua.Verdict.WhnfModels6E
import ConAgua.Verdict.WhnfPrepE

/-!
# `major_to_ctor`'s verdict claims (lane `verdicts-b`, helper `k2`)

No verdict site of its own: the claims are the `infer_io`, `whnf` and `defeq` slots'
(`KnotUpToE`) and `proof_irrel`'s (`ProofIrrelWE`), through `m2c_pre`, `m2c_check` and the arms
(`majorToCtorE_of`: `MajorToCtorE`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

theorem whnfM2CE_nv : ∀ f ∈ ["get_app_fn", "m2c_const_view", "ls_node", "fab_scope_ok",
    "get_app_args", "intern_const", "mk_app_n", "caps_never_zero", "m2c_eta2", "pin_at", "mk_proj",
    "and_rescue_slots", "pi_result", "env_find", "is_ctor_app"], f ∈ L.Checker.nvFns := by
  decide +kernel

/-- `proof_irrel`'s error claim at fuel `N + 1` (the premises of `ProofIrrelOKM`). -/
def ProofIrrelWE (p : Prog) : Prop :=
  ∀ (n : Nat), KnotUpTo p n → KnotUpToE p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d a b : Word), CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 →
    eb = (mode >>> 1) &&& 1 → HW a → HW b →
    CoreSpecE p (n + 1) "proof_irrel" [mode, vis, d, a, b]
      (proofIrrel (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) s₀ a₀

/-! ## `m2c_pre` -/

theorem pre_err_io {R : CoreFnsA} {d : Nat} {major : EIdx} {a : AState} {ce : CheckError}
    (h : (R.inferIO d major).run a = .error ce) (k : EIdx → NIdx → LsIdx → AM EIdx) :
    (m2cPreT R d major k).run a = .error ce := by
  simp only [m2cPreT, StateT.run_bind, h]; rfl

theorem pre_err_whnf {R : CoreFnsA} {d : Nat} {major ta : EIdx} {a a₁ : AState} {ce : CheckError}
    (h1 : (R.inferIO d major).run a = .ok (ta, a₁)) (h : (R.whnf d ta).run a₁ = .error ce)
    (k : EIdx → NIdx → LsIdx → AM EIdx) :
    (m2cPreT R d major k).run a = .error ce := by
  simp only [m2cPreT, StateT.run_bind, h1, except_ok_bind, h]; rfl

section pre
variable (p : Prog) (hp : M2CProg' p) (hnv : closedNV p L.Checker.nvFns = true)
include hp hnv

/-- **`m2c_pre`'s verdicts** are the `infer_io` and `whnf` slots' (before any continuation). -/
theorem m2cPreE_ok (N F : Nat) (hk : KnotUpTo p N) (hkE : KnotUpToE p N) (hnF : N ≤ F)
    (hn62 : N ≤ 2 ^ 62) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (eb mode d major : Word) (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1) (hmaj : HW major)
    (m : Mem) (a : AState) (M : ModeMaps) (hS : CoreS dn m a vis fe M eb) (er : Err)
    (h : callE p (N + 1) "m2c_pre" [mode, vis, d, major] m = .error er)
    (k : EIdx → NIdx → LsIdx → AM EIdx) :
    ErrClaim (m2cPreT (coreKnot (decMode mode) fe id F) d.toNat (decE major) k) a er := by
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (m2cPreE_spec p hp.pre (N + 1) ⟨m, Locals.init []⟩ mode vis d major) h
    (Err.code_ne_of_cls hk0)
  simp only [m2cPreE] at hW
  cases c1 : callE p N "infer_io" [mode, vis, d, major] m with
  | error e1 =>
    rw [c1, m2cPreE.k_infer_io.none] at hW; cases hW
    exact ErrClaim.of_run_err (fun ce h' => pre_err_io h' k)
      (CoreSpecE.of_callE ((hkE N (Nat.le_refl _)).inferIO F ⟨m, Locals.init []⟩ a dn vis fe M eb mode d
        major hnF hn62 ⟨hS, hm4, hebm⟩ hmaj) c1)
  | ok q =>
  obtain ⟨r1, m1⟩ := q
  rw [c1] at hW
  simp only [m2cPreE.k_infer_io] at hW
  obtain ⟨ok1, ⟨M1, hS1, -, -⟩, res1, hr1⟩ := CoreSpec.of_callW
    ((hk N (Nat.le_refl _)).inferIO F ⟨m, Locals.init []⟩ a dn vis fe M eb mode d major hnF hn62
      ⟨hS, hm4, hebm⟩ hmaj) (callW_of_callE c1)
  have hrun1 := AM.run_of_ok _ _ ok1
  rw [res1] at hrun1
  cases c2 : callE p N "whnf" [mode, vis, d, r1.headD 0] m1 with
  | error e2 =>
    rw [c2, m2cPreE.k_whnf.none] at hW; cases hW
    exact ErrClaim.of_run_err (fun ce h' => pre_err_whnf hrun1 h' k)
      (CoreSpecE.of_callE ((hkE N (Nat.le_refl _)).whnf F ⟨m1, Locals.init []⟩ _ dn vis fe M1 eb mode d _
        hnF hn62 ⟨hS1, hm4, hebm⟩ hr1) c2)
  | ok q =>
  obtain ⟨r2, m2⟩ := q
  rw [c2] at hW
  simp only [m2cPreE.k_whnf] at hW
  cases c3 : callE p N "get_app_fn" [r2.headD 0] m2 with
  | error e3 =>
    rw [c3, m2cPreE.k_get_app_fn.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfM2CE_nv "get_app_fn" (by simp)) c3
  | ok q =>
  obtain ⟨r3, m3⟩ := q
  rw [c3] at hW
  simp only [m2cPreE.k_get_app_fn] at hW
  split at hW
  · cases hW
  cases c4 : callE p N "m2c_const_view" [r3.headD 0] m3 with
  | error e4 =>
    rw [c4, m2cPreE.k_m2c_const_view.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfM2CE_nv "m2c_const_view" (by simp)) c4
  | ok q =>
  obtain ⟨r4, m4⟩ := q
  rw [c4] at hW
  simp only [m2cPreE.k_m2c_const_view] at hW
  exact ErrClaim.of_callE_nv hnv (whnfM2CE_nv "ls_node" (by simp))
    (err_of_k (by intro q e; simp [m2cPreE.k_ls_node]) (fun _ => rfl) hW)

end pre

/-! ## `m2c_check` -/

section checkErr
variable (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (tmaj fab major : EIdx)

theorem check_err_io (a a1 : AState) (h1 : (fabScopeOk depth fab major).run a = .ok (true, a1))
    (ce : CheckError) (h2 : (r.inferIO depth fab).run a1 = .error ce) :
    (m2cCheckT mode r fe depth tmaj fab major).run a = .error ce := by
  simp only [m2cCheckT, StateT.run_bind, h1, except_ok_bind, ↓reduceIte, h2]; rfl

theorem check_err_defeq (a a1 a2 : AState) (ta : EIdx)
    (h1 : (fabScopeOk depth fab major).run a = .ok (true, a1))
    (h2 : (r.inferIO depth fab).run a1 = .ok (ta, a2)) (ce : CheckError)
    (h3 : (r.defeq depth tmaj ta).run a2 = .error ce) :
    (m2cCheckT mode r fe depth tmaj fab major).run a = .error ce := by
  simp only [m2cCheckT, StateT.run_bind, h1, except_ok_bind, ↓reduceIte, h2, h3]; rfl

theorem check_err_pi (a a1 a2 a3 : AState) (ta : EIdx) (hv : mode.verifiedChecks = true)
    (h1 : (fabScopeOk depth fab major).run a = .ok (true, a1))
    (h2 : (r.inferIO depth fab).run a1 = .ok (ta, a2))
    (h3 : (r.defeq depth tmaj ta).run a2 = .ok (true, a3)) (ce : CheckError)
    (h4 : (proofIrrel r fe depth fab major).run a3 = .error ce) :
    (m2cCheckT mode r fe depth tmaj fab major).run a = .error ce := by
  simp only [m2cCheckT, StateT.run_bind, h1, except_ok_bind, ↓reduceIte, h2, h3, hv, h4]; rfl

end checkErr

section check
variable (p : Prog) (hp : M2CProg' p) (hc : IotaCallees p) (hnv : closedNV p L.Checker.nvFns = true)
  (hPI : ProofIrrelWE p)
include hp hc hnv hPI

/-- **`m2c_check`'s verdicts** are the slots' and `proof_irrel`'s. -/
theorem m2cCheckE_ok (N F : Nat) (hk : KnotUpTo p N) (hkE : KnotUpToE p N) (hnF : N ≤ F)
    (hn62 : N ≤ 2 ^ 62) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (eb mode d tmaj fab major : Word)
    (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1) (htm : HW tmaj) (hfab : HW fab)
    (hmaj : HW major) (m : Mem) (a : AState) (M : ModeMaps) (hS : CoreS dn m a vis fe M eb)
    (er : Err) (h : callE p (N + 1) "m2c_check" [mode, vis, d, tmaj, fab, major] m = .error er) :
    ErrClaim (m2cCheckT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE tmaj)
      (decE fab) (decE major)) a er := by
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (m2cCheckE_spec p hp.check (N + 1) ⟨m, Locals.init []⟩
    mode vis d tmaj fab major) h (Err.code_ne_of_cls hk0)
  simp only [m2cCheckE] at hW
  cases N with
  | zero =>
    obtain ⟨e', he', h0⟩ := callE_zero p "fab_scope_ok" [d, fab, major] m
    rw [he', m2cCheckE.k_fab_scope_ok.none] at hW; cases hW; exact absurd h0 hk0
  | succ N' =>
  cases c1 : callE p (N' + 1) "fab_scope_ok" [d, fab, major] m with
  | error e1 =>
    rw [c1, m2cCheckE.k_fab_scope_ok.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfM2CE_nv "fab_scope_ok" (by simp)) c1
  | ok q =>
  obtain ⟨r1, m1⟩ := q
  rw [c1] at hW
  simp only [m2cCheckE.k_fab_scope_ok] at hW
  obtain ⟨hrun1, ⟨M1, hS1, -, -⟩, -⟩ := CoreSpec.run
    (fabScopeOk_refines' p hp.toIotaProg' hc (N' + 1) ⟨m, Locals.init []⟩ a dn vis fe M eb d fab major
      hS hfab hmaj) (callW_of_callE c1)
  by_cases g1 : r1.headD 0 = 0
  · rw [ite_eq_left g1] at hW; cases hW
  rw [ite_eq_right g1] at hW
  rw [decBool_t_m2c g1] at hrun1
  cases c2 : callE p (N' + 1) "infer_io" [mode, vis, d, fab] m1 with
  | error e2 =>
    rw [c2, m2cCheckE.k_infer_io.none] at hW; cases hW
    exact ErrClaim.of_run_err (fun ce h' => check_err_io _ _ _ _ _ _ _ _ _ hrun1 ce h')
      (CoreSpecE.of_callE ((hkE _ (Nat.le_refl _)).inferIO F ⟨m1, Locals.init []⟩ _ dn vis fe M1 eb mode
        d fab hnF hn62 ⟨hS1, hm4, hebm⟩ hfab) c2)
  | ok q =>
  obtain ⟨r2, m2⟩ := q
  rw [c2] at hW
  simp only [m2cCheckE.k_infer_io] at hW
  obtain ⟨hrun2, ⟨M2, hS2, -, -⟩, hr2⟩ := CoreSpec.run
    ((hk _ (Nat.le_refl _)).inferIO F ⟨m1, Locals.init []⟩ _ dn vis fe M1 eb mode d fab hnF hn62
      ⟨hS1, hm4, hebm⟩ hfab) (callW_of_callE c2)
  rw [show decH r2 = decE (r2.headD 0) from rfl] at hrun2
  cases c3 : callE p (N' + 1) "defeq" [mode, vis, d, tmaj, r2.headD 0] m2 with
  | error e3 =>
    rw [c3, m2cCheckE.k_defeq.none] at hW; cases hW
    exact ErrClaim.of_run_err (fun ce h' => check_err_defeq _ _ _ _ _ _ _ _ _ _ _ hrun1 hrun2 ce h')
      (CoreSpecE.of_callE ((hkE _ (Nat.le_refl _)).defeq F ⟨m2, Locals.init []⟩ _ dn vis fe M2 eb mode d
        tmaj _ hnF hn62 ⟨hS2, hm4, hebm⟩ htm hr2) c3)
  | ok q =>
  obtain ⟨r3, m3⟩ := q
  rw [c3] at hW
  simp only [m2cCheckE.k_defeq] at hW
  obtain ⟨hrun3, ⟨M3, hS3, -, -⟩, -⟩ := CoreSpec.run
    ((hk _ (Nat.le_refl _)).defeq F ⟨m2, Locals.init []⟩ _ dn vis fe M2 eb mode d tmaj _ hnF hn62
      ⟨hS2, hm4, hebm⟩ htm hr2) (callW_of_callE c3)
  by_cases g3 : r3.headD 0 = 0
  · rw [ite_eq_left g3] at hW; cases hW
  rw [ite_eq_right g3] at hW
  rw [decBool_t_m2c g3] at hrun3
  have hv := decMode_verified mode hm4
  by_cases g4 : mode &&& 1 = 0
  · rw [ite_eq_left g4] at hW
    have hv' : (decMode mode).verifiedChecks = true := by rw [hv]; simpa using g4
    have hW' := err_of_k (by intro q e; simp only [m2cCheckE.k_proof_irrel, m2cCheckE.j1]; split <;> simp)
      (fun _ => rfl) hW
    exact ErrClaim.of_run_err (fun ce h' => check_err_pi _ _ _ _ _ _ _ _ _ _ _ _ hv' hrun1 hrun2 hrun3 ce h')
      (CoreSpecE.of_callE (hPI N' (hk.mono (Nat.le_succ _)) (hkE.mono (Nat.le_succ _)) F (by omega)
        (by omega) ⟨m3, Locals.init []⟩ _ dn vis fe M3 eb mode d fab major hS3 hm4 hebm hfab hmaj) hW')
  · rw [ite_eq_right g4] at hW
    simp only [m2cCheckE.j1] at hW
    split at hW <;> cases hW

end check

/-! ## The K arm -/

section kErr
variable (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)

theorem k2_err_check (ctor : NIdx) (cnP : Nat) (tmaj : EIdx) (ust : LsIdx) (major : EIdx)
    (a a2 a3 : AState) (xs : List EIdx) (hd fab : EIdx)
    (hargs : (getAppArgs coreWalkFuel tmaj).run a = .ok (xs, a)) (hle : cnP ≤ xs.length)
    (h2 : (internE (.const ctor ust)).run a = .ok (hd, a2))
    (h3 : (mkAppN hd (xs.take cnP)).run a2 = .ok (fab, a3)) (ce : CheckError)
    (h4 : (m2cCheckT mode r fe depth tmaj fab major).run a3 = .error ce) :
    (m2cK2T mode r fe depth ctor cnP tmaj ust major).run a = .error ce := by
  simp only [m2cK2T, StateT.run_bind, hargs, except_ok_bind, hle, ↓reduceIte, h2, h3]
  exact h4

end kErr

section karm
variable (p : Prog) (hp : M2CProg' p) (hc : IotaCallees p) (hpi : ProofIrrelOKM p)
  (hE : ErecKeptKnot p) (hnv : closedNV p L.Checker.nvFns = true) (hPI : ProofIrrelWE p)
include hp hc hpi hnv hPI

/-- **`m2c_k2`'s verdicts** are `m2c_check`'s. -/
theorem m2cK2E_ok (N F : Nat) (hk : KnotUpTo p N) (hkE : KnotUpToE p N) (hnF : N ≤ F)
    (hn62 : N ≤ 2 ^ 62) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (eb mode d ctor cnP tmaj ust major : Word) (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1)
    (hctor : HW ctor) (htm : HW tmaj) (hus : HW ust) (hmaj : HW major) (m : Mem) (a : AState)
    (M : ModeMaps) (hS : CoreS dn m a vis fe M eb)
    (hdus : ∃ ls, denoteLs a.store.lss (decI ust) = some ls) (er : Err)
    (h : callE p (N + 1) "m2c_k2" [mode, vis, d, ctor, cnP, tmaj, ust, major] m = .error er) :
    ErrClaim (m2cK2T (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI ctor)
      cnP.toNat (decE tmaj) (decI ust) (decE major)) a er := by
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (m2cK2E_spec p hp.k2 (N + 1) ⟨m, Locals.init []⟩
    mode vis d ctor cnP tmaj ust major) h (Err.code_ne_of_cls hk0)
  simp only [m2cK2E] at hW
  cases N with
  | zero =>
    obtain ⟨e', he', h0⟩ := callE_zero p "get_app_args" [tmaj] m
    rw [he', m2cK2E.k_get_app_args.none] at hW; cases hW; exact absurd h0 hk0
  | succ N' =>
  cases c1 : callE p (N' + 1) "get_app_args" [tmaj] m with
  | error e1 =>
    rw [c1, m2cK2E.k_get_app_args.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfM2CE_nv "get_app_args" (by simp)) c1
  | ok q =>
  obtain ⟨r1, m1⟩ := q
  rw [c1] at hW
  simp only [m2cK2E.k_get_app_args] at hW
  obtain ⟨t1, ht1, -, hfr1, hg1, htop1, -, xs, hargs, hsp1⟩ := triple_of_callE
    (s₀ := ⟨m, Locals.init []⟩) (getAppArgs_refines p hp.spine (N' + 1) _ a hS.arena.1 tmaj htm hS.spn) c1
  rw [ht1] at hfr1 hg1 hsp1
  have hS1 := hS.frame_stk hfr1 (by simp) (by simp)
  have hlen : xs.length = (r1.tail.headD 0).toNat := by simpa using hsp1.size
  by_cases g1 : r1.tail.headD 0 < cnP
  · rw [ite_eq_left g1] at hW; cases hW
  rw [ite_eq_right g1] at hW
  have hle : cnP.toNat ≤ xs.length := by rw [hlen]; exact UInt64.not_lt.mp g1
  cases c2 : callE p (N' + 1) "intern_const" [ctor, ust] m1 with
  | error e2 =>
    rw [c2, m2cK2E.k_intern_const.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfM2CE_nv "intern_const" (by simp)) c2
  | ok q =>
  obtain ⟨r2, m2⟩ := q
  rw [c2] at hW
  simp only [m2cK2E.k_intern_const] at hW
  obtain ⟨ok2, hD2, res2, hfr2, hh2⟩ := callW_internConst' p hp.constFind' hp.constPush'
    hp.internConst' (N' + 1) m1 a hS1.arena ctor ust hctor hus r2 m2 (callW_of_callE c2)
  have hrun2 := AM.run_of_ok _ _ ok2
  rw [res2] at hrun2
  have hS2 := hS1.of_const' hD2 (Keeps.run (keeps_cpl_internConst' _ _) hrun2) hfr2 hrun2 hdus
  have hsp2 : SpineR m2 (r1.headD 0) cnP (xs.take cnP.toNat).toArray :=
    (hsp1.take' (by rw [← hlen]; exact hle)).of_spn_core
      (hfr2.1 SPN (by simp [CREC, CSLOT, CLP, SPN]) (by decide))
  cases c3 : callE p (N' + 1) "mk_app_n" [r2.headD 0, r1.headD 0, cnP] m2 with
  | error e3 =>
    rw [c3, m2cK2E.k_mk_app_n.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfM2CE_nv "mk_app_n" (by simp)) c3
  | ok q =>
  obtain ⟨r3, m3⟩ := q
  rw [c3] at hW
  simp only [m2cK2E.k_mk_app_n] at hW
  obtain ⟨ok3, hD3, res3, hfr3, hh3⟩ := callW_mkAppN' p hp.spine (N' + 1) m2 _ hS2.arena
    (r2.headD 0) (r1.headD 0) cnP _ hh2 hsp2 r3 m3 (callW_of_callE c3)
  have hrun3 := AM.run_of_ok _ _ ok3
  rw [res3, show ((xs.take cnP.toNat).toArray).toList = xs.take cnP.toNat from rfl,
    show decE (r2.headD 0) = decI (r2.headD 0) from rfl] at hrun3
  have hS3 := hS2.of_app hD3 (Keeps.run (keeps_cpl_mkAppN' _ _) hrun3) hfr3
  have hW' := err_of_k (by intro q e; simp [m2cK2E.k_m2c_check]) (fun _ => rfl) hW
  exact ErrClaim.of_run_err (fun ce h' => k2_err_check _ _ _ _ _ _ _ _ _ a _ _ xs _ _ hargs hle hrun2
      hrun3 ce h')
    (m2cCheckE_ok p hp hc hnv hPI N' F (hk.mono (Nat.le_succ _)) (hkE.mono (Nat.le_succ _)) (by omega)
      (by omega) dn vis fe eb mode d tmaj (r3.headD 0) major hm4 hebm htm hh3 hmaj m3 _ M hS3 er hW')

include hE in
/-- **`m2c_k`'s verdicts** are `m2c_pre`'s and `m2c_k2`'s. -/
theorem m2cKE_ok (N F : Nat) (hk : KnotUpTo p N) (hkE : KnotUpToE p N) (hnF : N ≤ F)
    (hn62 : N ≤ 2 ^ 62) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (eb mode d T major ctor lpl cnP : Word) (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1)
    (_hT : HW T) (hmaj : HW major) (hctor : HW ctor) (m : Mem) (a : AState)
    (M : ModeMaps) (hS : CoreS dn m a vis fe M eb) (er : Err)
    (h : callE p (N + 1) "m2c_k" [mode, vis, d, T, major, ctor, lpl, cnP] m = .error er) :
    ErrClaim (m2cKT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI ctor)
      lpl.toNat cnP.toNat (decI T) (decE major)) a er := by
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (m2cKE_spec p hp.k (N + 1) ⟨m, Locals.init []⟩
    mode vis d T major ctor lpl cnP) h (Err.code_ne_of_cls hk0)
  simp only [m2cKE] at hW
  cases N with
  | zero =>
    obtain ⟨e', he', h0⟩ := callE_zero p "m2c_pre" [mode, vis, d, major] m
    rw [he', m2cKE.k_m2c_pre.none] at hW; cases hW; exact absurd h0 hk0
  | succ N' =>
  cases c1 : callE p (N' + 1) "m2c_pre" [mode, vis, d, major] m with
  | error e1 =>
    rw [c1, m2cKE.k_m2c_pre.none] at hW; cases hW
    unfold m2cKT
    exact m2cPreE_ok p hp hnv N' F (hk.mono (Nat.le_succ _)) (hkE.mono (Nat.le_succ _)) (by omega)
      (by omega) dn vis fe eb mode d major hm4 hebm hmaj m a M hS _ c1 _
  | ok q =>
  obtain ⟨L, m1⟩ := q
  rw [c1] at hW
  simp only [m2cKE.k_m2c_pre] at hW
  obtain ⟨a1, hpre, ⟨M1, hS1, hK1, hSt1⟩, -, hhw⟩ := m2cPre_ok p hp hE N' F
    (hk.mono (Nat.le_succ _)) (by omega) (by omega) dn vis fe eb mode d major hm4 hebm hmaj m a M hS
    L m1 (callW_of_callE c1)
  by_cases g0 : L.headD 0 = 0
  · rw [ite_eq_left g0] at hW; cases hW
  rw [ite_eq_right g0] at hW
  obtain ⟨htm, hT2, hus⟩ := hhw g0
  obtain ⟨l, hvls, hll, -⟩ := hpre.view g0
  have hpre' := m2cPreT_some hpre g0
  by_cases g2 : L.tail.tail.headD 0 ≠ T
  · rw [ite_eq_left g2] at hW; cases hW
  rw [ite_eq_right g2] at hW
  have g2' : L.tail.tail.headD 0 = T := by simpa using g2
  by_cases g3 : lpl ≠ L.tail.tail.tail.tail.headD 0
  · rw [ite_eq_left g3] at hW; cases hW
  rw [ite_eq_right g3] at hW
  have g3' : lpl = L.tail.tail.tail.tail.headD 0 := by simpa using g3
  have hW' := err_of_k (by intro q e; simp [m2cKE.k_m2c_k2]) (fun _ => rfl) hW
  have hc' : ((decI (L.tail.tail.headD 0) : NIdx) = decI T ∧ lpl.toNat = l.length) :=
    ⟨by rw [g2'], by rw [hll, g3']⟩
  refine ErrClaim.of_run_err (fun ce h' => ?_) (m2cK2E_ok p hp hc hpi hnv hPI N' F (hk.mono (Nat.le_succ _))
    (hkE.mono (Nat.le_succ _)) (by omega) (by omega) dn vis fe eb mode d ctor cnP _ _ major hm4 hebm hctor
    htm hus hmaj m1 a1 M1 hS1
    (by obtain ⟨_, _, _, _, _, _, _, _, hp5⟩ := hpre
        exact hS1.den.constLs _ _ _ (hp5 g0).2.2.1) er hW')
  unfold m2cKT; rw [hpre']
  simp only [StateT.run_bind, hvls, except_ok_bind]
  rw [ite_eq_left hc']; exact h'

end karm

/-! ## The η arm -/

section eta
variable (p : Prog) (hp : M2CProg' p) (hnv : closedNV p L.Checker.nvFns = true)
include hp hnv

/-- **`m2c_eta`'s verdicts** are `m2c_pre`'s (its fabrication `m2c_eta2` is outside the verdict
closure). -/
theorem m2cEtaE_ok (N F : Nat) (hk : KnotUpTo p N) (hkE : KnotUpToE p N) (hnF : N ≤ F)
    (hn62 : N ≤ 2 ^ 62) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (eb mode d T indP major : Word) (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1)
    (hmaj : HW major) (cvT : IConstantVal) (caps : IIndCaps) (m : Mem) (a : AState)
    (M : ModeMaps) (hS : CoreS dn m a vis fe M eb) (er : Err)
    (h : callE p (N + 1) "m2c_eta" [mode, vis, d, T, indP, major] m = .error er) :
    ErrClaim (m2cEtaT (coreKnot (decMode mode) fe id F) fe d.toNat (decI T) cvT caps (decE major)) a
      er := by
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (m2cEtaE_spec p hp.eta (N + 1) ⟨m, Locals.init []⟩
    mode vis d T indP major) h (Err.code_ne_of_cls hk0)
  simp only [m2cEtaE] at hW
  cases N with
  | zero =>
    obtain ⟨e', he', h0⟩ := callE_zero p "m2c_pre" [mode, vis, d, major] m
    rw [he', m2cEtaE.k_m2c_pre.none] at hW; cases hW; exact absurd h0 hk0
  | succ N' =>
  cases c1 : callE p (N' + 1) "m2c_pre" [mode, vis, d, major] m with
  | error e1 =>
    rw [c1, m2cEtaE.k_m2c_pre.none] at hW; cases hW
    unfold m2cEtaT
    exact m2cPreE_ok p hp hnv N' F (hk.mono (Nat.le_succ _)) (hkE.mono (Nat.le_succ _)) (by omega)
      (by omega) dn vis fe eb mode d major hm4 hebm hmaj m a M hS _ c1 _
  | ok q =>
  obtain ⟨L, m1⟩ := q
  rw [c1] at hW
  simp only [m2cEtaE.k_m2c_pre] at hW
  split at hW
  · cases hW
  cases c2 : callE p (N' + 1) "get_app_args" [L.tail.headD 0] m1 with
  | error e2 =>
    rw [c2, m2cEtaE.k_get_app_args.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfM2CE_nv "get_app_args" (by simp)) c2
  | ok q =>
  rw [c2] at hW
  simp only [m2cEtaE.k_get_app_args] at hW
  cases c3 : callE p (N' + 1) "caps_never_zero" _ _ with
  | error e3 =>
    rw [c3, m2cEtaE.k_caps_never_zero.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfM2CE_nv "caps_never_zero" (by simp)) c3
  | ok q =>
  rw [c3] at hW
  simp only [m2cEtaE.k_caps_never_zero] at hW
  repeat' split at hW
  all_goals first
    | cases hW
    | exact ErrClaim.of_callE_nv hnv (whnfM2CE_nv "m2c_eta2" (by simp))
        (err_of_k (by intro q e; simp [m2cEtaE.k_m2c_eta2]) (fun _ => rfl) hW)

end eta

/-! ## The `And` arm -/

/-- Error model of `m2c_and2`, by hand (the ok model `m2cAnd2W`: the pushes as `and2Push`). -/
def m2cAnd2HE (p : Prog) (n : Nat) (m : Mem) (mode vis d ctor T tmaj to tn ust major : Word) :
    Except Err (List Word × Mem) :=
  match callE p n "mk_proj" [T, 0, major] m with
  | .error e => .error e
  | .ok (r₁, m₁) =>
  match callE p n "mk_proj" [T, 1, major] m₁ with
  | .error e => .error e
  | .ok (r₂, m₂) =>
  match and2Push m₂ to tn (r₁.headD 0) (r₂.headD 0) with
  | none => .error (.abort 0)
  | some m₃ =>
  match callE p n "intern_const" [ctor, ust] m₃ with
  | .error e => .error e
  | .ok (r₄, m₄) =>
  match callE p n "mk_app_n" [r₄.headD 0, to, tn + 2] m₄ with
  | .error e => .error e
  | .ok (r₅, m₅) =>
  match callE p n "m2c_check" [mode, vis, d, tmaj, r₅.headD 0, major] m₅ with
  | .error e => .error e
  | .ok (r₆, m₆) => .ok ([r₆.headD 0], m₆)

set_option experimental.vcgen true in
theorem m2cAnd2HE_spec (p : Prog) (hp : p.lookup "m2c_and2" = some m2cAnd2L) (n : Nat) (s₀ : St)
    (mode vis d ctor T tmaj to tn ust major : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "m2c_and2" [mode, vis, d, ctor, T, tmaj, to, tn, ust, major]
    ⦃fun _ _ => True; fun ε => ε.code ≠ 0 →
      m2cAnd2HE p n s₀.mem mode vis d ctor T tmaj to tn ust major = .error ε⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, m2cAnd2L]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
    callE_spec p n "mk_proj", callE_spec p n "intern_const", callE_spec p n "mk_app_n",
    callE_spec p n "m2c_check"] <;>
  simp_all [-UInt64.toNat_add, m2cAnd2HE, and2Push, Mem.len64, SPN, CTL, BinOp.eval, Cmp.eval, LocEq,
    St.setLocs_cons, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Locals.init_cons_zero,
    Locals.init_cons_succ]

section andErr
variable (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)

theorem and2_err_check (ctor T : NIdx) (tmaj : EIdx) (targs : List EIdx) (ust : LsIdx) (major : EIdx)
    (a a1 a2 a4 a5 : AState) (p0 p1 hd fab : EIdx)
    (h1 : (internE (.proj T 0 major)).run a = .ok (p0, a1))
    (h2 : (internE (.proj T 1 major)).run a1 = .ok (p1, a2))
    (h4 : (internE (.const ctor ust)).run a2 = .ok (hd, a4))
    (h5 : (mkAppN hd (targs ++ [p0, p1])).run a4 = .ok (fab, a5)) (ce : CheckError)
    (h6 : (m2cCheckT mode r fe depth tmaj fab major).run a5 = .error ce) :
    (m2cAnd2T mode r fe depth ctor T tmaj targs ust major).run a = .error ce := by
  simp only [m2cAnd2T, StateT.run_bind, h1, except_ok_bind, h2, h4, h5]
  exact h6

end andErr

section andarm
variable (p : Prog) (hp : M2CProg' p) (hc : IotaCallees p) (hpi : ProofIrrelOKM p)
  (hE : ErecKeptKnot p) (hcc : ProjCallees p) (hnv : closedNV p L.Checker.nvFns = true)
  (hPI : ProofIrrelWE p)
include hp hc hpi hnv hPI

/-- **`m2c_and2`'s verdicts** are `m2c_check`'s. -/
theorem m2cAnd2E_ok (N F : Nat) (hk : KnotUpTo p N) (hkE : KnotUpToE p N) (hnF : N ≤ F)
    (hn62 : N ≤ 2 ^ 62) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (eb mode d ctor T tmaj to tn ust major : Word) (hm4 : mode < 4)
    (hebm : eb = (mode >>> 1) &&& 1) (hctor : HW ctor) (_hT : HW T) (htm : HW tmaj) (hus : HW ust)
    (hmaj : HW major) (targs : List EIdx) (m : Mem) (a : AState) (M : ModeMaps)
    (hS : CoreS dn m a vis fe M eb) (hsp : SpineR m to tn targs.toArray) (htop : to + tn = spTop m)
    (hvus : ∃ x c, a.store.view x = some (.const c (decI ust))) (er : Err)
    (h : callE p (N + 1) "m2c_and2" [mode, vis, d, ctor, T, tmaj, to, tn, ust, major] m = .error er) :
    ErrClaim (m2cAnd2T (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI ctor)
      (decI T) (decE tmaj) targs (decI ust) (decE major)) a er := by
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (m2cAnd2HE_spec p hp.and2 N ⟨m, Locals.init []⟩
    mode vis d ctor T tmaj to tn ust major) h (Err.code_ne_of_cls hk0)
  simp only [m2cAnd2HE] at hW
  cases N with
  | zero =>
    obtain ⟨e', he', h0⟩ := callE_zero p "mk_proj" [T, 0, major] m
    rw [he'] at hW; cases hW; exact absurd h0 hk0
  | succ N' =>
  cases c1 : callE p (N' + 1) "mk_proj" [T, 0, major] m with
  | error e1 =>
    rw [c1] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfM2CE_nv "mk_proj" (by simp)) c1
  | ok q =>
  obtain ⟨r1, m1⟩ := q
  rw [c1] at hW
  simp only at hW
  obtain ⟨ok1, hD1, res1, hfr1, hh1⟩ := callW_mkProj p hp.toIotaProg' (N' + 1) ⟨m, Locals.init []⟩ a
    hS.arena T 0 major r1 m1 (callW_of_callE c1)
  have hrun1 := AM.run_of_ok _ _ ok1
  rw [res1, show (0 : Word).toNat = 0 from rfl] at hrun1
  have hS1 := hS.of_proj hD1 (Keeps.run (keeps_cpl_internProj _ _ _) hrun1) hfr1
  obtain ⟨e1, t1⟩ := store_spn hfr1.pjStore
  cases c2 : callE p (N' + 1) "mk_proj" [T, 1, major] m1 with
  | error e2 =>
    rw [c2] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfM2CE_nv "mk_proj" (by simp)) c2
  | ok q =>
  obtain ⟨r2, m2⟩ := q
  rw [c2] at hW
  simp only at hW
  obtain ⟨ok2, hD2, res2, hfr2, hh2⟩ := callW_mkProj p hp.toIotaProg' (N' + 1) ⟨m1, Locals.init []⟩ _
    hS1.arena T 1 major r2 m2 (callW_of_callE c2)
  have hrun2 := AM.run_of_ok _ _ ok2
  rw [res2, show (1 : Word).toNat = 1 from rfl] at hrun2
  have hS2 := hS1.of_proj hD2 (Keeps.run (keeps_cpl_internProj _ _ _) hrun2) hfr2
  obtain ⟨e2, t2⟩ := store_spn hfr2.pjStore
  have hsp2 : SpineR m2 to tn targs.toArray := (hsp.of_spn_core e1).of_spn_core e2
  cases c3 : and2Push m2 to tn (r1.headD 0) (r2.headD 0) with
  | none => rw [c3] at hW; cases hW; exact absurd rfl hk0
  | some m3 =>
  rw [c3] at hW
  simp only at hW
  obtain ⟨hS3, hg3, hsp3⟩ := and2Push_ok hS2 hsp2 (by rw [t2, t1]; exact htop) hh1 hh2 c3
  cases c4 : callE p (N' + 1) "intern_const" [ctor, ust] m3 with
  | error e4 =>
    rw [c4] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfM2CE_nv "intern_const" (by simp)) c4
  | ok q =>
  obtain ⟨r4, m4⟩ := q
  rw [c4] at hW
  simp only at hW
  obtain ⟨ok4, hD4, res4, hfr4, hh4⟩ := callW_internConst' p hp.constFind' hp.constPush'
    hp.internConst' (N' + 1) m3 _ hS3.arena ctor ust hctor hus r4 m4 (callW_of_callE c4)
  have hrun4 := AM.run_of_ok _ _ ok4
  rw [res4] at hrun4
  have hS4 := hS3.of_const' hD4 (Keeps.run (keeps_cpl_internConst' _ _) hrun4) hfr4 hrun4 (by
    obtain ⟨x, c, hx⟩ := hvus
    have hx1 := internNodeE_fwd (v := .proj _ _ _) (by simpa [internE] using hrun1) x _
      (.inr ⟨_, _, rfl⟩) hx
    have hx2 := internNodeE_fwd (v := .proj _ _ _) (by simpa [internE] using hrun2) x _
      (.inr ⟨_, _, rfl⟩) hx1
    exact hS3.den.constLs _ _ _ hx2)
  have hsp4 := hsp3.of_spn_core (const_spn hfr4)
  cases c5 : callE p (N' + 1) "mk_app_n" [r4.headD 0, to, tn + 2] m4 with
  | error e5 =>
    rw [c5] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfM2CE_nv "mk_app_n" (by simp)) c5
  | ok q =>
  obtain ⟨r5, m5⟩ := q
  rw [c5] at hW
  simp only at hW
  obtain ⟨ok5, hD5, res5, hfr5, hh5⟩ := callW_mkAppN' p hp.spine (N' + 1) m4 _ hS4.arena
    (r4.headD 0) to (tn + 2) _ hh4 hsp4 r5 m5 (callW_of_callE c5)
  have hrun5 := AM.run_of_ok _ _ ok5
  rw [res5] at hrun5
  have hS5 := hS4.of_app hD5 (Keeps.run (keeps_cpl_mkAppN' _ _) hrun5) hfr5
  have hW' := err_of_k (k := fun (x : Except Err (List Word × Mem)) => match x with
      | .error e => (.error e : Except Err (List Word × Mem))
      | .ok (r₆, m₆) => .ok ([r₆.headD 0], m₆)) (by intro q e; simp) (fun _ => rfl) hW
  have el : ((targs.toArray.push (decE (r1.headD 0))).push (decE (r2.headD 0))).toList =
      targs ++ [decE (r1.headD 0), decE (r2.headD 0)] := by simp
  rw [el, show decE (r4.headD 0) = decI (r4.headD 0) from rfl] at hrun5 hS5
  have z0 : (0 : Word).toNat = 0 := rfl
  have z1 : (1 : Word).toNat = 1 := rfl
  simp only [z0, z1] at hrun2 hrun4 hrun5 hS5
  exact ErrClaim.of_run_err (fun ce h' => and2_err_check _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      hrun1 hrun2 hrun4 hrun5 ce h')
    (m2cCheckE_ok p hp hc hnv hPI N' F (hk.mono (Nat.le_succ _)) (hkE.mono (Nat.le_succ _)) (by omega)
      (by omega) dn vis fe eb mode d tmaj (r5.headD 0) major hm4 hebm htm hh5 hmaj m5 _ M hS5 er hW')

include hE hcc in
/-- **`m2c_and`'s verdicts** are `m2c_pre`'s and `m2c_and2`'s. -/
theorem m2cAndE_ok (N F : Nat) (hk : KnotUpTo p N) (hkE : KnotUpToE p N) (hnF : N ≤ F)
    (hn62 : N ≤ 2 ^ 62) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (eb mode d T major ctor lpl cnP : Word) (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1)
    (hT : HW T) (hmaj : HW major) (hctor : HW ctor) (m : Mem) (a : AState)
    (M : ModeMaps) (hS : CoreS dn m a vis fe M eb) (er : Err)
    (h : callE p (N + 1) "m2c_and" [mode, vis, d, T, major, ctor, lpl, cnP] m = .error er) :
    ErrClaim (m2cAndT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI ctor)
      lpl.toNat cnP.toNat (decI T) (decE major)) a er := by
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (m2cAndE_spec p hp.and_ (N + 1) ⟨m, Locals.init []⟩
    mode vis d T major ctor lpl cnP) h (Err.code_ne_of_cls hk0)
  simp only [m2cAndE] at hW
  cases N with
  | zero =>
    obtain ⟨e', he', h0⟩ := callE_zero p "pin_at" [11] m
    rw [he', m2cAndE.k_pin_at.none] at hW; cases hW; exact absurd h0 hk0
  | succ N' =>
  cases c1 : callE p (N' + 1) "pin_at" [11] m with
  | error e1 =>
    rw [c1, m2cAndE.k_pin_at.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfM2CE_nv "pin_at" (by simp)) c1
  | ok q =>
  obtain ⟨r1, m1⟩ := q
  rw [c1] at hW
  simp only [m2cAndE.k_pin_at] at hW
  obtain ⟨t1, ht1, hm1, -, hanHW, hpin⟩ := triple_of_callE (s₀ := ⟨m, Locals.init []⟩)
    (pinAt_refines p hp.pinat (N' + 1) _ a ⟨fun _ => hS.pins⟩ 11) c1
  have hm1' : m1 = m := ht1.symm.trans hm1
  rw [hm1'] at hW
  have hpin' : pinAnd.run a = .ok (decI (r1.headD 0), a) := by simpa [pinAnd, PIN_AND] using hpin
  by_cases g1 : T ≠ r1.headD 0
  · rw [ite_eq_left g1] at hW; cases hW
  rw [ite_eq_right g1] at hW
  have g1' : T = r1.headD 0 := by simpa using g1
  have hTan : (decI T : NIdx) = decI (r1.headD 0) := by rw [g1']
  cases c2 : callE p (N' + 1) "m2c_pre" [mode, vis, d, major] m with
  | error e2 =>
    rw [c2, m2cAndE.k_m2c_pre.none] at hW; cases hW
    refine ErrClaim.of_run_eqW (a' := a) ?_ (m2cPreE_ok p hp hnv N' F (hk.mono (Nat.le_succ _))
      (hkE.mono (Nat.le_succ _)) (by omega) (by omega) dn vis fe eb mode d major hm4 hebm hmaj m a M hS _ c2
      (fun tmaj T' ust => do
        match ← viewLsLen ust with
        | none => failDanglingLs
        | some ustl =>
        let targs ← getAppArgs coreWalkFuel tmaj
        let ars ← andRescueSlots fe (decI ctor) cnP.toNat ust
        if T' = decI T ∧ targs.length = cnP.toNat ∧ lpl.toNat = ustl ∧ ars = true then
          m2cAnd2T (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI ctor) (decI T) tmaj
            targs ust (decE major)
        else pure (decE major)))
    simp only [m2cAndT, StateT.run_bind, hpin', except_ok_bind]
    rw [ite_eq_left hTan]
    rfl
  | ok q =>
  obtain ⟨L, m2⟩ := q
  rw [c2] at hW
  simp only [m2cAndE.k_m2c_pre] at hW
  obtain ⟨a2, hpre, ⟨M2, hS2, hK2, hSt2⟩, -, hhw⟩ := m2cPre_ok p hp hE N' F
    (hk.mono (Nat.le_succ _)) (by omega) (by omega) dn vis fe eb mode d major hm4 hebm hmaj m a M hS
    L m2 (callW_of_callE c2)
  by_cases g0 : L.headD 0 = 0
  · rw [ite_eq_left g0] at hW; cases hW
  rw [ite_eq_right g0] at hW
  obtain ⟨htm, hT2, hus⟩ := hhw g0
  obtain ⟨l, -, hll, hvl⟩ := hpre.view g0
  have hpre' := m2cPreT_some hpre g0
  cases c3 : callE p (N' + 1) "get_app_args" [L.tail.headD 0] m2 with
  | error e3 =>
    rw [c3, m2cAndE.k_get_app_args.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfM2CE_nv "get_app_args" (by simp)) c3
  | ok q =>
  obtain ⟨r3, m3⟩ := q
  rw [c3] at hW
  simp only [m2cAndE.k_get_app_args] at hW
  obtain ⟨t3, ht3, -, hfr3, hg3, htop3, htop3', xs, hargs, hsp3⟩ := triple_of_callE
    (s₀ := ⟨m2, Locals.init []⟩) (getAppArgs_refines p hp.spine (N' + 1) _ a2 hS2.arena.1 _ htm hS2.spn) c3
  rw [ht3] at hfr3 hg3 hsp3 htop3'
  have hS3 := hS2.frame_stk hfr3 (by simp) (by simp)
  have hlen : xs.length = (r3.tail.headD 0).toNat := by simpa using hsp3.size
  cases c4 : callE p (N' + 1) "and_rescue_slots" [vis, ctor, cnP, L.tail.tail.tail.headD 0] m3 with
  | error e4 =>
    rw [c4, m2cAndE.k_and_rescue_slots.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfM2CE_nv "and_rescue_slots" (by simp)) c4
  | ok q =>
  obtain ⟨r4, m4⟩ := q
  rw [c4] at hW
  simp only [m2cAndE.k_and_rescue_slots] at hW
  obtain ⟨hrun4, ⟨M4, hS4, hK4, hSt4⟩, -⟩ := CoreSpec.run
    (andRescueSlots_refines' p hp.toIotaProg' hcc (N' + 1) ⟨m3, Locals.init []⟩ a2 dn vis fe M2 eb
      ctor cnP _ hS3 hctor hus (hpre.cview g0)) (callW_of_callE c4)
  have hstep : (m2cAndT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI ctor)
      lpl.toNat cnP.toNat (decI T) (decE major)).run a =
      (if (decI (L.tail.tail.headD 0) : NIdx) = decI T ∧ xs.length = cnP.toNat ∧
          lpl.toNat = (L.tail.tail.tail.tail.headD 0).toNat ∧ decBool r4 = true then
        m2cAnd2T (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI ctor) (decI T)
          (decE (L.tail.headD 0)) xs (decI (L.tail.tail.tail.headD 0)) (decE major)
      else pure (decE major)).run
        (AM.st (andRescueSlots fe (decI ctor) cnP.toNat (decI (L.tail.tail.tail.headD 0))) a2) := by
    simp only [m2cAndT, StateT.run_bind, hpin', except_ok_bind]
    rw [ite_eq_left hTan, hpre']
    simp only [StateT.run_bind, viewLsLen_some hvl, except_ok_bind, hargs, hrun4]
  by_cases g2 : L.tail.tail.headD 0 ≠ T
  · rw [ite_eq_left g2] at hW; cases hW
  rw [ite_eq_right g2] at hW
  have g2' : L.tail.tail.headD 0 = T := by simpa using g2
  by_cases g3 : r3.tail.headD 0 ≠ cnP
  · rw [ite_eq_left g3] at hW; cases hW
  rw [ite_eq_right g3] at hW
  have g3' : r3.tail.headD 0 = cnP := by simpa using g3
  by_cases g4 : lpl ≠ L.tail.tail.tail.tail.headD 0
  · rw [ite_eq_left g4] at hW; cases hW
  rw [ite_eq_right g4] at hW
  have g4' : lpl = L.tail.tail.tail.tail.headD 0 := by simpa using g4
  by_cases g5 : r4.headD 0 = 0
  · rw [ite_eq_left g5] at hW; cases hW
  rw [ite_eq_right g5] at hW
  have hcond : (decI (L.tail.tail.headD 0) : NIdx) = decI T ∧ xs.length = cnP.toNat ∧
      lpl.toNat = (L.tail.tail.tail.tail.headD 0).toNat ∧ decBool r4 = true :=
    ⟨by rw [g2'], by rw [hlen, g3'], by rw [g4'], decBool_t_m2c g5⟩
  have hW' := err_of_k (by intro q e; simp [m2cAndE.k_m2c_and2]) (fun _ => rfl) hW
  have hspn3 : (m3.arr64 SPN).size < 2 ^ 63 := hS3.spn
  have htop4 : r3.headD 0 + r3.tail.headD 0 = spTop m4 := by
    rw [hSt4.1, htop3', htop3]
  have hsp4 : SpineR m4 (r3.headD 0) (r3.tail.headD 0) xs.toArray :=
    hsp3.ofKept hSt4 (by
      have hb := hsp3.bound
      rw [htop3', ← htop3, UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
      exact Nat.le_refl _) hspn3
  refine ErrClaim.of_run_eqW (hstep.trans (by rw [ite_eq_left hcond])) ?_
  exact m2cAnd2E_ok p hp hc hpi hnv hPI N' F (hk.mono (Nat.le_succ _)) (hkE.mono (Nat.le_succ _))
    (by omega) (by omega) dn vis fe eb mode d ctor T _ _ _ _ major hm4 hebm hctor hT htm hus hmaj xs m4 _ M4
    hS4 hsp4 htop4
    (by obtain ⟨_, _, _, _, _, _, _, _, hp5⟩ := hpre
        exact ⟨_, _, view_after_noLss (keeps_noLss_andRescueSlots _ _ _ _) (hp5 g0).2.2.1⟩) er hW'

end andarm

/-! ## The dispatch, the family, the head, `major_to_ctor` -/

section top
variable (p : Prog) (hp : M2CProg' p) (hc : IotaCallees p) (hpi : ProofIrrelOKM p)
  (hE : ErecKeptKnot p) (hcc : ProjCallees p) (hnv : closedNV p L.Checker.nvFns = true)
  (hPI : ProofIrrelWE p)
include hp hc hpi hE hcc hnv hPI

/-- **`m2c_arms`'s verdicts** are the arm's. -/
theorem m2cArmsE_ok (N F : Nat) (hk : KnotUpTo p N) (hkE : KnotUpToE p N) (hnF : N ≤ F)
    (hn62 : N ≤ 2 ^ 62) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (eb mode d ro cvjP T indP major : Word) (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1)
    (hT : HW T) (hmaj : HW major) (rl : IRecRule) (cvj : IConstantVal) (cnP cnF : Nat)
    (cvT : IConstantVal) (caps : IIndCaps) (m : Mem) (a : AState) (M : ModeMaps)
    (hS : CoreS dn m a vis fe M eb) (hrl : decRule (m.arr64 EREC) ro.toNat = some rl)
    (hcj : decCI (m.arr64 EREC) dn cvjP.toNat = some (.ctorInfo cvj cnP cnF)) (er : Err)
    (h : callE p (N + 1) "m2c_arms" [mode, vis, d, ro, cvjP, T, indP, major] m = .error er) :
    ErrClaim (m2cArmsT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat rl cvj cnP (decI T)
      cvT caps (decE major)) a er := by
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (m2cArmsE_spec p hp.arms (N + 1) ⟨m, Locals.init []⟩
    mode vis d ro cvjP T indP major) h (Err.code_ne_of_cls hk0)
  simp only [m2cArmsE] at hW
  have hsz := hS.erec
  obtain ⟨⟨w0, e0, l0, hctor⟩, ⟨w9, e9, hkk⟩, ⟨w10, e10, heta⟩⟩ := decRule_words _ _ _ hrl
  obtain ⟨-, ⟨w3, e3, hlp⟩, -, ⟨w5, e5, hnp⟩⟩ := decCI_ctor_words _ dn _ cvj cnP cnF hcj
  have r0 : rdW (m.arr64 EREC) ro = w0 := by simp only [rdW, e0]; rfl
  have r9 : rdW (m.arr64 EREC) (ro + 9) = w9 := rdW_rec (k := 9) e9 (by decide) (by omega)
  have r10 : rdW (m.arr64 EREC) (ro + 10) = w10 := rdW_rec (k := 10) e10 (by decide) (by omega)
  have r3 : rdW (m.arr64 EREC) (cvjP + 3) = w3 := rdW_rec (k := 3) e3 (by decide) (by omega)
  have r5 : rdW (m.arr64 EREC) (cvjP + 5) = w5 := rdW_rec (k := 5) e5 (by decide) (by omega)
  rw [r0, r9, r10, r3, r5] at hW
  have hk1 : ∀ f vs, m2cArmsE.k_m2c_k p (callE p N f vs m) = .error er → callE p N f vs m = .error er :=
    fun f vs h => err_of_k (by intro q e; simp [m2cArmsE.k_m2c_k]) (fun _ => rfl) h
  cases N with
  | zero =>
    exfalso
    split at hW
    · obtain ⟨e', he', h0⟩ := callE_zero p "m2c_k" [mode, vis, d, T, major, w0, w3, w5] m
      rw [hk1 _ _ hW] at he'; cases he'; exact hk0 h0
    split at hW
    · obtain ⟨e', he', h0⟩ := callE_zero p "m2c_eta" [mode, vis, d, T, indP, major] m
      rw [hk1 _ _ hW] at he'; cases he'; exact hk0 h0
    · obtain ⟨e', he', h0⟩ := callE_zero p "m2c_and" [mode, vis, d, T, major, w0, w3, w5] m
      rw [hk1 _ _ hW] at he'; cases he'; exact hk0 h0
  | succ N' =>
  by_cases g9 : w9 ≠ 0
  · rw [ite_eq_left g9] at hW
    have hk' : rl.k = true := by rw [hkk]; simpa using g9
    have : m2cArmsT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat rl cvj cnP (decI T)
        cvT caps (decE major) = m2cKT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat
          (decI w0) w3.toNat w5.toNat (decI T) (decE major) := by
      simp only [m2cArmsT, hk', ↓reduceIte, hctor, hlp, hnp]
    rw [this]
    exact m2cKE_ok p hp hc hpi hE hnv hPI N' F (hk.mono (Nat.le_succ _)) (hkE.mono (Nat.le_succ _))
      (by omega) (by omega) dn vis fe eb mode d T major w0 w3 w5 hm4 hebm hT hmaj l0 m a M hS er (hk1 _ _ hW)
  rw [ite_eq_right g9] at hW
  have hk' : rl.k = false := by rw [hkk]; simpa using g9
  by_cases g10 : w10 ≠ 0
  · rw [ite_eq_left g10] at hW
    have he' : rl.eta = true := by rw [heta]; simpa using g10
    have : m2cArmsT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat rl cvj cnP (decI T)
        cvT caps (decE major) = m2cEtaT (coreKnot (decMode mode) fe id F) fe d.toNat (decI T) cvT caps
          (decE major) := by
      simp only [m2cArmsT, hk', he', Bool.false_eq_true, ↓reduceIte]
    rw [this]
    exact m2cEtaE_ok p hp hnv N' F (hk.mono (Nat.le_succ _)) (hkE.mono (Nat.le_succ _)) (by omega)
      (by omega) dn vis fe eb mode d T indP major hm4 hebm hmaj cvT caps m a M hS er (hk1 _ _ hW)
  rw [ite_eq_right g10] at hW
  have he' : rl.eta = false := by rw [heta]; simpa using g10
  have : m2cArmsT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat rl cvj cnP (decI T)
      cvT caps (decE major) = m2cAndT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat
        (decI w0) w3.toNat w5.toNat (decI T) (decE major) := by
    simp only [m2cArmsT, hk', he', Bool.false_eq_true, ↓reduceIte, hctor, hlp, hnp]
  rw [this]
  exact m2cAndE_ok p hp hc hpi hE hcc hnv hPI N' F (hk.mono (Nat.le_succ _)) (hkE.mono (Nat.le_succ _))
    (by omega) (by omega) dn vis fe eb mode d T major w0 w3 w5 hm4 hebm hT hmaj l0 m a M hS er (hk1 _ _ hW)

/-- **`m2c_ctor`'s verdicts** are `m2c_arms`'s. -/
theorem m2cCtorE_ok (N F : Nat) (hk : KnotUpTo p N) (hkE : KnotUpToE p N) (hnF : N ≤ F)
    (hn62 : N ≤ 2 ^ 62) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (eb mode d ro cvjP major : Word) (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1)
    (hmaj : HW major) (rl : IRecRule) (cvj : IConstantVal) (cnP cnF : Nat) (m : Mem) (a : AState)
    (M : ModeMaps) (hS : CoreS dn m a vis fe M eb) (hrl : decRule (m.arr64 EREC) ro.toNat = some rl)
    (hcj : decCI (m.arr64 EREC) dn cvjP.toNat = some (.ctorInfo cvj cnP cnF)) (er : Err)
    (h : callE p (N + 1) "m2c_ctor" [mode, vis, d, ro, cvjP, major] m = .error er) :
    ErrClaim (m2cCtorT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat rl cvj cnP
      (decE major)) a er := by
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (m2cCtorE_spec p hp.ctor (N + 1) ⟨m, Locals.init []⟩
    mode vis d ro cvjP major) h (Err.code_ne_of_cls hk0)
  simp only [m2cCtorE] at hW
  have hsz := hS.erec
  obtain ⟨-, -, ⟨w4, e4, l4, hty⟩, -⟩ := decCI_ctor_words _ dn _ cvj cnP cnF hcj
  have r4 : rdW (m.arr64 EREC) (cvjP + 4) = w4 := rdW_rec (k := 4) e4 (by decide) (by omega)
  rw [r4] at hW
  have hR := hS.arena.1
  cases c1 : callE p N "pi_result" [w4] m with
  | error e1 =>
    rw [c1, m2cCtorE.k_pi_result.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfM2CE_nv "pi_result" (by simp)) c1
  | ok q =>
  obtain ⟨r1, m1⟩ := q
  rw [c1] at hW
  simp only [m2cCtorE.k_pi_result] at hW
  obtain ⟨t1, ht1, hm1, -, hh1, hpr⟩ := triple_of_callE (s₀ := ⟨m, Locals.init []⟩)
    (piResult_refines' p hp.spine.pires N _ a hR w4 l4) c1
  have hm1' : m1 = m := ht1.symm.trans hm1
  rw [hm1'] at hW
  have hpr' : (piResult coreWalkFuel cvj.type).run a = .ok (decE (r1.headD 0), a) := by
    rw [hty]; exact hpr
  cases c2 : callE p N "get_app_fn" [r1.headD 0] m with
  | error e2 =>
    rw [c2, m2cCtorE.k_get_app_fn.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfM2CE_nv "get_app_fn" (by simp)) c2
  | ok q =>
  obtain ⟨r2, m2⟩ := q
  rw [c2] at hW
  simp only [m2cCtorE.k_get_app_fn] at hW
  obtain ⟨t2, ht2, hm2, -, hh2, hga⟩ := triple_of_callE (s₀ := ⟨m, Locals.init []⟩)
    (getAppFn_refines' p hp.spine.fn N _ a hR (r1.headD 0) hh1) c2
  have hm2' : m2 = m := ht2.symm.trans hm2
  rw [hm2'] at hW
  by_cases g2 : r2.headD 0 >>> 28 ≠ 3
  · rw [ite_eq_left g2] at hW; cases hW
  rw [ite_eq_right g2] at hW
  have g2' : r2.headD 0 >>> 28 = 3 := by simpa using g2
  have ht : ((decE (r2.headD 0)).tag == ETag.const) = true := by
    rw [decE_const_tag _ hh2]; simpa using g2'
  cases c3 : callE p N "m2c_const_view" [r2.headD 0] m with
  | error e3 =>
    rw [c3, m2cCtorE.k_m2c_const_view.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfM2CE_nv "m2c_const_view" (by simp)) c3
  | ok q =>
  obtain ⟨r3, m3⟩ := q
  rw [c3] at hW
  simp only [m2cCtorE.k_m2c_const_view] at hW
  obtain ⟨t3, ht3, -, hm3, hcv⟩ := triple_of_callE (s₀ := ⟨m, Locals.init []⟩)
    (m2cConstView_spec p hp.constView N _ (r2.headD 0)) c3
  have hm3' : m3 = m := ht3.symm.trans hm3
  rw [hm3'] at hW
  simp only [cvwW] at hcv
  obtain ⟨v1, hcv⟩ := of_ite_none hcv
  obtain ⟨v2, hcv⟩ := of_ite_none hcv
  have hr3 := (Option.some.inj hcv).symm
  obtain ⟨hvw, hn32, -⟩ := view_const_f m a hR (r2.headD 0) hh2 ⟨v1, UInt64.not_le.mp v2⟩ g2'
  have hn0 : tfld m CONST (tierW (r2.headD 0)) (idxW (r2.headD 0)) 0 = r3.headD 0 := by
    rw [hr3]; rfl
  rw [hn0] at hvw hn32
  cases c4 : callE p N "env_find" [r3.headD 0, vis] m with
  | error e4 =>
    rw [c4, m2cCtorE.k_env_find.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfM2CE_nv "env_find" (by simp)) c4
  | ok q =>
  obtain ⟨r4, m4⟩ := q
  rw [c4] at hW
  simp only [m2cCtorE.k_env_find] at hW
  obtain ⟨hm4', hfind, hfound⟩ := callW_envFindI p hp.toIotaProg' N m vis _ hS.env hn32 r4 m4
    (callW_of_callE c4)
  rw [hm4'] at hW
  have hview := view_run _ _ _ hvw
  by_cases g4 : r4.headD 0 = 0
  · rw [ite_eq_left g4] at hW; cases hW
  rw [ite_eq_right g4] at hW
  obtain ⟨ci, hci⟩ := hfound g4
  have hciE := (erecP_ext m).decCI hci
  have hfind' : fe.find? (decI (r3.headD 0)) = some ci := by
    rw [hfind]; simp only [decFound, g4, ↓reduceIte]; exact hci
  obtain ⟨wk, ewk, hind, -⟩ := decCI_kind34 _ dn _ ci hciE
  have rk : rdW (m.arr64 EREC) (r4.tail.headD 0) = wk := by simp only [rdW, ewk]; rfl
  rw [rk] at hW
  by_cases g5 : wk ≠ 3
  · rw [ite_eq_left g5] at hW; cases hW
  rw [ite_eq_right g5] at hW
  obtain ⟨cvT, caps, rfl⟩ := hind.mpr (by simpa using g5)
  have hW' := err_of_k (by intro q e; simp [m2cCtorE.k_m2c_arms]) (fun _ => rfl) hW
  cases N with
  | zero => exact ErrClaim.of_callE_zeroW hW'
  | succ N' =>
  refine ErrClaim.of_run_err (fun ce h' => ?_) (m2cArmsE_ok p hp hc hpi hE hcc hnv hPI N' F
    (hk.mono (Nat.le_succ _)) (hkE.mono (Nat.le_succ _)) (by omega) (by omega) dn vis fe eb mode d ro cvjP _
    _ major hm4 hebm hn32 hmaj rl cvj cnP cnF cvT caps m a M hS hrl hcj er hW')
  simp only [m2cCtorT, StateT.run_bind, hpr', except_ok_bind, hga, ht, ↓reduceIte, hview, hfind']
  exact h'

/-- **`m2c_head`'s verdicts** are `m2c_ctor`'s. -/
theorem m2cHeadE_ok (N F : Nat) (hk : KnotUpTo p N) (hkE : KnotUpToE p N) (hnF : N ≤ F)
    (hn62 : N ≤ 2 ^ 62) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (eb mode d ro rc major : Word) (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1)
    (hmaj : HW major) (rules : List IRecRule) (m : Mem) (a : AState) (M : ModeMaps)
    (hS : CoreS dn m a vis fe M eb) (hr : decRules (m.arr64 EREC) ro.toNat rc.toNat = some rules)
    (er : Err) (h : callE p (N + 1) "m2c_head" [mode, vis, d, ro, rc, major] m = .error er) :
    ErrClaim (m2cHeadT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat rules
      (decE major)) a er := by
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (m2cHeadE_spec p hp.head (N + 1) ⟨m, Locals.init []⟩
    mode vis d ro rc major) h (Err.code_ne_of_cls hk0)
  simp only [m2cHeadE] at hW
  cases N with
  | zero =>
    obtain ⟨e', he', h0⟩ := callE_zero p "is_ctor_app" [vis, major] m
    rw [he', m2cHeadE.k_is_ctor_app.none] at hW; cases hW; exact absurd h0 hk0
  | succ N' =>
  cases c1 : callE p (N' + 1) "is_ctor_app" [vis, major] m with
  | error e1 =>
    rw [c1, m2cHeadE.k_is_ctor_app.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfM2CE_nv "is_ctor_app" (by simp)) c1
  | ok q =>
  obtain ⟨r1, m1⟩ := q
  rw [c1] at hW
  simp only [m2cHeadE.k_is_ctor_app] at hW
  obtain ⟨hrun1, ⟨M1, hS1, hK1, hSt1⟩, -⟩ := CoreSpec.run
    (isCtorApp_refines p hp.toIotaProg' N' ⟨m, Locals.init []⟩ a dn vis fe M eb major hS hmaj)
    (callW_of_callE c1)
  have e1 : m1.arr64 EREC = m.arr64 EREC := hE _ _ _ _ _ _ (by simp) (callW_of_callE c1)
  by_cases g1 : r1.headD 0 ≠ 0
  · rw [ite_eq_left g1] at hW; cases hW
  rw [ite_eq_right g1] at hW
  rw [decBool_f_m2c (by simpa using g1)] at hrun1
  have hstep : (m2cHeadT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat rules
      (decE major)).run a = (match rules with
        | [rl] =>
          match fe.find? rl.ctor with
          | some (.ctorInfo cvj cnP _cnF) =>
            m2cCtorT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat rl cvj cnP
              (decE major)
          | _ => pure (decE major)
        | _ => pure (decE major)).run (AM.st (isCtorApp fe (decE major)) a) := by
    simp only [m2cHeadT, StateT.run_bind, hrun1, except_ok_bind, Bool.false_eq_true, ↓reduceIte]
    rfl
  obtain ⟨hlen, hget⟩ := decRules_get _ _ _ _ hr
  by_cases g2 : rc ≠ 1
  · rw [ite_eq_left g2] at hW; cases hW
  rw [ite_eq_right g2] at hW
  have g2' : rc = 1 := by simpa using g2
  subst g2'
  obtain ⟨rl, rfl⟩ : ∃ rl, rules = [rl] := by
    match rules, hlen with
    | [x], _ => exact ⟨x, rfl⟩
  have hrl : decRule (m.arr64 EREC) ro.toNat = some rl := by
    have := hget 0 (by decide); simpa using this
  obtain ⟨⟨w0, e0, l0, hctor⟩, -, -⟩ := decRule_words _ _ _ hrl
  have r0 : rdW (m1.arr64 EREC) ro = w0 := by rw [e1]; simp only [rdW, e0]; rfl
  rw [r0] at hW
  cases c2 : callE p (N' + 1) "env_find" [w0, vis] m1 with
  | error e2 =>
    rw [c2, m2cHeadE.k_env_find.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfM2CE_nv "env_find" (by simp)) c2
  | ok q =>
  obtain ⟨r2, m2⟩ := q
  rw [c2] at hW
  simp only [m2cHeadE.k_env_find] at hW
  obtain ⟨hm2, hfind, hfound⟩ := callW_envFindI p hp.toIotaProg' (N' + 1) m1 vis _ hS1.env l0 r2 m2
    (callW_of_callE c2)
  rw [hm2] at hW
  by_cases g3 : r2.headD 0 = 0
  · rw [ite_eq_left g3] at hW; cases hW
  rw [ite_eq_right g3] at hW
  obtain ⟨ci, hci⟩ := hfound g3
  have hciE := (erecP_ext m1).decCI hci
  have hfind' : fe.find? rl.ctor = some ci := by
    rw [hctor, hfind]; simp only [decFound, g3, ↓reduceIte]; exact hci
  obtain ⟨wk, ewk, -, hctr⟩ := decCI_kind34 _ dn _ ci hciE
  have rk : rdW (m1.arr64 EREC) (r2.tail.headD 0) = wk := by simp only [rdW, ewk]; rfl
  rw [rk] at hW
  by_cases g4 : wk ≠ 4
  · rw [ite_eq_left g4] at hW; cases hW
  rw [ite_eq_right g4] at hW
  obtain ⟨cvj, cnP, cnF, rfl⟩ := hctr.mpr (by simpa using g4)
  have hW' := err_of_k (by intro q e; simp [m2cHeadE.k_m2c_ctor]) (fun _ => rfl) hW
  refine ErrClaim.of_run_err (fun ce h' => ?_) (m2cCtorE_ok p hp hc hpi hE hcc hnv hPI N' F
    (hk.mono (Nat.le_succ _)) (hkE.mono (Nat.le_succ _)) (by omega) (by omega) dn vis fe eb mode d ro _
    major hm4 hebm hmaj rl cvj cnP cnF m1 _ M1 hS1 (by rw [e1]; exact hrl) hciE er hW')
  rw [hstep]; simp only [hfind']; exact h'

/-- **`MajorToCtorE`**: `major_to_ctor`'s verdicts are `m2c_head`'s. -/
theorem majorToCtorE_of : MajorToCtorE p := by
  intro n hk hkE F hnF s₀ a₀ dn vis fe MM eb mode d rec ro rc major rules hn62 hS hm4 hebm hmaj hr
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (mtcE_spec p hp.majorToCtor (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d rec ro rc major) hc0 (Err.code_ne_of_cls hk0)
  simp only [mtcE] at hW
  have hW' := err_of_k (by intro q e; simp [mtcE.k_m2c_head]) (fun _ => rfl) hW
  cases n with
  | zero => exact ErrClaim.of_callE_zeroW hW'
  | succ N =>
  rw [majorToCtor_eq]
  exact m2cHeadE_ok p hp hc hpi hE hcc hnv hPI N F (hk.mono (Nat.le_succ _)) (hkE.mono (Nat.le_succ _))
    (by omega) (by omega) dn vis fe eb mode d ro rc major hm4 hebm hmaj rules s₀.mem a₀ MM hS hr er hW'

end top

end L.Arena
