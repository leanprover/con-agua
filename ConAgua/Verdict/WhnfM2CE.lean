import ConAgua.Verdict.WhnfModels6E
import ConAgua.Verdict.WhnfSlotE
import ConAgua.Arena.WhnfM2CRefine5

/-!
# `major_to_ctor`'s verdict claims (lane `verdicts-b`, helper `k2`)

No verdict site of its own: the claims are the `infer_io`, `whnf` and `defeq` slots'
(`KnotUpToE`) and `proof_irrel`'s (`ProofIrrelE`), through `m2c_pre`, `m2c_check` and the arms
(`majorToCtorE_of`: `MajorToCtorE`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false

namespace L.Arena

theorem whnfM2CE_nv : ∀ f ∈ ["get_app_fn", "m2c_const_view", "ls_node", "fab_scope_ok",
    "get_app_args", "intern_const", "mk_app_n", "caps_never_zero", "m2c_eta2", "pin_at", "mk_proj",
    "and_rescue_slots", "pi_result", "env_find", "is_ctor_app"], f ∈ L.Checker.nvFns := by
  decide +kernel

/-- `proof_irrel`'s error claim at fuel `N + 1` (the premises of `ProofIrrelOKM`). -/
def ProofIrrelE (p : Prog) : Prop :=
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
  (hPI : ProofIrrelE p)
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
  · rw [if_pos g1] at hW; cases hW
  rw [if_neg g1] at hW
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
  · rw [if_pos g3] at hW; cases hW
  rw [if_neg g3] at hW
  rw [decBool_t_m2c g3] at hrun3
  have hv := decMode_verified mode hm4
  by_cases g4 : mode &&& 1 = 0
  · rw [if_pos g4] at hW
    have hv' : (decMode mode).verifiedChecks = true := by rw [hv]; simpa using g4
    have hW' := err_of_k (by intro q e; simp only [m2cCheckE.k_proof_irrel, m2cCheckE.j1]; split <;> simp)
      (fun _ => rfl) hW
    exact ErrClaim.of_run_err (fun ce h' => check_err_pi _ _ _ _ _ _ _ _ _ _ _ _ hv' hrun1 hrun2 hrun3 ce h')
      (CoreSpecE.of_callE (hPI N' (hk.mono (Nat.le_succ _)) (hkE.mono (Nat.le_succ _)) F (by omega)
        (by omega) ⟨m3, Locals.init []⟩ _ dn vis fe M3 eb mode d fab major hS3 hm4 hebm hfab hmaj) hW')
  · rw [if_neg g4] at hW
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
  (hE : ErecKeptKnot p) (hnv : closedNV p L.Checker.nvFns = true) (hPI : ProofIrrelE p)
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
  · rw [if_pos g1] at hW; cases hW
  rw [if_neg g1] at hW
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
    (hT : HW T) (hmaj : HW major) (hctor : HW ctor) (m : Mem) (a : AState)
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
  · rw [if_pos g0] at hW; cases hW
  rw [if_neg g0] at hW
  obtain ⟨htm, hT2, hus⟩ := hhw g0
  obtain ⟨l, hvls, hll, -⟩ := hpre.view g0
  have hpre' := m2cPreT_some hpre g0
  by_cases g2 : L.tail.tail.headD 0 ≠ T
  · rw [if_pos g2] at hW; cases hW
  rw [if_neg g2] at hW
  have g2' : L.tail.tail.headD 0 = T := by simpa using g2
  by_cases g3 : lpl ≠ L.tail.tail.tail.tail.headD 0
  · rw [if_pos g3] at hW; cases hW
  rw [if_neg g3] at hW
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
  rw [if_pos hc']; exact h'

end karm

end L.Arena
