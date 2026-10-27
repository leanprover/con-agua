import ConAgua.Verdict.WhnfIotaE
import ConAgua.Checker.NoVerdictTree
set_option linter.unusedSectionVars false

/-!
# `prepare_major`'s and `lit_major_to_ctor`'s verdict claims (lane `verdicts-b`, helper `k2`)

Neither has a verdict site of its own: `lit_major_to_ctor`'s claims are the `whnf` slot's,
`prepare_major`'s are `major_to_ctor`'s (`MajorToCtorE`, a hypothesis), `lit_major_to_ctor`'s and
the slot's (`prepareMajorE_of`: `PrepareMajorE`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

theorem whnfPrepE_nv : ∀ f ∈ ["lit_to_ctor_if_nat", "str_lit_supported", "str_lit_ctor",
    "rec_rule_k", "is_ctor_app", "is_str_lit"], f ∈ L.Checker.nvFns :=
  _root_.L.Checker.nv_sub (by decide +kernel)

/-! ## `lit_major_to_ctor` -/

theorem litMajorToCtor_err_str (r : CoreFnsA) (fe : IFEnv) (d : Nat) (h : EIdx) (a a₁ a₂ : AState)
    (ht : h.tag = ETag.lit) (s : String) (hv : a.store.view h = some (.lit (.strVal s)))
    (hs : (strLitSupported fe).run a = .ok (true, a₁)) (c : EIdx)
    (hc : (strLitToConstructor s).run a₁ = .ok (c, a₂)) (ce : CheckError)
    (hw : (r.whnf d c).run a₂ = .error ce) :
    (litMajorToCtor r fe d h).run a = .error ce := by
  have hv' : (view h).run a = .ok (.lit (.strVal s), a) := by
    simp [view, hv, StateT.run_bind, StateT.run_get]; rfl
  simp only [litMajorToCtor, ht, beq_self_eq_true, ↓reduceIte, StateT.run_bind, hv', except_ok_bind,
    hs, hc, hw]

/-- `lit_major_to_ctor`'s error claim at fuel `N + 1` (the premises of `litMajorToCtor_refines'`). -/
def LitMajorToCtorE (p : Prog) : Prop :=
  ∀ (N : Nat), KnotUpTo p N → KnotUpToE p N → ∀ (F : Nat), N ≤ F → N ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d h : Word), CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 →
    eb = (mode >>> 1) &&& 1 → HW h →
    CoreSpecE p (N + 1) "lit_major_to_ctor" [mode, vis, d, h]
      (litMajorToCtor (coreKnot (decMode mode) fe id F) fe d.toNat (decE h)) s₀ a₀

/-- **`LitMajorToCtorE`**: `lit_major_to_ctor`'s verdicts are the `whnf` slot's (on a supported
string literal). -/
theorem litMajorToCtorE_of (p : Prog) (hp : IotaProg' p) (hw : WhnfCallees p)
    (hsup : ∀ fe : IFEnv, SupKeep fe) (hnv : closedNV p L.Checker.nvFns = true) :
    LitMajorToCtorE p := by
  intro n hk hkE F hnF hn62 s₀ a₀ dn vis fe MM eb mode d h hS hm4 hebm hh
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (lmtcE_spec p hp.litMajorToCtor (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d h) hc0 (Err.code_ne_of_cls hk0)
  simp only [lmtcE] at hW
  have hR := hS.arena.1
  by_cases h8 : h >>> 28 ≠ 8
  · rw [ite_eq_left h8] at hW
    exact ErrClaim.of_callE_nv hnv (whnfPrepE_nv "lit_to_ctor_if_nat" (by simp))
      (err_of_k (by intro q e; simp [lmtcE.k_lit_to_ctor_if_nat]) (fun _ => rfl) hW)
  rw [ite_eq_right h8] at hW
  have h8' : h >>> 28 = 8 := by simpa using h8
  by_cases hsc : tierW h ≠ 0 ∧ rdW (s₀.mem.arr64 CTL) 1 = 0
  · rw [ite_eq_left hsc] at hW; cases hW; exact absurd rfl hk0
  rw [ite_eq_right hsc] at hW
  by_cases hbd : tcnt s₀.mem LIT (tierW h) ≤ idxW h
  · rw [ite_eq_left hbd] at hW; cases hW; exact absurd rfl hk0
  rw [ite_eq_right hbd] at hW
  have hvOK : viewOK s₀.mem h LIT := ⟨hsc, by simpa using hbd⟩
  obtain ⟨hviewS, -⟩ := view_lit_kind s₀.mem a₀ hR h hh hvOK h8'
  have htag : (decE h).tag = ETag.lit := (decE_tag_lit h hh).mpr h8'
  by_cases hkind : tfld s₀.mem LIT (tierW h) (idxW h) 0 ≠ 1
  · rw [ite_eq_left hkind] at hW
    exact ErrClaim.of_callE_nv hnv (whnfPrepE_nv "lit_to_ctor_if_nat" (by simp))
      (err_of_k (by intro q e; simp [lmtcE.k_lit_to_ctor_if_nat]) (fun _ => rfl) hW)
  rw [ite_eq_right hkind] at hW
  obtain ⟨str, hview⟩ := hviewS (by simpa using hkind)
  cases hc1 : callE p n "str_lit_supported" [vis] s₀.mem with
  | error e1 =>
    rw [hc1, lmtcE.k_str_lit_supported.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfPrepE_nv "str_lit_supported" (by simp)) hc1
  | ok q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [hc1] at hW
  simp only [lmtcE.k_str_lit_supported] at hW
  obtain ⟨hrun1, ⟨M₁, hS₁, -, -⟩, -⟩ := CoreSpec.run
    (hw.strLitSupported n ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe MM eb hS) (callW_of_callE hc1)
  by_cases h0 : r₁.headD 0 = 0
  · rw [ite_eq_left h0] at hW; cases hW
  rw [ite_eq_right h0] at hW
  rw [decBool_t_m2c h0] at hrun1
  cases hc2 : callE p n "str_lit_ctor" [h] m₁ with
  | error e2 =>
    rw [hc2, lmtcE.k_str_lit_ctor.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfPrepE_nv "str_lit_ctor" (by simp)) hc2
  | ok q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [hc2] at hW
  simp only [lmtcE.k_str_lit_ctor] at hW
  have hviewA : (AM.st (strLitSupported fe) a₀).store.view (decE h) = some (.lit (.strVal str)) :=
    hsup fe a₀ (decE h) _ hview
  obtain ⟨hrun2, ⟨M₂, hS₂, -, -⟩, hr₂⟩ := CoreSpec.run
    (hw.strLitCtor n ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb h str hS₁ hh hviewA) (callW_of_callE hc2)
  have hW' := err_of_k (by intro q e; simp [lmtcE.k_lit_to_ctor_if_nat]) (fun _ => rfl) hW
  exact ErrClaim.of_run_err (fun ce h' => litMajorToCtor_err_str _ fe d.toNat (decE h) a₀ _ _ htag str
      hview hrun1 _ hrun2 ce h')
    (CoreSpecE.of_callE ((hkE n (Nat.le_refl _)).whnf F ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode d _
      hnF hn62 ⟨hS₂, hm4, hebm⟩ hr₂) hW')

/-! ## `prepare_major` -/

/-- `major_to_ctor`'s error claim at fuel `N + 1` (the premises of `MajorToCtorOK`). -/
def MajorToCtorE (p : Prog) : Prop :=
  ∀ (N : Nat), KnotUpTo p N → KnotUpToE p N → ∀ (F : Nat), N ≤ F →
  ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d rec ro rc major : Word) (rules : List IRecRule),
    N ≤ 2 ^ 62 → CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 →
    HW major → decRules (s₀.mem.arr64 EREC) ro.toNat rc.toNat = some rules →
    CoreSpecE p (N + 1) "major_to_ctor" [mode, vis, d, rec, ro, rc, major]
      (majorToCtor (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI rec) rules
        (decE major)) s₀ a₀

/-- The twin's `prepareMajor` past the rescued major `me` (non-K). -/
def pmTailT (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (d : Nat) (rec : NIdx)
    (rules : List IRecRule) (me : EIdx) : AM EIdx := do
  if ← isCtorApp fe me then pure me
  else do
    let major₀ ← r.whnf d me
    let major₁ ← litMajorToCtor r fe d major₀
    majorToCtor mode r fe d rec rules major₁

section pmErr
variable (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (d : Nat) (rec : NIdx)
  (rules : List IRecRule) (major : EIdx)

theorem pm_err_K_m2c (hK : recRuleK rules = true) (a : AState) (ce : CheckError)
    (h1 : (majorToCtor mode r fe d rec rules major).run a = .error ce) :
    (prepareMajor mode r fe d rec rules major).run a = .error ce := by
  simp only [prepareMajor, hK, ↓reduceIte, StateT.run_bind, h1]; rfl

theorem pm_err_K_lmtc (hK : recRuleK rules = true) (a a1 a2 : AState) (mk : EIdx)
    (h1 : (majorToCtor mode r fe d rec rules major).run a = .ok (mk, a1))
    (h2 : (isCtorApp fe mk).run a1 = .ok (true, a2)) (ce : CheckError)
    (h3 : (litMajorToCtor r fe d mk).run a2 = .error ce) :
    (prepareMajor mode r fe d rec rules major).run a = .error ce := by
  simp only [prepareMajor, hK, ↓reduceIte, StateT.run_bind, h1, h2, h3, except_ok_bind]

theorem pm_err_nk_str (hK : recRuleK rules = false) (a a1 : AState)
    (hs : (isStrLit major).run a = .ok (true, a1)) (ce : CheckError)
    (ht : (pmTailT mode r fe d rec rules major).run a1 = .error ce) :
    (prepareMajor mode r fe d rec rules major).run a = .error ce := by
  simp only [prepareMajor, hK, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, hs, except_ok_bind, pure_bind]
  simpa [pmTailT, StateT.run_bind] using ht

theorem pm_err_nk_m2c (hK : recRuleK rules = false) (a a1 : AState)
    (hs : (isStrLit major).run a = .ok (false, a1)) (ce : CheckError)
    (hE : (majorToCtor mode r fe d rec rules major).run a1 = .error ce) :
    (prepareMajor mode r fe d rec rules major).run a = .error ce := by
  simp only [prepareMajor, hK, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, hs, except_ok_bind,
    hE]; rfl

theorem pm_err_nk_not (hK : recRuleK rules = false) (a a1 a2 : AState) (me : EIdx)
    (hs : (isStrLit major).run a = .ok (false, a1))
    (hE : (majorToCtor mode r fe d rec rules major).run a1 = .ok (me, a2)) (ce : CheckError)
    (ht : (pmTailT mode r fe d rec rules me).run a2 = .error ce) :
    (prepareMajor mode r fe d rec rules major).run a = .error ce := by
  simp only [prepareMajor, hK, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, hs, except_ok_bind,
    hE]
  simpa [pmTailT, StateT.run_bind] using ht

theorem tail_err_whnf (me : EIdx) (a a3 : AState) (hc : (isCtorApp fe me).run a = .ok (false, a3))
    (ce : CheckError) (hw : (r.whnf d me).run a3 = .error ce) :
    (pmTailT mode r fe d rec rules me).run a = .error ce := by
  simp only [pmTailT, StateT.run_bind, hc, except_ok_bind, Bool.false_eq_true, ↓reduceIte, hw]; rfl

theorem tail_err_lmtc (me m0 : EIdx) (a a3 a4 : AState)
    (hc : (isCtorApp fe me).run a = .ok (false, a3)) (hw : (r.whnf d me).run a3 = .ok (m0, a4))
    (ce : CheckError) (hl : (litMajorToCtor r fe d m0).run a4 = .error ce) :
    (pmTailT mode r fe d rec rules me).run a = .error ce := by
  simp only [pmTailT, StateT.run_bind, hc, except_ok_bind, Bool.false_eq_true, ↓reduceIte, hw, hl]; rfl

theorem tail_err_m2c (me m0 m1 : EIdx) (a a3 a4 a5 : AState)
    (hc : (isCtorApp fe me).run a = .ok (false, a3)) (hw : (r.whnf d me).run a3 = .ok (m0, a4))
    (hl : (litMajorToCtor r fe d m0).run a4 = .ok (m1, a5)) (ce : CheckError)
    (hf : (majorToCtor mode r fe d rec rules m1).run a5 = .error ce) :
    (pmTailT mode r fe d rec rules me).run a = .error ce := by
  simp only [pmTailT, StateT.run_bind, hc, except_ok_bind, Bool.false_eq_true, ↓reduceIte, hw, hl, hf]

end pmErr

section prep
variable (p : Prog) (hp : IotaProg4 p) (hc : IotaCallees p) (hw : WhnfCallees p)
  (hsup : ∀ fe : IFEnv, SupKeep fe) (hmtc : MajorToCtorOK p) (hE : ErecKeptKnot p)
  (hnv : closedNV p L.Checker.nvFns = true) (hM : MajorToCtorE p)

include hp hc hw hsup hmtc hE hnv hM in
/-- **The tail of `prepare_major`'s non-K arm fails only where `pmTailT` does.** -/
theorem pmTailE (N : Nat) (hk : KnotUpTo p (N + 1)) (hkE : KnotUpToE p (N + 1)) (F : Nat)
    (hnF : N + 1 ≤ F) (hn62 : N + 1 ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (eb mode d rec ro rc me : Word)
    (rules : List IRecRule) (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1) (hme : HW me)
    (m3 : Mem) (a : AState) (M : ModeMaps) (hS : CoreS dn m3 a vis fe M eb)
    (hrules : decRules (m3.arr64 EREC) ro.toNat rc.toNat = some rules) (er : Err)
    (h : pmE.j1 p (N + 1) mode vis d rec ro rc me m3 = .error er) :
    ErrClaim (pmTailT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI rec) rules
      (decE me)) a er := by
  have hk' : KnotUpTo p N := hk.mono (Nat.le_succ N)
  simp only [pmE.j1] at h
  cases c4 : callE p (N + 1) "is_ctor_app" [vis, me] m3 with
  | error e4 =>
    rw [c4, pmE.k_is_ctor_app_2.none] at h; cases h
    exact ErrClaim.of_callE_nv hnv (whnfPrepE_nv "is_ctor_app" (by simp)) c4
  | ok q =>
  obtain ⟨r4, m4⟩ := q
  rw [c4] at h
  simp only [pmE.k_is_ctor_app_2] at h
  obtain ⟨hrun4, ⟨M4, hS4, -, -⟩, -⟩ := CoreSpec.run
    (isCtorApp_refines p hp.toIotaProg' N ⟨m3, Locals.init []⟩ a dn vis fe M eb me hS hme)
    (callW_of_callE c4)
  by_cases hc4 : r4.headD 0 ≠ 0
  · rw [ite_eq_left hc4] at h; cases h
  rw [ite_eq_right hc4] at h
  have hb : decBool r4 = false := by
    unfold decBool; have : r4.headD 0 = 0 := Classical.not_not.mp hc4
    rw [this]; rfl
  rw [hb] at hrun4
  cases c5 : callE p (N + 1) "whnf" [mode, vis, d, me] m4 with
  | error e5 =>
    rw [c5, pmE.k_whnf.none] at h; cases h
    exact ErrClaim.of_run_err (fun ce h' => tail_err_whnf (hc := hrun4) (ce := ce) (hw := h') ..)
      (CoreSpecE.of_callE ((hkE (N + 1) (Nat.le_refl _)).whnf F ⟨m4, Locals.init []⟩ _ dn vis fe M4 eb
        mode d me hnF hn62 ⟨hS4, hm4, hebm⟩ hme) c5)
  | ok q =>
  obtain ⟨r5, m5⟩ := q
  rw [c5] at h
  simp only [pmE.k_whnf] at h
  obtain ⟨hrun5, ⟨M5, hS5, -, -⟩, hr5⟩ := CoreSpec.run
    ((hk (N + 1) (Nat.le_refl _)).whnf F ⟨m4, Locals.init []⟩ _ dn vis fe M4 eb mode d me hnF hn62
      ⟨hS4, hm4, hebm⟩ hme) (callW_of_callE c5)
  cases c6 : callE p (N + 1) "lit_major_to_ctor" [mode, vis, d, r5.headD 0] m5 with
  | error e6 =>
    rw [c6, pmE.k_lit_major_to_ctor_2.none] at h; cases h
    exact ErrClaim.of_run_err (fun ce h' => tail_err_lmtc (hc := hrun4) (hw := hrun5) (ce := ce) (hl := h') ..)
      (CoreSpecE.of_callE (litMajorToCtorE_of p hp.toIotaProg' hw hsup hnv N hk' (hkE.mono (by omega))
        F (by omega) (by omega) ⟨m5, Locals.init []⟩ _ dn vis fe M5 eb mode d (r5.headD 0) hS5 hm4 hebm
        hr5) c6)
  | ok q =>
  obtain ⟨r6, m6⟩ := q
  rw [c6] at h
  simp only [pmE.k_lit_major_to_ctor_2] at h
  obtain ⟨hrun6, ⟨M6, hS6, -, -⟩, hr6⟩ := CoreSpec.run
    (litMajorToCtor_refines' p hp.toIotaProg' hc hw hsup N hk' F (by omega) (by omega)
      ⟨m5, Locals.init []⟩ _ dn vis fe M5 eb mode d (r5.headD 0) hS5 hm4 hebm hr5) (callW_of_callE c6)
  have e4 : m4.arr64 EREC = m3.arr64 EREC := hE _ _ _ _ _ _ (by simp) (callW_of_callE c4)
  have e5 : m5.arr64 EREC = m4.arr64 EREC := hE _ _ _ _ _ _ (by simp) (callW_of_callE c5)
  have e6 : m6.arr64 EREC = m5.arr64 EREC := hE _ _ _ _ _ _ (by simp) (callW_of_callE c6)
  have hrules6 : decRules (m6.arr64 EREC) ro.toNat rc.toNat = some rules := by
    rw [e6, e5, e4]; exact hrules
  have h' := err_of_k (by intro q e; simp [pmE.k_lit_major_to_ctor]) (fun _ => rfl) h
  exact ErrClaim.of_run_err (fun ce h'' => tail_err_m2c (hc := hrun4) (hw := hrun5) (hl := hrun6) (ce := ce)
      (hf := h'') ..)
    (CoreSpecE.of_callE (hM N hk' (hkE.mono (by omega)) F (by omega) ⟨m6, Locals.init []⟩ _ dn vis fe
      M6 eb mode d rec ro rc (r6.headD 0) rules (by omega) hS6 hm4 hebm hr6 hrules6) h')

include hp hc hw hsup hmtc hE hnv hM in
/-- **`PrepareMajorE`**: `prepare_major`'s verdicts are `major_to_ctor`'s, `lit_major_to_ctor`'s
and the `whnf` slot's. -/
theorem prepareMajorE_of : PrepareMajorE p := by
  intro n hk hkE F hnF hn62 s₀ a₀ dn vis fe MM eb mode d rec ro rc major rules hS hm4 hebm hmaj hr
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (pmE_spec p hp.prepareMajor (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d rec ro rc major) hc0 (Err.code_ne_of_cls hk0)
  simp only [pmE] at hW
  cases c1 : callE p n "rec_rule_k" [ro, rc] s₀.mem with
  | error e1 =>
    rw [c1, pmE.k_rec_rule_k.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfPrepE_nv "rec_rule_k" (by simp)) c1
  | ok q =>
  obtain ⟨rk, m1⟩ := q
  rw [c1] at hW
  simp only [pmE.k_rec_rule_k] at hW
  obtain ⟨t1, ht1, hmem1, -, hkk⟩ := triple_of_callE
    (recRuleK_refines p hp.recRuleK n ⟨s₀.mem, Locals.init []⟩ ro rc rules
      (by have := hS.erec; show (s₀.mem.arr64 EREC).size < 2 ^ 64; omega) hr) c1
  have hm1 : m1 = s₀.mem := by rw [← ht1]; exact hmem1
  subst hm1
  cases n with
  | zero =>
    obtain ⟨e', he', -⟩ := callE_zero p "rec_rule_k" [ro, rc] s₀.mem
    rw [c1] at he'; cases he'
  | succ N =>
  have hk' : KnotUpTo p N := hk.mono (Nat.le_succ N)
  by_cases hkr : rk.headD 0 ≠ 0
  · -- the K arm
    rw [ite_eq_left hkr] at hW
    have hK : recRuleK rules = true := by rw [← hkk]; simpa using hkr
    cases c2 : callE p (N + 1) "major_to_ctor" [mode, vis, d, rec, ro, rc, major] s₀.mem with
    | error e2 =>
      rw [c2, pmE.k_major_to_ctor.none] at hW; cases hW
      exact ErrClaim.of_run_err (fun ce h' => pm_err_K_m2c _ _ _ _ _ _ _ hK a₀ ce h')
        (CoreSpecE.of_callE (hM N hk' (hkE.mono (by omega)) F (by omega) ⟨s₀.mem, Locals.init []⟩ a₀ dn vis
          fe MM eb mode d rec ro rc major rules (by omega) hS hm4 hebm hmaj hr) c2)
    | ok q =>
    obtain ⟨r2, m2⟩ := q
    rw [c2] at hW
    simp only [pmE.k_major_to_ctor] at hW
    obtain ⟨hrun2, ⟨M2, hS2, -, -⟩, hr2⟩ := CoreSpec.run
      (hmtc N hk' F (by omega) ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe MM eb mode d rec ro rc major rules
        (by omega) hS hm4 hebm hmaj hr) (callW_of_callE c2)
    cases c3 : callE p (N + 1) "is_ctor_app" [vis, r2.headD 0] m2 with
    | error e3 =>
      rw [c3, pmE.k_is_ctor_app.none] at hW; cases hW
      exact ErrClaim.of_callE_nv hnv (whnfPrepE_nv "is_ctor_app" (by simp)) c3
    | ok q =>
    obtain ⟨r3, m3⟩ := q
    rw [c3] at hW
    simp only [pmE.k_is_ctor_app] at hW
    obtain ⟨hrun3, ⟨M3, hS3, -, -⟩, -⟩ := CoreSpec.run
      (isCtorApp_refines p hp.toIotaProg' N ⟨m2, Locals.init []⟩ _ dn vis fe M2 eb (r2.headD 0) hS2 hr2)
      (callW_of_callE c3)
    by_cases hc3 : r3.headD 0 ≠ 0
    · rw [ite_eq_left hc3] at hW
      rw [decBool_t_m2c hc3] at hrun3
      have hW' := err_of_k (by intro q e; simp [pmE.k_lit_major_to_ctor]) (fun _ => rfl) hW
      exact ErrClaim.of_run_err (fun ce h' => pm_err_K_lmtc _ _ _ _ _ _ _ hK a₀ _ _ _ hrun2 hrun3 ce h')
        (CoreSpecE.of_callE (litMajorToCtorE_of p hp.toIotaProg' hw hsup hnv N hk' (hkE.mono (by omega))
          F (by omega) (by omega) ⟨m3, Locals.init []⟩ _ dn vis fe M3 eb mode d (r2.headD 0) hS3 hm4
          hebm hr2) hW')
    · rw [ite_eq_right hc3] at hW; cases hW
  · rw [ite_eq_right hkr] at hW
    have hK0 : recRuleK rules = false := by rw [← hkk, Classical.not_not.mp hkr]; rfl
    cases c2 : callE p (N + 1) "is_str_lit" [major] s₀.mem with
    | error e2 =>
      rw [c2, pmE.k_is_str_lit.none] at hW; cases hW
      exact ErrClaim.of_callE_nv hnv (whnfPrepE_nv "is_str_lit" (by simp)) c2
    | ok q =>
    obtain ⟨r2, m2⟩ := q
    rw [c2] at hW
    simp only [pmE.k_is_str_lit] at hW
    obtain ⟨hrun2, ⟨M2, hS2, -, -⟩, -⟩ := CoreSpec.run
      (isStrLit_refines p hp.isStrLit (N + 1) ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe MM eb major hS hmaj)
      (callW_of_callE c2)
    have hrules2 : decRules (m2.arr64 EREC) ro.toNat rc.toNat = some rules := by
      rw [hE _ _ _ _ _ _ (by simp) (callW_of_callE c2)]; exact hr
    by_cases hs2 : r2.headD 0 ≠ 0
    · rw [ite_eq_left hs2] at hW
      rw [decBool_t_m2c hs2] at hrun2
      exact ErrClaim.of_run_err (fun ce h' => pm_err_nk_str _ _ _ _ _ _ _ hK0 a₀ _ hrun2 ce h')
        (pmTailE p hp hc hw hsup hmtc hE hnv hM N hk hkE F hnF hn62 dn vis fe eb mode d rec ro rc major
          rules hm4 hebm hmaj m2 _ M2 hS2 hrules2 er hW)
    rw [ite_eq_right hs2] at hW
    rw [decBool_f_m2c (Classical.not_not.mp hs2)] at hrun2
    cases c3 : callE p (N + 1) "major_to_ctor" [mode, vis, d, rec, ro, rc, major] m2 with
    | error e3 =>
      rw [c3, pmE.k_major_to_ctor_2.none] at hW; cases hW
      exact ErrClaim.of_run_err (fun ce h' => pm_err_nk_m2c _ _ _ _ _ _ _ hK0 a₀ _ hrun2 ce h')
        (CoreSpecE.of_callE (hM N hk' (hkE.mono (by omega)) F (by omega) ⟨m2, Locals.init []⟩ _ dn vis
          fe M2 eb mode d rec ro rc major rules (by omega) hS2 hm4 hebm hmaj hrules2) c3)
    | ok q =>
    obtain ⟨r3, m3⟩ := q
    rw [c3] at hW
    simp only [pmE.k_major_to_ctor_2] at hW
    obtain ⟨hrun3, ⟨M3, hS3, -, -⟩, hr3⟩ := CoreSpec.run
      (hmtc N hk' F (by omega) ⟨m2, Locals.init []⟩ _ dn vis fe M2 eb mode d rec ro rc major rules
        (by omega) hS2 hm4 hebm hmaj hrules2) (callW_of_callE c3)
    have hrules3 : decRules (m3.arr64 EREC) ro.toNat rc.toNat = some rules := by
      rw [hE _ _ _ _ _ _ (by simp) (callW_of_callE c3)]; exact hrules2
    exact ErrClaim.of_run_err (fun ce h' => pm_err_nk_not _ _ _ _ _ _ _ hK0 a₀ _ _ _ hrun2 hrun3 ce h')
      (pmTailE p hp hc hw hsup hmtc hE hnv hM N hk hkE F hnF hn62 dn vis fe eb mode d rec ro rc
        (r3.headD 0) rules hm4 hebm hr3 m3 _ M3 hS3 hrules3 er hW)

end prep

end L.Arena
