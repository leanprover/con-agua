import ConAgua.Arena.DefEqKnot

/-!
# The knot's `whnf_core` and `whnf` slots' verdict claims (lane `verdicts-b`, helper `k2`)
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

/-- A continuation that passes errors on and fails nowhere else: its error is its argument's. -/
theorem err_of_k {β γ : Type} {k : Except Err β → Except Err γ}
    (hk : ∀ q e, k (.ok q) ≠ .error e) (hn : ∀ e, k (.error e) = .error e) {c : Except Err β}
    {er : Err} (h : k c = .error er) : c = .error er := by
  cases c with
  | error e => rw [hn] at h; cases h; rfl
  | ok q => exact absurd h (hk q er)

/-- A call at fuel `0` claims nothing. -/
theorem ErrClaim.of_callE_zeroW {α : Type} {T : AM α} {a : AState} {p : Prog} {f : FnName}
    {vs : List Word} {m : Mem} {e : Err} (h : callE p 0 f vs m = .error e) : ErrClaim T a e := by
  obtain ⟨e', he', h0⟩ := callE_zero p f vs m
  rw [h] at he'; cases he'
  exact ErrClaim.of_cls0 h0

/-- The callees of the whnf slots' bodies outside the verdict closure. -/
theorem whnfSlotE_nv : ∀ f ∈ ["wh_find", "wh_put", "unfold_definition"], f ∈ L.Checker.nvFns :=
  _root_.L.Checker.nv_sub (by decide +kernel)

/-! ## `whnf_core`: the step's and the slot's claims from their refinements -/

section core
variable (p : Prog) (hp : WhnfCoreProg p) (hwc : WhnfCallees p) (hcc : CoreCallees p)
  (hsup : ∀ fe : IFEnv, SupKeep fe) (hnv : closedNV p L.Checker.nvFns = true) (hI : IotaRecAtE p)

include hp hwc hcc hsup hnv hI in
/-- **`whnf_core_step`'s claim at every L fuel up to `n`** (`step_ref`'s error half). -/
theorem coreStepE_of (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) : CoreStepE p n :=
  fun j hj F hF hn s₀ a₀ dn vis fe MM eb mode cheap d e hs he =>
    RefE.coreSpecE (whnfCoreStepE_spec p hp (j + 1) s₀ mode cheap vis d e) hnv ⟨hkE.mono hj, hI⟩
      (step_ref p hp hwc hcc hsup j (hk.mono hj) F hF hn s₀ a₀ dn vis fe MM eb mode cheap d e hs he)

include hp hwc hcc hsup hnv hI in
/-- **The knot's `whnfCore` slot's verdicts, one level up** (`core_ref`'s error half). -/
theorem whnfCoreSlot_stepE (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) :
    WhnfCoreSlotE p (n + 1) :=
  fun F s₀ a₀ dn vis fe MM eb mode cheap d e hF hn hs he =>
    RefE.coreSpecE (whnfCoreE_spec p hp.core (n + 1) s₀ mode cheap vis d e) hnv
      (coreStepE_of p hp hwc hcc hsup hnv hI n hk hkE)
      (core_ref p hp hwc hcc hsup n hk F s₀ a₀ dn vis fe MM eb mode cheap d e hF hn hs he)

end core

/-! ## `whnf_step` -/

theorem whnfStep_err1 (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (e : EIdx) (a : AState)
    (ce : CheckError) (hw : (r.whnfCore false depth e).run a = .error ce) :
    (whnfStep r fe depth e).run a = .error ce := by
  simp only [whnfStep, StateT.run_bind, hw]; rfl

theorem whnfStep_err2 (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (e e₁ : EIdx) (a a₁ : AState)
    (ce : CheckError) (hw : (r.whnfCore false depth e).run a = .ok (e₁, a₁))
    (hr : (reduceNat r fe depth e₁).run a₁ = .error ce) :
    (whnfStep r fe depth e).run a = .error ce := by
  simp only [whnfStep, StateT.run_bind, hw, except_ok_bind, hr]; rfl

section wstep
variable (p : Prog) (hdp : WhnfDeltaProg' p) (hnv : closedNV p L.Checker.nvFns = true)
  (hR : ReduceNatE p)

include hdp hnv hR in
/-- **`whnf_step`'s verdicts**: `whnf_core`'s (the knot's slot) and `reduce_nat`'s (`ReduceNatE`);
`unfold_definition` claims nothing. -/
theorem whnfStep_refinesE (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) (F : Nat)
    (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb mode d e : Word)
    (hs : SlotPre s₀ a₀ dn vis fe MM eb mode) (he : HW e) :
    CoreSpecE p (n + 1) "whnf_step" [mode, vis, d, e]
      (whnfStep (coreKnot (decMode mode) fe id F) fe d.toNat (decE e)) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (whnfStep_specE p hdp.whnfStep (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d e) hc (Err.code_ne_of_cls hk0)
  rw [whnfStepE.arm1] at hW
  have hb0 : ((0 : Word) != 0) = false := rfl
  cases h1 : callE p n "whnf_core" [mode, 0, vis, d, e] s₀.mem with
  | error e1 =>
    rw [h1, whnfStepE.k_whnf_core.none] at hW; cases hW
    have hc1 := CoreSpecE.of_callE ((hkE n (Nat.le_refl _)).whnfCore F s₀ a₀ dn vis fe MM eb mode 0
      d e hF hn hs he) h1
    rw [hb0] at hc1
    exact ErrClaim.of_run_eq (fun ce h' => whnfStep_err1 _ _ _ _ _ ce h') hc1
  | ok q₁ =>
  obtain ⟨r₁, m₁⟩ := q₁
  rw [h1] at hW
  simp only [whnfStepE.k_whnf_core] at hW
  obtain ⟨hok1, ⟨M₁, hS₁, -, -⟩, hres1, hrw1⟩ := CoreSpec.of_callW
    ((hk n (Nat.le_refl _)).whnfCore F s₀ a₀ dn vis fe MM eb mode 0 d e hF hn hs he)
    (callW_of_callE h1)
  rw [hb0] at hok1 hS₁ hres1
  have hrun1 := AM.run_of_ok _ _ hok1
  rw [hres1] at hrun1
  generalize AM.st ((coreKnot (decMode mode) fe id F).whnfCore false d.toNat (decE e)) a₀ = a₁
    at hrun1 hS₁
  have hSP1 : SlotPre ⟨m₁, Locals.init []⟩ a₁ dn vis fe M₁ eb mode := ⟨hS₁, hs.mode4, hs.eb_mode⟩
  cases h2 : callE p n "reduce_nat" [mode, vis, d, r₁.headD 0] m₁ with
  | error e2 =>
    rw [h2, whnfStepE.k_reduce_nat.none] at hW; cases hW
    exact ErrClaim.of_run_err (fun ce h' => whnfStep_err2 _ _ _ _ _ _ _ ce hrun1 h')
      (CoreSpecE.of_callE (hR n hk hkE F ⟨m₁, Locals.init []⟩
        a₁ dn vis fe M₁ eb mode d (r₁.headD 0) (by omega) (by omega) hSP1 hrw1) h2)
  | ok q₂ =>
  obtain ⟨r₂, m₂⟩ := q₂
  rw [h2] at hW
  simp only [whnfStepE.k_reduce_nat] at hW
  split at hW
  · cases hW
  cases h3 : callE p n "unfold_definition" [vis, r₁.headD 0] m₂ with
  | error e3 =>
    exact ErrClaim.of_callE_nv hnv (whnfSlotE_nv "unfold_definition" (by simp))
      (by rw [h3, whnfStepE.k_unfold_definition.none] at hW; cases hW; exact h3)
  | ok q₃ =>
    rw [h3] at hW
    simp only [whnfStepE.k_unfold_definition] at hW
    split at hW <;> cases hW

end wstep

/-! ## `whnf_loop` -/

theorem whnfLoop_err (r : CoreFnsA) (fe : IFEnv) (d K : Nat) (e : EIdx) (a : AState)
    (ce : CheckError) (hs : (whnfStep r fe d e).run a = .error ce) :
    (whnfLoop r fe d (K + 1) e).run a = .error ce := by
  simp only [whnfLoop, StateT.run_bind, hs]; rfl

section wloop
variable (p : Prog) (hdp : WhnfDeltaProg' p) (hlp : InstLPOK p)
  (hnv : closedNV p L.Checker.nvFns = true) (hR : ReduceNatE p)

include hdp hlp hnv hR in
/-- **The loop's model fails only where `whnfLoop` does**, at every twin loop fuel `K ≥ k`. -/
theorem whnfLoopE_ok (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) (F : Nat) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (mode d : Word) (hmode : mode < 4) :
    ∀ k, k ≤ n + 1 → ∀ K, k ≤ K → ∀ (m : Mem) (a : AState) (MM : ModeMaps) (eb e : Word),
      CoreS dn m a vis fe MM eb → eb = (mode >>> 1) &&& 1 → HW e →
      ∀ er, whnfLoopE.loop1 p k m mode vis d e = .error er →
      ErrClaim (whnfLoop (coreKnot (decMode mode) fe id F) fe d.toNat K (decE e)) a er := by
  intro k
  induction k with
  | zero =>
    intro _ _ _ _ _ _ _ _ _ _ _ er h
    simp only [whnfLoopE.loop1] at h; cases h; exact ErrClaim.of_cls0 rfl
  | succ k ih =>
    intro hkn K hK m a MM eb e hS heb he er h
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    simp only [whnfLoopE.loop1] at h
    cases hc : callE p k "whnf_step" [mode, vis, d, e] m with
    | error e1 =>
      rw [hc, whnfLoopE.k_whnf_step.none] at h; cases h
      cases k with
      | zero => exact ErrClaim.of_callE_zeroW hc
      | succ j =>
      refine ErrClaim.of_run_eq (fun ce h' => whnfLoop_err _ _ _ K' _ a ce h') ?_
      exact CoreSpecE.of_callE (whnfStep_refinesE p hdp hnv hR j (hk.mono (by omega))
        (hkE.mono (by omega)) F (by omega) (by omega) ⟨m, Locals.init []⟩ a dn vis fe MM eb mode
        d e ⟨hS, hmode, heb⟩ he) hc
    | ok q =>
    obtain ⟨r, m₁⟩ := q
    have hstep := whnfStep_refines' p hdp hlp k (fun k' _ => reduceNat_refines p hdp k') F
      ⟨m, Locals.init []⟩ a dn vis fe MM eb mode d e (by omega) (by omega) ⟨hS, hmode, heb⟩ he
      (hk.mono (by omega))
    obtain ⟨hok, hA', hres, hrw⟩ := CoreSpec.of_callW hstep (callW_of_callE hc)
    have hsr := AM.run_of_ok _ _ hok
    rw [hres] at hsr
    by_cases h0 : r.headD 0 = 0
    · rw [hc, whnfLoopE.k_whnf_step.arm1 _ _ _ _ _ _ _ h0] at h; cases h
    rw [hc, whnfLoopE.k_whnf_step.arm2 _ _ _ _ _ _ _ h0] at h
    simp only [decStep, h0, ↓reduceIte] at hsr
    have hrun := whnfLoop_cont (coreKnot (decMode mode) fe id F) fe d.toNat K' (decE e) _ a _ hsr
    obtain ⟨M', hS₁, -, -⟩ := hA'
    exact ErrClaim.of_run_eqW hrun (ih (by omega) K' (by omega) m₁ _ M' eb _ hS₁ heb hrw.2 er h)

include hdp hlp hnv hR in
/-- **`whnf_loop`'s verdicts are `whnfLoop`'s** at every twin loop fuel `K ≥ n + 1`. -/
theorem whnfLoop_refinesE (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) (F K : Nat)
    (hF : n ≤ F) (hK : n + 1 ≤ K) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb mode d e : Word) (hs : SlotPre s₀ a₀ dn vis fe MM eb mode) (he : HW e) :
    CoreSpecE p (n + 1) "whnf_loop" [mode, vis, d, e]
      (whnfLoop (coreKnot (decMode mode) fe id F) fe d.toNat K (decE e)) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (whnfLoop_specE p hdp.whnfLoop (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d e) hc (Err.code_ne_of_cls hk0)
  rw [whnfLoopE.arm1] at hW
  exact whnfLoopE_ok p hdp hlp hnv hR n hk hkE F hF hn dn vis fe mode d hs.mode4
    (n + 1) (Nat.le_refl _) K hK s₀.mem a₀ MM eb e hs.rel hs.eb_mode he er hW

end wloop

/-! ## The `whnf` slot -/

theorem knot_whnf_miss_err (mode : ConLeche.CheckMode) (fe : IFEnv) (F : Nat) (d : Nat) (e : EIdx)
    (a : AState) (h : whnfStuckTag e = false) (hm : a.caches.whnfC[e]? = none) (ce : CheckError)
    (hb : (whnfBody (coreKnot mode fe id F) fe d e).run a = .error ce) :
    ((coreKnot mode fe id (F + 1)).whnf d e).run a = .error ce := by
  simp [coreKnot, h, hm, StateT.run_bind, hb]; try rfl

theorem k_wh_put_err {p : Prog} {x : Word} {c : Except Err (List Word × Mem)} {er : Err}
    (h : whnfE.k_wh_put p x c = .error er) : c = .error er := by
  cases c with
  | error => simpa [whnfE.k_wh_put] using h
  | ok q => simp [whnfE.k_wh_put] at h

section wslot
variable (p : Prog) (hdp : WhnfDeltaProg' p) (hlp : InstLPOK p)
  (hnv : closedNV p L.Checker.nvFns = true) (hR : ReduceNatE p)

include hdp hlp hnv hR in
/-- **The knot's `whnf` slot's verdicts, one level up**: a failing `whnf` at `n + 1` claims the
slot's failure (the body's, on a memo miss). -/
theorem whnfSlot_stepE (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) :
    WhnfSlotE p (n + 1) := by
  intro F s₀ a₀ dn vis fe MM eb mode d e hF hn hs he
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  refine CoreSpecE.of_runs fun er hc => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (whnf_specE p hdp.whnf (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d e) hc (Err.code_ne_of_cls hk0)
  simp only [whnfE] at hW
  have hS := hs.rel
  have heb := hS.core.eb1
  have hkey : ((mode >>> 1) &&& 1) <<< 32 = genW 0 eb := ebKey_eq mode eb hs.eb_mode
  by_cases hst : e >>> 28 = 2 ∨ e >>> 28 = 1 ∨ e >>> 28 = 5 ∨ e >>> 28 = 6 ∨ e >>> 28 = 8
  · rw [ite_eq_left hst] at hW; cases hW
  rw [ite_eq_right hst] at hW
  have ht : whnfStuckTag (decE e) = false := by rw [whnfStuck_iff e he]; simpa using hst
  cases h1 : callE p n "wh_find" [e, ((mode >>> 1) &&& 1) <<< 32] s₀.mem with
  | error e1 =>
    rw [h1, whnfE.k_wh_find.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfSlotE_nv "wh_find" (by simp)) h1
  | ok q =>
  obtain ⟨r₁, m₁⟩ := q
  obtain ⟨s', hs', rfl, hne, hr⟩ := triple_of_callE
    (memoFindG_spec whSch p _ hdp.whFind n ⟨s₀.mem, Locals.init []⟩ e _) h1
  subst hs'
  by_cases h1' : r₁.headD 0 ≠ 0
  · rw [h1, whnfE.k_wh_find.arm1 _ _ _ _ _ _ _ _ h1'] at hW; cases hW
  have h1'' : r₁.headD 0 = 0 := by simpa using h1'
  rw [h1, whnfE.k_wh_find.arm2 _ _ _ _ _ _ _ _ h1''] at hW
  rw [hkey] at hr
  have hmiss := (hS.core.wh.findE heb e he (hr ▸ hne)).2 (hr ▸ h1'')
  cases h2 : callE p n "whnf_loop" [mode, vis, d, e] s₀.mem with
  | error e2 =>
    rw [h2, whnfE.k_whnf_loop.none] at hW; cases hW
    refine ErrClaim.of_run_eq (fun ce h' => knot_whnf_miss_err _ fe F' d.toNat _ a₀ ht hmiss ce h') ?_
    cases n with
    | zero => exact ErrClaim.of_callE_zeroW h2
    | succ n' =>
    exact CoreSpecE.of_callE (whnfLoop_refinesE p hdp hlp hnv hR n' (hk.mono (by omega))
      (hkE.mono (by omega)) F' whnfLoopFuel (by omega) (by simp only [whnfLoopFuel]; omega)
      (by omega) s₀ a₀ dn vis fe MM eb mode d e hs he) h2
  | ok q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [h2] at hW
  simp only [whnfE.k_whnf_loop] at hW
  cases h3 : callE p n "wh_find" [e, ((mode >>> 1) &&& 1) <<< 32] m₂ with
  | error e3 =>
    rw [h3, whnfE.k_wh_find_2.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfSlotE_nv "wh_find" (by simp)) h3
  | ok q =>
  rw [h3] at hW
  simp only [whnfE.k_wh_find_2] at hW
  exact ErrClaim.of_callE_nv hnv (whnfSlotE_nv "wh_put" (by simp)) (k_wh_put_err hW)

end wslot

/-! ## The two slots' steps -/

/-- **The `whnf_core` and `whnf` slots' error halves, one level up** (the knot's `whnf` family's
part of `KnotStepE`), under the ok knot's program hypotheses and the error claims of the slot
bodies' callees `iota_rec_at`, `reduce_nat`. -/
theorem whnfSlotsE_step {p : Prog} (hq : KnotAllProg p) (hnv : closedNV p L.Checker.nvFns = true)
    (hI : IotaRecAtE p) (hR : ReduceNatE p) (n : Nat) (hk : KnotUpTo p n)
    (hkE : KnotUpToE p n) : WhnfCoreSlotE p (n + 1) ∧ WhnfSlotE p (n + 1) :=
  ⟨whnfCoreSlot_stepE p hq.core (KnotAllProg.whnfC hq) (KnotAllProg.coreC hq) supKeep_of hnv hI n
      hk hkE,
    whnfSlot_stepE p hq.delta (KnotAllProg.instLP hq) hnv hR n hk hkE⟩

end L.Arena
