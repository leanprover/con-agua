import ConAgua.Verdict.WhnfModelsE
import ConAgua.Arena.KnotE
import ConAgua.Arena.WhnfCoreLoop
import ConAgua.Arena.WhnfDeltaSlot
import ConAgua.Arena.DefEqKnot
import ConAgua.Checker.NoVerdictClosed

/-!
# The knot's `whnf_core` and `whnf` slots' verdict claims (lane `verdicts-b`, helper `k2`)
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace L.Arena

/-- The twin computations agree on the run from `a`. -/
theorem ErrClaim.of_run_eq' {α : Type} {T T' : AM α} {a a' : AState} {e : Err}
    (h : T.run a = T'.run a') (h' : ErrClaim T' a' e) : ErrClaim T a e := fun hk => by
  obtain ⟨ce, hce, hc⟩ := h' hk
  exact ⟨ce, h ▸ hce, hc⟩

/-- The twin's run from `a` fails where `T'`'s from `a'` does. -/
theorem ErrClaim.of_run_err {α β : Type} {T : AM α} {T' : AM β} {a a' : AState} {e : Err}
    (h : ∀ ce, T'.run a' = .error ce → T.run a = .error ce) (h' : ErrClaim T' a' e) :
    ErrClaim T a e := fun hk => by
  obtain ⟨ce, hce, hc⟩ := h' hk
  exact ⟨ce, h ce hce, hc⟩

/-- A call at fuel `0` claims nothing. -/
theorem ErrClaim.of_callE_zero {α : Type} {T : AM α} {a : AState} {p : Prog} {f : FnName}
    {vs : List Word} {m : Mem} {e : Err} (h : callE p 0 f vs m = .error e) : ErrClaim T a e := by
  obtain ⟨e', he', h0⟩ := callE_zero p f vs m
  rw [h] at he'; cases he'
  exact ErrClaim.of_cls0 h0

/-- The callees of the whnf slots' bodies outside the verdict closure. -/
theorem whnfSlotE_nv : ∀ f ∈ ["inst1", "wk_find", "wk_put", "wc_find", "wc_put", "wh_find",
    "wh_put", "unfold_definition"], f ∈ L.Checker.nvFns := by
  decide +kernel

/-! ## `whnf_core_step` -/

/-- `whnf_core_app`'s error claim (the `app` arm), at fuel `N + 1`. -/
def CoreAppE (p : Prog) : Prop :=
  ∀ N, KnotUpTo p N → KnotUpToE p N → ∀ (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb mode cheap d e : Word), N ≤ F → N ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe MM eb mode → HW e →
    CoreSpecE p (N + 1) "whnf_core_app" [mode, cheap, vis, d, e]
      (whnfCoreAppT (decMode mode) (coreKnot (decMode mode) fe id F) fe (cheap != 0) d.toNat
        (decE e)) s₀ a₀

/-- `whnf_core_step_proj`'s error claim (the `proj` arm), at fuel `N + 1`. -/
def StepProjE (p : Prog) : Prop :=
  ∀ N, KnotUpTo p N → KnotUpToE p N → ∀ (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb mode cheap d e sn i pe : Word), N ≤ F → N ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe MM eb mode →
    HW e → HW sn → HW pe →
    CoreSpecE p (N + 1) "whnf_core_step_proj" [mode, cheap, vis, d, e, sn, i, pe]
      (whnfCoreStepProj (decMode mode) (coreKnot (decMode mode) fe id F) fe (cheap != 0) d.toNat
        (decE e) (decI sn) i.toNat (decE pe)) s₀ a₀

theorem step_run_bvar {mode : ConLeche.CheckMode} {r : CoreFnsA} {fe : IFEnv} {cheap : Bool}
    {depth : Nat} {e : EIdx} {a : AState} (i : Nat) (hv : a.store.view e = some (.bvar i)) :
    (whnfCoreStep mode r fe cheap depth e).run a =
      (ConRon.Arena.fail (.notImplemented "whnf beyond the supported fragment") : AM WhnfStep).run a := by
  simp only [whnfCoreStep, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]; try rfl

section step
variable (p : Prog) (hnv : closedNV p L.Checker.nvFns = true)
  (hfs : p.lookup "whnf_core_step" = some whnfCoreStepL) (hA : CoreAppE p) (hP : StepProjE p)

include hnv hfs hA hP in
/-- **`whnf_core_step`'s verdicts**: a bound variable declines (the twin's `.bvar` arm); the `app`
and `proj` arms' are their callees' (`CoreAppE`, `StepProjE`). -/
theorem whnfCoreStep_refinesE (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) (F : Nat)
    (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb mode cheap d e : Word)
    (hs : SlotPre s₀ a₀ dn vis fe MM eb mode) (he : HW e) :
    CoreSpecE p (n + 1) "whnf_core_step" [mode, cheap, vis, d, e]
      (whnfCoreStep (decMode mode) (coreKnot (decMode mode) fe id F) fe (cheap != 0) d.toNat
        (decE e)) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (whnfCoreStep_specE p hfs (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode cheap vis d e) hc (Err.code_ne_of_cls hk0)
  simp only [whnfCoreStepE] at hW
  have hR := hs.rel.arena.1
  have hh : e.toNat < 2 ^ 32 := he
  by_cases ht : tierW e ≠ 0 ∧ rdW (s₀.mem.arr64 CTL) 1 = 0
  · rw [if_pos ht] at hW; cases hW; exact ErrClaim.of_cls0 rfl
  rw [if_neg ht] at hW
  by_cases g4 : e >>> 28 = 4
  · rw [if_pos g4] at hW
    by_cases hc4 : tcnt s₀.mem APP (tierW e) ≤ idxW e
    · rw [if_pos hc4] at hW; cases hW; exact ErrClaim.of_cls0 rfl
    rw [if_neg hc4] at hW
    cases h1 : callE p n "whnf_core_app" [mode, cheap, vis, d, e] s₀.mem with
    | ok q => rw [h1] at hW; simp [whnfCoreStepE.k_whnf_core_app] at hW
    | error e1 =>
    rw [h1, whnfCoreStepE.k_whnf_core_app.none] at hW; cases hW
    have hv := (view_app s₀.mem a₀ hR e hh ⟨ht, by simpa using hc4⟩ g4).1
    refine ErrClaim.of_run_eq' (step_run_app _ _ hv) ?_
    cases n with
    | zero => exact ErrClaim.of_callE_zero h1
    | succ N =>
    exact CoreSpecE.of_callE (hA N (hk.mono (by omega)) (hkE.mono (by omega)) F s₀ a₀ dn vis fe MM
      eb mode cheap d e (by omega) (by omega) hs he) h1
  rw [if_neg g4] at hW
  by_cases g9 : e >>> 28 = 9
  · rw [if_pos g9] at hW
    by_cases hc9 : tcnt s₀.mem PROJ (tierW e) ≤ idxW e
    · rw [if_pos hc9] at hW; cases hW; exact ErrClaim.of_cls0 rfl
    rw [if_neg hc9] at hW
    cases h1 : callE p n "whnf_core_step_proj" [mode, cheap, vis, d, e,
        tfld s₀.mem PROJ (tierW e) (idxW e) 0, tfld s₀.mem PROJ (tierW e) (idxW e) 1,
        tfld s₀.mem PROJ (tierW e) (idxW e) 2] s₀.mem with
    | ok q => rw [h1] at hW; simp [whnfCoreStepE.k_whnf_core_app] at hW
    | error e1 =>
    rw [h1, whnfCoreStepE.k_whnf_core_app.none] at hW; cases hW
    obtain ⟨hv, hsn, hpe⟩ := view_proj s₀.mem a₀ hR e hh ⟨ht, by simpa using hc9⟩ g9
    refine ErrClaim.of_run_eq' (step_run_proj _ _ _ hv) ?_
    cases n with
    | zero => exact ErrClaim.of_callE_zero h1
    | succ N =>
    exact CoreSpecE.of_callE (hP N (hk.mono (by omega)) (hkE.mono (by omega)) F s₀ a₀ dn vis fe MM
      eb mode cheap d e _ _ _ (by omega) (by omega) hs he hsn hpe) h1
  rw [if_neg g9] at hW
  by_cases g7 : e >>> 28 = 7
  · rw [if_pos g7] at hW
    by_cases hc7 : tcnt s₀.mem LET (tierW e) ≤ idxW e
    · rw [if_pos hc7] at hW; cases hW; exact ErrClaim.of_cls0 rfl
    rw [if_neg hc7] at hW
    cases h1 : callE p n "inst1" [tfld s₀.mem LET (tierW e) (idxW e) 2,
        tfld s₀.mem LET (tierW e) (idxW e) 1, 0] s₀.mem with
    | ok q => rw [h1] at hW; simp [whnfCoreStepE.k_inst1] at hW
    | error e1 =>
    rw [h1, whnfCoreStepE.k_inst1.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfSlotE_nv "inst1" (by simp)) h1
  rw [if_neg g7] at hW
  by_cases g0 : e >>> 28 = 0
  · rw [if_pos g0] at hW
    by_cases hc0 : tcnt s₀.mem BVAR (tierW e) ≤ idxW e
    · rw [if_pos hc0] at hW; cases hW; exact ErrClaim.of_cls0 rfl
    rw [if_neg hc0] at hW
    cases hW
    have hv := view_bvar s₀.mem a₀ hR e hh ⟨ht, by simpa using hc0⟩ g0
    refine ErrClaim.of_run_eq' (step_run_bvar _ hv) ?_
    exact ErrClaim.fail _ _ rfl
  rw [if_neg g0] at hW
  repeat' split at hW
  all_goals (cases hW <;> exact ErrClaim.of_cls0 rfl)

end step

/-! ## `whnf_core_loop` -/

theorem whnfCoreLoop_err (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (c : Bool)
    (d K : Nat) (e : EIdx) (a : AState) (ce : CheckError)
    (hs : (whnfCoreStep mode r fe c d e).run a = .error ce) :
    (whnfCoreLoop mode r fe c d (K + 1) e).run a = .error ce := by
  simp only [whnfCoreLoop, StateT.run_bind, hs]; rfl

section loop
variable (p : Prog) (hp : WhnfCoreProg p) (hwc : WhnfCallees p) (hcc : CoreCallees p)
  (hsup : ∀ fe : IFEnv, SupKeep fe) (hnv : closedNV p L.Checker.nvFns = true)
  (hA : CoreAppE p) (hP : StepProjE p)

include hp hwc hcc hsup hnv hA hP in
/-- **The loop's model fails only where `whnfCoreLoop` does**, at every twin loop fuel `K ≥ k`. -/
theorem coreLoopE_ok (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) (F : Nat) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (mode cheap d : Word) (hmode : mode < 4) :
    ∀ k, k ≤ n + 1 → ∀ K, k ≤ K + 1 → ∀ (m : Mem) (a : AState) (MM : ModeMaps) (eb e : Word),
      CoreS dn m a vis fe MM eb → eb = (mode >>> 1) &&& 1 → HW e →
      ∀ er, whnfCoreLoopE.loop1 p k m mode cheap vis d e = .error er →
      ErrClaim (whnfCoreLoop (decMode mode) (coreKnot (decMode mode) fe id F) fe (cheap != 0)
        d.toNat K (decE e)) a er := by
  intro k
  induction k with
  | zero =>
    intro _ _ _ _ _ _ _ _ _ _ _ er h
    simp only [whnfCoreLoopE.loop1] at h; cases h; exact ErrClaim.of_cls0 rfl
  | succ k ih =>
    intro hkn K hK m a MM eb e hS heb he er h
    simp only [whnfCoreLoopE.loop1, if_pos rfl] at h
    cases hc : callE p k "whnf_core_step" [mode, cheap, vis, d, e] m with
    | error e1 =>
      rw [hc, whnfCoreLoopE.k_whnf_core_step.none] at h; cases h
      cases k with
      | zero => exact ErrClaim.of_callE_zero hc
      | succ j =>
      obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
      refine ErrClaim.of_run_eq (fun ce h' => whnfCoreLoop_err _ _ _ _ _ K' _ a ce h') ?_
      exact CoreSpecE.of_callE (whnfCoreStep_refinesE p hnv hp.step hA hP j (hk.mono (by omega))
        (hkE.mono (by omega)) F (by omega) (by omega) ⟨m, Locals.init []⟩ a dn vis fe MM eb mode
        cheap d e ⟨hS, hmode, heb⟩ he) hc
    | ok q =>
    obtain ⟨r, m₁⟩ := q
    cases k with
    | zero =>
      obtain ⟨e', he', -⟩ := callE_zero p "whnf_core_step" [mode, cheap, vis, d, e] m
      rw [hc] at he'; cases he'
    | succ j =>
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    have hstep := whnfCoreStep_refines' p hp hwc hcc hsup j (hk.mono (by omega)) F (by omega)
      (by omega) ⟨m, Locals.init []⟩ a dn vis fe MM eb mode cheap d e ⟨hS, hmode, heb⟩ he
    obtain ⟨hok, hA', hres, hrw⟩ := CoreSpec.of_callW hstep (callW_of_callE hc)
    have hsr := AM.run_of_ok _ _ hok
    rw [hres] at hsr
    by_cases h0 : r.headD 0 = 0
    · rw [hc, whnfCoreLoopE.k_whnf_core_step.arm1 _ _ _ _ _ _ _ _ h0] at h; cases h
    rw [hc, whnfCoreLoopE.k_whnf_core_step.arm2 _ _ _ _ _ _ _ _ h0] at h
    simp only [decStep, h0, ↓reduceIte] at hsr
    have hrun := whnfCoreLoop_cont (decMode mode) (coreKnot (decMode mode) fe id F) fe
      (cheap != 0) d.toNat K' (decE e) _ a _ hsr
    obtain ⟨M', hS₁, -, -⟩ := hA'
    exact ErrClaim.of_run_eq' hrun (ih (by omega) K' (by omega) m₁ _ M' eb _ hS₁ heb hrw.2 er h)

include hp hwc hcc hsup hnv hA hP in
/-- **`whnf_core_loop`'s verdicts are `whnfCoreLoop`'s** at every twin loop fuel `K ≥ n`. -/
theorem whnfCoreLoop_refinesE (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) (F K : Nat)
    (hF : n ≤ F) (hK : n ≤ K) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb mode cheap d e : Word) (hs : SlotPre s₀ a₀ dn vis fe MM eb mode) (he : HW e) :
    CoreSpecE p (n + 1) "whnf_core_loop" [mode, cheap, vis, d, e]
      (whnfCoreLoop (decMode mode) (coreKnot (decMode mode) fe id F) fe (cheap != 0) d.toNat K
        (decE e)) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (whnfCoreLoop_specE p hp.loop (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode cheap vis d e) hc (Err.code_ne_of_cls hk0)
  rw [whnfCoreLoopE.arm1] at hW
  exact coreLoopE_ok p hp hwc hcc hsup hnv hA hP n hk hkE F hF hn dn vis fe mode cheap d hs.mode4
    (n + 1) (Nat.le_refl _) K (by omega) s₀.mem a₀ MM eb e hs.rel hs.eb_mode he er hW

end loop

/-! ## The `whnf_core` slot -/

section twin
variable (mode : ConLeche.CheckMode) (fe : IFEnv) (F : Nat) (d : Nat) (e : EIdx) (a : AState)

theorem knot_whnfCore_missK_err (h : whnfCoreStuckTag e = false)
    (hm : a.caches.whnfCoreCheapC[e]? = none) (ce : CheckError)
    (hb : (whnfCoreBody mode (coreKnot mode fe id F) fe true d e).run a = .error ce) :
    ((coreKnot mode fe id (F + 1)).whnfCore true d e).run a = .error ce := by
  simp [coreKnot, h, hm, StateT.run_bind, hb]; try rfl

theorem knot_whnfCore_missF_err (h : whnfCoreStuckTag e = false)
    (hm : a.caches.whnfCoreC[e]? = none) (ce : CheckError)
    (hb : (whnfCoreBody mode (coreKnot mode fe id F) fe false d e).run a = .error ce) :
    ((coreKnot mode fe id (F + 1)).whnfCore false d e).run a = .error ce := by
  simp [coreKnot, h, hm, StateT.run_bind, hb]; try rfl

end twin

theorem k_wk_put_err {p : Prog} {x : Word} {c : Except Err (List Word × Mem)} {er : Err}
    (h : whnfCoreE.k_wk_put p x c = .error er) : c = .error er := by
  cases c with
  | error => simpa [whnfCoreE.k_wk_put] using h
  | ok q => simp [whnfCoreE.k_wk_put] at h

section slot
variable (p : Prog) (hp : WhnfCoreProg p) (hwc : WhnfCallees p) (hcc : CoreCallees p)
  (hsup : ∀ fe : IFEnv, SupKeep fe) (hnv : closedNV p L.Checker.nvFns = true)
  (hA : CoreAppE p) (hP : StepProjE p)

include hp hwc hcc hsup hnv hA hP in
/-- **The knot's `whnfCore` slot's verdicts, one level up**: a failing `whnf_core` at `n + 1`
claims the slot's failure (the body's, on a memo miss). -/
theorem whnfCoreSlot_stepE (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) :
    WhnfCoreSlotE p (n + 1) := by
  intro F s₀ a₀ dn vis fe MM eb mode cheap d e hF hn hs he
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  refine CoreSpecE.of_runs fun er hc => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (whnfCore_specE p hp.core (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode cheap vis d e) hc (Err.code_ne_of_cls hk0)
  simp only [whnfCoreE] at hW
  have hS := hs.rel
  have heb := hS.core.eb1
  have hkey : ((mode >>> 1) &&& 1) <<< 32 = genW 0 eb := ebKey_eq mode eb hs.eb_mode
  by_cases hst : e >>> 28 ≠ 4 ∧ e >>> 28 ≠ 9 ∧ e >>> 28 ≠ 7 ∧ e >>> 28 ≠ 0
  · rw [if_pos hst] at hW; cases hW
  rw [if_neg hst] at hW
  have ht : whnfCoreStuckTag (decE e) = false := by rw [stuck_iff e he]; simpa using hst
  -- the body's claim at fuel `n`
  have body : ∀ (c : Word) (er' : Err),
      callE p n "whnf_core_loop" [mode, c, vis, d, e] s₀.mem = .error er' →
      ErrClaim (whnfCoreBody (decMode mode) (coreKnot (decMode mode) fe id F') fe (c != 0) d.toNat
        (decE e)) a₀ er' := by
    intro c er' h2
    cases n with
    | zero => exact ErrClaim.of_callE_zero h2
    | succ n' =>
    exact CoreSpecE.of_callE (whnfCoreLoop_refinesE p hp hwc hcc hsup hnv hA hP n'
      (hk.mono (by omega)) (hkE.mono (by omega)) F' whnfCoreLoopFuel (by omega)
      (by simp only [whnfCoreLoopFuel]; omega) (by omega) s₀ a₀ dn vis fe MM eb mode c d e hs he) h2
  by_cases hc : cheap ≠ 0
  · rw [if_pos hc] at hW
    have hcb : (cheap != 0) = true := by simpa using hc
    rw [hcb]
    cases h1 : callE p n "wk_find" [e, ((mode >>> 1) &&& 1) <<< 32] s₀.mem with
    | error e1 =>
      rw [h1, whnfCoreE.k_wk_find.none] at hW; cases hW
      exact ErrClaim.of_callE_nv hnv (whnfSlotE_nv "wk_find" (by simp)) h1
    | ok q =>
    obtain ⟨r₁, m₁⟩ := q
    obtain ⟨s', hs', rfl, hne, hr⟩ := triple_of_callE
      (memoFindG_spec wkSch p _ hp.wkf n ⟨s₀.mem, Locals.init []⟩ e _) h1
    subst hs'
    by_cases h1' : r₁.headD 0 ≠ 0
    · rw [h1, whnfCoreE.k_wk_find.arm1 _ _ _ _ _ _ _ _ h1'] at hW; cases hW
    have h1'' : r₁.headD 0 = 0 := by simpa using h1'
    rw [h1, whnfCoreE.k_wk_find.arm2 _ _ _ _ _ _ _ _ h1''] at hW
    rw [hkey] at hr
    have hmiss := (hS.core.wk.findE heb e he (hr ▸ hne)).2 (hr ▸ h1'')
    cases h2 : callE p n "whnf_core_loop" [mode, 1, vis, d, e] s₀.mem with
    | error e2 =>
      rw [h2, whnfCoreE.k_whnf_core_loop.none] at hW; cases hW
      exact ErrClaim.of_run_eq (fun ce h' => knot_whnfCore_missK_err _ fe F' d.toNat _ a₀ ht hmiss ce h')
        (body 1 _ h2)
    | ok q =>
    obtain ⟨r₂, m₂⟩ := q
    rw [h2] at hW
    simp only [whnfCoreE.k_whnf_core_loop] at hW
    cases h3 : callE p n "wk_find" [e, ((mode >>> 1) &&& 1) <<< 32] m₂ with
    | error e3 =>
      rw [h3, whnfCoreE.k_wk_find_2.none] at hW; cases hW
      exact ErrClaim.of_callE_nv hnv (whnfSlotE_nv "wk_find" (by simp)) h3
    | ok q =>
    rw [h3] at hW
    simp only [whnfCoreE.k_wk_find_2] at hW
    exact ErrClaim.of_callE_nv hnv (whnfSlotE_nv "wk_put" (by simp)) (k_wk_put_err hW)
  · rw [if_neg hc] at hW
    have hcb : (cheap != 0) = false := by simpa using hc
    rw [hcb]
    cases h1 : callE p n "wc_find" [e, ((mode >>> 1) &&& 1) <<< 32] s₀.mem with
    | error e1 =>
      rw [h1, whnfCoreE.k_wc_find.none] at hW; cases hW
      exact ErrClaim.of_callE_nv hnv (whnfSlotE_nv "wc_find" (by simp)) h1
    | ok q =>
    obtain ⟨r₁, m₁⟩ := q
    obtain ⟨s', hs', rfl, hne, hr⟩ := triple_of_callE
      (memoFindG_spec wcSch p _ hp.wcf n ⟨s₀.mem, Locals.init []⟩ e _) h1
    subst hs'
    by_cases h1' : r₁.headD 0 ≠ 0
    · rw [h1, whnfCoreE.k_wc_find.arm1 _ _ _ _ _ _ _ _ h1'] at hW; cases hW
    have h1'' : r₁.headD 0 = 0 := by simpa using h1'
    rw [h1, whnfCoreE.k_wc_find.arm2 _ _ _ _ _ _ _ _ h1''] at hW
    rw [hkey] at hr
    have hmiss := (hS.core.wc.findE heb e he (hr ▸ hne)).2 (hr ▸ h1'')
    cases h2 : callE p n "whnf_core_loop" [mode, 0, vis, d, e] s₀.mem with
    | error e2 =>
      rw [h2, whnfCoreE.k_whnf_core_loop_2.none] at hW; cases hW
      exact ErrClaim.of_run_eq (fun ce h' => knot_whnfCore_missF_err _ fe F' d.toNat _ a₀ ht hmiss ce h')
        (body 0 _ h2)
    | ok q =>
    obtain ⟨r₂, m₂⟩ := q
    rw [h2] at hW
    simp only [whnfCoreE.k_whnf_core_loop_2] at hW
    cases h3 : callE p n "wc_find" [e, ((mode >>> 1) &&& 1) <<< 32] m₂ with
    | error e3 =>
      rw [h3, whnfCoreE.k_wc_find_2.none] at hW; cases hW
      exact ErrClaim.of_callE_nv hnv (whnfSlotE_nv "wc_find" (by simp)) h3
    | ok q =>
    rw [h3] at hW
    simp only [whnfCoreE.k_wc_find_2] at hW
    exact ErrClaim.of_callE_nv hnv (whnfSlotE_nv "wc_put" (by simp)) (k_wk_put_err hW)

end slot

/-! ## `whnf_step` -/

/-- `reduce_nat`'s error claim, at fuel `N + 1`. -/
def ReduceNatE (p : Prog) : Prop :=
  ∀ N, KnotUpTo p N → KnotUpToE p N → ∀ (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb mode d e : Word), N ≤ F → N ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe MM eb mode → HW e →
    CoreSpecE p (N + 1) "reduce_nat" [mode, vis, d, e]
      (reduceNat (coreKnot (decMode mode) fe id F) fe d.toNat (decE e)) s₀ a₀

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
    cases n with
    | zero => exact ErrClaim.of_callE_zero h2
    | succ N =>
    exact ErrClaim.of_run_err (fun ce h' => whnfStep_err2 _ _ _ _ _ _ _ ce hrun1 h')
      (CoreSpecE.of_callE (hR N (hk.mono (by omega)) (hkE.mono (by omega)) F ⟨m₁, Locals.init []⟩
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
    simp only [whnfLoopE.loop1, if_pos rfl] at h
    cases hc : callE p k "whnf_step" [mode, vis, d, e] m with
    | error e1 =>
      rw [hc, whnfLoopE.k_whnf_step.none] at h; cases h
      cases k with
      | zero => exact ErrClaim.of_callE_zero hc
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
    exact ErrClaim.of_run_eq' hrun (ih (by omega) K' (by omega) m₁ _ M' eb _ hS₁ heb hrw.2 er h)

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
  · rw [if_pos hst] at hW; cases hW
  rw [if_neg hst] at hW
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
    | zero => exact ErrClaim.of_callE_zero h2
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
bodies' callees `whnf_core_app`, `whnf_core_step_proj`, `reduce_nat`. -/
theorem whnfSlotsE_step {p : Prog} (hq : KnotAllProg p) (hnv : closedNV p L.Checker.nvFns = true)
    (hA : CoreAppE p) (hP : StepProjE p) (hR : ReduceNatE p) (n : Nat) (hk : KnotUpTo p n)
    (hkE : KnotUpToE p n) : WhnfCoreSlotE p (n + 1) ∧ WhnfSlotE p (n + 1) :=
  ⟨whnfCoreSlot_stepE p hq.core (KnotAllProg.whnfC hq) (KnotAllProg.coreC hq) supKeep_of hnv hA hP n
      hk hkE,
    whnfSlot_stepE p hq.delta (KnotAllProg.instLP hq) hnv hR n hk hkE⟩

end L.Arena
