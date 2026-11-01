module

public import ConAgua.Arena.WhnfCoreStep
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop
public import Std.WP.Tactic
import ConAgua.Arena.WhnfCoreProj
import ConAgua.Arena.WhnfCoreSlot
import ConAgua.L.ModelGen
public import ConAgua.Verdict.WhnfModelsE
import ConAgua.Arena.RefWalk
import ConAgua.Front.Preserve
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# The `whnf_core` loop and slot (phase 5, lane `whnf`)

The loop's unified model `whnfCoreLoopE` refines `whnfCoreLoop`, both outcomes, iteration by
iteration through `whnf_core_step`'s (`step_ref`, both outcomes, over its unified model); the body
is the loop at `whnfCoreLoopFuel`, and the slot one level up (`core_ref`, both outcomes) is the memo
around the body.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## The dispatcher refines `whnfCoreStep` -/

/-- The views `whnfCoreStep` returns as they are. -/
def isDoneV : ENodeView → Bool
  | .sort _ | .fvar _ _ | .forallE _ _ | .lam _ _ | .const _ _ | .lit _ => true
  | _ => false

section stepRuns
variable {mode : ConLeche.CheckMode} {r : CoreFnsA} {fe : IFEnv} {cheap : Bool} {depth : Nat}
  {e : EIdx} {a : AState}

theorem step_run_done (v : ENodeView) (hv : a.store.view e = some v) (hd : isDoneV v = true) :
    (whnfCoreStep mode r fe cheap depth e).run a = .ok (.done e, a) := by
  simp only [whnfCoreStep, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]
  cases v <;> simp [isDoneV] at hd <;> rfl

theorem step_run_app (f x : EIdx) (hv : a.store.view e = some (.app f x)) :
    (whnfCoreStep mode r fe cheap depth e).run a = (whnfCoreAppT mode r fe cheap depth e).run a := by
  simp only [whnfCoreStep, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]; try rfl

theorem step_run_proj (sn : NIdx) (i : Nat) (pe : EIdx) (hv : a.store.view e = some (.proj sn i pe)) :
    (whnfCoreStep mode r fe cheap depth e).run a =
      (whnfCoreStepProj mode r fe cheap depth e sn i pe).run a := by
  simp only [whnfCoreStep, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]; try rfl

theorem step_run_let (t v b : EIdx) (hv : a.store.view e = some (.letE t v b)) :
    (whnfCoreStep mode r fe cheap depth e).run a =
      (do let e' ← instantiate1Fast coreWalkFuel b v 0; pure (WhnfStep.cont e') : AM WhnfStep).run a := by
  simp only [whnfCoreStep, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]; try rfl

theorem step_run_bvar (i : Nat) (hv : a.store.view e = some (.bvar i)) :
    (whnfCoreStep mode r fe cheap depth e).run a =
      (ConRon.Arena.fail (.notImplemented "whnf beyond the supported fragment") : AM WhnfStep).run a := by
  simp only [whnfCoreStep, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]; try rfl

end stepRuns

section step
variable (p : Prog) (hp : WhnfCoreProg p) (hwc : WhnfCallees p) (hcc : CoreCallees p)
  (hsup : ∀ fe : IFEnv, SupKeep fe)

include hp hwc hcc hsup in
/-- **`whnf_core_step` refines `whnfCoreStep`, both outcomes**: a bound variable declines (the
twin's `.bvar` arm); the `app` and `proj` arms' errors are `whnf_core_app`'s and
`whnf_core_step_proj`'s (`AppG`). -/
theorem step_ref (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode cheap d e : Word) (hs : SlotPre s₀ a₀ dn vis fe MM eb mode)
    (he : HW e) :
    RefE (AppG p n) (whnfCoreStepE p (n + 1) s₀.mem mode cheap vis d e)
      (whnfCoreStep (decMode mode) (coreKnot (decMode mode) fe id F) fe (cheap != 0) d.toNat
        (decE e)) a₀ (CorePost decStep dn s₀.mem vis fe MM eb ResW) := by
  have hS := hs.rel
  have hR := hS.arena.base
  have hh : e.toNat < 2 ^ 32 := he
  simp only [whnfCoreStepE]
  refine RefE.abort0 (by decide) fun ht => ?_
  -- a stuck arm answers `(0, e)` after its view check
  have done : ∀ v : ENodeView, a₀.store.view (decE e) = some v → isDoneV v = true →
      RefE (AppG p n) (.ok ([0, e], s₀.mem))
        (whnfCoreStep (decMode mode) (coreKnot (decMode mode) fe id F) fe (cheap != 0) d.toNat
          (decE e)) a₀ (CorePost decStep dn s₀.mem vis fe MM eb ResW) := fun v hv hd =>
    RefE.ret (step_run_done v hv hd) (CorePost.ret hS (by simp [decStep])
      ⟨by show HW (0 : Word); unfold HW; decide, he⟩)
  have vok : ∀ c : TRec, ¬ tcnt s₀.mem c (tierW e) ≤ idxW e → viewOK s₀.mem e c :=
    fun c hc => ⟨ht, by simpa using hc⟩
  by_cases g4 : tagW e = 4
  · rw [ite_eq_left g4]
    refine RefE.abort0 (by decide) fun hc4 => ?_
    refine RefE.of_run_eq (step_run_app _ _ (view_app s₀.mem a₀ hR e hh ⟨ht, by simpa using hc4⟩ g4).1) ?_
    cases n with
    | zero => exact RefE.of_cls0 rfl
    | succ N =>
    have h1 := capp_ref p hp hwc hcc N (hk.mono (by omega)) F (by omega) (by omega) s₀ a₀ dn vis fe MM
      eb mode cheap d e hs he
    exact RefE.lastE (K := whnfCoreStepE.k_whnf_core_app p) (fun _ => rfl) (fun _ => rfl)
      (·.mono (Nat.le_succ N)) h1
      fun _ _ _ _ h => ⟨h.after, h.res, h.valid⟩
  rw [ite_eq_right g4]
  by_cases g9 : tagW e = 9
  · rw [ite_eq_left g9]
    refine RefE.abort0 (by decide) fun hc9 => ?_
    obtain ⟨hv, hsn, hpe⟩ := view_proj s₀.mem a₀ hR e hh (vok _ hc9) g9
    refine RefE.of_run_eq (step_run_proj _ _ _ hv) ?_
    cases n with
    | zero => exact RefE.of_cls0 rfl
    | succ N =>
    have h1 := stepProj_ref p hp hwc.strLitSupported hwc.strLitCtor hcc.toProjCallees hcc.erec N
      (hk.mono (by omega)) F (by omega) (by omega) s₀ a₀ dn vis fe MM eb mode cheap d e
      (tfld s₀.mem PROJ (tierW e) (idxW e) 0) (tfld s₀.mem PROJ (tierW e) (idxW e) 1)
      (tfld s₀.mem PROJ (tierW e) (idxW e) 2) hs he hsn hpe (hsup fe)
    exact RefE.lastE (K := whnfCoreStepE.k_whnf_core_app p) (fun _ => rfl) (fun _ => rfl)
      (·.knot.mono (Nat.le_succ N)) h1
      fun _ _ _ _ h => ⟨h.after, h.res, h.valid⟩
  rw [ite_eq_right g9]
  by_cases g7 : tagW e = 7
  · rw [ite_eq_left g7]
    refine RefE.abort0 (by decide) fun hc7 => ?_
    obtain ⟨hv, -, hvv, hbb⟩ := view_let s₀.mem a₀ hR e hh (vok _ hc7) g7
    refine RefE.of_run_eq (step_run_let _ _ _ hv) ?_
    refine RefE.bind_callW (s₀ := s₀) (fun _ => rfl) (hcc.inst1 n s₀ a₀ dn vis fe MM eb _ _ 0 hS hbb hvv)
      fun r₁ m₁ _ h₁ => RefE.ret rfl ⟨h₁.after, by simp [decStep, decH], ⟨by
        show HW (1 : Word); unfold HW; decide, h₁.resOk⟩⟩
  rw [ite_eq_right g7]
  by_cases g0 : tagW e = 0
  · rw [ite_eq_left g0]
    refine RefE.abort0 (by decide) fun hc0 => ?_
    exact fun _ => ErrClaim.of_run_eqW (step_run_bvar _ (view_bvar s₀.mem a₀ hR e hh (vok _ hc0) g0))
      (ErrClaim.fail _ _ rfl)
  rw [ite_eq_right g0]
  by_cases g1 : tagW e = 1
  · rw [ite_eq_left g1]
    refine RefE.abort0 (by decide) fun hc => ?_
    obtain ⟨i, ty, hv'⟩ := view_fvar s₀.mem a₀ hR e hh (vok _ hc) g1
    exact done _ hv' rfl
  rw [ite_eq_right g1]
  by_cases g2 : tagW e = 2
  · rw [ite_eq_left g2]
    refine RefE.abort0 (by decide) fun hc => ?_
    obtain ⟨u, hv'⟩ := view_sort s₀.mem a₀ hR e hh (vok _ hc) g2
    exact done _ hv' rfl
  rw [ite_eq_right g2]
  by_cases g3 : tagW e = 3
  · rw [ite_eq_left g3]
    refine RefE.abort0 (by decide) fun hc => ?_
    obtain ⟨c, us, hv'⟩ := view_const s₀.mem a₀ hR e hh (vok _ hc) g3
    exact done _ hv' rfl
  rw [ite_eq_right g3]
  by_cases g5 : tagW e = 5
  · rw [ite_eq_left g5]
    refine RefE.abort0 (by decide) fun hc => ?_
    exact done _ (view_lam s₀.mem a₀ hR e hh (vok _ hc) g5).1 rfl
  rw [ite_eq_right g5]
  by_cases g6 : tagW e = 6
  · rw [ite_eq_left g6]
    refine RefE.abort0 (by decide) fun hc => ?_
    exact done _ (view_forall s₀.mem a₀ hR e hh (vok _ hc) g6).1 rfl
  rw [ite_eq_right g6]
  by_cases g8 : tagW e = 8
  · rw [ite_eq_left g8]
    refine RefE.abort0 (by decide) fun hc => ?_
    obtain ⟨l, hv'⟩ := view_lit s₀.mem a₀ hR e hh (vok _ hc) g8
    exact done _ hv' rfl
  rw [ite_eq_right g8]
  exact RefE.of_cls0 (by decide)

include hp hwc hcc hsup in
/-- **`whnf_core_step` refines `whnfCoreStep`** (`step_ref`'s ok half). -/
theorem whnfCoreStep_refines' (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode cheap d e : Word) (hs : SlotPre s₀ a₀ dn vis fe MM eb mode)
    (he : HW e) :
    CoreSpec p (n + 1) "whnf_core_step" [mode, cheap, vis, d, e]
      (whnfCoreStep (decMode mode) (coreKnot (decMode mode) fe id F) fe (cheap != 0) d.toNat
        (decE e)) decStep s₀ a₀ dn vis fe MM eb ResW :=
  RefE.coreSpec (whnfCoreStepE_spec p hp (n + 1) s₀ mode cheap vis d e)
    (step_ref p hp hwc hcc hsup n hk F hF hn s₀ a₀ dn vis fe MM eb mode cheap d e hs he)

end step


/-- **`whnf_core_loop`'s model, both outcomes**: each iteration a run of `whnf_core_step`
(`callE`), done on `(0, v)`, continuing on `(1, e')`. -/
l_model whnfCoreLoop_specE (p : Prog) (hf : p.lookup "whnf_core_loop" = some whnfCoreLoopL)
  fns [hf ↦ whnfCoreLoopE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  finish [tierW, idxW] unified

/-- **`whnf_core_step`'s error claim** at every L fuel up to `n` (what the loop's errors claim
from; `step_ref`'s error half, `coreStepE_of`). -/
def CoreStepE (p : Prog) (n : Nat) : Prop :=
  ∀ j, j ≤ n → ∀ (F : Nat), j ≤ F → j ≤ 2 ^ 62 → ∀ (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb mode cheap d e : Word), SlotPre s₀ a₀ dn vis fe MM eb mode → HW e →
    CoreSpecE p (j + 1) "whnf_core_step" [mode, cheap, vis, d, e]
      (whnfCoreStep (decMode mode) (coreKnot (decMode mode) fe id F) fe (cheap != 0) d.toNat
        (decE e)) s₀ a₀

section loopRef
variable (p : Prog) (hp : WhnfCoreProg p) (hwc : WhnfCallees p) (hcc : CoreCallees p)
  (hsup : ∀ fe : IFEnv, SupKeep fe)

include hp hwc hcc hsup in
/-- **The loop refines `whnfCoreLoop`, both outcomes**, at every twin loop fuel `K ≥ k`: each
iteration is `whnf_core_step`'s (`whnfCoreStep_refines'`, its error claim `CoreStepE`). -/
theorem coreLoop_ref (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (mode cheap d : Word)
    (hmode : mode < 4) :
    ∀ k, k ≤ n + 1 → ∀ K, k ≤ K + 1 → ∀ (m : Mem) (a : AState) (MM : ModeMaps) (eb e : Word),
      CoreS dn m a vis fe MM eb → eb = (mode >>> 1) &&& 1 → HW e →
      RefE (CoreStepE p n) (whnfCoreLoopE.loop1 p k m mode cheap vis d e)
        (whnfCoreLoop (decMode mode) (coreKnot (decMode mode) fe id F) fe (cheap != 0)
          d.toNat K (decE e)) a
        (fun v y a' => CorePost decH dn m vis fe MM eb ResH ([v.1], v.2) y a') := by
  intro k
  induction k with
  | zero =>
    intro _ _ _ _ _ _ _ _ _ _ _
    simp only [whnfCoreLoopE.loop1]; exact RefE.of_cls0 rfl
  | succ k ih =>
    intro hkn K hK m a MM eb e hS heb he
    simp only [whnfCoreLoopE.loop1]
    cases k with
    | zero => exact RefE.callE_zero (fun _ => whnfCoreLoopE.k_whnf_core_step.none ..)
    | succ j =>
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    have hs : SlotPre ⟨m, Locals.init []⟩ a dn vis fe MM eb mode := ⟨hS, hmode, heb⟩
    rw [whnfCoreLoop.eq_2]
    refine RefE.bind_callE (s₀ := ⟨m, Locals.init []⟩) (fun _ => whnfCoreLoopE.k_whnf_core_step.none ..)
      (whnfCoreStep_refines' p hp hwc hcc hsup j (hk.mono (by omega)) F (by omega) (by omega) _ a dn vis
        fe MM eb mode cheap d e hs he)
      (fun (hG : CoreStepE p n) => hG j (by omega) F (by omega) (by omega) _ a dn vis fe MM eb mode cheap
        d e hs he)
      fun r m₁ _ h₁ => RefE.after_core (w := fun v : Word × Mem => ([v.1], v.2)) h₁ fun M₁ hS₁ _ => ?_
    by_cases h0 : r.headD 0 = 0
    · rw [whnfCoreLoopE.k_whnf_core_step.arm1 _ _ _ _ _ _ _ _ h0]
      simp only [decStep, h0, ↓reduceIte]
      exact RefE.ret rfl (CorePost.ret hS₁ rfl h₁.resOk.2)
    rw [whnfCoreLoopE.k_whnf_core_step.arm2 _ _ _ _ _ _ _ _ h0]
    simp only [decStep, h0, ↓reduceIte]
    exact ih (by omega) K' (by omega) m₁ _ M₁ eb _ hS₁ heb h₁.resOk.2

include hp hwc hcc hsup in
/-- `whnf_core_loop` from its run, both outcomes (`coreLoop_ref` at the call's fuel). -/
theorem whnfCoreLoop_ref (n : Nat) (hk : KnotUpTo p n) (F K : Nat) (hF : n ≤ F) (hK : n ≤ K)
    (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (MM : ModeMaps) (eb mode cheap d e : Word)
    (hs : SlotPre s₀ a₀ dn vis fe MM eb mode) (he : HW e) :
    RefE (CoreStepE p n) (whnfCoreLoopE p (n + 1) s₀.mem mode cheap vis d e)
      (whnfCoreLoop (decMode mode) (coreKnot (decMode mode) fe id F) fe (cheap != 0) d.toNat K
        (decE e)) a₀
      (fun v y a' => CorePost decH dn s₀.mem vis fe MM eb ResH ([v.1], v.2) y a') := by
  rw [whnfCoreLoopE.arm1]
  exact coreLoop_ref p hp hwc hcc hsup n hk F hF hn dn vis fe mode cheap d hs.mode4 (n + 1)
    (Nat.le_refl _) K (by omega) s₀.mem a₀ MM eb e hs.rel hs.eb_mode he

include hp hwc hcc hsup in
/-- **`whnf_core_loop` refines `whnfCoreLoop` at every twin loop fuel `K ≥ n`** (the ok half). -/
theorem whnfCoreLoop_refines' (n : Nat) (hk : KnotUpTo p n) (F K : Nat) (hF : n ≤ F) (hK : n ≤ K)
    (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (MM : ModeMaps) (eb mode cheap d e : Word)
    (hs : SlotPre s₀ a₀ dn vis fe MM eb mode) (he : HW e) :
    CoreSpec p (n + 1) "whnf_core_loop" [mode, cheap, vis, d, e]
      (whnfCoreLoop (decMode mode) (coreKnot (decMode mode) fe id F) fe (cheap != 0) d.toNat K
        (decE e)) decH s₀ a₀ dn vis fe MM eb :=
  CoreSpec.of_refE (w := fun v => ([v.1], v.2))
    (whnfCoreLoop_specE p hp.loop (n + 1) s₀ mode cheap vis d e)
    (whnfCoreLoop_ref p hp hwc hcc hsup n hk F K hF hK hn s₀ a₀ dn vis fe MM eb mode cheap d e hs he)
    fun _ _ => ⟨rfl, rfl, id⟩

include hp hwc hcc hsup in
/-- **`whnf_core_loop` refines `whnfCoreBody`** (the loop at `whnfCoreLoopFuel = 2^62`). -/
theorem whnfCoreBody_refines' (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (MM : ModeMaps) (eb mode cheap d e : Word)
    (hs : SlotPre s₀ a₀ dn vis fe MM eb mode) (he : HW e) :
    CoreSpec p (n + 1) "whnf_core_loop" [mode, cheap, vis, d, e]
      (whnfCoreBody (decMode mode) (coreKnot (decMode mode) fe id F) fe (cheap != 0) d.toNat
        (decE e)) decH s₀ a₀ dn vis fe MM eb :=
  whnfCoreLoop_refines' p hp hwc hcc hsup n hk F whnfCoreLoopFuel hF (by simp only [whnfCoreLoopFuel]; omega) hn s₀
    a₀ dn vis fe MM eb mode cheap d e hs he

end loopRef

/-! ## The slot: a mode memo around the body -/

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

section slot
variable (p : Prog) (hp : WhnfCoreProg p) (hwc : WhnfCallees p) (hcc : CoreCallees p)
  (hsup : ∀ fe : IFEnv, SupKeep fe)

include hp hwc hcc hsup in
/-- **`whnf_core` at `n + 1` refines the knot's `whnfCore` slot of `coreKnot mode fe id F`, both
outcomes**, `F ≥ n + 1`: a stuck tag answers itself, a memo hit its entry, a miss the body's
answer (`whnf_core_loop` at `n`, through its run), recorded. The errors are the body's
(`CoreStepE`). -/
theorem core_ref (n : Nat) (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb mode cheap d e : Word) (hF : n + 1 ≤ F) (hn : n + 1 ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe MM eb mode) (he : HW e) :
    RefE (CoreStepE p n) (whnfCoreE p (n + 1) s₀.mem mode cheap vis d e)
      ((coreKnot (decMode mode) fe id F).whnfCore (cheap != 0) d.toNat (decE e)) a₀
      (CorePost decH dn s₀.mem vis fe MM eb ResH) := by
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  have hS := hs.rel
  have heb := hS.core.eb1
  have hkey : ((mode >>> 1) &&& 1) <<< 32 = genW 0 eb := ebKey_eq mode eb hs.eb_mode
  simp only [whnfCoreE]
  by_cases hst : tagW e ≠ 4 ∧ tagW e ≠ 9 ∧ tagW e ≠ 7 ∧ tagW e ≠ 0
  · rw [ite_eq_left hst]
    have ht : whnfCoreStuckTag (decE e) = true := by rw [stuck_iff e he]; simpa using hst
    exact RefE.ret (knot_whnfCore_stuck _ fe F' (cheap != 0) d.toNat _ a₀ ht) (CorePost.ret hS rfl he)
  rw [ite_eq_right hst]
  have ht : whnfCoreStuckTag (decE e) = false := by rw [stuck_iff e he]; simpa using hst
  -- the body's error claim at fuel `n' + 1`
  have body : ∀ (n' : Nat), n = n' + 1 → ∀ (c : Word) (er : Err),
      callE p (n' + 1) "whnf_core_loop" [mode, c, vis, d, e] s₀.mem = .error er → CoreStepE p n →
      ErrClaim (whnfCoreBody (decMode mode) (coreKnot (decMode mode) fe id F') fe (c != 0) d.toNat
        (decE e)) a₀ er := by
    intro n' hn' c er h2 hG
    exact CoreSpecE.of_callE (RefE.coreSpecE (whnfCoreLoop_specE p hp.loop (n' + 1) s₀ mode c vis d e)
      trivial (fun j hj => hG j (by omega)) (whnfCoreLoop_ref p hp hwc hcc hsup n' (hk.mono (by omega))
        F' whnfCoreLoopFuel (by omega) (by simp only [whnfCoreLoopFuel]; omega) (by omega) s₀ a₀ dn vis
        fe MM eb mode c d e hs he)) h2
  by_cases hc : cheap ≠ 0
  · rw [ite_eq_left hc]
    have hcb : (cheap != 0) = true := by simpa using hc
    rw [hcb]
    refine RefE.onlySim (fun _ => rfl) (fun _ _ h => callW_memoFind hp.wkf h) fun r₁ m₁ ⟨hm, hne, hr⟩ => ?_
    rw [hkey] at hr
    subst hm hr
    have hf := hS.core.wk.findE heb e he hne
    simp only [whnfCoreE.k_wk_find]
    by_cases h1' : (mfindG wkSch s₀.mem e (genW 0 eb)).headD 0 ≠ 0
    · rw [ite_eq_left h1']
      exact RefE.ret (knot_whnfCore_hitK _ fe F' d.toNat _ a₀ ht _ (hf.1 h1').1)
        (CorePost.ret hS rfl (hf.1 h1').2)
    rw [ite_eq_right h1']
    have hmiss := hf.2 (by simpa using h1')
    cases n with
    | zero => exact RefE.callE_zero (fun _ => rfl)
    | succ n' =>
    rcases h2 : callE p (n' + 1) "whnf_core_loop" [mode, 1, vis, d, e] s₀.mem with e2 | ⟨r₂, m₂⟩
    · exact fun hG => ErrClaim.of_run_eq (fun ce h' => knot_whnfCore_missK_err _ fe F' d.toNat _ a₀ ht
        hmiss ce h') (body n' rfl 1 _ h2 hG)
    obtain ⟨hok, ⟨M', hS₁, hK₁, hSt₁⟩, hres, hrw⟩ := CoreSpec.of_callW
      (whnfCoreBody_refines' p hp hwc hcc hsup n' (hk.mono (by omega)) F' (by omega) (by omega) s₀ a₀ dn
        vis fe MM eb mode 1 d e hs he) (callW_of_callE h2)
    simp only [whnfCoreE.k_whnf_core_loop]
    refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r₃ m₃ h3 => ?_
    simp only [whnfCoreE.k_wk_find_2]
    refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r₄ m₄ h4 => ?_
    simp only [whnfCoreE.k_wk_put]
    have hset := callW_memoSet hp.wkf hp.wkp h3 h4
    rw [hkey] at hset
    obtain ⟨hS₂, hSt₂⟩ := hS₁.set_wk e (r₂.headD 0) he hrw hset
    have hb1 : ((1 : Word) != 0) = true := rfl
    rw [hb1] at hok hres
    have hrun := knot_whnfCore_missK _ fe F' d.toNat _ a₀ ht hmiss _ _ (AM.run_of_ok _ _ hok)
    rw [hres] at hrun
    exact RefE.ret hrun ⟨⟨_, hS₂, hK₁.wk _ _, hSt₁.trans hSt₂⟩, rfl, hrw⟩
  · rw [ite_eq_right hc]
    have hcb : (cheap != 0) = false := by simpa using hc
    rw [hcb]
    refine RefE.onlySim (fun _ => rfl) (fun _ _ h => callW_memoFind hp.wcf h) fun r₁ m₁ ⟨hm, hne, hr⟩ => ?_
    rw [hkey] at hr
    subst hm hr
    have hf := hS.core.wc.findE heb e he hne
    simp only [whnfCoreE.k_wc_find]
    by_cases h1' : (mfindG wcSch s₀.mem e (genW 0 eb)).headD 0 ≠ 0
    · rw [ite_eq_left h1']
      exact RefE.ret (knot_whnfCore_hitF _ fe F' d.toNat _ a₀ ht _ (hf.1 h1').1)
        (CorePost.ret hS rfl (hf.1 h1').2)
    rw [ite_eq_right h1']
    have hmiss := hf.2 (by simpa using h1')
    cases n with
    | zero => exact RefE.callE_zero (fun _ => rfl)
    | succ n' =>
    rcases h2 : callE p (n' + 1) "whnf_core_loop" [mode, 0, vis, d, e] s₀.mem with e2 | ⟨r₂, m₂⟩
    · exact fun hG => ErrClaim.of_run_eq (fun ce h' => knot_whnfCore_missF_err _ fe F' d.toNat _ a₀ ht
        hmiss ce h') (body n' rfl 0 _ h2 hG)
    obtain ⟨hok, ⟨M', hS₁, hK₁, hSt₁⟩, hres, hrw⟩ := CoreSpec.of_callW
      (whnfCoreBody_refines' p hp hwc hcc hsup n' (hk.mono (by omega)) F' (by omega) (by omega) s₀ a₀ dn
        vis fe MM eb mode 0 d e hs he) (callW_of_callE h2)
    simp only [whnfCoreE.k_whnf_core_loop_2]
    refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r₃ m₃ h3 => ?_
    simp only [whnfCoreE.k_wc_find_2]
    refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r₄ m₄ h4 => ?_
    simp only [whnfCoreE.k_wk_put]
    have hset := callW_memoSet hp.wcf hp.wcp h3 h4
    rw [hkey] at hset
    obtain ⟨hS₂, hSt₂⟩ := hS₁.set_wc e (r₂.headD 0) he hrw hset
    have hb0 : ((0 : Word) != 0) = false := rfl
    rw [hb0] at hok hres
    have hrun := knot_whnfCore_missF _ fe F' d.toNat _ a₀ ht hmiss _ _ (AM.run_of_ok _ _ hok)
    rw [hres] at hrun
    exact RefE.ret hrun ⟨⟨_, hS₂, hK₁.wc _ _, hSt₁.trans hSt₂⟩, rfl, hrw⟩

include hp hwc hcc hsup in
/-- **The knot's `whnfCore` slot, one level up** (`core_ref`'s ok half): given the knot at every
fuel up to `n` (for the body's callees), `whnf_core` at `n + 1` refines the slot. Over the bundles
`WhnfCallees`, `CoreCallees` and `SupKeep` (`DefEqKnot.lean` builds them from real proofs). -/
theorem whnfCoreSlot_step (n : Nat) (hk : KnotUpTo p n) : WhnfCoreSlot p (n + 1) :=
  fun F s₀ a₀ dn vis fe MM eb mode cheap d e hF hn hs he =>
    RefE.coreSpec (whnfCoreE_spec p hp.core (n + 1) s₀ mode cheap vis d e)
      (core_ref p hp hwc hcc hsup n hk F s₀ a₀ dn vis fe MM eb mode cheap d e hF hn hs he)

end slot

end L.Arena
