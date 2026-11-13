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
import all ConAgua.Arena.WhnfCore

@[expose] public section

/-!
# The `whnf_core` loop and slot (phase 5, lane `whnf`; con-ron's #572 memo policy)

`whnf_core`'s unified model `whnfCoreE` is the loop: its iteration `whnfCoreE.loop1` refines
`whnfCoreLoop` from pending keys on the stack (`PendR`), both outcomes, iteration by iteration
through `whnf_core_step`'s (`step_ref`, both outcomes, over its unified model); the slot one level
up (`core_ref`) is the loop at `whnfCoreLoopFuel` from no pending keys (`knot_whnfCore_eq`).
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
variable {mode : ConLeche.CheckMode} {eager : Bool} {r : CoreFnsA} {fe : IFEnv} {cheap : Bool} {depth : Nat}
  {h e : EIdx} {a : AState}

theorem step_run_done (v : ENodeView) (hv : a.store.view e = some v) (hd : isDoneV v = true) :
    (whnfCoreStep mode r fe cheap depth h e).run a = .ok (.done e, a) := by
  simp only [whnfCoreStep, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]
  cases v <;> simp [isDoneV] at hd <;> rfl

theorem step_run_app (f x : EIdx) (hv : a.store.view e = some (.app f x)) (hs : isStuckHead h = false) :
    (whnfCoreStep mode r fe cheap depth h e).run a = (whnfCoreStepApp mode r fe cheap depth e).run a := by
  simp only [whnfCoreStep, StateT.run_bind, view_run _ _ _ hv, except_ok_bind, hs]; try rfl

theorem step_run_stuck (f x : EIdx) (hv : a.store.view e = some (.app f x)) (hs : isStuckHead h = true) :
    (whnfCoreStep mode r fe cheap depth h e).run a = (whnfStuck mode r fe depth h e).run a := by
  simp only [whnfCoreStep, StateT.run_bind, view_run _ _ _ hv, except_ok_bind, hs]; try rfl

theorem step_run_proj (sn : NIdx) (i : Nat) (pe : EIdx) (hv : a.store.view e = some (.proj sn i pe)) :
    (whnfCoreStep mode r fe cheap depth h e).run a =
      (whnfCoreStepProj mode r fe cheap depth e sn i pe).run a := by
  simp only [whnfCoreStep, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]; try rfl

theorem step_run_let (t v b : EIdx) (hv : a.store.view e = some (.letE t v b)) :
    (whnfCoreStep mode r fe cheap depth h e).run a =
      (do let e' ← instantiate1Fast coreWalkFuel b v 0; pure (WhnfStep.cont e') : AM WhnfStep).run a := by
  simp only [whnfCoreStep, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]; try rfl

theorem step_run_bvar (i : Nat) (hv : a.store.view e = some (.bvar i)) :
    (whnfCoreStep mode r fe cheap depth h e).run a =
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
    (MM : ModeMaps) (eb mode cheap d h e : Word) (hs : SlotPre s₀ a₀ dn vis fe MM eb mode)
    (hh : HW h) (he : HW e) :
    RefE (AppG p n) (whnfCoreStepE p (n + 1) s₀.mem mode cheap vis d h e)
      (whnfCoreStep (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe (cheap != 0) d.toNat
        (decE h) (decE e)) a₀ (CorePost decStep dn s₀.mem vis fe MM eb ResW) := by
  have hS := hs.rel
  have hR := hS.arena.base
  have hh' : e.toNat < 2 ^ 32 := he
  simp only [whnfCoreStepE]
  refine RefE.abort0 (by decide) fun ht => ?_
  -- a stuck arm answers `(0, e)` after its view check
  have done : ∀ v : ENodeView, a₀.store.view (decE e) = some v → isDoneV v = true →
      RefE (AppG p n) (.ok ([0, e], s₀.mem))
        (whnfCoreStep (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe (cheap != 0) d.toNat
          (decE h) (decE e)) a₀ (CorePost decStep dn s₀.mem vis fe MM eb ResW) := fun v hv hd =>
    RefE.ret (step_run_done v hv hd) (CorePost.ret hS (by simp [decStep])
      ⟨by show HW (0 : Word); unfold HW; decide, he⟩)
  have vok : ∀ c : TRec, ¬ tcnt s₀.mem c (tierW e) ≤ idxW e → viewOK s₀.mem e c :=
    fun c hc => ⟨ht, by simpa using hc⟩
  by_cases g4 : tagW e = 4
  · rw [ite_eq_left g4]
    sorry
  rw [ite_eq_right g4]
  by_cases g9 : tagW e = 9
  · rw [ite_eq_left g9]
    refine RefE.abort0 (by decide) fun hc9 => ?_
    obtain ⟨hv, hsn, hpe⟩ := view_proj s₀.mem a₀ hR e hh' (vok _ hc9) g9
    refine RefE.of_run_eq (step_run_proj _ _ _ hv) ?_
    cases n with
    | zero => exact RefE.of_cls0 rfl
    | succ N =>
    have h1 := stepProj_ref p hp hwc.strLitStored hwc.strLitCtor hcc.toProjCallees hcc.erec N
      (hk.mono (by omega)) F (by omega) (by omega) s₀ a₀ dn vis fe MM eb mode cheap d e
      (tfld s₀.mem PROJ (tierW e) (idxW e) 0) (tfld s₀.mem PROJ (tierW e) (idxW e) 1)
      (tfld s₀.mem PROJ (tierW e) (idxW e) 2) hs he hsn hpe (hsup fe)
    exact RefE.lastE (K := whnfCoreStepE.k_whnf_stuck p) (fun _ => rfl) (fun _ => rfl)
      (·.knot.mono (Nat.le_succ N)) h1
      fun _ _ _ _ h => ⟨h.after, h.res, h.valid⟩
  rw [ite_eq_right g9]
  by_cases g7 : tagW e = 7
  · rw [ite_eq_left g7]
    refine RefE.abort0 (by decide) fun hc7 => ?_
    obtain ⟨hv, -, hvv, hbb⟩ := view_let s₀.mem a₀ hR e hh' (vok _ hc7) g7
    refine RefE.of_run_eq (step_run_let _ _ _ hv) ?_
    refine RefE.bind_callW (s₀ := s₀) (fun _ => rfl) (hcc.inst1 n s₀ a₀ dn vis fe MM eb _ _ 0 hS hbb hvv)
      fun r₁ m₁ _ h₁ => RefE.ret rfl ⟨h₁.after, by simp [decStep, decH], ⟨by
        show HW (1 : Word); unfold HW; decide, h₁.resOk⟩⟩
  rw [ite_eq_right g7]
  by_cases g0 : tagW e = 0
  · rw [ite_eq_left g0]
    refine RefE.abort0 (by decide) fun hc0 => ?_
    exact fun _ => L.Arena.ErrClaim.congr_run (step_run_bvar _ (view_bvar s₀.mem a₀ hR e hh' (vok _ hc0) g0))
      (ErrClaim.fail _ _ rfl)
  rw [ite_eq_right g0]
  by_cases g1 : tagW e = 1
  · rw [ite_eq_left g1]
    refine RefE.abort0 (by decide) fun hc => ?_
    obtain ⟨i, ty, hv'⟩ := view_fvar s₀.mem a₀ hR e hh' (vok _ hc) g1
    exact done _ hv' rfl
  rw [ite_eq_right g1]
  by_cases g2 : tagW e = 2
  · rw [ite_eq_left g2]
    refine RefE.abort0 (by decide) fun hc => ?_
    obtain ⟨u, hv'⟩ := view_sort s₀.mem a₀ hR e hh' (vok _ hc) g2
    exact done _ hv' rfl
  rw [ite_eq_right g2]
  by_cases g3 : tagW e = 3
  · rw [ite_eq_left g3]
    refine RefE.abort0 (by decide) fun hc => ?_
    obtain ⟨c, us, hv'⟩ := view_const s₀.mem a₀ hR e hh' (vok _ hc) g3
    exact done _ hv' rfl
  rw [ite_eq_right g3]
  by_cases g5 : tagW e = 5
  · rw [ite_eq_left g5]
    refine RefE.abort0 (by decide) fun hc => ?_
    exact done _ (view_lam s₀.mem a₀ hR e hh' (vok _ hc) g5).1 rfl
  rw [ite_eq_right g5]
  by_cases g6 : tagW e = 6
  · rw [ite_eq_left g6]
    refine RefE.abort0 (by decide) fun hc => ?_
    exact done _ (view_forall s₀.mem a₀ hR e hh' (vok _ hc) g6).1 rfl
  rw [ite_eq_right g6]
  by_cases g8 : tagW e = 8
  · rw [ite_eq_left g8]
    refine RefE.abort0 (by decide) fun hc => ?_
    obtain ⟨l, hv'⟩ := view_lit s₀.mem a₀ hR e hh' (vok _ hc) g8
    exact done _ hv' rfl
  rw [ite_eq_right g8]
  exact RefE.of_cls0 (by decide)

include hp hwc hcc hsup in
/-- **`whnf_core_step` refines `whnfCoreStep`** (`step_ref`'s ok half). -/
theorem whnfCoreStep_refines' (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode cheap d h e : Word) (hs : SlotPre s₀ a₀ dn vis fe MM eb mode)
    (hh : HW h) (he : HW e) :
    CoreSpec p (n + 1) "whnf_core_step" [mode, cheap, vis, d, h, e]
      (whnfCoreStep (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe (cheap != 0) d.toNat
        (decE h) (decE e)) decStep s₀ a₀ dn vis fe MM eb ResW :=
  RefE.coreSpec (whnfCoreStepE_spec p hp (n + 1) s₀ mode cheap vis d h e)
    (step_ref p hp hwc hcc hsup n hk F hF hn s₀ a₀ dn vis fe MM eb mode cheap d h e hs hh he)

end step

/-- **`whnf_core_step`'s error claim** at every L fuel up to `n` (what the loop's errors claim
from; `step_ref`'s error half, `coreStepE_of`). -/
def CoreStepE (p : Prog) (n : Nat) : Prop :=
  ∀ j, j ≤ n → ∀ (F : Nat), j ≤ F → j ≤ 2 ^ 62 → ∀ (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb mode cheap d h e : Word), SlotPre s₀ a₀ dn vis fe MM eb mode → HW h → HW e →
    CoreSpecE p (j + 1) "whnf_core_step" [mode, cheap, vis, d, h, e]
      (whnfCoreStep (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe (cheap != 0) d.toNat
        (decE h) (decE e)) s₀ a₀

/-! ## The pending keys -/

/-- **The loop's pending keys** at memory `m`: `pend` is the stack slice `SPN[pb, pb + pn)` right
below the top, `pendC` its suffix from `pc`. -/
structure PendR (m : Mem) (pb pn pc : Word) (pend pendC : Array EIdx) : Prop where
  slice : SpineR m pb pn pend
  pc_le : pc.toNat ≤ pn.toNat
  suffix : pend.extract pc.toNat pend.size = pendC
  top : spTop m = pb + pn

section loopRef
variable (p : Prog) (hp : WhnfCoreProg p) (hwc : WhnfCallees p) (hcc : CoreCallees p)
  (hsup : ∀ fe : IFEnv, SupKeep fe)

include hp hwc hcc hsup in
/-- **The loop refines `whnfCoreLoop`, both outcomes**, at every twin loop fuel `K ≥ k`, from
pending keys `pend`/`pendC` (`PendR`) above the entry's top `pb`: each iteration is
`whnf_core_step`'s (`whnfCoreStep_refines'`, its error claim `CoreStepE`). -/
@[refines ConRon.Arena.whnfCoreLoop]
theorem coreLoop_ref (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (mode cheap d pb : Word)
    (hmode : mode < 4) (m₀ : Mem) (MM₀ : ModeMaps) (eb : Word) (heb : eb = (mode >>> 1) &&& 1)
    (htop₀ : spTop m₀ = pb) :
    ∀ k, k ≤ n + 1 → ∀ K, k ≤ K + 1 → ∀ (m : Mem) (a : AState) (MM : ModeMaps) (e pn pc : Word)
      (pend pendC : Array EIdx),
      CoreS dn m a vis fe MM eb → KeptAll MM₀ MM eb → HW e → PendR m pb pn pc pend pendC →
      (∀ j : Word, j < pb → spW m j = spW m₀ j) → (m.arr64 SPN).size = (m₀.arr64 SPN).size →
      BKept m₀ m → PoolGrew m₀ m →
      RefE (CoreStepE p n) (whnfCoreE.loop1 p k m mode cheap vis d e pb pn pc)
        (whnfCoreLoop (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe (cheap != 0)
          d.toNat K (decE e) pend pendC) a
        (CorePost decH dn m₀ vis fe MM₀ eb ResH) := by
  sorry

end loopRef

/-! ## The slot: the loop at `whnfCoreLoopFuel`, no pending keys -/

/-- **The knot's `whnfCore` slot is the body** one level down (con-ron's #572: no stuck-tag test,
no memo in the slot). -/
theorem knot_whnfCore_eq (mode : ConLeche.CheckMode) (eager : Bool) (fe : IFEnv) (F : Nat) (c : Bool)
    (d : Nat) (e : EIdx) :
    (coreKnot mode eager fe id (F + 1)).whnfCore c d e =
      whnfCoreLoop mode (coreKnot mode eager fe id F) fe c d whnfCoreLoopFuel e #[] #[] := by
  simp only [coreKnot, whnfCoreBody, id]

section slot
variable (p : Prog) (hp : WhnfCoreProg p) (hwc : WhnfCallees p) (hcc : CoreCallees p)
  (hsup : ∀ fe : IFEnv, SupKeep fe)

include hp hwc hcc hsup in
/-- **`whnf_core` at `n + 1` refines the knot's `whnfCore` slot of `coreKnot mode eager fe id F`, both
outcomes**, `F ≥ n + 1`: the loop from no pending keys at the entry's top (`coreLoop_ref`). The
errors are the step's (`CoreStepE`). -/
theorem core_ref (n : Nat) (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb mode cheap d e : Word) (hF : n + 1 ≤ F) (hn : n + 1 ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe MM eb mode) (he : HW e) :
    RefE (CoreStepE p n) (whnfCoreE p (n + 1) s₀.mem mode cheap vis d e)
      ((coreKnot (decMode mode) (decEager mode) fe id F).whnfCore (cheap != 0) d.toNat (decE e)) a₀
      (CorePost decH dn s₀.mem vis fe MM eb ResH) := by
  sorry

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
