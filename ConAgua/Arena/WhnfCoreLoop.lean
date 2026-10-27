import ConAgua.Arena.WhnfCoreStep
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import ConAgua.Arena.WhnfCoreProj
import ConAgua.Arena.WhnfCoreSlot

/-!
# The `whnf_core` loop and slot (phase 5, lane `whnf`)

The loop's model `coreLoopW` refines `whnfCoreLoop` iteration by iteration through
`whnfCoreStep_refines`; the body is the loop at `whnfCoreLoopFuel`, and the slot one level up
(`whnfCoreSlot_step`) is the memo around the body.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## The dispatcher -/

/-- The result of a stuck arm: `(0, e)` if the view check passes. -/
def stuckW (m : Mem) (c : TRec) (e : Word) : Option (Word × Word × Mem) :=
  if tcnt m c (tierW e) ≤ idxW e then none else some (0, e, m)

/-- The model of `whnf_core_step`. -/
def coreStepW (p : Prog) (n : Nat) (m : Mem) (mode cheap vis d e : Word) :
    Option (Word × Word × Mem) :=
  let t := tierW e
  let i := idxW e
  if t ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if e >>> 28 = 4 then
    if tcnt m APP t ≤ i then none else
    match callW p n "whnf_core_app" [mode, cheap, vis, d, e] m with
    | none => none
    | some (r, m') => some (r.headD 0, r.tail.headD 0, m')
  else if e >>> 28 = 9 then
    if tcnt m PROJ t ≤ i then none else
    match callW p n "whnf_core_step_proj" [mode, cheap, vis, d, e,
        tfld m PROJ t i 0, tfld m PROJ t i 1,
        tfld m PROJ t i 2] m with
    | none => none
    | some (r, m') => some (r.headD 0, r.tail.headD 0, m')
  else if e >>> 28 = 7 then
    if tcnt m LET t ≤ i then none else
    match callW p n "inst1" [tfld m LET t i 2,
        tfld m LET t i 1, 0] m with
    | none => none
    | some (r, m') => some (1, r.headD 0, m')
  else if e >>> 28 = 0 then none
  else if e >>> 28 = 1 then stuckW m FVAR e
  else if e >>> 28 = 2 then stuckW m SORT e
  else if e >>> 28 = 3 then stuckW m CONST e
  else if e >>> 28 = 5 then stuckW m LAM e
  else if e >>> 28 = 6 then stuckW m FORALL e
  else if e >>> 28 = 8 then stuckW m LIT e
  else none

theorem coreStep_spec (p : Prog) (hp : p.lookup "whnf_core_step" = some whnfCoreStepL) (n : Nat)
    (s₀ : St) (mode cheap vis d e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "whnf_core_step" [mode, cheap, vis, d, e]
    ⦃fun r s' => LocEq s' s₀ ∧
      coreStepW p n s₀.mem mode cheap vis d e = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, whnfCoreStepL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt,
      tcntM, evalE_tierE, evalE_idxE,
      callW_spec p n "whnf_core_app", callW_spec p n "whnf_core_step_proj", callW_spec p n "inst1"] <;>
    finish [coreStepW, stuckW, tierW, idxW]

/-! ## The dispatcher refines `whnfCoreStep` -/

theorem whnf_coreRef_congr {α : Type} [Inhabited α] {T T' : AM α} {a₀ : AState} {dec : List Word → α}
    {dn : NIdx → Option ConLeche.Name} {m₀ : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps}
    {eb : Word} {r : List Word} {m : Mem} {ok : List Word → Prop} (h : T.run a₀ = T'.run a₀)
    (h' : CoreRef T' a₀ dec dn m₀ vis fe M eb r m ok) : CoreRef T a₀ dec dn m₀ vis fe M eb r m ok := by
  unfold CoreRef AM.ok AM.st AM.res at *; rw [h]; exact h'

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

end stepRuns

theorem stepRef_done {T : AM WhnfStep} {a : AState} {dn : NIdx → Option ConLeche.Name} {m : Mem}
    {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb e : Word} {r : List Word}
    (hS : CoreS dn m a vis fe M eb) (hrun : T.run a = .ok (.done (decE e), a)) (he : HW e)
    (h0 : r.headD 0 = 0) (h1 : r.tail.headD 0 = e) :
    CoreRef T a decStep dn m vis fe M eb r m ResW := by
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  refine ⟨hok, ?_, ?_, ?_⟩
  · rw [hst]; exact ⟨M, hS, KeptAll.refl _ _, StackKept.refl _⟩
  · rw [hres]; simp only [decStep, h0, h1, ↓reduceIte]
  · exact ⟨by rw [h0]; unfold HW; decide, by rw [h1]; exact he⟩

section step
variable (p : Prog) (hp : WhnfCoreProg p) (hwc : WhnfCallees p) (hcc : CoreCallees p)
  (hsup : ∀ fe : IFEnv, SupKeep fe)

include hp hwc hcc hsup in
/-- **`whnf_core_step` refines `whnfCoreStep`.** -/
theorem whnfCoreStep_refines' (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode cheap d e : Word) (hs : SlotPre s₀ a₀ dn vis fe MM eb mode)
    (he : HW e) :
    CoreSpec p (n + 1) "whnf_core_step" [mode, cheap, vis, d, e]
      (whnfCoreStep (decMode mode) (coreKnot (decMode mode) fe id F) fe (cheap != 0) d.toNat
        (decE e)) decStep s₀ a₀ dn vis fe MM eb ResW := by
  refine triple_post (coreStep_spec p hp.step n s₀ mode cheap vis d e) fun r s' ⟨hloc, hW⟩ =>
    ⟨hloc, ?_⟩
  have hS := hs.rel
  have hR := hS.arena.1
  have hh : e.toNat < 2 ^ 32 := he
  simp only [coreStepW] at hW
  by_cases ht : tierW e ≠ 0 ∧ rdW (s₀.mem.arr64 CTL) 1 = 0
  · simp [ht] at hW
  rw [ite_eq_right ht] at hW
  -- the stuck arms
  have stuck : ∀ c : TRec, stuckW s₀.mem c e = some (r.headD 0, r.tail.headD 0, s'.mem) →
      viewOK s₀.mem e c ∧ r.headD 0 = 0 ∧ r.tail.headD 0 = e ∧ s'.mem = s₀.mem := by
    intro c h
    simp only [stuckW] at h
    split at h
    · simp at h
    · rename_i hle
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨⟨ht, by simpa using hle⟩, h.1.symm, h.2.1.symm, h.2.2.symm⟩
  have done : ∀ c : TRec, stuckW s₀.mem c e = some (r.headD 0, r.tail.headD 0, s'.mem) →
      (∀ v, a₀.store.view (decE e) = some v → isDoneV v = true → CoreRef (whnfCoreStep (decMode mode) (coreKnot (decMode mode) fe id F) fe
          (cheap != 0) d.toNat (decE e)) a₀ decStep dn s₀.mem vis fe MM eb r s'.mem ResW) := by
    intro c h v hv hd
    obtain ⟨-, h0, h1, hm⟩ := stuck c h
    rw [hm]
    exact stepRef_done hS (step_run_done v hv hd) he h0 h1
  by_cases g4 : e >>> 28 = 4
  · rw [ite_eq_left g4] at hW
    by_cases hc4 : tcnt s₀.mem APP (tierW e) ≤ idxW e
    · simp [hc4] at hW
    rw [ite_eq_right hc4] at hW
    -- application
    rcases hca : callW p n "whnf_core_app" [mode, cheap, vis, d, e] s₀.mem with _ | ⟨r₁, m₁⟩ <;>
      simp only [hca, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨h0, h1, hm⟩ := hW
    cases n with
    | zero => simp [callW_zero] at hca
    | succ N =>
    have hv := (view_app s₀.mem a₀ hR e hh ⟨ht, by simpa using hc4⟩ g4).1
    have happ := coreApp_refines p hp hwc hcc N (hk.mono (by omega)) F (by omega) (by omega) s₀ a₀ dn vis fe
      MM eb mode cheap d e hs he
    obtain ⟨hok, hA, hres, hrw⟩ := CoreSpec.of_callW happ hca
    refine whnf_coreRef_congr (step_run_app _ _ hv) ⟨hok, hm ▸ hA, ?_, ?_⟩
    · rw [hres]; simp only [decStep, h0, h1]
    · unfold ResW; rw [← h0, ← h1]; exact hrw
  rw [ite_eq_right g4] at hW
  by_cases g9 : e >>> 28 = 9
  · rw [ite_eq_left g9] at hW
    by_cases hc9 : tcnt s₀.mem PROJ (tierW e) ≤ idxW e
    · simp [hc9] at hW
    rw [ite_eq_right hc9] at hW
    -- projection
    rcases hca : callW p n "whnf_core_step_proj" [mode, cheap, vis, d, e,
        tfld s₀.mem PROJ (tierW e) (idxW e) 0,
        tfld s₀.mem PROJ (tierW e) (idxW e) 1,
        tfld s₀.mem PROJ (tierW e) (idxW e) 2] s₀.mem with _ | ⟨r₁, m₁⟩ <;>
      simp only [hca, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨h0, h1, hm⟩ := hW
    cases n with
    | zero => simp [callW_zero] at hca
    | succ N =>
    obtain ⟨hv, hsn, hpe⟩ := view_proj s₀.mem a₀ hR e hh ⟨ht, by simpa using hc9⟩ g9
    have hpr := whnfCoreStepProj_refines' p hp hwc.strLitSupported hwc.strLitCtor hcc.toProjCallees
      hp.lsn hcc.erec N (hk.mono (by omega)) F (by omega) (by omega) s₀ a₀ dn
      vis fe MM eb mode cheap d e (tfld s₀.mem PROJ (tierW e) (idxW e) 0)
      (tfld s₀.mem PROJ (tierW e) (idxW e) 1)
      (tfld s₀.mem PROJ (tierW e) (idxW e) 2) hs he hsn hpe (hsup fe)
    obtain ⟨hok, hA, hres, hrw⟩ := CoreSpec.of_callW hpr hca
    refine whnf_coreRef_congr (step_run_proj _ _ _ hv) ⟨hok, hm ▸ hA, ?_, ?_⟩
    · rw [hres]; simp only [decStep, h0, h1]
    · unfold ResW; rw [← h0, ← h1]; exact hrw
  rw [ite_eq_right g9] at hW
  by_cases g7 : e >>> 28 = 7
  · rw [ite_eq_left g7] at hW
    by_cases hc7 : tcnt s₀.mem LET (tierW e) ≤ idxW e
    · simp [hc7] at hW
    rw [ite_eq_right hc7] at hW
    -- let
    rcases hca : callW p n "inst1" [tfld s₀.mem LET (tierW e) (idxW e) 2,
        tfld s₀.mem LET (tierW e) (idxW e) 1, 0] s₀.mem with _ | ⟨r₁, m₁⟩ <;>
      simp only [hca, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨h0, h1, hm⟩ := hW
    obtain ⟨hv, -, hvv, hbb⟩ := view_let s₀.mem a₀ hR e hh ⟨ht, by simpa using hc7⟩ g7
    have hi := hcc.inst1 n s₀ a₀ dn vis fe MM eb _ _ 0 hS hbb hvv
    obtain ⟨hok, hA, hres, hrw⟩ := CoreSpec.of_callW hi hca
    have hrun := AM.run_of_ok _ _ hok
    refine whnf_coreRef_congr (step_run_let _ _ _ hv) ?_
    have hrun' : (instantiate1Fast coreWalkFuel
        (decE (tfld s₀.mem LET (tierW e) (idxW e) 2))
        (decE (tfld s₀.mem LET (tierW e) (idxW e) 1)) 0 >>=
        fun e' => pure (WhnfStep.cont e') : AM WhnfStep).run a₀ =
        .ok (.cont (decE (r₁.headD 0)), AM.st (instantiate1Fast coreWalkFuel
        (decE (tfld s₀.mem LET (tierW e) (idxW e) 2))
        (decE (tfld s₀.mem LET (tierW e) (idxW e) 1)) 0) a₀) := by
      simp only [StateT.run_bind]
      rw [show ((0 : Word).toNat) = 0 from rfl] at hrun hres
      rw [hrun, hres]; rfl
    obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hrun'
    refine ⟨hok', ?_, ?_, ?_⟩
    · rw [hst', ← hm]; exact hA
    · rw [hres']; simp only [decStep, ← h0, ← h1]; rfl
    · exact ⟨by rw [← h0]; unfold HW; decide, by rw [← h1]; exact hrw⟩
  rw [ite_eq_right g7] at hW
  by_cases g0 : e >>> 28 = 0
  · simp [g0] at hW
  rw [ite_eq_right g0] at hW
  by_cases g1 : e >>> 28 = 1
  · rw [ite_eq_left g1] at hW
    obtain ⟨hv, -⟩ := stuck _ hW
    obtain ⟨i, ty, hv'⟩ := view_fvar s₀.mem a₀ hR e hh hv g1
    exact done _ hW _ hv' rfl
  rw [ite_eq_right g1] at hW
  by_cases g2 : e >>> 28 = 2
  · rw [ite_eq_left g2] at hW
    obtain ⟨hv, -⟩ := stuck _ hW
    obtain ⟨u, hv'⟩ := view_sort s₀.mem a₀ hR e hh hv g2
    exact done _ hW _ hv' rfl
  rw [ite_eq_right g2] at hW
  by_cases g3 : e >>> 28 = 3
  · rw [ite_eq_left g3] at hW
    obtain ⟨hv, -⟩ := stuck _ hW
    obtain ⟨c, us, hv'⟩ := view_const s₀.mem a₀ hR e hh hv g3
    exact done _ hW _ hv' rfl
  rw [ite_eq_right g3] at hW
  by_cases g5 : e >>> 28 = 5
  · rw [ite_eq_left g5] at hW
    obtain ⟨hv, -⟩ := stuck _ hW
    exact done _ hW _ (view_lam s₀.mem a₀ hR e hh hv g5).1 rfl
  rw [ite_eq_right g5] at hW
  by_cases g6 : e >>> 28 = 6
  · rw [ite_eq_left g6] at hW
    obtain ⟨hv, -⟩ := stuck _ hW
    exact done _ hW _ (view_forall s₀.mem a₀ hR e hh hv g6).1 rfl
  rw [ite_eq_right g6] at hW
  by_cases g8 : e >>> 28 = 8
  · rw [ite_eq_left g8] at hW
    obtain ⟨hv, -⟩ := stuck _ hW
    obtain ⟨l, hv'⟩ := view_lit s₀.mem a₀ hR e hh hv g8
    exact done _ hW _ hv' rfl
  rw [ite_eq_right g8] at hW
  simp at hW

end step


section loopRef
variable (p : Prog) (hp : WhnfCoreProg p) (hwc : WhnfCallees p) (hcc : CoreCallees p)
  (hsup : ∀ fe : IFEnv, SupKeep fe)

include hp hwc hcc hsup in
/-- **The model of the loop refines `whnfCoreLoop`** at every twin loop fuel `K ≥ k`. -/
theorem coreLoopW_ok (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (mode cheap d : Word)
    (hmode : mode < 4) :
    ∀ k, k ≤ n + 1 → ∀ K, k ≤ K + 1 → ∀ (m m' : Mem) (a : AState) (MM : ModeMaps) (eb e v : Word),
      CoreS dn m a vis fe MM eb → eb = (mode >>> 1) &&& 1 → HW e →
      coreLoopW p k m mode cheap vis d e = some (v, m') →
      CoreRef (whnfCoreLoop (decMode mode) (coreKnot (decMode mode) fe id F) fe (cheap != 0)
        d.toNat K (decE e)) a decH dn m vis fe MM eb [v] m' := by
  intro k
  induction k with
  | zero => intro _ _ _ _ _ _ _ _ _ _ _ _ _ h; simp [coreLoopW] at h
  | succ k ih =>
    intro hkn K hK m m' a MM eb e v hS heb he h
    simp only [coreLoopW] at h
    rcases hc : callW p k "whnf_core_step" [mode, cheap, vis, d, e] m with _ | ⟨r, m₁⟩ <;>
      simp only [hc, reduceCtorEq] at h
    cases k with
    | zero => simp [callW_zero] at hc
    | succ j =>
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    have hstep := whnfCoreStep_refines' p hp hwc hcc hsup j (hk.mono (by omega)) F (by omega) (by omega)
      ⟨m, Locals.init []⟩ a dn vis fe MM eb mode cheap d e ⟨hS, hmode, heb⟩ he
    obtain ⟨hok, hA, hres, hrw⟩ := CoreSpec.of_callW hstep hc
    have hsr := AM.run_of_ok _ _ hok
    rw [hres] at hsr
    by_cases h0 : r.headD 0 = 0
    · rw [ite_eq_left h0] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      simp only [decStep, h0, ↓reduceIte] at hsr
      have hrun := whnfCoreLoop_done (decMode mode) (coreKnot (decMode mode) fe id F) fe
        (cheap != 0) d.toNat K' (decE e) _ a _ hsr
      obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hrun
      exact ⟨hok', hst' ▸ hA, hres', hrw.2⟩
    · rw [ite_eq_right h0] at h
      simp only [decStep, h0, ↓reduceIte] at hsr
      have hrun := whnfCoreLoop_cont (decMode mode) (coreKnot (decMode mode) fe id F) fe
        (cheap != 0) d.toNat K' (decE e) _ a _ hsr
      obtain ⟨M', hS₁, hK₁, hSt₁⟩ := hA
      obtain ⟨hok₂, hA₂, hres₂, hrw₂⟩ := ih (by omega) K' (by omega) m₁ m' _ M' eb _ v hS₁ heb hrw.2 h
      rw [AM.run_of_ok _ _ hok₂] at hrun
      obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hrun
      refine ⟨hok', ?_, hres'.trans hres₂, hrw₂⟩
      rw [hst']
      exact CoreAfter.comp hK₁ hSt₁ hA₂

include hp hwc hcc hsup in
/-- **`whnf_core_loop` refines `whnfCoreLoop` at every twin loop fuel `K ≥ n`.** -/
theorem whnfCoreLoop_refines' (n : Nat) (hk : KnotUpTo p n) (F K : Nat) (hF : n ≤ F) (hK : n ≤ K)
    (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (MM : ModeMaps) (eb mode cheap d e : Word)
    (hs : SlotPre s₀ a₀ dn vis fe MM eb mode) (he : HW e) :
    CoreSpec p (n + 1) "whnf_core_loop" [mode, cheap, vis, d, e]
      (whnfCoreLoop (decMode mode) (coreKnot (decMode mode) fe id F) fe (cheap != 0) d.toNat K
        (decE e)) decH s₀ a₀ dn vis fe MM eb := by
  refine triple_post (whnfCoreLoop_spec p hp n s₀ mode cheap vis d e) fun r s' ⟨hloc, hW⟩ => ⟨hloc,
    ?_⟩
  obtain ⟨hok, hA, hres, hrw⟩ := coreLoopW_ok p hp hwc hcc hsup n hk F hF hn dn vis fe mode cheap d hs.mode4
    (n + 1) (Nat.le_refl _) K (by omega) s₀.mem s'.mem a₀ MM eb e (r.headD 0) hs.rel hs.eb_mode he hW
  exact ⟨hok, hA, hres, hrw⟩

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

section slot
variable (p : Prog) (hp : WhnfCoreProg p) (hwc : WhnfCallees p) (hcc : CoreCallees p)
  (hsup : ∀ fe : IFEnv, SupKeep fe)

include hp hwc hcc hsup in
/-- **The knot's `whnfCore` slot, one level up**: given the knot at every fuel up to `n` (for
the body's callees), `whnf_core` at `n + 1` refines the slot of `coreKnot mode fe id F`,
`F ≥ n + 1`. The body's own refinement is `whnfCoreBody_refines'`. Over the bundles
`WhnfCallees`, `CoreCallees` and `SupKeep` (`DefEqKnot.lean` builds them from real proofs). -/
theorem whnfCoreSlot_step (n : Nat) (hk : KnotUpTo p n) : WhnfCoreSlot p (n + 1) := by
  intro F s₀ a₀ dn vis fe MM eb mode cheap d e hF hn hs he
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  refine triple_post (whnfCore_spec p hp n s₀ mode cheap vis d e) fun r s' ⟨hloc, hW⟩ => ⟨hloc, ?_⟩
  have hS := hs.rel
  have heb := hS.core.eb1
  have hkey : ebKey mode = genW 0 eb := ebKey_eq mode eb hs.eb_mode
  by_cases hst : e >>> 28 ≠ 4 ∧ e >>> 28 ≠ 9 ∧ e >>> 28 ≠ 7 ∧ e >>> 28 ≠ 0
  · rw [whnfCoreW_stuck _ _ _ _ _ _ _ _ hst] at hW
    obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
    have ht : whnfCoreStuckTag (decE e) = true := by rw [stuck_iff e he]; simpa using hst
    obtain ⟨hok, hst', hres⟩ := AM.of_run_ok _ _ _ _ (knot_whnfCore_stuck _ fe F' (cheap != 0) d.toNat _ a₀ ht)
    refine ⟨hok, ?_, by rw [hres, decH, ← hr], by unfold ResH; rw [← hr]; exact he⟩
    rw [hst', ← hm]; exact ⟨MM, hS, KeptAll.refl _ _, StackKept.refl _⟩
  have ht : whnfCoreStuckTag (decE e) = false := by rw [stuck_iff e he]; simpa using hst
  by_cases hc : cheap ≠ 0
  · rw [whnfCoreW_cheap _ _ _ _ _ _ _ _ hst hc, hkey] at hW
    have hcb : (cheap != 0) = true := by simpa using hc
    rw [hcb]
    unfold memoSlotW at hW
    by_cases h0 : mfindG wkSch s₀.mem e (genW 0 eb) = []
    · simp [h0] at hW
    rw [ite_eq_right h0] at hW
    have hf := hS.core.wk.findE heb e he h0
    by_cases h1 : (mfindG wkSch s₀.mem e (genW 0 eb)).headD 0 ≠ 0
    · rw [ite_eq_left h1] at hW
      obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
      obtain ⟨hok, hst', hres⟩ := AM.of_run_ok _ _ _ _
        (knot_whnfCore_hitK _ fe F' d.toNat _ a₀ ht _ (hf.1 h1).1)
      refine ⟨hok, ?_, by rw [hres, decH, ← hr], by unfold ResH; rw [← hr]; exact (hf.1 h1).2⟩
      rw [hst', ← hm]; exact ⟨MM, hS, KeptAll.refl _ _, StackKept.refl _⟩
    rw [ite_eq_right h1] at hW
    have hmiss := hf.2 (by simpa using h1)
    rcases hcall : callW p n "whnf_core_loop" [mode, 1, vis, d, e] s₀.mem with _ | ⟨r₁, m₁⟩ <;>
      simp only [hcall, reduceCtorEq] at hW
    cases n with
    | zero => simp [callW_zero] at hcall
    | succ n' =>
    have hbody := whnfCoreBody_refines' p hp hwc hcc hsup n' (hk.mono (by omega)) F' (by omega) (by omega) s₀ a₀ dn vis
      fe MM eb mode 1 d e hs he
    obtain ⟨hok, ⟨M', hS₁, hK₁, hSt₁⟩, hres, hrw⟩ := CoreSpec.of_callW hbody hcall
    cases hset : msetG wkSch m₁ e (genW 0 eb) (r₁.headD 0) with
    | none => rw [hset] at hW; cases hW
    | some m₂ =>
    rw [hset] at hW
    obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
    obtain ⟨hS₂, hSt₂⟩ := hS₁.set_wk e (r₁.headD 0) he hrw hset
    have hb1 : ((1 : Word) != 0) = true := rfl
    rw [hb1] at hok hres
    have hrun := knot_whnfCore_missK _ fe F' d.toNat _ a₀ ht hmiss _ _ (AM.run_of_ok _ _ hok)
    obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hrun
    refine ⟨hok', ?_, by rw [hres', hres]; simp only [decH, hr],
      by unfold ResH; rw [← hr]; exact hrw⟩
    rw [hst', ← hm, hres]
    exact ⟨_, hS₂, hK₁.wk _ _, hSt₁.trans hSt₂⟩
  · have hc0 : cheap = 0 := by simpa using hc
    rw [whnfCoreW_full _ _ _ _ _ _ _ _ hst hc0, hkey] at hW
    have hcb : (cheap != 0) = false := by simp [hc0]
    rw [hcb]
    unfold memoSlotW at hW
    by_cases h0 : mfindG wcSch s₀.mem e (genW 0 eb) = []
    · simp [h0] at hW
    rw [ite_eq_right h0] at hW
    have hf := hS.core.wc.findE heb e he h0
    by_cases h1 : (mfindG wcSch s₀.mem e (genW 0 eb)).headD 0 ≠ 0
    · rw [ite_eq_left h1] at hW
      obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
      obtain ⟨hok, hst', hres⟩ := AM.of_run_ok _ _ _ _
        (knot_whnfCore_hitF _ fe F' d.toNat _ a₀ ht _ (hf.1 h1).1)
      refine ⟨hok, ?_, by rw [hres, decH, ← hr], by unfold ResH; rw [← hr]; exact (hf.1 h1).2⟩
      rw [hst', ← hm]; exact ⟨MM, hS, KeptAll.refl _ _, StackKept.refl _⟩
    rw [ite_eq_right h1] at hW
    have hmiss := hf.2 (by simpa using h1)
    rcases hcall : callW p n "whnf_core_loop" [mode, 0, vis, d, e] s₀.mem with _ | ⟨r₁, m₁⟩ <;>
      simp only [hcall, reduceCtorEq] at hW
    cases n with
    | zero => simp [callW_zero] at hcall
    | succ n' =>
    have hbody := whnfCoreBody_refines' p hp hwc hcc hsup n' (hk.mono (by omega)) F' (by omega) (by omega) s₀ a₀ dn vis
      fe MM eb mode 0 d e hs he
    obtain ⟨hok, ⟨M', hS₁, hK₁, hSt₁⟩, hres, hrw⟩ := CoreSpec.of_callW hbody hcall
    cases hset : msetG wcSch m₁ e (genW 0 eb) (r₁.headD 0) with
    | none => rw [hset] at hW; cases hW
    | some m₂ =>
    rw [hset] at hW
    obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
    obtain ⟨hS₂, hSt₂⟩ := hS₁.set_wc e (r₁.headD 0) he hrw hset
    have hb0 : ((0 : Word) != 0) = false := rfl
    rw [hb0] at hok hres
    have hrun := knot_whnfCore_missF _ fe F' d.toNat _ a₀ ht hmiss _ _ (AM.run_of_ok _ _ hok)
    obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hrun
    refine ⟨hok', ?_, by rw [hres', hres]; simp only [decH, hr],
      by unfold ResH; rw [← hr]; exact hrw⟩
    rw [hst', ← hm, hres]
    exact ⟨_, hS₂, hK₁.wc _ _, hSt₁.trans hSt₂⟩

end slot

end L.Arena
