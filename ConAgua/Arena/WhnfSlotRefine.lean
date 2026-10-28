import ConAgua.Verdict.WhnfNatE
import ConAgua.Arena.WhnfDeltaSlot
import ConAgua.Arena.WhnfCoreLoop

/-!
# The knot's `whnf` slot: `whnf_step`, `whnf_loop`, `whnf`, both outcomes

One refinement per function over its unified model (`Verdict/WhnfModelsE.lean`): `wstep_ref`
(the `whnf_core` slot through its run, `reduce_nat` through its unified model, `unfold_definition`
lifted), `wloop_ref` (each iteration `whnf_step`'s unified model), `whnf_ref` (the mode memo around
the loop). The errors are the knot's slots' (`KnotUpToE`). The ok halves are the knot's interfaces
(`WhnfStepSpec'`, `WhnfLoopSpec`, `WhnfSlot`), the error half `WhnfSlotE` (`whnfSlot_stepE`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

theorem whnfLoop_err (r : CoreFnsA) (fe : IFEnv) (d K : Nat) (e : EIdx) (a : AState)
    (ce : CheckError) (hs : (whnfStep r fe d e).run a = .error ce) :
    (whnfLoop r fe d (K + 1) e).run a = .error ce := by
  simp only [whnfLoop, StateT.run_bind, hs]; rfl

theorem knot_whnf_miss_err (mode : ConLeche.CheckMode) (fe : IFEnv) (F : Nat) (d : Nat) (e : EIdx)
    (a : AState) (h : whnfStuckTag e = false) (hm : a.caches.whnfC[e]? = none) (ce : CheckError)
    (hb : (whnfBody (coreKnot mode fe id F) fe d e).run a = .error ce) :
    ((coreKnot mode fe id (F + 1)).whnf d e).run a = .error ce := by
  simp [coreKnot, h, hm, StateT.run_bind, hb]; try rfl

section refs
variable (p : Prog) (hp : WhnfDeltaProg' p) (hno : NatOpResultOK p) (hlp : InstLPOK p)

include hp hno hlp in
/-- **`whnf_step` refines `whnfStep`, both outcomes**: the errors are the `whnf_core` slot's and
`reduce_nat`'s. -/
theorem wstep_ref (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d e : Word) (hs : SlotPre s₀ a₀ dn vis fe MM eb mode) (he : HW e) :
    RefE (KnotUpToE p n) (whnfStepE p (n + 1) s₀.mem mode vis d e)
      (whnfStep (coreKnot (decMode mode) fe id F) fe d.toNat (decE e)) a₀
      (CorePost decStep dn s₀.mem vis fe MM eb ResW) := by
  have hs' : SlotPre ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe MM eb mode := ⟨hs.rel, hs.mode4, hs.eb_mode⟩
  have hW1 := (hk n (Nat.le_refl _)).whnfCore F _ a₀ dn vis fe MM eb mode 0 d e hF hn hs' he
  rw [show ((0 : Word) != 0) = false from rfl] at hW1
  have hE1 : KnotUpToE p n → CoreSpecE p n "whnf_core" [mode, 0, vis, d, e]
      ((coreKnot (decMode mode) fe id F).whnfCore false d.toNat (decE e)) ⟨s₀.mem, Locals.init []⟩ a₀ :=
    fun hG => by
      have h := (hG n (Nat.le_refl _)).whnfCore F _ a₀ dn vis fe MM eb mode 0 d e hF hn hs' he
      rwa [show ((0 : Word) != 0) = false from rfl] at h
  simp only [whnfStepE]
  unfold whnfStep
  refine RefE.bind_callE (s₀ := ⟨s₀.mem, Locals.init []⟩) (x := whnfStepE.k_whnf_core p n mode vis d)
    (fun _ => rfl) hW1 hE1 (fun r₁ m₁ _ h1 => ?_)
  obtain ⟨-, ⟨M₁, hS₁, hK₁, hSt₁⟩, -, hrw₁⟩ := h1
  simp only [whnfStepE.k_whnf_core]
  have h2 := reduceNat_ref p hp hno n F hF hn hk ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode d
    (r₁.headD 0) ⟨hS₁, hs.mode4, hs.eb_mode⟩ hrw₁
  rcases c2 : reduceNatE p n m₁ mode vis d (r₁.headD 0) with e2 | ⟨r₂, m₂⟩
  · rw [c2] at h2; exact RefE.bind_left h2
  rw [c2] at h2
  obtain ⟨y2, a2, hrun2, ⟨⟨M₂, hS₂, hK₂, hSt₂⟩, hy2, hrw₂⟩⟩ := h2
  refine RefE.bind_right hrun2 ?_
  subst hy2
  simp only [whnfStepE.k_reduce_nat]
  by_cases hf2 : r₂.headD 0 ≠ 0
  · rw [ite_eq_left hf2]
    have hsome : decOptR r₂ = some (decE (r₂.tail.headD 0)) := by
      simp only [decOptR, decOpt, ite_eq_right hf2]
    rw [hsome]
    exact RefE.ret rfl ⟨⟨M₂, hS₂, hK₁.trans hK₂, hSt₁.trans hSt₂⟩, by simp [decStep],
      ⟨by show HW (1 : Word); unfold HW; decide, hrw₂.2⟩⟩
  rw [ite_eq_right hf2]
  have hnone : decOptR r₂ = none := by
    simp only [decOptR, decOpt]; rw [ite_eq_left (by simpa using hf2)]
  rw [hnone]
  rcases h3 : callW p n "unfold_definition" [vis, r₁.headD 0] m₂ with _ | ⟨r₃, m₃⟩
  · rw [liftE_none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨hok3, ⟨M₃, hS₃, hK₃, hSt₃⟩, hres3, hrw3⟩ := CoreSpec.of_callW (s₀ := ⟨m₂, Locals.init []⟩)
    (unfoldDefinition_refines' p hp n _ a2 dn vis fe M₂ eb (r₁.headD 0) hS₂ hrw₁ hlp) h3
  have hrun3 := AM.run_of_ok _ _ hok3
  rw [hres3] at hrun3
  refine RefE.bind_right hrun3 ?_
  simp only [whnfStepE.k_unfold_definition]
  by_cases hf3 : r₃.headD 0 ≠ 0
  · rw [ite_eq_left hf3]
    have hsome : decOptR r₃ = some (decE (r₃.tail.headD 0)) := by
      simp only [decOptR, decOpt, ite_eq_right hf3]
    rw [hsome]
    exact RefE.ret rfl ⟨⟨M₃, hS₃, (hK₁.trans hK₂).trans hK₃, (hSt₁.trans hSt₂).trans hSt₃⟩,
      by simp [decStep], ⟨by show HW (1 : Word); unfold HW; decide, hrw3.2⟩⟩
  rw [ite_eq_right hf3]
  have hnone3 : decOptR r₃ = none := by
    simp only [decOptR, decOpt]; rw [ite_eq_left (by simpa using hf3)]
  rw [hnone3]
  exact RefE.ret rfl ⟨⟨M₃, hS₃, (hK₁.trans hK₂).trans hK₃, (hSt₁.trans hSt₂).trans hSt₃⟩,
    by simp [decStep, decH], ⟨by show HW (0 : Word); unfold HW; decide, hrw₁⟩⟩

include hp hno hlp in
/-- **The loop refines `whnfLoop`, both outcomes**, at every twin loop fuel `K ≥ k`: each
iteration is `whnf_step`'s (`wstep_ref`). -/
theorem wloop_ref (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (mode d : Word) (hmode : mode < 4) :
    ∀ k, k ≤ n + 1 → ∀ K, k ≤ K → ∀ (m : Mem) (a : AState) (MM : ModeMaps) (eb e : Word),
      CoreS dn m a vis fe MM eb → eb = (mode >>> 1) &&& 1 → HW e →
      RefE (KnotUpToE p n) (whnfLoopE.loop1 p k m mode vis d e)
        (whnfLoop (coreKnot (decMode mode) fe id F) fe d.toNat K (decE e)) a
        (fun v y a' => CorePost decH dn m vis fe MM eb ResH ([v.1], v.2) y a') := by
  intro k
  induction k with
  | zero =>
    intro _ _ _ _ _ _ _ _ _ _ _
    simp only [whnfLoopE.loop1]; exact RefE.of_cls0 rfl
  | succ k ih =>
    intro hkn K hK m a MM eb e hS heb he
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    simp only [whnfLoopE.loop1, ite_true]
    cases k with
    | zero => simp only [whnfStepE, whnfLoopE.k_whnf_step]; exact RefE.of_cls0 rfl
    | succ j =>
    have h1 := wstep_ref p hp hno hlp j (hk.mono (by omega)) F (by omega) (by omega)
      ⟨m, Locals.init []⟩ a dn vis fe MM eb mode d e ⟨hS, hmode, heb⟩ he
    rcases c1 : whnfStepE p (j + 1) m mode vis d e with e1 | ⟨r, m₁⟩
    · rw [c1] at h1
      simp only [whnfLoopE.k_whnf_step]
      exact fun hG => ErrClaim.of_run_eq (fun ce h' => whnfLoop_err _ fe d.toNat K' _ a ce h')
        (h1 (hG.mono (by omega)))
    rw [c1] at h1
    obtain ⟨y, a1, hrun, ⟨⟨M', hS₁, hK₁, hSt₁⟩, hy, hrw⟩⟩ := h1
    rw [hy] at hrun
    simp only [whnfLoopE.k_whnf_step]
    by_cases h0 : r.headD 0 = 0
    · rw [ite_eq_left h0]
      simp only [decStep, h0, ↓reduceIte] at hrun
      exact RefE.ret (whnfLoop_done _ fe d.toNat K' (decE e) _ a _ hrun) ⟨⟨M', hS₁, hK₁, hSt₁⟩, rfl, hrw.2⟩
    rw [ite_eq_right h0]
    simp only [decStep, h0, ↓reduceIte] at hrun
    exact RefE.of_run_eq (whnfLoop_cont _ fe d.toNat K' (decE e) _ a _ hrun)
      ((ih (by omega) K' (by omega) m₁ _ M' eb _ hS₁ heb hrw.2).mono
        fun _ _ _ h => ⟨CoreAfter.comp hK₁ hSt₁ h.after, h.res, h.valid⟩)

include hp hno hlp in
/-- **`whnf` at `n + 1` refines the knot's `whnf` slot of `coreKnot mode fe id F`, both
outcomes**, `F ≥ n + 1`: a stuck tag answers itself, a memo hit its entry, a miss the body's
answer (`whnf_loop` at `n`, its unified model), recorded. -/
theorem whnf_ref (n : Nat) (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb mode d e : Word)
    (hF : n + 1 ≤ F) (hn : n + 1 ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe MM eb mode) (he : HW e) :
    RefE (KnotUpToE p n) (whnfE p (n + 1) s₀.mem mode vis d e)
      ((coreKnot (decMode mode) fe id F).whnf d.toNat (decE e)) a₀
      (CorePost decH dn s₀.mem vis fe MM eb ResH) := by
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  have hS := hs.rel
  have heb := hS.core.eb1
  have hkey : ((mode >>> 1) &&& 1) <<< 32 = genW 0 eb := ebKey_eq mode eb hs.eb_mode
  simp only [whnfE]
  by_cases hst : e >>> 28 = 2 ∨ e >>> 28 = 1 ∨ e >>> 28 = 5 ∨ e >>> 28 = 6 ∨ e >>> 28 = 8
  · rw [ite_eq_left hst]
    have ht : whnfStuckTag (decE e) = true := by rw [whnfStuck_iff e he]; simpa using hst
    exact RefE.ret (knot_whnf_stuck _ fe F' d.toNat _ a₀ ht) (CorePost.ret hS rfl he)
  rw [ite_eq_right hst]
  have ht : whnfStuckTag (decE e) = false := by rw [whnfStuck_iff e he]; simpa using hst
  rcases h1 : callW p n "wh_find" [e, ((mode >>> 1) &&& 1) <<< 32] s₀.mem with _ | ⟨r₁, m₁⟩
  · rw [liftE_none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨rfl, hne, hr⟩ := callW_memoFind hp.whFind h1
  rw [hkey] at hr
  subst hr
  have hf := hS.core.wh.findE heb e he hne
  simp only [whnfE.k_wh_find]
  by_cases h1' : (mfindG whSch s₀.mem e (genW 0 eb)).headD 0 ≠ 0
  · rw [ite_eq_left h1']
    exact RefE.ret (knot_whnf_hit _ fe F' d.toNat _ a₀ ht _ (hf.1 h1').1)
      (CorePost.ret hS rfl (hf.1 h1').2)
  rw [ite_eq_right h1']
  have hmiss := hf.2 (by simpa using h1')
  cases n with
  | zero => simp only [whnfLoopE, whnfE.k_whnf_loop]; exact RefE.of_cls0 rfl
  | succ n' =>
  have h2 := wloop_ref p hp hno hlp n' (hk.mono (by omega)) F' (by omega) (by omega) dn vis fe mode d
    hs.mode4 (n' + 1) (Nat.le_refl _) whnfLoopFuel (by simp only [whnfLoopFuel]; omega) s₀.mem a₀ MM eb
    e hS hs.eb_mode he
  rcases c2 : whnfLoopE p (n' + 1) s₀.mem mode vis d e with e2 | ⟨x, m₂⟩
  · simp only [whnfLoopE] at c2
    rw [c2] at h2
    exact fun hG => ErrClaim.of_run_eq (fun ce h' => knot_whnf_miss_err _ fe F' d.toNat _ a₀ ht hmiss ce h')
      (h2 (hG.mono (by omega)))
  simp only [whnfLoopE] at c2
  rw [c2] at h2
  obtain ⟨y, a1, hrun, ⟨⟨M', hS₁, hK₁, hSt₁⟩, hy, hrw⟩⟩ := h2
  simp only [whnfE.k_whnf_loop]
  rcases h3 : callW p (n' + 1) "wh_find" [e, ((mode >>> 1) &&& 1) <<< 32] m₂ with _ | ⟨r₃, m₃⟩
  · rw [liftE_none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  simp only [whnfE.k_wh_find_2]
  rcases h4 : callW p (n' + 1) "wh_put" [e, ((mode >>> 1) &&& 1) <<< 32, x, r₃.headD 0,
      r₃.tail.headD 0] m₃ with _ | ⟨r₄, m₄⟩
  · rw [liftE_none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  simp only [whnfE.k_wh_put]
  have hset := callW_memoSet hp.whFind hp.whPut h3 h4
  rw [hkey] at hset
  obtain ⟨hS₂, hSt₂⟩ := hS₁.set_wh e x he hrw hset
  have hrun' := knot_whnf_miss _ fe F' d.toNat _ a₀ ht hmiss _ _ hrun
  rw [hy] at hrun'
  exact RefE.ret hrun' ⟨⟨_, hS₂, hK₁.wh _ _, hSt₁.trans hSt₂⟩, rfl, hrw⟩

end refs

/-! ## The halves -/

section halves
variable (p : Prog) (hp : WhnfDeltaProg' p) (hlp : InstLPOK p)

include hp hlp in
/-- **`whnf_step` refines `whnfStep`** (`wstep_ref`'s ok half). -/
theorem whnfStep_refines' (hno : NatOpResultOK p) (n : Nat) : WhnfStepSpec' p n := by
  intro F s₀ a₀ dn vis fe MM eb mode d e hF hn hs he hk
  cases n with
  | zero =>
    exact RefE.coreSpec (G := True) (whnfStepE_spec p hp.toWhnfDeltaProg 0 s₀ mode vis d e)
      (RefE.of_cls0 rfl)
  | succ n =>
  exact RefE.coreSpec (whnfStepE_spec p hp.toWhnfDeltaProg (n + 1) s₀ mode vis d e)
    (wstep_ref p hp hno hlp n (hk.mono (by omega)) F (by omega) (by omega) s₀ a₀ dn vis fe MM eb mode
      d e hs he)

include hp hlp in
/-- **`whnf_loop` refines `whnfLoop`** (`wloop_ref`'s ok half), under the knot's fuel bound. -/
@[refines ConRon.Arena.whnfBody]
theorem whnfLoop_refines (hno : NatOpResultOK p) (n : Nat) (hn : n ≤ 2 ^ 62) : WhnfLoopSpec p n := by
  intro F K s₀ a₀ dn vis fe MM eb mode d e hF hK hs he hk
  cases n with
  | zero =>
    exact CoreSpec.of_refE (G := True) (w := fun v => ([v.1], v.2))
      (whnfLoopE_spec p hp.toWhnfDeltaProg 0 s₀ mode vis d e) (RefE.of_cls0 rfl)
      fun _ _ => ⟨rfl, rfl, id⟩
  | succ n =>
  exact CoreSpec.of_refE (w := fun v => ([v.1], v.2))
    (whnfLoopE_spec p hp.toWhnfDeltaProg (n + 1) s₀ mode vis d e)
    (wloop_ref p hp hno hlp n (hk.mono (by omega)) F (by omega) (by omega) dn vis fe mode d hs.mode4
      (n + 1) (Nat.le_refl _) K hK s₀.mem a₀ MM eb e hs.rel hs.eb_mode he)
    fun _ _ => ⟨rfl, rfl, id⟩

include hp hlp in
/-- **`whnf` refines the knot's `whnf` slot** (`whnf_ref`'s ok half): `WhnfSlot p (n + 1)` from
`KnotUpTo p n`. -/
theorem whnf_refines (hno : NatOpResultOK p) (n : Nat) (hk : KnotUpTo p n) : WhnfSlot p (n + 1) :=
  fun F s₀ a₀ dn vis fe MM eb mode d e hF hn hs he =>
    RefE.coreSpec (whnfE_spec p hp.toWhnfDeltaProg (n + 1) s₀ mode vis d e)
      (whnf_ref p hp hno hlp n hk F s₀ a₀ dn vis fe MM eb mode d e hF hn hs he)

include hp hlp in
/-- **The knot's `whnf` slot's verdicts, one level up** (`whnf_ref`'s error half). -/
theorem whnfSlot_stepE (hno : NatOpResultOK p) (hnv : closedNV p L.Checker.nvFns = true) (n : Nat)
    (hk : KnotUpTo p n) (hkE : KnotUpToE p n) : WhnfSlotE p (n + 1) :=
  fun F s₀ a₀ dn vis fe MM eb mode d e hF hn hs he =>
    RefE.coreSpecE (whnfE_spec p hp.toWhnfDeltaProg (n + 1) s₀ mode vis d e) hnv hkE
      (whnf_ref p hp hno hlp n hk F s₀ a₀ dn vis fe MM eb mode d e hF hn hs he)

end halves

end L.Arena
