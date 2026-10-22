import ConAgua.Arena.WhnfCoreStep

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

section loopRef
variable (p : Prog) (hp : WhnfCoreProg p)

include hp in
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
    cases hc : callW p k "whnf_core_step" [mode, cheap, vis, d, e] m with
    | none => simp [hc] at h
    | some q =>
    obtain ⟨r, m₁⟩ := q
    simp only [hc] at h
    cases k with
    | zero => simp [callW_zero] at hc
    | succ j =>
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    have hstep := whnfCoreStep_refines p hp j (hk.mono (by omega)) F (by omega) (by omega)
      ⟨m, Locals.init []⟩ a dn vis fe MM eb mode cheap d e ⟨hS, hmode, heb⟩ he
    obtain ⟨hok, hA, hres, hrw⟩ := CoreSpec.of_callW hstep hc
    have hsr := AM.run_of_ok _ _ hok
    rw [hres] at hsr
    by_cases h0 : r.headD 0 = 0
    · rw [if_pos h0] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [decStep, h0, ↓reduceIte] at hsr
      have hrun := whnfCoreLoop_done (decMode mode) (coreKnot (decMode mode) fe id F) fe
        (cheap != 0) d.toNat K' (decE e) _ a _ hsr
      obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hrun
      exact ⟨hok', hst' ▸ hA, hres', hrw.2⟩
    · rw [if_neg h0] at h
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

include hp in
/-- **`whnf_core_loop` refines `whnfCoreLoop` at every twin loop fuel `K ≥ n`.** -/
@[refines ConRon.Arena.whnfCoreLoop]
theorem whnfCoreLoop_refines (n : Nat) (hk : KnotUpTo p n) (F K : Nat) (hF : n ≤ F) (hK : n ≤ K)
    (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (MM : ModeMaps) (eb mode cheap d e : Word)
    (hs : SlotPre s₀ a₀ dn vis fe MM eb mode) (he : HW e) :
    CoreSpec p (n + 1) "whnf_core_loop" [mode, cheap, vis, d, e]
      (whnfCoreLoop (decMode mode) (coreKnot (decMode mode) fe id F) fe (cheap != 0) d.toNat K
        (decE e)) decH s₀ a₀ dn vis fe MM eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (whnfCoreLoop_spec p hp n s₀ mode cheap vis d e)
  subst hs0
  refine ⟨hloc, ?_⟩
  obtain ⟨hok, hA, hres, hrw⟩ := coreLoopW_ok p hp n hk F hF hn dn vis fe mode cheap d hs.mode4
    (n + 1) (Nat.le_refl _) K (by omega) s.mem s'.mem a₀ MM eb e (r.headD 0) hs.rel hs.eb_mode he hW
  exact ⟨hok, hA, hres, hrw⟩

include hp in
/-- **`whnf_core_loop` refines `whnfCoreBody`** (the loop at `whnfCoreLoopFuel = 2^62`). -/
@[refines ConRon.Arena.whnfCoreBody]
theorem whnfCoreBody_refines (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (MM : ModeMaps) (eb mode cheap d e : Word)
    (hs : SlotPre s₀ a₀ dn vis fe MM eb mode) (he : HW e) :
    CoreSpec p (n + 1) "whnf_core_loop" [mode, cheap, vis, d, e]
      (whnfCoreBody (decMode mode) (coreKnot (decMode mode) fe id F) fe (cheap != 0) d.toNat
        (decE e)) decH s₀ a₀ dn vis fe MM eb :=
  whnfCoreLoop_refines p hp n hk F whnfCoreLoopFuel hF (by simp only [whnfCoreLoopFuel]; omega) hn s₀
    a₀ dn vis fe MM eb mode cheap d e hs he

end loopRef

section slot
variable (p : Prog) (hp : WhnfCoreProg p)

include hp in
/-- **The knot's `whnfCore` slot, one level up**: given the knot at every fuel up to `n` (for
the body's callees), `whnf_core` at `n + 1` refines the slot of `coreKnot mode fe id F`,
`F ≥ n + 1`. The body's own refinement is `whnfCoreBody_refines`. -/
theorem whnfCoreSlot_step (n : Nat) (hk : KnotUpTo p n) : WhnfCoreSlot p (n + 1) := by
  intro F s₀ a₀ dn vis fe MM eb mode cheap d e hF hn hs he
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (whnfCore_spec p hp n s₀ mode cheap vis d e)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hS := hs.rel
  have heb := hS.core.eb1
  have hkey : ebKey mode = genW 0 eb := ebKey_eq mode eb hs.eb_mode
  by_cases hst : e >>> 28 ≠ 4 ∧ e >>> 28 ≠ 9 ∧ e >>> 28 ≠ 7 ∧ e >>> 28 ≠ 0
  · rw [whnfCoreW_stuck _ _ _ _ _ _ _ _ hst] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
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
    by_cases h0 : mfindG wkSch s.mem e (genW 0 eb) = []
    · simp [h0] at hW
    rw [if_neg h0] at hW
    have hf := hS.core.wk.findE heb e he h0
    by_cases h1 : (mfindG wkSch s.mem e (genW 0 eb)).headD 0 ≠ 0
    · rw [if_pos h1] at hW
      simp only [Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨hr, hm⟩ := hW
      obtain ⟨hok, hst', hres⟩ := AM.of_run_ok _ _ _ _
        (knot_whnfCore_hitK _ fe F' d.toNat _ a₀ ht _ (hf.1 h1).1)
      refine ⟨hok, ?_, by rw [hres, decH, ← hr], by unfold ResH; rw [← hr]; exact (hf.1 h1).2⟩
      rw [hst', ← hm]; exact ⟨MM, hS, KeptAll.refl _ _, StackKept.refl _⟩
    rw [if_neg h1] at hW
    have hmiss := hf.2 (by simpa using h1)
    cases hcall : callW p n "whnf_core_loop" [mode, 1, vis, d, e] s.mem with
    | none => simp [hcall] at hW
    | some q =>
    obtain ⟨r₁, m₁⟩ := q
    simp only [hcall] at hW
    cases n with
    | zero => simp [callW_zero] at hcall
    | succ n' =>
    have hbody := whnfCoreBody_refines p hp n' (hk.mono (by omega)) F' (by omega) (by omega) s a₀ dn vis
      fe MM eb mode 1 d e hs he
    obtain ⟨hok, ⟨M', hS₁, hK₁, hSt₁⟩, hres, hrw⟩ := CoreSpec.of_callW hbody hcall
    cases hset : msetG wkSch m₁ e (genW 0 eb) (r₁.headD 0) with
    | none => rw [hset] at hW; cases hW
    | some m₂ =>
    rw [hset] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
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
    by_cases h0 : mfindG wcSch s.mem e (genW 0 eb) = []
    · simp [h0] at hW
    rw [if_neg h0] at hW
    have hf := hS.core.wc.findE heb e he h0
    by_cases h1 : (mfindG wcSch s.mem e (genW 0 eb)).headD 0 ≠ 0
    · rw [if_pos h1] at hW
      simp only [Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨hr, hm⟩ := hW
      obtain ⟨hok, hst', hres⟩ := AM.of_run_ok _ _ _ _
        (knot_whnfCore_hitF _ fe F' d.toNat _ a₀ ht _ (hf.1 h1).1)
      refine ⟨hok, ?_, by rw [hres, decH, ← hr], by unfold ResH; rw [← hr]; exact (hf.1 h1).2⟩
      rw [hst', ← hm]; exact ⟨MM, hS, KeptAll.refl _ _, StackKept.refl _⟩
    rw [if_neg h1] at hW
    have hmiss := hf.2 (by simpa using h1)
    cases hcall : callW p n "whnf_core_loop" [mode, 0, vis, d, e] s.mem with
    | none => simp [hcall] at hW
    | some q =>
    obtain ⟨r₁, m₁⟩ := q
    simp only [hcall] at hW
    cases n with
    | zero => simp [callW_zero] at hcall
    | succ n' =>
    have hbody := whnfCoreBody_refines p hp n' (hk.mono (by omega)) F' (by omega) (by omega) s a₀ dn vis
      fe MM eb mode 0 d e hs he
    obtain ⟨hok, ⟨M', hS₁, hK₁, hSt₁⟩, hres, hrw⟩ := CoreSpec.of_callW hbody hcall
    cases hset : msetG wcSch m₁ e (genW 0 eb) (r₁.headD 0) with
    | none => rw [hset] at hW; cases hW
    | some m₂ =>
    rw [hset] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
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
