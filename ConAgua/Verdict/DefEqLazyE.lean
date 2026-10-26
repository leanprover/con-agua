import ConAgua.Verdict.DefEqLoopsE

/-!
# The lazy-delta step's error claims (lane `verdicts-b`, helper `k3`)

The error halves of `DefEqMidLazy.lean`: `lds_left`, `lds_right`, `lds_unfold2`, `lds_same`,
`lds_both`, `lazy_delta_step`. Each follows its ok proof over the generated error model; the
callees outside this family are hypotheses in their ok refinements' shapes (`DeltaQuickE`,
`TryUnfoldProjAppE`: the whnf family's; `DefeqSpineE`: this family's, `DefEqSpineE.lean`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.deprecated false

namespace L.Arena

/-! ## The callees' error specs -/

/-- **`delta_quick`'s error spec** (whnf family; the error half of `deltaQuick_refines`). -/
def DeltaQuickE (p : Prog) : Prop :=
  ∀ (n : Nat), KnotUpTo p n → KnotUpToE p n → ∀ (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word),
    n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe M eb mode → HW a → HW b → d.toNat < 2 ^ 63 →
    CoreSpecE p (n + 1) "delta_quick" [mode, vis, d, a, b]
      (deltaQuick (decMode mode) (coreKnot (decMode mode) fe id F) d.toNat (decE a) (decE b)) s₀ a₀

/-- **`try_unfold_proj_app`'s error spec** (whnf family; the error half of
`tryUnfoldProjApp_refines`). -/
def TryUnfoldProjAppE (p : Prog) : Prop :=
  ∀ (n : Nat), KnotUpTo p n → KnotUpToE p n → ∀ (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d e : Word),
    n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe M eb mode → HW e →
    CoreSpecE p (n + 1) "try_unfold_proj_app" [mode, vis, d, e]
      (tryUnfoldProjApp (coreKnot (decMode mode) fe id F) d.toNat (decE e)) s₀ a₀

/-- **`defeq_spine`'s error spec** (the error half of `defeqSpine_refines`). -/
def DefeqSpineE (p : Prog) : Prop :=
  ∀ (n : Nat), KnotUpTo p n → KnotUpToE p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
  ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d a b : Word), SlotPre s₀ a₀ dn vis fe M eb mode → HW a → HW b →
    CoreSpecE p (n + 1) "defeq_spine" [mode, vis, d, a, b]
      (defeqSpine (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) s₀ a₀

/-- The one-side unfoldings' error spec (`lds_left` at `left`, `lds_right` else). -/
def LdsOneE (p : Prog) (f : FnName) (left : Bool) : Prop :=
  ∀ (n : Nat), KnotUpTo p n → KnotUpToE p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
  ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d a b : Word), SlotPre s₀ a₀ dn vis fe M eb mode → HW a → HW b →
    d.toNat < 2 ^ 63 →
    CoreSpecE p (n + 1) f [mode, vis, d, a, b]
      (ldsOneT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat left (decE a) (decE b)) s₀ a₀

/-! ## `lds_left`, `lds_right` -/

l_model ldsLeft_specE (p : Prog) (hf : p.lookup "lds_left" = some ldsLeftL)
  fns [hf ↦ ldsLeftE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

l_model ldsRight_specE (p : Prog) (hf : p.lookup "lds_right" = some ldsRightL)
  fns [hf ↦ ldsRightE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

/-- **`lds_left`'s error claim**. -/
theorem ldsLeft_refinesE (p : Prog) (hp : LazyProg p) (hc : LazyCallees p) (hdqE : DeltaQuickE p)
    (hnv : closedNV p L.Checker.nvFns = true) : LdsOneE p "lds_left" true := by
  intro n hk hkE F hF hn s₀ a₀ dn vis fe M eb mode d a b hs ha hb hd
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hkc : er.cls = 0
  · exact ErrClaim.of_cls0 hkc
  have hW := triple_of_callE_err (ldsLeft_specE p hp.left (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d a b) hc0 (Err.code_ne_of_cls hkc)
  rw [ldsLeftE.arm1] at hW
  have hS := hs.rel
  unfold ldsOneT
  simp only [↓reduceIte]
  cases h1 : callE p n "unfold_definition" [vis, a] s₀.mem with
  | error e =>
    rw [h1, ldsLeftE.k_unfold_definition.none] at hW; cases hW
    exact ErrClaim.of_nv hnv (by simp [defeqNVList]) h1
  | ok q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [h1] at hW
  simp only [ldsLeftE.k_unfold_definition] at hW
  have e₁ := CoreSpec.of_callW (hc.unfold n ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe M eb a hS ha)
    (callW_of_callE h1)
  refine ErrClaim.bind_core e₁ (fun M₁ hS₁ => ?_)
  by_cases h0 : r₁.headD 0 = 0
  · rw [if_pos h0] at hW; cases hW
  rw [if_neg h0] at hW
  rw [decOptR_some h0]
  cases h2 : callE p n "whnf_core" [mode, 1, vis, d, r₁.tail.headD 0] m₁ with
  | error e =>
    rw [h2, ldsLeftE.k_whnf_core.none] at hW; cases hW
    exact ErrClaim.bind_left (CoreSpecE.of_callE (s₀ := ⟨m₁, Locals.init []⟩)
      ((hkE n (Nat.le_refl _)).whnfCore F _ _ dn vis fe M₁ eb mode 1 d _ hF hn
        ⟨hS₁, hs.mode4, hs.eb_mode⟩ e₁.2.2.2.2) h2)
  | ok q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [h2] at hW
  simp only [ldsLeftE.k_whnf_core] at hW
  have e₂ := CoreSpec.of_callW ((hk n (Nat.le_refl _)).whnfCore F ⟨m₁, Locals.init []⟩ _ dn vis fe M₁
    eb mode 1 d _ hF hn ⟨hS₁, hs.mode4, hs.eb_mode⟩ e₁.2.2.2.2) (callW_of_callE h2)
  refine ErrClaim.bind_core e₂ (fun M₂ hS₂ => ?_)
  have h3 := tailE (ldsLeftE.k_delta_quick.none p) (fun ⟨_, _⟩ => ⟨_, rfl⟩) hW
  refine ErrClaim.of_callE_succ h3 fun j hj h' => ?_
  subst hj
  exact CoreSpecE.of_callE (s₀ := ⟨m₂, Locals.init []⟩) (hdqE j (hk.mono (by omega))
    (hkE.mono (by omega)) F _ _ dn vis fe M₂ eb mode d _ b (by omega) (by omega)
    ⟨hS₂, hs.mode4, hs.eb_mode⟩ e₂.2.2.2 hb hd) h'

/-- **`lds_right`'s error claim**. -/
theorem ldsRight_refinesE (p : Prog) (hp : LazyProg p) (hc : LazyCallees p) (hdqE : DeltaQuickE p)
    (hnv : closedNV p L.Checker.nvFns = true) : LdsOneE p "lds_right" false := by
  intro n hk hkE F hF hn s₀ a₀ dn vis fe M eb mode d a b hs ha hb hd
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hkc : er.cls = 0
  · exact ErrClaim.of_cls0 hkc
  have hW := triple_of_callE_err (ldsRight_specE p hp.right (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d a b) hc0 (Err.code_ne_of_cls hkc)
  rw [ldsRightE.arm1] at hW
  have hS := hs.rel
  unfold ldsOneT
  simp only [Bool.false_eq_true, ↓reduceIte]
  cases h1 : callE p n "unfold_definition" [vis, b] s₀.mem with
  | error e =>
    rw [h1, ldsRightE.k_unfold_definition.none] at hW; cases hW
    exact ErrClaim.of_nv hnv (by simp [defeqNVList]) h1
  | ok q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [h1] at hW
  simp only [ldsRightE.k_unfold_definition] at hW
  have e₁ := CoreSpec.of_callW (hc.unfold n ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe M eb b hS hb)
    (callW_of_callE h1)
  refine ErrClaim.bind_core e₁ (fun M₁ hS₁ => ?_)
  by_cases h0 : r₁.headD 0 = 0
  · rw [if_pos h0] at hW; cases hW
  rw [if_neg h0] at hW
  rw [decOptR_some h0]
  cases h2 : callE p n "whnf_core" [mode, 1, vis, d, r₁.tail.headD 0] m₁ with
  | error e =>
    rw [h2, ldsRightE.k_whnf_core.none] at hW; cases hW
    exact ErrClaim.bind_left (CoreSpecE.of_callE (s₀ := ⟨m₁, Locals.init []⟩)
      ((hkE n (Nat.le_refl _)).whnfCore F _ _ dn vis fe M₁ eb mode 1 d _ hF hn
        ⟨hS₁, hs.mode4, hs.eb_mode⟩ e₁.2.2.2.2) h2)
  | ok q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [h2] at hW
  simp only [ldsRightE.k_whnf_core] at hW
  have e₂ := CoreSpec.of_callW ((hk n (Nat.le_refl _)).whnfCore F ⟨m₁, Locals.init []⟩ _ dn vis fe M₁
    eb mode 1 d _ hF hn ⟨hS₁, hs.mode4, hs.eb_mode⟩ e₁.2.2.2.2) (callW_of_callE h2)
  refine ErrClaim.bind_core e₂ (fun M₂ hS₂ => ?_)
  have h3 := tailE (ldsRightE.k_delta_quick.none p) (fun ⟨_, _⟩ => ⟨_, rfl⟩) hW
  refine ErrClaim.of_callE_succ h3 fun j hj h' => ?_
  subst hj
  exact CoreSpecE.of_callE (s₀ := ⟨m₂, Locals.init []⟩) (hdqE j (hk.mono (by omega))
    (hkE.mono (by omega)) F _ _ dn vis fe M₂ eb mode d a _ (by omega) (by omega)
    ⟨hS₂, hs.mode4, hs.eb_mode⟩ ha e₂.2.2.2 hd) h'

end L.Arena
