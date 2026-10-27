import ConAgua.Verdict.DefEqTailE

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
  · rw [ite_eq_left h0] at hW; cases hW
  rw [ite_eq_right h0] at hW
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
  · rw [ite_eq_left h0] at hW; cases hW
  rw [ite_eq_right h0] at hW
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

/-! ## `lds_unfold2`, `lds_same` -/

namespace L.Arena

l_model ldsUnfold2_specE (p : Prog) (hf : p.lookup "lds_unfold2" = some ldsUnfold2L)
  fns [hf ↦ ldsUnfold2E] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

/-- **`lds_unfold2`'s error spec** (the error half of `ldsUnfold2_refines`). -/
def LdsUnfold2E (p : Prog) : Prop :=
  ∀ (n : Nat), KnotUpTo p n → KnotUpToE p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
  ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d a b : Word), SlotPre s₀ a₀ dn vis fe M eb mode → HW a → HW b →
    d.toNat < 2 ^ 63 →
    CoreSpecE p (n + 1) "lds_unfold2" [mode, vis, d, a, b]
      (unfold2T (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) s₀ a₀

/-- **`lds_unfold2`'s error claim**. -/
theorem ldsUnfold2_refinesE (p : Prog) (hp : LazyProg p) (hc : LazyCallees p) (hdqE : DeltaQuickE p)
    (hnv : closedNV p L.Checker.nvFns = true) : LdsUnfold2E p := by
  intro n hk hkE F hF hn s₀ a₀ dn vis fe M eb mode d a b hs ha hb hd
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hkc : er.cls = 0
  · exact ErrClaim.of_cls0 hkc
  have hW := triple_of_callE_err (ldsUnfold2_specE p hp.unfold2 (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d a b) hc0 (Err.code_ne_of_cls hkc)
  rw [ldsUnfold2E.arm1] at hW
  have hS := hs.rel
  unfold unfold2T
  cases h1 : callE p n "unfold_definition" [vis, a] s₀.mem with
  | error e =>
    rw [h1, ldsUnfold2E.k_unfold_definition.none] at hW; cases hW
    exact ErrClaim.of_nv hnv (by simp [defeqNVList]) h1
  | ok q =>
  obtain ⟨ra, m₁⟩ := q
  rw [h1, ldsUnfold2E.k_unfold_definition.arm1] at hW
  have e₁ := CoreSpec.of_callW (hc.unfold n ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe M eb a hS ha)
    (callW_of_callE h1)
  refine ErrClaim.bind_core e₁ (fun M₁ hS₁ => ?_)
  cases h2 : callE p n "unfold_definition" [vis, b] m₁ with
  | error e =>
    rw [h2, ldsUnfold2E.k_unfold_definition_2.none] at hW; cases hW
    exact ErrClaim.of_nv hnv (by simp [defeqNVList]) h2
  | ok q =>
  obtain ⟨rb, m₂⟩ := q
  rw [h2] at hW
  have e₂ := CoreSpec.of_callW (hc.unfold n ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb b hS₁ hb)
    (callW_of_callE h2)
  refine ErrClaim.bind_core e₂ (fun M₂ hS₂ => ?_)
  by_cases h0 : ra.headD 0 = 0 ∨ rb.headD 0 = 0
  · rw [ldsUnfold2E.k_unfold_definition_2.arm1 (hc1 := h0)] at hW; cases hW
  rw [ldsUnfold2E.k_unfold_definition_2.arm2 (hc1 := h0)] at hW
  have ha0 : ra.headD 0 ≠ 0 := fun h => h0 (.inl h)
  have hb0 : rb.headD 0 ≠ 0 := fun h => h0 (.inr h)
  rw [decOptR_some ha0, decOptR_some hb0]
  have hK := hk n (Nat.le_refl _)
  have hKE := hkE n (Nat.le_refl _)
  cases h3 : callE p n "whnf_core" [mode, 1, vis, d, ra.tail.headD 0] m₂ with
  | error e =>
    rw [h3, ldsUnfold2E.k_whnf_core.none] at hW; cases hW
    exact ErrClaim.bind_left (CoreSpecE.of_callE (s₀ := ⟨m₂, Locals.init []⟩)
      (hKE.whnfCore F _ _ dn vis fe M₂ eb mode 1 d _ hF hn ⟨hS₂, hs.mode4, hs.eb_mode⟩ e₁.2.2.2.2) h3)
  | ok q =>
  obtain ⟨r₃, m₃⟩ := q
  rw [h3, ldsUnfold2E.k_whnf_core.arm1] at hW
  have e₃ := CoreSpec.of_callW (hK.whnfCore F ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode 1 d _ hF hn
    ⟨hS₂, hs.mode4, hs.eb_mode⟩ e₁.2.2.2.2) (callW_of_callE h3)
  refine ErrClaim.bind_core e₃ (fun M₃ hS₃ => ?_)
  cases h4 : callE p n "whnf_core" [mode, 1, vis, d, rb.tail.headD 0] m₃ with
  | error e =>
    rw [h4, ldsUnfold2E.k_whnf_core_2.none] at hW; cases hW
    exact ErrClaim.bind_left (CoreSpecE.of_callE (s₀ := ⟨m₃, Locals.init []⟩)
      (hKE.whnfCore F _ _ dn vis fe M₃ eb mode 1 d _ hF hn ⟨hS₃, hs.mode4, hs.eb_mode⟩ e₂.2.2.2.2) h4)
  | ok q =>
  obtain ⟨r₄, m₄⟩ := q
  rw [h4, ldsUnfold2E.k_whnf_core_2.arm1] at hW
  have e₄ := CoreSpec.of_callW (hK.whnfCore F ⟨m₃, Locals.init []⟩ _ dn vis fe M₃ eb mode 1 d _ hF hn
    ⟨hS₃, hs.mode4, hs.eb_mode⟩ e₂.2.2.2.2) (callW_of_callE h4)
  refine ErrClaim.bind_core e₄ (fun M₄ hS₄ => ?_)
  have h5 := tailE (ldsUnfold2E.k_delta_quick.none p) (fun ⟨_, _⟩ => ⟨_, rfl⟩) hW
  refine ErrClaim.of_callE_succ h5 fun j hj h' => ?_
  subst hj
  exact CoreSpecE.of_callE (s₀ := ⟨m₄, Locals.init []⟩) (hdqE j (hk.mono (by omega))
    (hkE.mono (by omega)) F _ _ dn vis fe M₄ eb mode d _ _ (by omega) (by omega)
    ⟨hS₄, hs.mode4, hs.eb_mode⟩ e₃.2.2.2 e₄.2.2.2 hd) h'

l_model ldsSame_specE (p : Prog) (hf : p.lookup "lds_same" = some ldsSameL)
  fns [hf ↦ ldsSameE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

/-- **`lds_same`'s error spec** (the error half of `ldsSame_refines`). -/
def LdsSameE (p : Prog) : Prop :=
  ∀ (n : Nat), KnotUpTo p n → KnotUpToE p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
  ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d a b ka ha kb hb : Word), SlotPre s₀ a₀ dn vis fe M eb mode → HW a →
    HW b → d.toNat < 2 ^ 63 →
    CoreSpecE p (n + 1) "lds_same" [mode, vis, d, a, b, ka, ha, kb, hb]
      (sameT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)
        (decHintW ka ha) (decHintW kb hb)) s₀ a₀

/-- **`lds_same`'s error claim**. -/
theorem ldsSame_refinesE (p : Prog) (hp : LazyProg p) (hc : LazyCallees p) (hspE : DefeqSpineE p)
    (hu2E : LdsUnfold2E p) (hnv : closedNV p L.Checker.nvFns = true) : LdsSameE p := by
  intro n hk hkE F hF hn s₀ a₀ dn vis fe M eb mode d a b ka ha kb hb hs hwa hwb hd
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hkc : er.cls = 0
  · exact ErrClaim.of_cls0 hkc
  have hW := triple_of_callE_err (ldsSame_specE p hp.same (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d a b ka ha kb hb) hc0 (Err.code_ne_of_cls hkc)
  rw [ldsSameE.arm1] at hW
  have hS := hs.rel
  unfold sameT
  cases h1 : callE p n "same_const_heads" [a, b] s₀.mem with
  | error e =>
    rw [h1, ldsSameE.k_same_const_heads.none] at hW; cases hW
    exact ErrClaim.of_nv hnv (by simp [defeqNVList]) h1
  | ok q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [h1] at hW
  obtain ⟨k, rfl⟩ := callE_succ h1
  have e₁ := CoreSpec.of_callW (sameConstHeads_refines p hp.mid.leaf k s₀ a₀ dn vis fe M eb a b hS hwa
    hwb) (callW_of_callE h1)
  refine ErrClaim.bind_core e₁ (fun M₁ hS₁ => ?_)
  rw [sameRegular_w]
  -- the unfold arm
  have unf : ∀ (m₂ : Mem) (M₂ : ModeMaps) (a₂ : AState), CoreS dn m₂ a₂ vis fe M₂ eb →
      ldsSameE.j1 p (k + 1) mode vis d a b 0 m₂ = .error er →
      ErrClaim (unfold2T (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b))
        a₂ er := by
    intro m₂ M₂ a₂ hS₂ h
    rw [ldsSameE.j1.arm2 (hc1 := rfl)] at h
    have h3 := tailE (ldsSameE.k_lds_unfold2.none p) (fun ⟨_, _⟩ => ⟨_, rfl⟩) h
    exact CoreSpecE.of_callE (s₀ := ⟨m₂, Locals.init []⟩)
      (hu2E k (hk.mono (by omega)) (hkE.mono (by omega)) F (by omega) (by omega) _ a₂ dn vis fe M₂ eb
        mode d a b ⟨hS₂, hs.mode4, hs.eb_mode⟩ hwa hwb hd) h3
  by_cases hcnd : 2 ≤ ka ∧ 2 ≤ kb ∧ ha = hb ∧ r₁.headD 0 ≠ 0
  · rw [ldsSameE.k_same_const_heads.arm1 (hc1 := hcnd)] at hW
    have hsch : (decide (2 ≤ ka ∧ 2 ≤ kb ∧ ha = hb) && decBool r₁) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq, hcnd.1, hcnd.2.1, hcnd.2.2.1, true_and,
        decBool_t hcnd.2.2.2]
    simp only [hsch, ↓reduceIte]
    cases h2 : callE p (k + 1) "defeq_spine" [mode, vis, d, a, b] m₁ with
    | error e =>
      rw [h2, ldsSameE.k_defeq_spine.none] at hW; cases hW
      exact ErrClaim.bind_left (CoreSpecE.of_callE (s₀ := ⟨m₁, Locals.init []⟩)
        (hspE k (hk.mono (by omega)) (hkE.mono (by omega)) F (by omega) (by omega) _ _ dn vis fe M₁
          eb mode d a b ⟨hS₁, hs.mode4, hs.eb_mode⟩ hwa hwb) h2)
    | ok q =>
    obtain ⟨r₂, m₂⟩ := q
    rw [h2, ldsSameE.k_defeq_spine.arm1] at hW
    have e₂ := CoreSpec.of_callW (defeqSpine_refines p hp.spine hc.store k (hk.mono (by omega)) F
      (by omega) (by omega) ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode d a b ⟨hS₁, hs.mode4, hs.eb_mode⟩
      hwa hwb) (callW_of_callE h2)
    refine ErrClaim.bind_core e₂ (fun M₂ hS₂ => ?_)
    by_cases h2 : r₂.headD 0 ≠ 0
    · rw [ldsSameE.j1.arm1 (hc1 := h2)] at hW; cases hW
    have h2' : r₂.headD 0 = 0 := by simpa using h2
    rw [h2'] at hW
    rw [decBool_f h2']
    exact unf _ _ _ hS₂ hW
  · rw [ldsSameE.k_same_const_heads.arm2 (hc1 := hcnd)] at hW
    have hsch : (decide (2 ≤ ka ∧ 2 ≤ kb ∧ ha = hb) && decBool r₁) = false := by
      by_cases hz : r₁.headD 0 = 0
      · rw [decBool_f hz]; simp
      · have : ¬ (2 ≤ ka ∧ 2 ≤ kb ∧ ha = hb) := fun h => hcnd ⟨h.1, h.2.1, h.2.2, hz⟩
        simp [this]
    simp only [hsch, Bool.false_eq_true, ↓reduceIte, pure_bind]
    exact unf _ _ _ hS₁ hW

end L.Arena

/-! ## `lds_both`, `lazy_delta_step` -/

namespace L.Arena

l_model ldsBoth_specE (p : Prog) (hf : p.lookup "lds_both" = some ldsBothL)
  fns [hf ↦ ldsBothE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

/-- **`lds_both`'s error spec** (the error half of `ldsBoth_refines`). -/
def LdsBothE (p : Prog) : Prop :=
  ∀ (n : Nat), KnotUpTo p n → KnotUpToE p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
  ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d a b : Word), SlotPre s₀ a₀ dn vis fe M eb mode → HW a → HW b →
    d.toNat < 2 ^ 63 →
    CoreSpecE p (n + 1) "lds_both" [mode, vis, d, a, b]
      (bothT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) s₀ a₀

/-- **`lds_both`'s error claim**. -/
theorem ldsBoth_refinesE (p : Prog) (hp : LazyProg p) (hlE : LdsOneE p "lds_left" true)
    (hrE : LdsOneE p "lds_right" false) (hsE : LdsSameE p) (hnv : closedNV p L.Checker.nvFns = true) :
    LdsBothE p := by
  intro n hk hkE F hF hn s₀ a₀ dn vis fe M eb mode d a b hs ha hb hd
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hkc : er.cls = 0
  · exact ErrClaim.of_cls0 hkc
  have hW := triple_of_callE_err (ldsBoth_specE p hp.both (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d a b) hc0 (Err.code_ne_of_cls hkc)
  rw [ldsBothE.arm1] at hW
  have hS := hs.rel
  unfold bothT
  cases h1 : callE p n "head_hint" [vis, a] s₀.mem with
  | error e =>
    rw [h1, ldsBothE.k_head_hint.none] at hW; cases hW
    exact ErrClaim.of_nv hnv (by simp [defeqNVList]) h1
  | ok q =>
  obtain ⟨ra, m₁⟩ := q
  rw [h1, ldsBothE.k_head_hint.arm1] at hW
  obtain ⟨k, rfl⟩ := callE_succ h1
  have e₁ := CoreSpec.of_callW (headHint_refines p hp.mid.leaf k s₀ a₀ dn vis fe M eb a hS ha)
    (callW_of_callE h1)
  refine ErrClaim.bind_core e₁ (fun M₁ hS₁ => ?_)
  cases h2 : callE p (k + 1) "head_hint" [vis, b] m₁ with
  | error e =>
    rw [h2, ldsBothE.k_head_hint_2.none] at hW; cases hW
    exact ErrClaim.of_nv hnv (by simp [defeqNVList]) h2
  | ok q =>
  obtain ⟨rb, m₂⟩ := q
  rw [h2, ldsBothE.k_head_hint_2.arm1] at hW
  have e₂ := CoreSpec.of_callW (headHint_refines p hp.mid.leaf k ⟨m₁, Locals.init []⟩ _ dn vis fe M₁
    eb b hS₁ hb) (callW_of_callE h2)
  refine ErrClaim.bind_core e₂ (fun M₂ hS₂ => ?_)
  -- an arm's failure is its callee's
  have arm : ∀ (f : FnName) (args : List Word) (m₃ : Mem) (T : AM DeltaStepA) (a₂ : AState),
      ldsBothE.k_lds_left p (callE p (k + 1) f args m₃) = .error er →
      (∀ e, callE p (k + 1) f args m₃ = .error e → ErrClaim T a₂ e) → ErrClaim T a₂ er := by
    intro f args m₃ T a₂ h hT
    exact hT er (tailE (ldsBothE.k_lds_left.none p) (fun ⟨_, _⟩ => ⟨_, rfl⟩) h)
  cases h3 : callE p (k + 1) "hint_lt" [rb.headD 0, rb.tail.headD 0, ra.headD 0, ra.tail.headD 0] m₂
    with
  | error e =>
    rw [h3, ldsBothE.k_hint_lt.none] at hW; cases hW
    exact ErrClaim.of_nv hnv (by simp [defeqNVList]) h3
  | ok q =>
  obtain ⟨rl, m₃⟩ := q
  rw [h3] at hW
  obtain ⟨t₃, ht₃, hm₃, -, hlt₁, -⟩ := triple_of_callE (s₀ := ⟨m₂, Locals.init []⟩)
    (hintLt_refines p hp.mid.leaf k ⟨m₂, Locals.init []⟩ _ _ _ _) h3
  have hm₃' : m₃ = m₂ := by rw [← ht₃, hm₃]
  subst hm₃'
  have hdh : ∀ r : List Word, decHintR r = decHintW (r.headD 0) (r.tail.headD 0) := fun _ => rfl
  rw [hdh ra, hdh rb]
  by_cases h1 : rl.headD 0 ≠ 0
  · rw [ldsBothE.k_hint_lt.arm1 (hc1 := h1)] at hW
    have hl : ConLeche.ReducibilityHint.lt (decHintW (rb.headD 0) (rb.tail.headD 0))
        (decHintW (ra.headD 0) (ra.tail.headD 0)) = true := by rw [← hlt₁]; exact decBool_t h1
    simp only [hl, ↓reduceIte]
    exact arm _ _ _ _ _ hW (fun e he => CoreSpecE.of_callE (s₀ := ⟨m₃, Locals.init []⟩)
      (hlE k (hk.mono (by omega)) (hkE.mono (by omega)) F (by omega) (by omega) _ _ dn vis fe M₂ eb
        mode d a b ⟨hS₂, hs.mode4, hs.eb_mode⟩ ha hb hd) he)
  have h1' : rl.headD 0 = 0 := by simpa using h1
  rw [ldsBothE.k_hint_lt.arm2 (hc1 := h1')] at hW
  have hl : ConLeche.ReducibilityHint.lt (decHintW (rb.headD 0) (rb.tail.headD 0))
      (decHintW (ra.headD 0) (ra.tail.headD 0)) = false := by rw [← hlt₁]; exact decBool_f h1'
  simp only [hl, Bool.false_eq_true, ↓reduceIte]
  cases h5 : callE p (k + 1) "hint_lt" [ra.headD 0, ra.tail.headD 0, rb.headD 0, rb.tail.headD 0] m₃
    with
  | error e =>
    rw [h5, ldsBothE.k_hint_lt_2.none] at hW; cases hW
    exact ErrClaim.of_nv hnv (by simp [defeqNVList]) h5
  | ok q =>
  obtain ⟨rl₂, m₅⟩ := q
  rw [h5] at hW
  obtain ⟨t₅, ht₅, hm₅, -, hlt₂, -⟩ := triple_of_callE (s₀ := ⟨m₃, Locals.init []⟩)
    (hintLt_refines p hp.mid.leaf k ⟨m₃, Locals.init []⟩ _ _ _ _) h5
  have hm₅' : m₅ = m₃ := by rw [← ht₅, hm₅]
  subst hm₅'
  simp only [ldsBothE.k_hint_lt_2] at hW
  by_cases h2 : rl₂.headD 0 ≠ 0
  · rw [ite_eq_left h2] at hW
    have hl2 : ConLeche.ReducibilityHint.lt (decHintW (ra.headD 0) (ra.tail.headD 0))
        (decHintW (rb.headD 0) (rb.tail.headD 0)) = true := by rw [← hlt₂]; exact decBool_t h2
    simp only [hl2, ↓reduceIte]
    exact arm _ _ _ _ _ hW (fun e he => CoreSpecE.of_callE (s₀ := ⟨m₅, Locals.init []⟩)
      (hrE k (hk.mono (by omega)) (hkE.mono (by omega)) F (by omega) (by omega) _ _ dn vis fe M₂ eb
        mode d a b ⟨hS₂, hs.mode4, hs.eb_mode⟩ ha hb hd) he)
  have h2' : rl₂.headD 0 = 0 := by simpa using h2
  rw [ite_eq_right h2] at hW
  have hl2 : ConLeche.ReducibilityHint.lt (decHintW (ra.headD 0) (ra.tail.headD 0))
      (decHintW (rb.headD 0) (rb.tail.headD 0)) = false := by rw [← hlt₂]; exact decBool_f h2'
  simp only [hl2, Bool.false_eq_true, ↓reduceIte]
  exact arm _ _ _ _ _ hW (fun e he => CoreSpecE.of_callE (s₀ := ⟨m₅, Locals.init []⟩)
    (hsE k (hk.mono (by omega)) (hkE.mono (by omega)) F (by omega) (by omega) _ _ dn vis fe M₂ eb
      mode d a b _ _ _ _ ⟨hS₂, hs.mode4, hs.eb_mode⟩ ha hb hd) he)

l_model lazyDeltaStep_specE (p : Prog) (hf : p.lookup "lazy_delta_step" = some lazyDeltaStepL)
  fns [hf ↦ lazyDeltaStepE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

/-- **`lazy_delta_step`'s error claim** (`LazyDeltaStepE`, the error half of
`lazyDeltaStep_refines`). -/
theorem lazyDeltaStep_refinesE (p : Prog) (hp : LazyProg p)
    (hdqE : DeltaQuickE p) (htuE : TryUnfoldProjAppE p) (hlE : LdsOneE p "lds_left" true)
    (hrE : LdsOneE p "lds_right" false) (hbE : LdsBothE p) (hnv : closedNV p L.Checker.nvFns = true) :
    LazyDeltaStepE p := by
  intro n hk hkE F hF hn s₀ a₀ dn vis fe M eb mode d a b hs ha hb hd
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hkc : er.cls = 0
  · exact ErrClaim.of_cls0 hkc
  have hW := triple_of_callE_err (lazyDeltaStep_specE p hp.step (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d a b) hc0 (Err.code_ne_of_cls hkc)
  simp only [lazyDeltaStepE] at hW
  have hS := hs.rel
  rw [lazyDeltaStep_eq]
  cases h1 : callE p n "unfoldable_head" [vis, a] s₀.mem with
  | error e =>
    rw [h1, lazyDeltaStepE.k_unfoldable_head.none] at hW; cases hW
    exact ErrClaim.of_nv hnv (by simp [defeqNVList]) h1
  | ok q =>
  obtain ⟨ra, m₁⟩ := q
  rw [h1] at hW
  simp only [lazyDeltaStepE.k_unfoldable_head] at hW
  obtain ⟨k, rfl⟩ := callE_succ h1
  have e₁ := CoreSpec.of_callW (unfoldableHead_refines p hp.mid.leaf k s₀ a₀ dn vis fe M eb a hS ha)
    (callW_of_callE h1)
  refine ErrClaim.bind_core e₁ (fun M₁ hS₁ => ?_)
  cases h2 : callE p (k + 1) "unfoldable_head" [vis, b] m₁ with
  | error e =>
    rw [h2, lazyDeltaStepE.k_unfoldable_head_2.none] at hW; cases hW
    exact ErrClaim.of_nv hnv (by simp [defeqNVList]) h2
  | ok q =>
  obtain ⟨rb, m₂⟩ := q
  rw [h2] at hW
  simp only [lazyDeltaStepE.k_unfoldable_head_2] at hW
  have e₂ := CoreSpec.of_callW (unfoldableHead_refines p hp.mid.leaf k ⟨m₁, Locals.init []⟩ _ dn vis
    fe M₁ eb b hS₁ hb) (callW_of_callE h2)
  refine ErrClaim.bind_core e₂ (fun M₂ hS₂ => ?_)
  have arm : ∀ (f : FnName) (args : List Word) (m₃ : Mem) (T : AM DeltaStepA) (a₂ : AState),
      lazyDeltaStepE.k_delta_quick p (callE p (k + 1) f args m₃) = .error er →
      (∀ e, callE p (k + 1) f args m₃ = .error e → ErrClaim T a₂ e) → ErrClaim T a₂ er := by
    intro f args m₃ T a₂ h hT
    exact hT er (tailE (lazyDeltaStepE.k_delta_quick.none p) (fun ⟨_, _⟩ => ⟨_, rfl⟩) h)
  have hk' : KnotUpTo p k := hk.mono (by omega)
  have hkE' : KnotUpToE p k := hkE.mono (by omega)
  by_cases h00 : ra.headD 0 = 0 ∧ rb.headD 0 = 0
  · rw [ite_eq_left h00] at hW; cases hW
  rw [ite_eq_right h00] at hW
  by_cases hb0 : rb.headD 0 = 0
  · have ha0 : ra.headD 0 ≠ 0 := fun h => h00 ⟨h, hb0⟩
    rw [ite_eq_left hb0] at hW
    rw [decBool_t ha0, decBool_f hb0]
    cases h3 : callE p (k + 1) "try_unfold_proj_app" [mode, vis, d, b] m₂ with
    | error e =>
      rw [h3, lazyDeltaStepE.k_try_unfold_proj_app.none] at hW; cases hW
      exact ErrClaim.bind_left (CoreSpecE.of_callE (s₀ := ⟨m₂, Locals.init []⟩)
        (htuE k hk' hkE' F _ _ dn vis fe M₂ eb mode d b (by omega) (by omega)
          ⟨hS₂, hs.mode4, hs.eb_mode⟩ hb) h3)
    | ok q =>
    obtain ⟨rt, m₃⟩ := q
    rw [h3] at hW
    simp only [lazyDeltaStepE.k_try_unfold_proj_app] at hW
    have e₃ := CoreSpec.of_callW (tryUnfoldProjApp_refines p hp.mid k hk' F ⟨m₂, Locals.init []⟩ _ dn
      vis fe M₂ eb mode d b (by omega) (by omega) ⟨hS₂, hs.mode4, hs.eb_mode⟩ hb) (callW_of_callE h3)
    refine ErrClaim.bind_core e₃ (fun M₃ hS₃ => ?_)
    by_cases ht : rt.headD 0 ≠ 0
    · rw [ite_eq_left ht] at hW
      rw [decOptR_some ht]
      exact arm _ _ _ _ _ hW (fun e he => ErrClaim.of_callE_succ he fun j hj h' => by
        cases Nat.add_right_cancel hj
        exact CoreSpecE.of_callE (s₀ := ⟨m₃, Locals.init []⟩)
          (hdqE k hk' hkE' F _ _ dn vis fe M₃ eb mode d a _ (by omega) (by omega)
            ⟨hS₃, hs.mode4, hs.eb_mode⟩ ha e₃.2.2.2.2 hd) h')
    rw [ite_eq_right ht] at hW
    rw [decOptR_none (by simpa using ht)]
    exact arm _ _ _ _ _ hW (fun e he => CoreSpecE.of_callE (s₀ := ⟨m₃, Locals.init []⟩)
      (hlE k hk' hkE' F (by omega) (by omega) _ _ dn vis fe M₃ eb mode d a b
        ⟨hS₃, hs.mode4, hs.eb_mode⟩ ha hb hd) he)
  rw [ite_eq_right hb0] at hW
  by_cases ha0 : ra.headD 0 = 0
  · rw [ite_eq_left ha0] at hW
    rw [decBool_f ha0, decBool_t hb0]
    cases h3 : callE p (k + 1) "try_unfold_proj_app" [mode, vis, d, a] m₂ with
    | error e =>
      rw [h3, lazyDeltaStepE.k_try_unfold_proj_app_2.none] at hW; cases hW
      exact ErrClaim.bind_left (CoreSpecE.of_callE (s₀ := ⟨m₂, Locals.init []⟩)
        (htuE k hk' hkE' F _ _ dn vis fe M₂ eb mode d a (by omega) (by omega)
          ⟨hS₂, hs.mode4, hs.eb_mode⟩ ha) h3)
    | ok q =>
    obtain ⟨rt, m₃⟩ := q
    rw [h3] at hW
    simp only [lazyDeltaStepE.k_try_unfold_proj_app_2] at hW
    have e₃ := CoreSpec.of_callW (tryUnfoldProjApp_refines p hp.mid k hk' F ⟨m₂, Locals.init []⟩ _ dn
      vis fe M₂ eb mode d a (by omega) (by omega) ⟨hS₂, hs.mode4, hs.eb_mode⟩ ha) (callW_of_callE h3)
    refine ErrClaim.bind_core e₃ (fun M₃ hS₃ => ?_)
    by_cases ht : rt.headD 0 ≠ 0
    · rw [ite_eq_left ht] at hW
      rw [decOptR_some ht]
      exact arm _ _ _ _ _ hW (fun e he => ErrClaim.of_callE_succ he fun j hj h' => by
        cases Nat.add_right_cancel hj
        exact CoreSpecE.of_callE (s₀ := ⟨m₃, Locals.init []⟩)
          (hdqE k hk' hkE' F _ _ dn vis fe M₃ eb mode d _ b (by omega) (by omega)
            ⟨hS₃, hs.mode4, hs.eb_mode⟩ e₃.2.2.2.2 hb hd) h')
    rw [ite_eq_right ht] at hW
    rw [decOptR_none (by simpa using ht)]
    exact arm _ _ _ _ _ hW (fun e he => CoreSpecE.of_callE (s₀ := ⟨m₃, Locals.init []⟩)
      (hrE k hk' hkE' F (by omega) (by omega) _ _ dn vis fe M₃ eb mode d a b
        ⟨hS₃, hs.mode4, hs.eb_mode⟩ ha hb hd) he)
  rw [ite_eq_right ha0] at hW
  rw [decBool_t ha0, decBool_t hb0]
  exact arm _ _ _ _ _ hW (fun e he => CoreSpecE.of_callE (s₀ := ⟨m₂, Locals.init []⟩)
    (hbE k hk' hkE' F (by omega) (by omega) _ _ dn vis fe M₂ eb mode d a b
      ⟨hS₂, hs.mode4, hs.eb_mode⟩ ha hb hd) he)

end L.Arena

/-! ## `lazy_iter`, the lazy-delta loop, `lazy_delta_reduction` -/

namespace L.Arena

/-- **`lazy_nat`'s error spec** (whnf family; the error half of `lazyNat_refines`). -/
def LazyNatE (p : Prog) : Prop :=
  ∀ (n : Nat), KnotUpTo p n → KnotUpToE p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
  ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d a b : Word), SlotPre s₀ a₀ dn vis fe M eb mode → HW a → HW b →
    CoreSpecE p (n + 1) "lazy_nat" [mode, vis, d, a, b]
      (natT (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) s₀ a₀

/-- **`defeq_offset`'s error spec** (the error half of `defeqOffset_refines`). -/
def DefeqOffsetE (p : Prog) : Prop :=
  ∀ (n : Nat), KnotUpTo p n → KnotUpToE p n → ∀ (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word),
    n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe M eb mode → HW a → HW b →
    CoreSpecE p (n + 1) "defeq_offset" [mode, vis, d, a, b]
      (defeqOffset (coreKnot (decMode mode) fe id F) d.toNat (decE a) (decE b)) s₀ a₀

/-- **`lazy_iter`'s error spec** (the error half of `lazyIter_refines`). -/
def LazyIterE (p : Prog) : Prop :=
  ∀ (n : Nat), KnotUpTo p n → KnotUpToE p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
  ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d a b : Word), SlotPre s₀ a₀ dn vis fe M eb mode → HW a → HW b →
    d.toNat < 2 ^ 63 →
    CoreSpecE p (n + 1) "lazy_iter" [mode, vis, d, a, b]
      (iterT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) s₀ a₀

l_model lazyIter_specE (p : Prog) (hf : p.lookup "lazy_iter" = some lazyIterL)
  fns [hf ↦ lazyIterE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

/-- **`lazy_iter`'s error claim**. -/
theorem lazyIter_refinesE (p : Prog) (hp : LazyProg p) (hc : LazyCallees p) (hofE : DefeqOffsetE p)
    (hnatE : LazyNatE p) (hstE : LazyDeltaStepE p) (hnv : closedNV p L.Checker.nvFns = true) :
    LazyIterE p := by
  intro n hk hkE F hF hn s₀ a₀ dn vis fe M eb mode d a b hs ha hb hd
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hkc : er.cls = 0
  · exact ErrClaim.of_cls0 hkc
  have hW := triple_of_callE_err (lazyIter_specE p hp.iter (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d a b) hc0 (Err.code_ne_of_cls hkc)
  rw [lazyIterE.arm1] at hW
  have hS := hs.rel
  -- the step arm
  have stepArm : ∀ (m₃ : Mem) (M₃ : ModeMaps) (a₃ : AState), CoreS dn m₃ a₃ vis fe M₃ eb →
      lazyIterE.j1 p n mode vis d a b m₃ = .error er →
      ErrClaim (α := LazyResA ⊕ (EIdx × EIdx)) (lazyDeltaStep (decMode mode)
        (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b) >>= fun st => match st with
          | .cont a' b' => pure (.inr (a', b'))
          | .eq => pure (.inl (.verdict true))
          | .diff => pure (.inl (.verdict false))
          | .unknown => pure (.inl (.unknown (decE a) (decE b)))) a₃ er := by
    intro m₃ M₃ a₃ hS₃ h
    rw [lazyIterE.j1.arm1] at h
    have h4 := tailE (lazyIterE.k_lazy_delta_step.none p a b) (fun ⟨r, m⟩ => by
      simp only [lazyIterE.k_lazy_delta_step]; repeat' split
      all_goals exact ⟨_, rfl⟩) h
    refine ErrClaim.bind_left (ErrClaim.of_callE_succ h4 fun j hj h' => ?_)
    subst hj
    exact CoreSpecE.of_callE (s₀ := ⟨m₃, Locals.init []⟩) (hstE j (hk.mono (by omega))
      (hkE.mono (by omega)) F (by omega) (by omega) _ a₃ dn vis fe M₃ eb mode d a b
      ⟨hS₃, hs.mode4, hs.eb_mode⟩ ha hb hd) h'
  unfold iterT
  cases h1 : callE p n "defeq_offset" [mode, vis, d, a, b] s₀.mem with
  | error e =>
    rw [h1, lazyIterE.k_defeq_offset.none] at hW; cases hW
    refine ErrClaim.bind_left (ErrClaim.of_callE_succ h1 fun j hj h' => ?_)
    subst hj
    exact CoreSpecE.of_callE (hofE j (hk.mono (by omega)) (hkE.mono (by omega)) F s₀ a₀ dn vis fe M eb
      mode d a b (by omega) (by omega) hs ha hb) h'
  | ok q =>
  obtain ⟨ro, m₁⟩ := q
  rw [h1] at hW
  obtain ⟨k, rfl⟩ := callE_succ h1
  have e₁ := CoreSpec.of_callW (defeqOffset_refines p hp.mid hc.natPred k (hk.mono (by omega)) F s₀ a₀
    dn vis fe M eb mode d a b (by omega) (by omega) hs ha hb) (callW_of_callE h1)
  refine ErrClaim.bind_core e₁ (fun M₁ hS₁ => ?_)
  by_cases h0 : ro.headD 0 ≠ 0
  · rw [lazyIterE.k_defeq_offset.arm1 (hc1 := h0)] at hW; cases hW
  have h0' : ro.headD 0 = 0 := by simpa using h0
  rw [lazyIterE.k_defeq_offset.arm2 (hc1 := h0')] at hW
  have : decOB ro = none := by simp only [decOB, h0', ↓reduceIte]
  rw [this]
  cases h2 : callE p (k + 1) "lazy_fold_ok" [mode, a, b] m₁ with
  | error e =>
    rw [h2, lazyIterE.k_lazy_fold_ok.none] at hW; cases hW
    exact ErrClaim.of_nv hnv (by simp [defeqNVList]) h2
  | ok q =>
  obtain ⟨rf, m₂⟩ := q
  rw [h2] at hW
  have e₂ := CoreSpec.of_callW (s₀ := ⟨m₁, Locals.init []⟩)
    (lazyFoldOk_refines p hp.mid hc.hasFvar k _ _ dn vis fe M₁ eb mode a b hS₁ hs.mode4 ha hb)
    (callW_of_callE h2)
  refine ErrClaim.bind_core e₂ (fun M₂ hS₂ => ?_)
  by_cases hf : rf.headD 0 ≠ 0
  · rw [lazyIterE.k_lazy_fold_ok.arm1 (hc1 := hf)] at hW
    rw [decBool_t hf]
    simp only [↓reduceIte]
    cases h3 : callE p (k + 1) "lazy_nat" [mode, vis, d, a, b] m₂ with
    | error e =>
      rw [h3, lazyIterE.k_lazy_nat.none] at hW; cases hW
      exact ErrClaim.bind_left (CoreSpecE.of_callE (s₀ := ⟨m₂, Locals.init []⟩)
        (hnatE k (hk.mono (by omega)) (hkE.mono (by omega)) F (by omega) (by omega) _ _ dn vis fe M₂
          eb mode d a b ⟨hS₂, hs.mode4, hs.eb_mode⟩ ha hb) h3)
    | ok q =>
    obtain ⟨rn, m₃⟩ := q
    rw [h3] at hW
    have e₃ := CoreSpec.of_callW (s₀ := ⟨m₂, Locals.init []⟩)
      (lazyNat_refines p hp hc k (hk.mono (by omega)) F (by omega) (by omega) _ _ dn vis fe M₂ eb mode
        d a b ⟨hS₂, hs.mode4, hs.eb_mode⟩ ha hb) (callW_of_callE h3)
    refine ErrClaim.bind_core e₃ (fun M₃ hS₃ => ?_)
    by_cases h3 : rn.headD 0 ≠ 3
    · rw [lazyIterE.k_lazy_nat.arm1 (hc1 := h3)] at hW; cases hW
    have h3' : rn.headD 0 = 3 := by simpa using h3
    rw [lazyIterE.k_lazy_nat.arm2 (hc1 := h3')] at hW
    have : decNat rn = none := by simp only [decNat, h3', ↓reduceIte]
    rw [this]
    exact stepArm _ _ _ hS₃ hW
  have hf' : rf.headD 0 = 0 := by simpa using hf
  rw [lazyIterE.k_lazy_fold_ok.arm2 (hc1 := hf')] at hW
  rw [decBool_f hf']
  simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]
  exact stepArm _ _ _ hS₂ hW

l_model lazyDeltaReduction_specE (p : Prog) (hf : p.lookup "lazy_delta_reduction" = some lazyDeltaReductionL)
  fns [hf ↦ ldrE tuple] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

theorem ldrE_loop1_zero (p : Prog) (m : Mem) (mode vis d a b : Word) :
    ldrE.loop1 p 0 m mode vis d a b = .error .outOfFuel := by
  unfold ldrE.loop1; rfl

/-- **The lazy-delta loop's error claim** at every twin fuel `K` with `j ≤ K + 1` (the error half of
`lazyW_ok`). -/
theorem lazyLoop_okE (p : Prog) (hp : LazyProg p) (hc : LazyCallees p) (hitE : LazyIterE p)
    (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (mode d : Word) (hmode : mode < 4)
    (hd : d.toNat < 2 ^ 63) :
    ∀ j, j ≤ n + 1 → ∀ K, j ≤ K + 1 → ∀ (a b : Word) (m : Mem) (s : AState) (M : ModeMaps)
      (eb : Word) (er : Err), CoreS dn m s vis fe M eb → eb = (mode >>> 1) &&& 1 → HW a → HW b →
      ldrE.loop1 p j m mode vis d a b = .error er →
      ErrClaim (lazyDeltaReduction (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat K
        (decE a) (decE b)) s er := by
  intro j
  induction j with
  | zero =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ h
    rw [ldrE_loop1_zero] at h; cases h
    exact ErrClaim.of_cls0 Err.cls_outOfFuel
  | succ j ih =>
    intro hjn K hK a b m s M eb er hS heb ha hb h
    rw [ldrE.loop1.arm1 (hc1 := rfl)] at h
    cases hc1 : callE p j "lazy_iter" [mode, vis, d, a, b] m with
    | error e =>
      rw [hc1, ldrE.k_lazy_iter.none] at h; cases h
      refine ErrClaim.of_callE_succ hc1 fun j' hj h' => ?_
      subst hj
      obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
      rw [lazyDeltaReduction_succ_eq, lazyLvl_eq]
      refine ErrClaim.bind_left ?_
      exact CoreSpecE.of_callE (s₀ := ⟨m, Locals.init []⟩) (hitE j' (hk.mono (by omega))
        (hkE.mono (by omega)) F (by omega) (by omega) _ s dn vis fe M eb mode d a b ⟨hS, hmode, heb⟩
        ha hb hd) h'
    | ok q =>
    obtain ⟨r, m₁⟩ := q
    rw [hc1] at h
    obtain ⟨j', rfl⟩ := callE_succ hc1
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    rw [lazyDeltaReduction_succ_eq, lazyLvl_eq]
    have e := CoreSpec.of_callW (s₀ := ⟨m, Locals.init []⟩)
      (lazyIter_refines p hp hc j' (hk.mono (by omega)) F (by omega) (by omega) _ s dn vis fe M eb mode
        d a b ⟨hS, hmode, heb⟩ ha hb hd) (callW_of_callE hc1)
    obtain ⟨-, hr1, hr2⟩ := e.2.2.2
    refine ErrClaim.bind_core e (fun M₁ hS₁ => ?_)
    by_cases h3 : r.headD 0 ≠ 3
    · rw [ldrE.k_lazy_iter.arm1 (hc1 := h3)] at h; cases h
    have h3' : r.headD 0 = 3 := by simpa using h3
    rw [ldrE.k_lazy_iter.arm2 (hc1 := h3')] at h
    rw [decIter_cont h3']
    exact ih (by omega) K' (by omega) _ _ m₁ _ M₁ eb er hS₁ heb hr1 hr2 h

/-- **`lazy_delta_reduction`'s error claim** (`LazyDeltaReductionE`, the error half of
`lazyDeltaReduction_refines`). -/
theorem lazyDeltaReduction_refinesE (p : Prog) (hp : LazyProg p) (hc : LazyCallees p)
    (hitE : LazyIterE p) : LazyDeltaReductionE p := by
  intro n hk hkE F hF hn s₀ a₀ dn vis fe M eb mode d a b hs ha hb hd
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hkc : er.cls = 0
  · exact ErrClaim.of_cls0 hkc
  have hW := triple_of_callE_err (lazyDeltaReduction_specE p hp.red (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d a b) hc0 (Err.code_ne_of_cls hkc)
  rw [ldrE.arm1] at hW
  have hL : (2 : Nat) ^ 62 = defeqLoopFuel := rfl
  exact lazyLoop_okE p hp hc hitE n hk hkE F hF hn dn vis fe mode d hs.mode4 hd (n + 1)
    (Nat.le_refl _) defeqLoopFuel (by rw [← hL]; omega) a b _ a₀ M eb er hs.rel hs.eb_mode ha hb hW

end L.Arena

/-! ## `defeq_offset` -/

namespace L.Arena

l_model defeqOffset_specE (p : Prog) (hf : p.lookup "defeq_offset" = some defeqOffsetL)
  fns [hf ↦ defeqOffsetE tuple] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

/-- **`defeq_offset`'s error claim** (`DefeqOffsetE`). -/
theorem defeqOffset_refinesE (p : Prog) (hp : DefEqMidProg p) (hnp : NatPredW p)
    (hnv : closedNV p L.Checker.nvFns = true) : DefeqOffsetE p := by
  intro n hk hkE F s₀ a₀ dn vis fe M eb mode d a b hF hn hs ha hb
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hkc : er.cls = 0
  · exact ErrClaim.of_cls0 hkc
  have hW := triple_of_callE_err (defeqOffset_specE p hp.off (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d a b) hc0 (Err.code_ne_of_cls hkc)
  unfold defeqOffset
  simp only [defeqOffsetE] at hW
  cases hc1 : callE p n "is_nat_zero" [a] s₀.mem with
  | error e =>
    rw [hc1, defeqOffsetE.k_is_nat_zero.none] at hW; cases hW
    exact ErrClaim.of_nv hnv (by simp [defeqNVList]) hc1
  | ok q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [hc1, defeqOffsetE.k_is_nat_zero.arm1] at hW
  obtain ⟨k, rfl⟩ := callE_succ hc1
  have h₁ := CoreSpec.of_callW (isNatZero_refines p hp.leaf k s₀ a₀ dn vis fe M eb a hs.rel ha)
    (callW_of_callE hc1)
  refine ErrClaim.bind_core h₁ (fun M₁ hS₁ => ?_)
  cases hc2 : callE p (k + 1) "is_nat_zero" [b] m₁ with
  | error e =>
    rw [hc2, defeqOffsetE.k_is_nat_zero_2.none] at hW; cases hW
    exact ErrClaim.of_nv hnv (by simp [defeqNVList]) hc2
  | ok q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [hc2] at hW
  have h₂ := CoreSpec.of_callW (s₀ := ⟨m₁, Locals.init []⟩)
    (isNatZero_refines p hp.leaf k _ _ dn vis fe M₁ eb b hS₁ hb) (callW_of_callE hc2)
  refine ErrClaim.bind_core h₂ (fun M₂ hS₂ => ?_)
  by_cases hzz : r₁.headD 0 ≠ 0 ∧ r₂.headD 0 ≠ 0
  · rw [defeqOffsetE.k_is_nat_zero_2.arm1 (hc1 := hzz)] at hW; cases hW
  have hzb : (decBool r₁ && decBool r₂) = false := by
    by_cases h : r₁.headD 0 = 0
    · rw [decBool_f h]; rfl
    · have h' : r₂.headD 0 = 0 := Classical.byContradiction fun h' => hzz ⟨h, h'⟩
      rw [decBool_f h']; simp
  simp only [hzb, Bool.false_eq_true, ↓reduceIte, tag_beq_lit a ha, tag_beq_lit b hb,
    Bool.and_eq_true, decide_eq_true_eq]
  by_cases hll : a >>> 28 = 8 ∧ b >>> 28 = 8
  · rw [defeqOffsetE.k_is_nat_zero_2.arm2 (hc1 := hzz) (hc2 := hll)] at hW; cases hW
  simp only [hll, ↓reduceIte]
  rw [defeqOffsetE.k_is_nat_zero_2.arm3 (hc1 := hzz) (hc2 := hll)] at hW
  cases hc3 : callE p (k + 1) "nat_pred" [a] m₂ with
  | error e =>
    rw [hc3, defeqOffsetE.k_nat_pred.none] at hW; cases hW
    exact ErrClaim.of_nv hnv (by simp [defeqNVList]) hc3
  | ok q =>
  obtain ⟨r₃, m₃⟩ := q
  rw [hc3] at hW
  have h₃ := CoreSpec.of_callW (s₀ := ⟨m₂, Locals.init []⟩)
    (hnp (k + 1) _ _ dn vis fe M₂ eb a hS₂ ha) (callW_of_callE hc3)
  refine ErrClaim.bind_core h₃ (fun M₃ hS₃ => ?_)
  by_cases h3 : r₃.headD 0 = 0
  · rw [defeqOffsetE.k_nat_pred.arm1 (hc1 := h3)] at hW; cases hW
  rw [defeqOffsetE.k_nat_pred.arm2 (hc1 := h3)] at hW
  rw [decOptR_some h3]
  cases hc4 : callE p (k + 1) "nat_pred" [b] m₃ with
  | error e =>
    rw [hc4, defeqOffsetE.k_nat_pred_2.none] at hW; cases hW
    exact ErrClaim.of_nv hnv (by simp [defeqNVList]) hc4
  | ok q =>
  obtain ⟨r₄, m₄⟩ := q
  rw [hc4] at hW
  have h₄ := CoreSpec.of_callW (s₀ := ⟨m₃, Locals.init []⟩)
    (hnp (k + 1) _ _ dn vis fe M₃ eb b hS₃ hb) (callW_of_callE hc4)
  refine ErrClaim.bind_core h₄ (fun M₄ hS₄ => ?_)
  by_cases h4 : r₄.headD 0 = 0
  · rw [defeqOffsetE.k_nat_pred_2.arm1 (hc1 := h4)] at hW; cases hW
  rw [defeqOffsetE.k_nat_pred_2.arm2 (hc1 := h4)] at hW
  rw [decOptR_some h4]
  have h5 := tailE (defeqOffsetE.k_defeq.none p) (fun ⟨_, _⟩ => ⟨_, rfl⟩) hW
  exact ErrClaim.bind_left (CoreSpecE.of_callE (s₀ := ⟨m₄, Locals.init []⟩)
    ((hkE (k + 1) (Nat.le_refl _)).defeq F _ _ dn vis fe M₄ eb mode d _ _ hF hn
      ⟨hS₄, hs.mode4, hs.eb_mode⟩ h₃.2.2.2.2 h₄.2.2.2.2) h5)

end L.Arena
