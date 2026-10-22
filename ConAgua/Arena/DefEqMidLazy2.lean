import ConAgua.Arena.DefEqMidLazy

/-!
# The lazy-delta loop: `lazy_nat`, `lazy_iter`, `lazy_delta_reduction` (lane `defeq`)

One iteration of the twin's `lazyDeltaReduction` is `iterT` (offsets, the literal acceleration
`natT`, one `lazyDeltaStep`), answering a result (`inl`) or the next pair (`inr`); the twin's loop
is `iterT` then its own recursion (`lazyLvl_eq`, the unfolding by `delta` and `rfl` as
`defeqPeel`'s). `lazy_iter` refines `iterT`, the uncounted L loop the twin's at
`defeqLoopFuel = 2^62` (`lazyW_ok`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## `lazy_nat` -/

/-- The literal acceleration of one lazy-delta iteration (the twin's two `reduceNat` matches,
`nf` true). -/
def natT (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (a b : EIdx) : AM (Option Bool) := do
  match ← reduceNat r fe depth a with
  | some a₂ => do
    let v ← r.defeq depth a₂ b
    pure (some v)
  | none =>
    match ← reduceNat r fe depth b with
    | some b₂ => do
      let v ← r.defeq depth a b₂
      pure (some v)
    | none => pure none

/-- `(k, 0, 0)`: `3` none, else `some (k != 0)`. -/
def decNat (r : List Word) : Option Bool := if r.headD 0 = 3 then none else some (r.headD 0 != 0)

section lnK
variable (p : Prog) (n : Nat) (mode vis d a b : Word)

def lnK4 (res : Option (List Word × Mem)) : Option (Word × Word × Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => some (if r.headD 0 ≠ 0 then 1 else 0, 0, 0, m)

def lnK2 (res : Option (List Word × Mem)) : Option (Word × Word × Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if r.headD 0 ≠ 0 then lnK4 (callW p n "defeq" [mode, vis, d, a, r.tail.headD 0] m)
    else some (3, 0, 0, m)

def lnK1 (res : Option (List Word × Mem)) : Option (Word × Word × Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if r.headD 0 ≠ 0 then lnK4 (callW p n "defeq" [mode, vis, d, r.tail.headD 0, b] m)
    else lnK2 p n mode vis d a (callW p n "reduce_nat" [mode, vis, d, b] m)

variable (r : List Word) (m : Mem)
theorem lnK4_s : lnK4 (some (r, m)) = some (if r.headD 0 ≠ 0 then 1 else 0, 0, 0, m) := rfl
theorem lnK2_t (h : r.headD 0 ≠ 0) : lnK2 p n mode vis d a (some (r, m)) =
    lnK4 (callW p n "defeq" [mode, vis, d, a, r.tail.headD 0] m) := by
  simp only [lnK2, h, ne_eq, not_false_eq_true, ↓reduceIte]
theorem lnK2_f (h : r.headD 0 = 0) : lnK2 p n mode vis d a (some (r, m)) = some (3, 0, 0, m) := by
  simp only [lnK2, h, ne_eq, not_true_eq_false, ↓reduceIte]
theorem lnK1_t (h : r.headD 0 ≠ 0) : lnK1 p n mode vis d a b (some (r, m)) =
    lnK4 (callW p n "defeq" [mode, vis, d, r.tail.headD 0, b] m) := by
  simp only [lnK1, h, ne_eq, not_false_eq_true, ↓reduceIte]
theorem lnK1_f (h : r.headD 0 = 0) : lnK1 p n mode vis d a b (some (r, m)) =
    lnK2 p n mode vis d a (callW p n "reduce_nat" [mode, vis, d, b] m) := by
  simp only [lnK1, h, ne_eq, not_true_eq_false, ↓reduceIte]
end lnK

theorem lazyNat_spec (p : Prog) (hp : LazyProg p) (n : Nat) (s₀ : St) (mode vis d a b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "lazy_nat" [mode, vis, d, a, b]
    ⦃fun r s' => LocEq s' s₀ ∧ lnK1 p n mode vis d a b (callW p n "reduce_nat" [mode, vis, d, a] s₀.mem) =
      some (r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.nat]
  simp only [callFn, lazyNatL]
  sym (gen := 80) (instances := 5000) only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "reduce_nat",
      callW_spec p n "defeq"] <;>
    finish [lnK1_t, lnK1_f, lnK2_t, lnK2_f, lnK4_s, St.setLocs_mem']

theorem decNat_ite (w : Word) (r : List Word) (h : (if w ≠ 0 then (1 : Word) else 0) = r.headD 0) :
    decNat r = some (w != 0) := by
  unfold decNat; rw [← h]
  by_cases hw : w = 0
  · subst hw; rfl
  · simp only [ne_eq, hw, not_false_eq_true, ↓reduceIte, Option.some.injEq]
    simp [hw]

theorem resH_ite' (w : Word) (r : List Word) (h : (if w ≠ 0 then (1 : Word) else 0) = r.headD 0) :
    ResH r := by
  unfold ResH HW; rw [← h]; split <;> decide

/-- **`lazy_nat` refines `natT`** at the knot. -/
theorem lazyNat_refines (p : Prog) (hp : LazyProg p) (hc : LazyCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) :
    CoreSpec p (n + 1) "lazy_nat" [mode, vis, d, a, b]
      (natT (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) decNat s₀ a₀ dn vis fe
      M eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun (lazyNat_spec p hp n s₀ mode vis d a b)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hS := hs.rel
  unfold natT
  cases hc1 : callW p n "reduce_nat" [mode, vis, d, a] s.mem with
  | none => rw [hc1] at hW; cases hW
  | some q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [hc1] at hW
  have e₁ := CoreSpec.of_callW (hc.reduceNat n F s a₀ dn vis fe M eb mode d a hF hs ha hk) hc1
  refine coreRef_bind e₁ (fun M₁ hS₁ => ?_)
  -- a `defeq` run, then `pure (some v)`
  have dq : ∀ (x y : Word) (m₂ : Mem) (M₂ : ModeMaps) (a₂ : AState), CoreS dn m₂ a₂ vis fe M₂ eb →
      HW x → HW y →
      lnK4 (callW p n "defeq" [mode, vis, d, x, y] m₂) =
        some (r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, s'.mem) →
      CoreRef ((coreKnot (decMode mode) fe id F).defeq d.toNat (decE x) (decE y) >>= fun v =>
        pure (some v)) a₂ decNat dn m₂ vis fe M₂ eb r s'.mem := by
    intro x y m₂ M₂ a₂ hS₂ hx hy h
    cases hc2 : callW p n "defeq" [mode, vis, d, x, y] m₂ with
    | none => rw [hc2] at h; cases h
    | some q =>
    obtain ⟨r₂, m₃⟩ := q
    rw [hc2, lnK4_s, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq] at h
    obtain ⟨g1, g2, g3, hm⟩ := h
    have e₂ := CoreSpec.of_callW (s₀ := ⟨m₂, Locals.init []⟩)
      ((hk n (Nat.le_refl _)).defeq F _ _ dn vis fe M₂ eb mode d x y hF hn ⟨hS₂, hs.mode4, hs.eb_mode⟩
        hx hy) hc2
    refine coreRef_bind e₂ (fun M₃ hS₃ => ?_)
    rw [← hm]
    exact coreRef_ret hS₃ (decNat_ite _ _ g1).symm (resH_ite' _ _ g1)
  by_cases h1 : r₁.headD 0 ≠ 0
  · rw [lnK1_t (h := h1)] at hW
    rw [decOptR_some h1]
    exact dq _ _ _ _ _ hS₁ e₁.2.2.2.2 hb hW
  have h1' : r₁.headD 0 = 0 := by simpa using h1
  rw [lnK1_f (h := h1')] at hW
  rw [decOptR_none h1']
  cases hc2 : callW p n "reduce_nat" [mode, vis, d, b] m₁ with
  | none => rw [hc2] at hW; cases hW
  | some q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [hc2] at hW
  have e₂ := CoreSpec.of_callW (s₀ := ⟨m₁, Locals.init []⟩)
    (hc.reduceNat n F ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode d b hF ⟨hS₁, hs.mode4, hs.eb_mode⟩ hb hk) hc2
  refine coreRef_bind e₂ (fun M₂ hS₂ => ?_)
  by_cases h2 : r₂.headD 0 ≠ 0
  · rw [lnK2_t (h := h2)] at hW
    rw [decOptR_some h2]
    exact dq _ _ _ _ _ hS₂ ha e₂.2.2.2.2 hW
  have h2' : r₂.headD 0 = 0 := by simpa using h2
  rw [lnK2_f (h := h2'), Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq] at hW
  obtain ⟨g1, g2, g3, hm⟩ := hW
  rw [decOptR_none h2', ← hm]
  exact coreRef_ret hS₂ (by simp only [decNat, ← g1, ↓reduceIte]) (by unfold ResH; rw [← g1]; exact hw3)

end L.Arena
