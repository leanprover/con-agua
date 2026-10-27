import ConAgua.Arena.DefEqMidLazy
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen

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

/-- `lazy_nat`'s answer word: `0`, `1` (a verdict) or `3` (no reduct). -/
def NatW (r : List Word) : Prop := r.headD 0 = 0 ∨ r.headD 0 = 1 ∨ r.headD 0 = 3

/-- `(k, 0, 0)`: `3` none, else `some (k != 0)`. -/
def decNat (r : List Word) : Option Bool := if r.headD 0 = 3 then none else some (r.headD 0 != 0)

/-- **`lazy_nat` is its model `lnW`** (generated). -/
l_model lazyNat_spec (p : Prog) (hp : LazyProg p)
  fns [hp.nat ↦ lnW tuple]
  specs [callW_spec p n "reduce_nat", callW_spec p n "defeq"]
  grind [arena_grind] simp [St.setLocs_mem']

theorem decNat_ite (w : Word) (r : List Word) (h : (if w ≠ 0 then (1 : Word) else 0) = r.headD 0) :
    decNat r = some (w != 0) := by
  unfold decNat; rw [← h]
  by_cases hw : w = 0
  · subst hw; rfl
  · simp only [ne_eq, hw, not_false_eq_true, ↓reduceIte]
    simp [hw]

/-- **`lazy_nat` refines `natT`** at the knot. -/
theorem lazyNat_refines (p : Prog) (hp : LazyProg p) (hc : LazyCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) :
    CoreSpec p (n + 1) "lazy_nat" [mode, vis, d, a, b]
      (natT (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) decNat s₀ a₀ dn vis fe
      M eb NatW := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun (lazyNat_spec p hp (n + 1) s₀ mode vis d a b)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hS := hs.rel
  unfold natT
  rw [lnW.arm1] at hW
  cases hc1 : callW p n "reduce_nat" [mode, vis, d, a] s.mem with
  | none => rw [hc1] at hW; cases hW
  | some q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [hc1] at hW
  have e₁ := CoreSpec.of_callW (hc.reduceNat n hn F s a₀ dn vis fe M eb mode d a hF hs ha hk) hc1
  refine coreRef_bind e₁ (fun M₁ hS₁ => ?_)
  -- a `defeq` run, then `pure (some v)`
  have dq : ∀ (x y : Word) (m₂ : Mem) (M₂ : ModeMaps) (a₂ : AState), CoreS dn m₂ a₂ vis fe M₂ eb →
      HW x → HW y →
      lnW.k_defeq p (callW p n "defeq" [mode, vis, d, x, y] m₂) =
        some (r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, s'.mem) →
      CoreRef ((coreKnot (decMode mode) fe id F).defeq d.toNat (decE x) (decE y) >>= fun v =>
        pure (some v)) a₂ decNat dn m₂ vis fe M₂ eb r s'.mem NatW := by
    intro x y m₂ M₂ a₂ hS₂ hx hy h
    cases hc2 : callW p n "defeq" [mode, vis, d, x, y] m₂ with
    | none => rw [hc2] at h; cases h
    | some q =>
    obtain ⟨r₂, m₃⟩ := q
    rw [hc2, lnW.k_defeq.arm1, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq] at h
    obtain ⟨g1, g2, g3, hm⟩ := h
    have e₂ := CoreSpec.of_callW (s₀ := ⟨m₂, Locals.init []⟩)
      ((hk n (Nat.le_refl _)).defeq F _ _ dn vis fe M₂ eb mode d x y hF hn ⟨hS₂, hs.mode4, hs.eb_mode⟩
        hx hy) hc2
    refine coreRef_bind e₂ (fun M₃ hS₃ => ?_)
    rw [← hm]
    exact coreRef_ret hS₃ (decNat_ite _ _ g1).symm (by
      unfold NatW; rw [← g1]; split
      · exact .inr (.inl rfl)
      · exact .inl rfl)
  by_cases h1 : r₁.headD 0 ≠ 0
  · rw [lnW.k_reduce_nat.arm1 (hc1 := h1)] at hW
    rw [decOptR_some h1]
    exact dq _ _ _ _ _ hS₁ e₁.2.2.2.2 hb hW
  have h1' : r₁.headD 0 = 0 := by simpa using h1
  rw [lnW.k_reduce_nat.arm2 (hc1 := h1')] at hW
  rw [decOptR_none h1']
  cases hc2 : callW p n "reduce_nat" [mode, vis, d, b] m₁ with
  | none => rw [hc2] at hW; cases hW
  | some q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [hc2] at hW
  have e₂ := CoreSpec.of_callW (s₀ := ⟨m₁, Locals.init []⟩)
    (hc.reduceNat n hn F ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode d b hF ⟨hS₁, hs.mode4, hs.eb_mode⟩ hb hk) hc2
  refine coreRef_bind e₂ (fun M₂ hS₂ => ?_)
  by_cases h2 : r₂.headD 0 ≠ 0
  · rw [lnW.k_reduce_nat_2.arm1 (hc1 := h2)] at hW
    rw [decOptR_some h2]
    exact dq _ _ _ _ _ hS₂ ha e₂.2.2.2.2 hW
  have h2' : r₂.headD 0 = 0 := by simpa using h2
  rw [lnW.k_reduce_nat_2.arm2 (hc1 := h2'), Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq] at hW
  obtain ⟨g1, g2, g3, hm⟩ := hW
  rw [decOptR_none h2', ← hm]
  exact coreRef_ret hS₂ (by simp only [decNat, ← g1, ↓reduceIte]) (.inr (.inr g1.symm))

/-! ## One iteration -/

/-- One iteration of the twin's `lazyDeltaReduction`: a result (`inl`), or the pair to go on
with (`inr`). -/
def iterT (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (a b : EIdx) :
    AM (LazyResA ⊕ (EIdx × EIdx)) := do
  match ← defeqOffset r depth a b with
  | some v => pure (.inl (.verdict v))
  | none =>
  let nf ← lazyFoldOk mode a b
  let o ← if nf then natT r fe depth a b else pure none
  match o with
  | some v => pure (.inl (.verdict v))
  | none =>
  match ← lazyDeltaStep mode r fe depth a b with
  | .cont a' b' => pure (.inr (a', b'))
  | .eq => pure (.inl (.verdict true))
  | .diff => pure (.inl (.verdict false))
  | .unknown => pure (.inl (.unknown a b))

/-- One level of the twin's `lazyDeltaReduction`, verbatim, the recursion abstracted as `cont`. -/
def lazyLvl (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (cont : EIdx → EIdx → AM LazyResA) (a b : EIdx) : AM LazyResA := do
    match ← defeqOffset r depth a b with
    | some v => pure (.verdict v)
    | none =>
    let nf ← lazyFoldOk mode a b
    match ← (if nf then reduceNat r fe depth a else pure none) with
    | some a₂ => do
      let v ← r.defeq depth a₂ b
      pure (.verdict v)
    | none =>
    match ← (if nf then reduceNat r fe depth b else pure none) with
    | some b₂ => do
      let v ← r.defeq depth a b₂
      pure (.verdict v)
    | none =>
    match ← lazyDeltaStep mode r fe depth a b with
    | .cont a' b' => cont a' b'
    | .eq => pure (.verdict true)
    | .diff => pure (.verdict false)
    | .unknown => pure (.unknown a b)

theorem lazyDeltaReduction_succ_eq (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv)
    (depth n : Nat) (a b : EIdx) :
    lazyDeltaReduction mode r fe depth (n + 1) a b =
      lazyLvl mode r fe depth (lazyDeltaReduction mode r fe depth n) a b := by
  delta lazyDeltaReduction lazyLvl
  exact rfl

theorem lazyLvl_eq (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (cont : EIdx → EIdx → AM LazyResA) (a b : EIdx) :
    lazyLvl mode r fe depth cont a b = (iterT mode r fe depth a b >>= fun x => match x with
      | .inl res => pure res
      | .inr (a', b') => cont a' b') := by
  unfold lazyLvl iterT natT
  simp only [bind_assoc]
  congr 1; funext o
  cases o with
  | some v => simp only [pure_bind]
  | none =>
  simp only [bind_assoc]
  congr 1; funext nf
  cases nf with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, pure_bind, bind_assoc]
    congr 1; funext st
    cases st <;> simp only [pure_bind]
  | true =>
    simp only [↓reduceIte, bind_assoc]
    congr 1; funext x
    cases x with
    | some a₂ => simp only [bind_assoc, pure_bind]
    | none =>
      simp only [bind_assoc]
      congr 1; funext y
      cases y with
      | some b₂ => simp only [bind_assoc, pure_bind]
      | none =>
        simp only [pure_bind, bind_assoc]
        congr 1; funext st
        cases st <;> simp only [pure_bind]

/-! ## `lazy_iter` -/

instance : Inhabited (LazyResA ⊕ (EIdx × EIdx)) := ⟨.inl (.verdict false)⟩

/-- `(k, x, y)`: `0`/`1` a verdict, `3` go on with `(x, y)`, else `.unknown x y` (`2`). -/
def decIter (r : List Word) : LazyResA ⊕ (EIdx × EIdx) :=
  if r.headD 0 = 0 then .inl (.verdict false)
  else if r.headD 0 = 1 then .inl (.verdict true)
  else if r.headD 0 = 3 then .inr (decE (r.tail.headD 0), decE (r.tail.tail.headD 0))
  else .inl (.unknown (decE (r.tail.headD 0)) (decE (r.tail.tail.headD 0)))

/-- **`lazy_iter` is its model `itW`** (generated). -/
l_model lazyIter_spec (p : Prog) (hp : LazyProg p)
  fns [hp.iter ↦ itW tuple]
  specs [callW_spec p n "defeq_offset", callW_spec p n "lazy_fold_ok", callW_spec p n "lazy_nat",
    callW_spec p n "lazy_delta_step"]
  grind [arena_grind] heartbeats 1000000 simp [St.setLocs_mem']

/-- **`lazy_iter` refines `iterT`** at the knot. -/
theorem lazyIter_refines (p : Prog) (hp : LazyProg p) (hc : LazyCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) (hd : d.toNat < 2 ^ 63) :
    CoreSpec p (n + 1) "lazy_iter" [mode, vis, d, a, b]
      (iterT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) decIter
      s₀ a₀ dn vis fe M eb Res3 := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun (lazyIter_spec p hp (n + 1) s₀ mode vis d a b)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hS := hs.rel
  -- the step arm
  have stepArm : ∀ (m₃ : Mem) (M₃ : ModeMaps) (a₃ : AState), CoreS dn m₃ a₃ vis fe M₃ eb →
      itW.j1 p n mode vis d a b m₃ = some (r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, s'.mem) →
      CoreRef (lazyDeltaStep (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE a)
        (decE b) >>= fun st => match st with
          | .cont a' b' => pure (.inr (a', b'))
          | .eq => pure (.inl (.verdict true))
          | .diff => pure (.inl (.verdict false))
          | .unknown => pure (.inl (.unknown (decE a) (decE b))))
        a₃ decIter dn m₃ vis fe M₃ eb r s'.mem Res3 := by
    intro m₃ M₃ a₃ hS₃ h
    rw [itW.j1.arm1] at h
    cases hc4 : callW p n "lazy_delta_step" [mode, vis, d, a, b] m₃ with
    | none => rw [hc4] at h; cases h
    | some q =>
    obtain ⟨rs, m₄⟩ := q
    rw [hc4] at h
    obtain ⟨k, rfl⟩ := callW_succ hc4
    have e₄ := CoreSpec.of_callW (s₀ := ⟨m₃, Locals.init []⟩)
      (lazyDeltaStep_refines p hp hc k (hk.mono (by omega)) F (by omega) (by omega) _ a₃ dn vis fe M₃
        eb mode d a b ⟨hS₃, hs.mode4, hs.eb_mode⟩ ha hb hd) hc4
    refine coreRef_bind e₄ (fun M₄ hS₄ => ?_)
    obtain ⟨-, hx, hy⟩ := e₄.2.2.2
    by_cases k0 : rs.headD 0 = 0
    · rw [itW.k_lazy_delta_step.arm1 (hc1 := k0), Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq] at h
      obtain ⟨g1, g2, g3, hm⟩ := h
      have : decDS rs = .cont (decE (rs.tail.headD 0)) (decE (rs.tail.tail.headD 0)) := by
        simp only [decDS, k0, ↓reduceIte]
      rw [this, ← hm]
      exact coreRef_ret hS₄ (by simp only [decIter, ← g1, ← g2, ← g3]; rfl)
        (res3_of hw3 hx hy g1 g2 g3)
    by_cases k1 : rs.headD 0 = 1
    · rw [itW.k_lazy_delta_step.arm2 (hc1 := k0) (hc2 := k1), Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq] at h
      obtain ⟨g1, g2, g3, hm⟩ := h
      have : decDS rs = .eq := by rw [decDS, ite_eq_right k0, ite_eq_left k1]
      rw [this, ← hm]
      exact coreRef_ret hS₄ (by simp only [decIter, ← g1]; rfl) (res3_of hw1 hw0 hw0 g1 g2 g3)
    by_cases k2 : rs.headD 0 = 2
    · rw [itW.k_lazy_delta_step.arm3 (hc1 := k0) (hc2 := k1) (hc3 := k2), Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq] at h
      obtain ⟨g1, g2, g3, hm⟩ := h
      have : decDS rs = .diff := by rw [decDS, ite_eq_right k0, ite_eq_right k1, ite_eq_left k2]
      rw [this, ← hm]
      exact coreRef_ret hS₄ (by simp only [decIter, ← g1]; rfl) (res3_of hw0 hw0 hw0 g1 g2 g3)
    rw [itW.k_lazy_delta_step.arm4 (hc1 := k0) (hc2 := k1) (hc3 := k2), Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq,
      Prod.mk.injEq] at h
    obtain ⟨g1, g2, g3, hm⟩ := h
    have : decDS rs = .unknown := by rw [decDS, ite_eq_right k0, ite_eq_right k1, ite_eq_right k2]
    rw [this, ← hm]
    exact coreRef_ret hS₄ (by simp only [decIter, ← g1, ← g2, ← g3]; rfl) (res3_of hw2 ha hb g1 g2 g3)
  unfold iterT
  rw [itW.arm1] at hW
  cases hc1 : callW p n "defeq_offset" [mode, vis, d, a, b] s.mem with
  | none => rw [hc1] at hW; cases hW
  | some q =>
  obtain ⟨ro, m₁⟩ := q
  rw [hc1] at hW
  obtain ⟨k, rfl⟩ := callW_succ hc1
  have e₁ := CoreSpec.of_callW (defeqOffset_refines p hp.mid hc.natPred k (hk.mono (by omega)) F s a₀
    dn vis fe M eb mode d a b (by omega) (by omega) hs ha hb) hc1
  refine coreRef_bind e₁ (fun M₁ hS₁ => ?_)
  by_cases h0 : ro.headD 0 ≠ 0
  · rw [itW.k_defeq_offset.arm1 (hc1 := h0), Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq] at hW
    obtain ⟨g1, g2, g3, hm⟩ := hW
    have : decOB ro = some (ro.tail.headD 0 != 0) := by simp only [decOB, h0, ↓reduceIte]
    rw [this, ← hm]
    by_cases hv : ro.tail.headD 0 ≠ 0
    · rw [ite_eq_left hv] at g1
      have hb' : (ro.tail.headD 0 != 0) = true := bne_iff_ne.mpr hv
      exact coreRef_ret hS₁ (by rw [hb']; simp only [decIter, ← g1]; rfl)
        (res3_of hw1 hw0 hw0 g1 g2 g3)
    · have hv' : ro.tail.headD 0 = 0 := by simpa using hv
      rw [ite_eq_right hv] at g1
      exact coreRef_ret hS₁ (by simp only [decIter, ← g1, hv']; rfl) (res3_of hw0 hw0 hw0 g1 g2 g3)
  have h0' : ro.headD 0 = 0 := by simpa using h0
  rw [itW.k_defeq_offset.arm2 (hc1 := h0')] at hW
  have : decOB ro = none := by simp only [decOB, h0', ↓reduceIte]
  rw [this]
  cases hc2 : callW p (k + 1) "lazy_fold_ok" [mode, a, b] m₁ with
  | none => rw [hc2] at hW; cases hW
  | some q =>
  obtain ⟨rf, m₂⟩ := q
  rw [hc2] at hW
  have e₂ := CoreSpec.of_callW (s₀ := ⟨m₁, Locals.init []⟩)
    (lazyFoldOk_refines p hp.mid hc.hasFvar k _ _ dn vis fe M₁ eb mode a b hS₁ hs.mode4 ha hb) hc2
  refine coreRef_bind e₂ (fun M₂ hS₂ => ?_)
  by_cases hf : rf.headD 0 ≠ 0
  · rw [itW.k_lazy_fold_ok.arm1 (hc1 := hf)] at hW
    rw [decBool_t hf]
    simp only [↓reduceIte]
    cases hc3 : callW p (k + 1) "lazy_nat" [mode, vis, d, a, b] m₂ with
    | none => rw [hc3] at hW; cases hW
    | some q =>
    obtain ⟨rn, m₃⟩ := q
    rw [hc3] at hW
    have e₃ := CoreSpec.of_callW (s₀ := ⟨m₂, Locals.init []⟩)
      (lazyNat_refines p hp hc k (hk.mono (by omega)) F (by omega) (by omega) _ _ dn vis fe M₂ eb mode
        d a b ⟨hS₂, hs.mode4, hs.eb_mode⟩ ha hb) hc3
    have hnw := e₃.2.2.2
    refine coreRef_bind e₃ (fun M₃ hS₃ => ?_)
    by_cases h3 : rn.headD 0 ≠ 3
    · rw [itW.k_lazy_nat.arm1 (hc1 := h3), Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq] at hW
      obtain ⟨g1, g2, g3, hm⟩ := hW
      have : decNat rn = some (rn.headD 0 != 0) := by simp only [decNat, h3, ↓reduceIte]
      rw [this, ← hm]
      rcases hnw with e0 | e1 | e3
      · exact coreRef_ret hS₃ (by simp only [decIter, ← g1, e0]; rfl)
          (res3_of hw0 hw0 hw0 (e0.symm.trans g1) g2 g3)
      · exact coreRef_ret hS₃ (by simp only [decIter, ← g1, e1]; rfl)
          (res3_of hw1 hw0 hw0 (e1.symm.trans g1) g2 g3)
      · exact absurd e3 h3
    have h3' : rn.headD 0 = 3 := by simpa using h3
    rw [itW.k_lazy_nat.arm2 (hc1 := h3')] at hW
    have : decNat rn = none := by simp only [decNat, h3', ↓reduceIte]
    rw [this]
    exact stepArm _ _ _ hS₃ hW
  have hf' : rf.headD 0 = 0 := by simpa using hf
  rw [itW.k_lazy_fold_ok.arm2 (hc1 := hf')] at hW
  rw [decBool_f hf']
  simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]
  exact stepArm _ _ _ hS₂ hW

/-! ## The loop -/

/-- **The model of `lazy_delta_reduction`'s loop** at L fuel `j`. -/
def lazyW (p : Prog) : Nat → Mem → Word → Word → Word → Word → Word →
    Option (Word × Word × Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | j + 1, m, mode, vis, d, a, b =>
    match callW p j "lazy_iter" [mode, vis, d, a, b] m with
    | none => none
    | some (r, m₁) =>
      if r.headD 0 ≠ 3 then some (r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, m₁)
      else lazyW p j m₁ mode vis d (r.tail.headD 0) (r.tail.tail.headD 0)

section lzArms
variable (p : Prog) (j : Nat) (m m₁ : Mem) (mode vis d a b : Word) (r : List Word)
theorem lazyW_n (hc : callW p j "lazy_iter" [mode, vis, d, a, b] m = none) :
    lazyW p (j + 1) m mode vis d a b = none := by simp only [lazyW, hc]
theorem lazyW_done (hc : callW p j "lazy_iter" [mode, vis, d, a, b] m = some (r, m₁))
    (h : r.headD 0 ≠ 3) :
    lazyW p (j + 1) m mode vis d a b = some (r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, m₁) := by
  simp only [lazyW, hc, h, ne_eq, not_false_eq_true, ↓reduceIte]
theorem lazyW_cont (hc : callW p j "lazy_iter" [mode, vis, d, a, b] m = some (r, m₁))
    (h : r.headD 0 = 3) :
    lazyW p (j + 1) m mode vis d a b = lazyW p j m₁ mode vis d (r.tail.headD 0) (r.tail.tail.headD 0) := by
  simp only [lazyW, hc, h, ne_eq, not_true_eq_false, ↓reduceIte]
end lzArms

theorem lazyDeltaLoop_spec (p : Prog) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n lazyDeltaLoop
    ⦃fun r s' => r ≠ .brk ∧
      lazyW p n s₀.mem (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 4) =
        some ((r.retOr [0]).headD 0, (r.retOr [0]).tail.headD 0, (r.retOr [0]).tail.tail.headD 0,
          s'.mem) ∧ r ≠ .normal; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := lazyDeltaLoop) rfl]
    sym (gen := 80) (instances := 5000) only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih, callW_spec p n "lazy_iter"] <;>
      finish [lazyW_n, lazyW_done, lazyW_cont, St.setLocs_mem']

theorem lazyDeltaReduction_spec (p : Prog) (hp : LazyProg p) (n : Nat) (s₀ : St) (mode vis d a b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "lazy_delta_reduction" [mode, vis, d, a, b]
    ⦃fun r s' => LocEq s' s₀ ∧ lazyW p (n + 1) s₀.mem mode vis d a b =
      some (r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.red]
  simp only [callFn, lazyDeltaReductionL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      fun s => Triple.step_exec (lazyDeltaLoop_spec p (n + 1) s)] <;>
    finish

theorem decIter_done {r : List Word} (h : r.headD 0 ≠ 3) : decIter r = .inl (decLR r) := by
  unfold decIter decLR
  by_cases h0 : r.headD 0 = 0
  · simp only [h0, ↓reduceIte]
  by_cases h1 : r.headD 0 = 1
  · simp only [h1, ↓reduceIte]; rfl
  rw [ite_eq_right h0, ite_eq_right h1, ite_eq_right h, ite_eq_right h0, ite_eq_right h1]

theorem decIter_cont {r : List Word} (h : r.headD 0 = 3) :
    decIter r = .inr (decE (r.tail.headD 0), decE (r.tail.tail.headD 0)) := by
  unfold decIter; rw [h]; rfl

section loopRef
variable (p : Prog) (hp : LazyProg p) (hc : LazyCallees p)

include hp hc in
/-- **The loop's model refines `lazyDeltaReduction`** at every twin fuel `K` with `j ≤ K + 1`. -/
theorem lazyW_ok (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (mode d : Word) (hmode : mode < 4)
    (hd : d.toNat < 2 ^ 63) :
    ∀ j, j ≤ n + 1 → ∀ K, j ≤ K + 1 → ∀ (a b : Word) (m m' : Mem) (s : AState) (M : ModeMaps)
      (eb x y z : Word), CoreS dn m s vis fe M eb → eb = (mode >>> 1) &&& 1 → HW a → HW b →
      lazyW p j m mode vis d a b = some (x, y, z, m') →
      CoreRef (lazyDeltaReduction (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat K
        (decE a) (decE b)) s decLR dn m vis fe M eb [x, y, z] m' Res3 := by
  intro j
  induction j with
  | zero => intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h; simp [lazyW] at h
  | succ j ih =>
    intro hjn K hK a b m m' s M eb x y z hS heb ha hb h
    cases hc1 : callW p j "lazy_iter" [mode, vis, d, a, b] m with
    | none => rw [lazyW_n (hc := hc1)] at h; cases h
    | some q =>
    obtain ⟨r, m₁⟩ := q
    obtain ⟨j', rfl⟩ := callW_succ hc1
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    rw [lazyDeltaReduction_succ_eq, lazyLvl_eq]
    have e := CoreSpec.of_callW (s₀ := ⟨m, Locals.init []⟩)
      (lazyIter_refines p hp hc j' (hk.mono (by omega)) F (by omega) (by omega) _ s dn vis fe M eb mode
        d a b ⟨hS, hmode, heb⟩ ha hb hd) hc1
    obtain ⟨-, hr1, hr2⟩ := e.2.2.2
    refine coreRef_bind e (fun M₁ hS₁ => ?_)
    by_cases h3 : r.headD 0 ≠ 3
    · rw [lazyW_done (hc := hc1) (h := h3), Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      rw [decIter_done h3]
      refine coreRef_ret hS₁ rfl ?_
      obtain ⟨g0, -, -⟩ := e.2.2.2
      exact ⟨g0, hr1, hr2⟩
    have h3' : r.headD 0 = 3 := by simpa using h3
    rw [lazyW_cont (hc := hc1) (h := h3')] at h
    rw [decIter_cont h3']
    exact ih (by omega) K' (by omega) _ _ m₁ m' _ M₁ eb x y z hS₁ heb hr1 hr2 h

include hp hc in
/-- **`lazy_delta_reduction` refines `lazyDeltaReduction` at `defeqLoopFuel`** (the twin's call in
`defeqBody`). -/
@[refines ConRon.Arena.lazyDeltaReduction]
theorem lazyDeltaReduction_refines (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode)
    (ha : HW a) (hb : HW b) (hd : d.toNat < 2 ^ 63) :
    CoreSpec p (n + 1) "lazy_delta_reduction" [mode, vis, d, a, b]
      (lazyDeltaReduction (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat defeqLoopFuel
        (decE a) (decE b)) decLR s₀ a₀ dn vis fe M eb Res3 := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (lazyDeltaReduction_spec p hp n s₀ mode vis d a b)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hL : (2 : Nat) ^ 62 = defeqLoopFuel := rfl
  obtain ⟨g1, g2, g3, g4⟩ := lazyW_ok p hp hc n hk F hF hn dn vis fe mode d hs.mode4 hd (n + 1)
    (Nat.le_refl _) defeqLoopFuel (by rw [← hL]; omega) a b s.mem s'.mem a₀ M eb _ _ _ hs.rel
    hs.eb_mode ha hb hW
  refine ⟨g1, g2, g3.trans rfl, ?_⟩
  obtain ⟨h1, h2, h3⟩ := g4
  exact ⟨h1, h2, h3⟩

end loopRef

end L.Arena
