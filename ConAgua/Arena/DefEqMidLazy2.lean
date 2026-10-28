import ConAgua.Arena.DefEqMidLazy
import ConAgua.Verdict.WhnfNatE
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen

/-!
# The lazy-delta loop: `lazy_nat`, `lazy_iter`, `lazy_delta_reduction` (lane `defeq`)

One iteration of the twin's `lazyDeltaReduction` is `iterT` (offsets, the literal acceleration
`natT`, one `lazyDeltaStep`), answering a result (`inl`) or the next pair (`inr`); the twin's loop
is `iterT` then its own recursion (`lazyLvl_eq`, the unfolding by `delta` and `rfl` as
`defeqPeel`'s). `lazy_iter` refines `iterT`, the uncounted L loop the twin's at
`defeqLoopFuel = 2^62`, both outcomes (`lazy_ref`).
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

theorem decNat_ite (w : Word) (r : List Word) (h : (if w ≠ 0 then (1 : Word) else 0) = r.headD 0) :
    decNat r = some (w != 0) := by
  unfold decNat; rw [← h]
  by_cases hw : w = 0
  · subst hw; rfl
  · simp only [ne_eq, hw, not_false_eq_true, ↓reduceIte]
    simp [hw]

/-- What `lazy_nat`'s errors claim: the knot's slots' and `reduce_nat`'s. -/
structure LnG (p : Prog) (n : Nat) : Prop where
  knot : KnotUpToE p n
  reduceNat : ReduceNatE p

/-- **`lazy_nat` refines `natT`, both outcomes**: the errors are `reduce_nat`'s and the `defeq`
slot's. -/
theorem ln_ref (p : Prog) (hc : LazyCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) :
    RefE (LnG p n) (lnE p (n + 1) s₀.mem mode vis d a b)
      (natT (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) a₀
      (CorePost decNat dn s₀.mem vis fe M eb NatW) := by
  simp only [lnE]
  unfold natT
  -- a `defeq` run, then `pure (some v)`
  have dq : ∀ (x y : Word) (m₂ : Mem) (M₂ : ModeMaps) (a₂ : AState), CoreS dn m₂ a₂ vis fe M₂ eb →
      HW x → HW y →
      RefE (LnG p n) (lnE.k_defeq p (callE p n "defeq" [mode, vis, d, x, y] m₂))
        ((coreKnot (decMode mode) fe id F).defeq d.toNat (decE x) (decE y) >>= fun v =>
          pure (some v)) a₂ (CorePost decNat dn m₂ vis fe M₂ eb NatW) := by
    intro x y m₂ M₂ a₂ hS₂ hx hy
    rcases c2 : callE p n "defeq" [mode, vis, d, x, y] m₂ with e2 | ⟨r₂, m₃⟩
    · exact fun hG => ErrClaim.bind_left (CoreSpecE.of_callE (s₀ := ⟨m₂, Locals.init []⟩)
        ((hG.knot n (Nat.le_refl _)).defeq F _ _ dn vis fe M₂ eb mode d x y hF hn
          ⟨hS₂, hs.mode4, hs.eb_mode⟩ hx hy) c2)
    have e₂ := CoreSpec.of_callW (s₀ := ⟨m₂, Locals.init []⟩)
      ((hk n (Nat.le_refl _)).defeq F _ _ dn vis fe M₂ eb mode d x y hF hn ⟨hS₂, hs.mode4, hs.eb_mode⟩
        hx hy) (callW_of_callE c2)
    refine RefE.bind_core (w := id) e₂ (fun M₃ hS₃ _ => ?_)
    exact RefE.ret rfl (CorePost.ret hS₃ (decNat_ite _ _ rfl).symm (by
      unfold NatW; split
      · exact .inr (.inl rfl)
      · exact .inl rfl))
  rcases c1 : callE p n "reduce_nat" [mode, vis, d, a] s₀.mem with e1 | ⟨r₁, m₁⟩
  · exact fun hG => ErrClaim.bind_left (CoreSpecE.of_callE
      (hG.reduceNat n hk hG.knot F s₀ a₀ dn vis fe M eb mode d a hF hn hs ha) c1)
  have e₁ := CoreSpec.of_callW (hc.reduceNat n hn F s₀ a₀ dn vis fe M eb mode d a hF hs ha hk)
    (callW_of_callE c1)
  refine RefE.bind_core (w := id) e₁ (fun M₁ hS₁ _ => ?_)
  by_cases h1 : r₁.headD 0 ≠ 0
  · simp only [lnE.k_reduce_nat, decOptR_some h1]; rw [ite_eq_left h1]
    exact dq _ _ _ _ _ hS₁ e₁.2.2.2.2 hb
  have h1' : r₁.headD 0 = 0 := by simpa using h1
  simp only [lnE.k_reduce_nat, h1', ne_eq, not_true_eq_false, ↓reduceIte, decOptR_none h1']
  rcases c2 : callE p n "reduce_nat" [mode, vis, d, b] m₁ with e2 | ⟨r₂, m₂⟩
  · exact fun hG => ErrClaim.bind_left (CoreSpecE.of_callE (s₀ := ⟨m₁, Locals.init []⟩)
      (hG.reduceNat n hk hG.knot F _ _ dn vis fe M₁ eb mode d b hF hn ⟨hS₁, hs.mode4, hs.eb_mode⟩ hb) c2)
  have e₂ := CoreSpec.of_callW (s₀ := ⟨m₁, Locals.init []⟩)
    (hc.reduceNat n hn F ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode d b hF ⟨hS₁, hs.mode4, hs.eb_mode⟩ hb hk)
    (callW_of_callE c2)
  refine RefE.bind_core (w := id) e₂ (fun M₂ hS₂ _ => ?_)
  by_cases h2 : r₂.headD 0 ≠ 0
  · simp only [lnE.k_reduce_nat_2, decOptR_some h2]; rw [ite_eq_left h2]
    exact dq _ _ _ _ _ hS₂ ha e₂.2.2.2.2
  have h2' : r₂.headD 0 = 0 := by simpa using h2
  simp only [lnE.k_reduce_nat_2, h2', ne_eq, not_true_eq_false, ↓reduceIte, decOptR_none h2']
  exact RefE.ret rfl (CorePost.ret hS₂ (by simp only [decNat]; rfl) (.inr (.inr rfl)))

/-- **`lazy_nat` refines `natT`** at the knot (`ln_ref`'s ok half). -/
theorem lazyNat_refines (p : Prog) (hp : LazyProg p) (hc : LazyCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) :
    CoreSpec p (n + 1) "lazy_nat" [mode, vis, d, a, b]
      (natT (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) decNat s₀ a₀ dn vis fe
      M eb NatW :=
  RefE.coreSpec (lnE_spec p hp.nat (n + 1) s₀ mode vis d a b)
    (ln_ref p hc n hk F hF hn s₀ a₀ dn vis fe M eb mode d a b hs ha hb)

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

/-- **`lazy_delta_reduction`'s model, both outcomes** (the loop `ldrE.loop1`: one `lazy_iter`
run per iteration, `callE`). -/
l_model lazyDeltaReduction_specE (p : Prog)
    (hf : p.lookup "lazy_delta_reduction" = some lazyDeltaReductionL)
  fns [hf ↦ ldrE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] unified

/-- **`lazy_iter`'s error claim** at every L fuel up to `n` (what the loop's errors claim from;
`lazyIter_refinesE`, `Verdict/DefEqLazyE.lean`). -/
def LazyIterUpToE (p : Prog) (n : Nat) : Prop :=
  ∀ j, j ≤ n → ∀ (F : Nat), j ≤ F → j ≤ 2 ^ 62 →
  ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d a b : Word), SlotPre s₀ a₀ dn vis fe M eb mode → HW a → HW b →
    d.toNat < 2 ^ 63 →
    CoreSpecE p (j + 1) "lazy_iter" [mode, vis, d, a, b]
      (iterT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) s₀ a₀

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
/-- **The loop refines `lazyDeltaReduction`, both outcomes**, at every twin fuel `K` with
`j ≤ K + 1`: each iteration is `lazy_iter`'s (`lazyIter_refines`, its claim `LazyIterUpToE`). -/
theorem lazy_ref (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (mode d : Word) (hmode : mode < 4)
    (hd : d.toNat < 2 ^ 63) :
    ∀ j, j ≤ n + 1 → ∀ K, j ≤ K + 1 → ∀ (a b : Word) (m : Mem) (s : AState) (M : ModeMaps)
      (eb : Word), CoreS dn m s vis fe M eb → eb = (mode >>> 1) &&& 1 → HW a → HW b →
      RefE (LazyIterUpToE p n) (ldrE.loop1 p j m mode vis d a b)
        (lazyDeltaReduction (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat K
          (decE a) (decE b)) s
        (fun v y a' => CorePost decLR dn m vis fe M eb Res3 v y a') := by
  intro j
  induction j with
  | zero =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _
    unfold ldrE.loop1; exact RefE.of_cls0 rfl
  | succ j ih =>
    intro hjn K hK a b m s M eb hS heb ha hb
    rw [ldrE.loop1.arm1 (hc1 := rfl)]
    rcases hc1 : callE p j "lazy_iter" [mode, vis, d, a, b] m with e | ⟨r, m₁⟩
    · rw [ldrE.k_lazy_iter.none]
      cases j with
      | zero =>
        obtain ⟨e', he', h0⟩ := callE_zero p "lazy_iter" [mode, vis, d, a, b] m
        rw [hc1] at he'; cases he'; exact RefE.of_cls0 h0
      | succ j' =>
      obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
      rw [lazyDeltaReduction_succ_eq, lazyLvl_eq]
      exact RefE.bind_left fun hG => CoreSpecE.of_callE (s₀ := ⟨m, Locals.init []⟩)
        (hG j' (by omega) F (by omega) (by omega) _ s dn vis fe M eb mode d a b ⟨hS, hmode, heb⟩
          ha hb hd) hc1
    obtain ⟨j', rfl⟩ := callW_succ (callW_of_callE hc1)
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    rw [lazyDeltaReduction_succ_eq, lazyLvl_eq]
    have e := CoreSpec.of_callW (s₀ := ⟨m, Locals.init []⟩)
      (lazyIter_refines p hp hc j' (hk.mono (by omega)) F (by omega) (by omega) _ s dn vis fe M eb mode
        d a b ⟨hS, hmode, heb⟩ ha hb hd) (callW_of_callE hc1)
    obtain ⟨g0, hr1, hr2⟩ := e.2.2.2
    refine RefE.bind_core (w := id) e (fun M₁ hS₁ _ => ?_)
    by_cases h3 : r.headD 0 ≠ 3
    · rw [ldrE.k_lazy_iter.arm1 (hc1 := h3), decIter_done h3]
      exact RefE.ret rfl (CorePost.ret hS₁ rfl ⟨g0, hr1, hr2⟩)
    have h3' : r.headD 0 = 3 := by simpa using h3
    rw [ldrE.k_lazy_iter.arm2 (hc1 := h3'), decIter_cont h3']
    exact ih (by omega) K' (by omega) _ _ m₁ _ M₁ eb hS₁ heb hr1 hr2

include hp hc in
/-- `lazy_delta_reduction` from its run, both outcomes (`lazy_ref` at `defeqLoopFuel`). -/
theorem lazyDeltaReduction_ref (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode)
    (ha : HW a) (hb : HW b) (hd : d.toNat < 2 ^ 63) :
    RefE (LazyIterUpToE p n) (ldrE p (n + 1) s₀.mem mode vis d a b)
      (lazyDeltaReduction (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat defeqLoopFuel
        (decE a) (decE b)) a₀
      (fun v y a' => CorePost decLR dn s₀.mem vis fe M eb Res3 v y a') := by
  rw [ldrE.arm1]
  have hL : (2 : Nat) ^ 62 = defeqLoopFuel := rfl
  exact lazy_ref p hp hc n hk F hF hn dn vis fe mode d hs.mode4 hd (n + 1) (Nat.le_refl _)
    defeqLoopFuel (by rw [← hL]; omega) a b s₀.mem a₀ M eb hs.rel hs.eb_mode ha hb

include hp hc in
/-- **`lazy_delta_reduction` refines `lazyDeltaReduction` at `defeqLoopFuel`** (the twin's call in
`defeqBody`; `lazyDeltaReduction_ref`'s ok half). -/
@[refines ConRon.Arena.lazyDeltaReduction]
theorem lazyDeltaReduction_refines (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode)
    (ha : HW a) (hb : HW b) (hd : d.toNat < 2 ^ 63) :
    CoreSpec p (n + 1) "lazy_delta_reduction" [mode, vis, d, a, b]
      (lazyDeltaReduction (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat defeqLoopFuel
        (decE a) (decE b)) decLR s₀ a₀ dn vis fe M eb Res3 :=
  CoreSpec.of_refE (w := id)
    (lazyDeltaReduction_specE p hp.red (n + 1) s₀ mode vis d a b)
    (lazyDeltaReduction_ref p hp hc n hk F hF hn s₀ a₀ dn vis fe M eb mode d a b hs ha hb hd)
    fun _ _ => ⟨rfl, rfl, id⟩

end loopRef

end L.Arena
