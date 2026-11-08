module

public import ConAgua.Arena.DefEqMidLazy
public import ConAgua.Verdict.WhnfNatE
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.RefWalk
import ConAgua.Checker.NoVerdictTree
import ConAgua.Front.Preserve
import all ConAgua.Arena.DefEq

@[expose] public section

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
      (natT (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE a) (decE b)) a₀
      (CorePost decNat dn s₀.mem vis fe M eb NatW) := by
  simp only [lnE]
  unfold natT
  -- a `defeq` run, then `pure (some v)`
  have dq : ∀ (x y : Word) (m₂ : Mem) (M₂ : ModeMaps) (a₂ : AState), CoreS dn m₂ a₂ vis fe M₂ eb →
      HW x → HW y →
      RefE (LnG p n) (lnE.k_defeq p (callE p n "defeq" [mode, vis, d, x, y] m₂))
        ((coreKnot (decMode mode) (decEager mode) fe id F).defeq d.toNat (decE x) (decE y) >>= fun v =>
          pure (some v)) a₂ (CorePost decNat dn m₂ vis fe M₂ eb NatW) := by
    intro x y m₂ M₂ a₂ hS₂ hx hy
    have hs₂ : SlotPre ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode := ⟨hS₂, hs.mode4, hs.eb_mode⟩
    refine RefE.bind_callE (fun _ => rfl) ((hk n (Nat.le_refl _)).defeq F _ _ dn vis fe M₂ eb mode d x y hF hn
      hs₂ hx hy) (fun (hG : LnG p n) => (hG.knot n (Nat.le_refl _)).defeq F _ _ dn vis fe M₂ eb mode d x y hF
        hn hs₂ hx hy) fun r₂ m₃ _ e₂ => RefE.after_core (w := id) e₂ fun M₃ hS₃ _ => ?_
    exact RefE.ret rfl (CorePost.ret hS₃ (decNat_ite _ _ rfl).symm (by
      unfold NatW; split
      · exact .inr (.inl rfl)
      · exact .inl rfl))
  refine RefE.bind_callE (fun _ => rfl) (hc.reduceNat n hn F s₀ a₀ dn vis fe M eb mode d a hF hs ha hk)
    (fun (hG : LnG p n) => hG.reduceNat n hk hG.knot F s₀ a₀ dn vis fe M eb mode d a hF hn hs ha)
    fun r₁ m₁ _ e₁ => RefE.after_core (w := id) e₁ fun M₁ hS₁ _ => ?_
  by_cases h1 : r₁.headD 0 ≠ 0
  · simp only [lnE.k_reduce_nat, decOptR_some h1]; rw [ite_eq_left h1]
    exact dq _ _ _ _ _ hS₁ e₁.resOk.2 hb
  have h1' : r₁.headD 0 = 0 := by simpa using h1
  simp only [lnE.k_reduce_nat, h1', ne_eq, not_true_eq_false, ↓reduceIte, decOptR_none h1']
  have hs₁ : SlotPre ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode := ⟨hS₁, hs.mode4, hs.eb_mode⟩
  refine RefE.bind_callE (fun _ => rfl) (hc.reduceNat n hn F _ _ dn vis fe M₁ eb mode d b hF hs₁ hb hk)
    (fun (hG : LnG p n) => hG.reduceNat n hk hG.knot F _ _ dn vis fe M₁ eb mode d b hF hn hs₁ hb)
    fun r₂ m₂ _ e₂ => RefE.after_core (w := id) e₂ fun M₂ hS₂ _ => ?_
  by_cases h2 : r₂.headD 0 ≠ 0
  · simp only [lnE.k_reduce_nat_2, decOptR_some h2]; rw [ite_eq_left h2]
    exact dq _ _ _ _ _ hS₂ ha e₂.resOk.2
  have h2' : r₂.headD 0 = 0 := by simpa using h2
  simp only [lnE.k_reduce_nat_2, h2', ne_eq, not_true_eq_false, ↓reduceIte, decOptR_none h2']
  exact RefE.ret rfl (CorePost.ret hS₂ (by simp only [decNat]; rfl) (.inr (.inr rfl)))

/-- **`lazy_nat` refines `natT`** at the knot (`ln_ref`'s ok half). -/
theorem lazyNat_refines (p : Prog) (hp : LazyProg p) (hc : LazyCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) :
    CoreSpec p (n + 1) "lazy_nat" [mode, vis, d, a, b]
      (natT (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE a) (decE b)) decNat s₀ a₀ dn vis fe
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

/-- **`lazy_iter`'s model, both outcomes** (generated; `lazy_fold_ok` lifted, the other callees by
their unified models). -/
l_model itE_spec (p : Prog) (hf : p.lookup "lazy_iter" = some lazyIterL)
    (ho : p.lookup "defeq_offset" = some defeqOffsetL) (hna : p.lookup "lazy_nat" = some lazyNatL)
    (hst : p.lookup "lazy_delta_step" = some lazyDeltaStepL)
    (hbo : p.lookup "lds_both" = some ldsBothL)
    (ht : p.lookup "try_unfold_proj_app" = some tryUnfoldProjAppL)
    (hl : p.lookup "lds_left" = some ldsLeftL) (hr' : p.lookup "lds_right" = some ldsRightL)
    (hs : p.lookup "lds_same" = some ldsSameL)
    (hu : p.lookup "lds_unfold2" = some ldsUnfold2L) (hq : p.lookup "delta_quick" = some deltaQuickL)
    (h1 : p.lookup "defeq_spine" = some defeqSpineL) (h2 : p.lookup "defeq_spine2" = some defeqSpine2L)
    (hc : p.lookup "spine_cmp" = some spineCmpL) (hr : p.lookup "defeq_list_rev" = some defeqListRevL)
  fns [hf ↦ itE list]
  specs [offE_spec p ho n, callW_spec p n "lazy_fold_ok", lnE_spec p hna n,
    ldsE_spec p hst hbo ht hl hr' hs hu hq h1 h2 hc hr n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **What the lazy-delta loop's errors claim from**: the knot's slots and the verdict closure
(`KnotNvG`), `reduce_nat`'s claim (through `lazy_nat`). -/
structure LazyG (p : Prog) (n : Nat) : Prop extends KnotNvG p n where
  reduceNat : ReduceNatE p

theorem LazyG.mono {p : Prog} {n n' : Nat} (h : LazyG p n) (hn : n' ≤ n) : LazyG p n' :=
  ⟨h.toKnotNvG.mono hn, h.reduceNat⟩

/-- **`lazy_iter` refines `iterT`, both outcomes**: the errors are `defeq_offset`'s, `lazy_nat`'s
and `lazy_delta_step`'s. -/
theorem it_ref (p : Prog) (hp : LazyProg p) (hc : LazyCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) (hd : d.toNat < 2 ^ 63) :
    RefE (LazyG p n) (itE p (n + 1) s₀.mem mode vis d a b)
      (iterT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE a) (decE b)) a₀
      (CorePost decIter dn s₀.mem vis fe M eb Res3) := by
  have hS := hs.rel
  -- the step arm
  have stepArm : ∀ (m₃ : Mem) (M₃ : ModeMaps) (a₃ : AState), CoreS dn m₃ a₃ vis fe M₃ eb →
      RefE (LazyG p n) (itE.j1 p n mode vis d a b m₃)
        (lazyDeltaStep (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE a)
          (decE b) >>= fun st => match st with
          | .cont a' b' => pure (.inr (a', b'))
          | .eq => pure (.inl (.verdict true))
          | .diff => pure (.inl (.verdict false))
          | .unknown => pure (.inl (.unknown (decE a) (decE b))))
        a₃ (CorePost decIter dn m₃ vis fe M₃ eb Res3) := by
    intro m₃ M₃ a₃ hS₃
    cases n with
    | zero => exact RefE.of_cls0 (e := .outOfFuel) rfl
    | succ k =>
    simp only [itE.j1]
    refine RefE.bind_coreE (w := id) (fun _ => rfl) (fun hG => hG.toKnotNvG.mono (by omega))
      (lds_ref p hp hc k (hk.mono (by omega)) F (by omega) (by omega) ⟨m₃, Locals.init []⟩ a₃
        dn vis fe M₃ eb mode d a b ⟨hS₃, hs.mode4, hs.eb_mode⟩ ha hb hd)
      (fun rs m₄ _ hP M₄ hS₄ _ => ?_)
    simp only [itE.k_lazy_delta_step]
    obtain ⟨-, hx, hy⟩ := hP.resOk
    by_cases k0 : rs.headD 0 = 0
    · rw [ite_eq_left k0, show decDS rs = .cont (decE (rs.tail.headD 0)) (decE (rs.tail.tail.headD 0))
        by simp only [decDS, k0, ↓reduceIte]]
      exact RefE.ret rfl (CorePost.ret hS₄ rfl ⟨hw3, hx, hy⟩)
    rw [ite_eq_right k0]
    by_cases k1 : rs.headD 0 = 1
    · rw [ite_eq_left k1, show decDS rs = .eq by rw [decDS, ite_eq_right k0, ite_eq_left k1]]
      exact RefE.ret rfl (CorePost.ret hS₄ rfl ⟨hw1, hw0, hw0⟩)
    rw [ite_eq_right k1]
    by_cases k2 : rs.headD 0 = 2
    · rw [ite_eq_left k2, show decDS rs = .diff by
        rw [decDS, ite_eq_right k0, ite_eq_right k1, ite_eq_left k2]]
      exact RefE.ret rfl (CorePost.ret hS₄ rfl ⟨hw0, hw0, hw0⟩)
    rw [ite_eq_right k2, show decDS rs = .unknown by
      rw [decDS, ite_eq_right k0, ite_eq_right k1, ite_eq_right k2]]
    exact RefE.ret rfl (CorePost.ret hS₄ rfl ⟨hw2, ha, hb⟩)
  unfold iterT
  cases n with
  | zero => exact RefE.of_cls0 (e := .outOfFuel) rfl
  | succ k =>
  simp only [itE]
  refine RefE.bind_coreE (w := id) (fun _ => rfl) (fun hG => hG.knot.mono (by omega))
    (off_ref p hp.mid hc.natPred k (hk.mono (by omega)) F s₀ a₀ dn vis fe M eb mode d a b
      (by omega) (by omega) hs ha hb)
    (fun ro m₁ _ _ M₁ hS₁ _ => ?_)
  simp only [itE.k_defeq_offset]
  by_cases h0 : ro.headD 0 ≠ 0
  · rw [ite_eq_left h0, show decOB ro = some (ro.tail.headD 0 != 0) by
      simp only [decOB, h0, ↓reduceIte]]
    by_cases hv : ro.tail.headD 0 ≠ 0
    · rw [ite_eq_left hv, show (ro.tail.headD 0 != 0) = true from bne_iff_ne.mpr hv]
      exact RefE.ret rfl (CorePost.ret hS₁ rfl ⟨hw1, hw0, hw0⟩)
    · have hv' : ro.tail.headD 0 = 0 := by simpa using hv
      rw [ite_eq_right hv, hv']
      exact RefE.ret rfl (CorePost.ret hS₁ rfl ⟨hw0, hw0, hw0⟩)
  have h0' : ro.headD 0 = 0 := by simpa using h0
  rw [ite_eq_right h0, show decOB ro = none by simp only [decOB, h0', ↓reduceIte]]
  refine RefE.bind_callW (fun _ => rfl) (lazyFoldOk_refines p hp.mid hc.hasFvar k ⟨m₁, Locals.init []⟩ _ dn
    vis fe M₁ eb mode a b hS₁ hs.mode4 ha hb) fun rf m₂ _ e₂ => RefE.after_core (w := id) e₂ fun M₂ hS₂ _ => ?_
  dsimp only [itE.k_lazy_fold_ok]
  by_cases hf : rf.headD 0 ≠ 0
  · rw [ite_eq_left hf, decBool_t hf]
    simp only [↓reduceIte]
    refine RefE.bind_coreE (w := id) (fun _ => rfl)
      (fun hG => ⟨hG.knot.mono (by omega), hG.reduceNat⟩)
      (ln_ref p hc k (hk.mono (by omega)) F (by omega) (by omega) ⟨m₂, Locals.init []⟩ _ dn vis
        fe M₂ eb mode d a b ⟨hS₂, hs.mode4, hs.eb_mode⟩ ha hb)
      (fun rn m₃ _ hP M₃ hS₃ _ => ?_)
    simp only [itE.k_lazy_nat]
    by_cases h3 : rn.headD 0 ≠ 3
    · rw [ite_eq_left h3, show decNat rn = some (rn.headD 0 != 0) by simp only [decNat, h3, ↓reduceIte]]
      rcases hP.resOk with e0 | e1 | e3
      · rw [e0]; exact RefE.ret rfl (CorePost.ret hS₃ rfl ⟨hw0, hw0, hw0⟩)
      · rw [e1]; exact RefE.ret rfl (CorePost.ret hS₃ rfl ⟨hw1, hw0, hw0⟩)
      · exact absurd e3 h3
    have h3' : rn.headD 0 = 3 := by simpa using h3
    rw [ite_eq_right (fun h => h h3'), show decNat rn = none by simp only [decNat, h3', ↓reduceIte]]
    exact stepArm _ _ _ hS₃
  have hf' : rf.headD 0 = 0 := by simpa using hf
  rw [ite_eq_right hf, decBool_f hf']
  simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]
  exact stepArm _ _ _ hS₂

/-- **`lazy_iter` refines `iterT`** at the knot (`it_ref`'s ok half). -/
theorem lazyIter_refines (p : Prog) (hp : LazyProg p) (hc : LazyCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) (hd : d.toNat < 2 ^ 63) :
    CoreSpec p (n + 1) "lazy_iter" [mode, vis, d, a, b]
      (iterT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE a) (decE b)) decIter
      s₀ a₀ dn vis fe M eb Res3 :=
  RefE.coreSpec (itE_spec p hp.iter hp.mid.off hp.nat hp.step hp.both hp.mid.tupa hp.left hp.right
    hp.same hp.unfold2 hp.mid.dq hp.spine.sp hp.spine.sp2 hp.spine.cmp hp.spine.rev (n + 1) s₀ mode vis
    d a b) (it_ref p hp hc n hk F hF hn s₀ a₀ dn vis fe M eb mode d a b hs ha hb hd)

/-! ## The loop -/

/-- **`lazy_delta_reduction`'s model, both outcomes** (the loop `ldrE.loop1`: one `lazy_iter`
run per iteration, `callE`). -/
l_model lazyDeltaReduction_specE (p : Prog)
    (hf : p.lookup "lazy_delta_reduction" = some lazyDeltaReductionL)
  fns [hf ↦ ldrE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified

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
`j ≤ K + 1`: each iteration is `lazy_iter`'s (`it_ref`). -/
theorem lazy_ref (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (mode d : Word) (hmode : mode < 4)
    (hd : d.toNat < 2 ^ 63) :
    ∀ j, j ≤ n + 1 → ∀ K, j ≤ K + 1 → ∀ (a b : Word) (m : Mem) (s : AState) (M : ModeMaps)
      (eb : Word), CoreS dn m s vis fe M eb → eb = (mode >>> 1) &&& 1 → HW a → HW b →
      RefE (LazyG p n) (ldrE.loop1 p j m mode vis d a b)
        (lazyDeltaReduction (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat K
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
    cases j with
    | zero => exact RefE.callE_zero fun _ => ldrE.k_lazy_iter.none ..
    | succ j' =>
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    rw [lazyDeltaReduction_succ_eq, lazyLvl_eq]
    refine RefE.bind_callE (s₀ := ⟨m, Locals.init []⟩) (fun _ => ldrE.k_lazy_iter.none ..)
      (lazyIter_refines p hp hc j' (hk.mono (by omega)) F (by omega) (by omega) _ s dn vis fe M eb mode
        d a b ⟨hS, hmode, heb⟩ ha hb hd)
      (fun (hG : LazyG p n) => RefE.coreSpecE (itE_spec p hp.iter hp.mid.off hp.nat hp.step hp.both
        hp.mid.tupa hp.left hp.right hp.same hp.unfold2 hp.mid.dq hp.spine.sp hp.spine.sp2 hp.spine.cmp
        hp.spine.rev (j' + 1) ⟨m, Locals.init []⟩ mode vis d a b) hG.nv (hG.mono (by omega))
        (it_ref p hp hc j' (hk.mono (by omega)) F (by omega) (by omega) _ s dn vis fe M eb mode d a b
          ⟨hS, hmode, heb⟩ ha hb hd)) fun r m₁ _ e => RefE.after_core (w := id) e fun M₁ hS₁ _ => ?_
    obtain ⟨g0, hr1, hr2⟩ := e.resOk
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
    RefE (LazyG p n) (ldrE p (n + 1) s₀.mem mode vis d a b)
      (lazyDeltaReduction (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat defeqLoopFuel
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
      (lazyDeltaReduction (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat defeqLoopFuel
        (decE a) (decE b)) decLR s₀ a₀ dn vis fe M eb Res3 :=
  CoreSpec.of_refE (w := id)
    (lazyDeltaReduction_specE p hp.red (n + 1) s₀ mode vis d a b)
    (lazyDeltaReduction_ref p hp hc n hk F hF hn s₀ a₀ dn vis fe M eb mode d a b hs ha hb hd)
    fun _ _ => ⟨rfl, rfl, id⟩

end loopRef

end L.Arena
