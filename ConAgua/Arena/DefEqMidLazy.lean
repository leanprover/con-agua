import ConAgua.Arena.DefEqMidSpine
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen

/-!
# Lazy delta: the step and the loop (lane `defeq`)

`lazyDeltaStep` split for the proofs (`DefEq.lean`): `lds_left`/`lds_right` (one side unfolded,
the cheap `whnfCore`, `deltaQuick`), `lds_unfold2` (both), `lds_same` (equal hints: the same-head
spine shortcut, else `lds_unfold2`), `lds_both` (the hints), `lazy_delta_step` (the dispatch on
`unfoldableHead`). `lazyDeltaReduction`'s iteration is `lazy_iter` (offsets, the literal
acceleration `lazy_nat`, the step), its loop `lazyDeltaLoop`. Each has one refinement for both
outcomes (`*_ref`, the errors' claims under `KnotNvG`).

`unfold_definition` and `reduce_nat` are lane `whnf`'s (`WhnfDelta.lean`); their refinements are
`sorry` there, so they enter here as hypotheses (`UnfoldDefOK`, `ReduceNatSpec`), with the other
callees without proofs (`LazyCallees`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-- `unfold_definition(vis, e)` refines `unfoldDefinition` (`WhnfDelta.lean`'s
`unfoldDefinition_refines`, a `sorry` there). -/
def UnfoldDefOK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb e : Word), CoreS dn s₀.mem a₀ vis fe M eb → HW e →
    CoreSpec p n "unfold_definition" [vis, e] (unfoldDefinition fe (decE e)) decOptR s₀ a₀ dn vis fe
      M eb ResW

/-- **The callees without proofs** of the lazy-delta layer and below. -/
structure LazyCallees (p : Prog) : Prop where
  instList : InstListOK p
  inst1 : Inst1OK p
  hasFvar : HasFvarOK p
  natPred : NatPredW p
  unfold : UnfoldDefOK p
  reduceNat : ∀ n, n ≤ 2 ^ 62 → ReduceNatSpec p n
  store : StoreDenotes

/-- The lookups of this file. -/
structure LazyProg (p : Prog) : Prop where
  spine : SpineDProg p
  left : p.lookup "lds_left" = some ldsLeftL
  right : p.lookup "lds_right" = some ldsRightL
  unfold2 : p.lookup "lds_unfold2" = some ldsUnfold2L
  same : p.lookup "lds_same" = some ldsSameL
  both : p.lookup "lds_both" = some ldsBothL
  step : p.lookup "lazy_delta_step" = some lazyDeltaStepL
  nat : p.lookup "lazy_nat" = some lazyNatL
  iter : p.lookup "lazy_iter" = some lazyIterL
  red : p.lookup "lazy_delta_reduction" = some lazyDeltaReductionL

theorem LazyProg.mid {p : Prog} (hp : LazyProg p) : DefEqMidProg p := hp.spine.quick.lams.mid

/-- Every spec holds at fuel `0` (nothing returns). -/
theorem coreSpec_zero {α : Type} [Inhabited α] (p : Prog) (f : FnName) (args : List Word) (T : AM α)
    (dec : List Word → α) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (M : ModeMaps) (eb : Word) (ok : List Word → Prop) :
    CoreSpec p 0 f args T dec s₀ a₀ dn vis fe M eb ok := by
  apply L.M.triple_of_run
  intro s r s' hs hrun
  exact (L.M.of_run (P := fun s => s = s₀) hs hrun (invoke_zero_false p f args s₀)).elim

/-- `quick_defeq` at every fuel up to `n + 1`, from the knot up to `n`. -/
theorem quickUpTo {p : Prog} (hp : LazyProg p) (hc : LazyCallees p) {n : Nat} (hk : KnotUpTo p n) :
    ∀ k, k ≤ n + 1 → QuickDefeqSpec p k := by
  intro k hkn
  cases k with
  | zero => intro F s₀ a₀ dn vis fe M eb mode d x y _ _ _ _ _ _; exact coreSpec_zero _ _ _ _ _ _ _ _ _ _ _ _ _
  | succ k =>
    exact quickDefeq_refines p hp.spine.quick hc.instList hc.inst1 hc.store k (hk.mono (by omega))

/-- `quick_defeq`'s error claim at every fuel up to `n + 1`, from the knot up to `n` and its error
half with the verdict closure (`qd_ref`). -/
theorem quickWEUpTo {p : Prog} (hp : LazyProg p) (hc : LazyCallees p) {n : Nat} (hk : KnotUpTo p n)
    (hG : KnotNvG p n) : ∀ k, k ≤ n + 1 → QuickDefeqWE p k := by
  intro k hkn
  cases k with
  | zero => intro F s₀ a₀ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _; exact CoreSpecE.zero p _ _ _ s₀ a₀
  | succ k =>
    intro F s₀ a₀ dn vis fe M eb mode d x y hF hn hs hx hy hd
    have qp := hp.spine.quick
    exact RefE.coreSpecE (qdE_spec p qp.qd qp.qs qp.qf qp.ql qp.lams.peel.binders qp.lams.lams (k + 1)
      s₀ mode vis d x y) hG.nv (hG.mono (by omega))
      (qd_ref p qp hc.instList hc.inst1 hc.store k (hk.mono (by omega)) F s₀ a₀ dn vis fe M eb mode d
        x y (by omega) (by omega) hs hx hy hd)

/-! ## `lds_left`, `lds_right` -/

/-- One side unfolded, as the twin's `lazyDeltaStep` does it (`a` when `left`). -/
def ldsOneT (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (left : Bool)
    (a b : EIdx) : AM DeltaStepA := do
  if left then
    match ← unfoldDefinition fe a with
    | some a₂ => do
      let a₃ ← r.whnfCore true depth a₂
      deltaQuick mode r depth a₃ b
    | none => pure .unknown
  else
    match ← unfoldDefinition fe b with
    | some b₂ => do
      let b₃ ← r.whnfCore true depth b₂
      deltaQuick mode r depth a b₃
    | none => pure .unknown

/-- **`delta_quick` as a tail call, both outcomes** (`dq_ref` with `quick_defeq` from the knot). -/
theorem dq_tail {p : Prog} (hp : LazyProg p) (hc : LazyCallees p)
    {K : Except Err (List Word × Mem) → Except Err (List Word × Mem)}
    (hK1 : ∀ e, K (.error e) = .error e)
    (hK2 : ∀ v : List Word × Mem,
      K (.ok v) = .ok ([v.1.headD 0, v.1.tail.headD 0, v.1.tail.tail.headD 0], v.2))
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) (hd : d.toNat < 2 ^ 63) :
    RefE (KnotNvG p n) (K (dqE p n s₀.mem mode vis d a b))
      (deltaQuick (decMode mode) (coreKnot (decMode mode) fe id F) d.toNat (decE a) (decE b)) a₀
      (CorePost decDS dn s₀.mem vis fe M eb Res3) := by
  cases n with
  | zero =>
    rw [show dqE p 0 s₀.mem mode vis d a b = .error .outOfFuel from rfl, hK1]
    exact RefE.of_cls0 rfl
  | succ j =>
  exact RefE.tail_relist3 hK1 hK2 (fun hG => quickWEUpTo hp hc hk hG j (by omega))
    (dq_ref p j (quickUpTo hp hc hk j (by omega)) F s₀ a₀ dn vis fe M eb mode d a b (by omega)
      (by omega) hs ha hb hd)

/-- **`lds_left`'s model, both outcomes** (generated; `unfold_definition` lifted, the `whnf_core`
slot through its run, `delta_quick` by its unified model). -/
l_model llE_spec (p : Prog) (hf : p.lookup "lds_left" = some ldsLeftL)
    (hq : p.lookup "delta_quick" = some deltaQuickL)
  fns [hf ↦ llE list]
  specs [callW_spec p n "unfold_definition", dqE_spec p hq n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **`lds_right`'s model, both outcomes** (as `lds_left`'s). -/
l_model lrE_spec (p : Prog) (hf : p.lookup "lds_right" = some ldsRightL)
    (hq : p.lookup "delta_quick" = some deltaQuickL)
  fns [hf ↦ lrE list]
  specs [callW_spec p n "unfold_definition", dqE_spec p hq n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **`lds_left` refines the left unfolding of `lazyDeltaStep`, both outcomes**: the errors are
the `whnf_core` slot's and `delta_quick`'s. -/
theorem ll_ref (p : Prog) (hp : LazyProg p) (hc : LazyCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) (hd : d.toNat < 2 ^ 63) :
    RefE (KnotNvG p n) (llE p (n + 1) s₀.mem mode vis d a b)
      (ldsOneT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat true (decE a) (decE b)) a₀
      (CorePost decDS dn s₀.mem vis fe M eb Res3) := by
  have hS := hs.rel
  unfold ldsOneT
  simp only [↓reduceIte, llE]
  rcases c1 : callW p n "unfold_definition" [vis, a] s₀.mem with _ | ⟨r₁, m₁⟩
  · rw [liftE_none, llE.k_unfold_definition.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]; simp only [llE.k_unfold_definition]
  have e₁ := CoreSpec.of_callW (hc.unfold n s₀ a₀ dn vis fe M eb a hS ha) c1
  refine RefE.bind_core (w := id) e₁ (fun M₁ hS₁ _ => ?_)
  by_cases h0 : r₁.headD 0 = 0
  · rw [ite_eq_left h0, decOptR_none h0]
    exact RefE.ret rfl (CorePost.ret hS₁ rfl ⟨hw3, hw0, hw0⟩)
  rw [ite_eq_right h0, decOptR_some h0]
  rcases c2 : callE p n "whnf_core" [mode, 1, vis, d, r₁.tail.headD 0] m₁ with e | ⟨r₂, m₂⟩
  · exact fun hG => ErrClaim.bind_left (CoreSpecE.of_callE (s₀ := ⟨m₁, Locals.init []⟩)
      ((hG.knot n (Nat.le_refl _)).whnfCore F _ _ dn vis fe M₁ eb mode 1 d _ hF hn
        ⟨hS₁, hs.mode4, hs.eb_mode⟩ e₁.resOk.2) c2)
  have e₂ := CoreSpec.of_callW (s₀ := ⟨m₁, Locals.init []⟩)
    ((hk n (Nat.le_refl _)).whnfCore F _ _ dn vis fe M₁ eb mode 1 d _ hF hn
      ⟨hS₁, hs.mode4, hs.eb_mode⟩ e₁.resOk.2) (callW_of_callE c2)
  simp only [llE.k_whnf_core]
  refine RefE.bind_core (w := id) e₂ (fun M₂ hS₂ _ => ?_)
  exact dq_tail hp hc (fun _ => rfl) (fun _ => rfl) n hk F hF hn ⟨m₂, Locals.init []⟩ _ dn vis fe M₂
    eb mode d _ b ⟨hS₂, hs.mode4, hs.eb_mode⟩ e₂.resOk hb hd

/-- **`lds_right` refines the right unfolding of `lazyDeltaStep`, both outcomes**. -/
theorem lr_ref (p : Prog) (hp : LazyProg p) (hc : LazyCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) (hd : d.toNat < 2 ^ 63) :
    RefE (KnotNvG p n) (lrE p (n + 1) s₀.mem mode vis d a b)
      (ldsOneT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat false (decE a) (decE b)) a₀
      (CorePost decDS dn s₀.mem vis fe M eb Res3) := by
  have hS := hs.rel
  unfold ldsOneT
  simp only [Bool.false_eq_true, ↓reduceIte, lrE]
  rcases c1 : callW p n "unfold_definition" [vis, b] s₀.mem with _ | ⟨r₁, m₁⟩
  · rw [liftE_none, lrE.k_unfold_definition.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]; simp only [lrE.k_unfold_definition]
  have e₁ := CoreSpec.of_callW (hc.unfold n s₀ a₀ dn vis fe M eb b hS hb) c1
  refine RefE.bind_core (w := id) e₁ (fun M₁ hS₁ _ => ?_)
  by_cases h0 : r₁.headD 0 = 0
  · rw [ite_eq_left h0, decOptR_none h0]
    exact RefE.ret rfl (CorePost.ret hS₁ rfl ⟨hw3, hw0, hw0⟩)
  rw [ite_eq_right h0, decOptR_some h0]
  rcases c2 : callE p n "whnf_core" [mode, 1, vis, d, r₁.tail.headD 0] m₁ with e | ⟨r₂, m₂⟩
  · exact fun hG => ErrClaim.bind_left (CoreSpecE.of_callE (s₀ := ⟨m₁, Locals.init []⟩)
      ((hG.knot n (Nat.le_refl _)).whnfCore F _ _ dn vis fe M₁ eb mode 1 d _ hF hn
        ⟨hS₁, hs.mode4, hs.eb_mode⟩ e₁.resOk.2) c2)
  have e₂ := CoreSpec.of_callW (s₀ := ⟨m₁, Locals.init []⟩)
    ((hk n (Nat.le_refl _)).whnfCore F _ _ dn vis fe M₁ eb mode 1 d _ hF hn
      ⟨hS₁, hs.mode4, hs.eb_mode⟩ e₁.resOk.2) (callW_of_callE c2)
  simp only [lrE.k_whnf_core]
  refine RefE.bind_core (w := id) e₂ (fun M₂ hS₂ _ => ?_)
  exact dq_tail hp hc (fun _ => rfl) (fun _ => rfl) n hk F hF hn ⟨m₂, Locals.init []⟩ _ dn vis fe M₂
    eb mode d a _ ⟨hS₂, hs.mode4, hs.eb_mode⟩ ha e₂.resOk hd

/-! ## `lds_unfold2` -/

/-- Both sides unfolded, as the twin's `lazyDeltaStep` does it at equal hints. -/
def unfold2T (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (a b : EIdx) :
    AM DeltaStepA := do
  match ← unfoldDefinition fe a, ← unfoldDefinition fe b with
  | some a₂, some b₂ => do
    let a₃ ← r.whnfCore true depth a₂
    let b₃ ← r.whnfCore true depth b₂
    deltaQuick mode r depth a₃ b₃
  | _, _ => pure .unknown

/-- **`lds_unfold2`'s model, both outcomes** (generated; as `lds_left`'s). -/
l_model u2E_spec (p : Prog) (hf : p.lookup "lds_unfold2" = some ldsUnfold2L)
    (hq : p.lookup "delta_quick" = some deltaQuickL)
  fns [hf ↦ u2E list]
  specs [callW_spec p n "unfold_definition", dqE_spec p hq n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **`lds_unfold2` refines `unfold2T`, both outcomes**: the errors are the `whnf_core` slot's and
`delta_quick`'s. -/
theorem u2_ref (p : Prog) (hp : LazyProg p) (hc : LazyCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) (hd : d.toNat < 2 ^ 63) :
    RefE (KnotNvG p n) (u2E p (n + 1) s₀.mem mode vis d a b)
      (unfold2T (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) a₀
      (CorePost decDS dn s₀.mem vis fe M eb Res3) := by
  have hS := hs.rel
  unfold unfold2T
  simp only [u2E]
  rcases c1 : callW p n "unfold_definition" [vis, a] s₀.mem with _ | ⟨ra, m₁⟩
  · rw [liftE_none, u2E.k_unfold_definition.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]; simp only [u2E.k_unfold_definition]
  have e₁ := CoreSpec.of_callW (hc.unfold n s₀ a₀ dn vis fe M eb a hS ha) c1
  refine RefE.bind_core (w := id) e₁ (fun M₁ hS₁ _ => ?_)
  rcases c2 : callW p n "unfold_definition" [vis, b] m₁ with _ | ⟨rb, m₂⟩
  · rw [liftE_none, u2E.k_unfold_definition_2.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]; simp only [u2E.k_unfold_definition_2]
  have e₂ := CoreSpec.of_callW (s₀ := ⟨m₁, Locals.init []⟩)
    (hc.unfold n _ _ dn vis fe M₁ eb b hS₁ hb) c2
  refine RefE.bind_core (w := id) e₂ (fun M₂ hS₂ _ => ?_)
  by_cases h0 : ra.headD 0 = 0 ∨ rb.headD 0 = 0
  · rw [ite_eq_left h0]
    rcases h0 with h0 | h0
    · rw [decOptR_none h0]
      exact RefE.ret rfl (CorePost.ret hS₂ rfl ⟨hw3, hw0, hw0⟩)
    · rw [decOptR_none h0]
      cases decOptR ra <;> exact RefE.ret rfl (CorePost.ret hS₂ rfl ⟨hw3, hw0, hw0⟩)
  rw [ite_eq_right h0]
  have ha0 : ra.headD 0 ≠ 0 := fun h => h0 (.inl h)
  have hb0 : rb.headD 0 ≠ 0 := fun h => h0 (.inr h)
  rw [decOptR_some ha0, decOptR_some hb0]
  rcases c3 : callE p n "whnf_core" [mode, 1, vis, d, ra.tail.headD 0] m₂ with e | ⟨r₃, m₃⟩
  · exact fun hG => ErrClaim.bind_left (CoreSpecE.of_callE (s₀ := ⟨m₂, Locals.init []⟩)
      ((hG.knot n (Nat.le_refl _)).whnfCore F _ _ dn vis fe M₂ eb mode 1 d _ hF hn
        ⟨hS₂, hs.mode4, hs.eb_mode⟩ e₁.resOk.2) c3)
  have e₃ := CoreSpec.of_callW (s₀ := ⟨m₂, Locals.init []⟩)
    ((hk n (Nat.le_refl _)).whnfCore F _ _ dn vis fe M₂ eb mode 1 d _ hF hn
      ⟨hS₂, hs.mode4, hs.eb_mode⟩ e₁.resOk.2) (callW_of_callE c3)
  simp only [u2E.k_whnf_core]
  refine RefE.bind_core (w := id) e₃ (fun M₃ hS₃ _ => ?_)
  rcases c4 : callE p n "whnf_core" [mode, 1, vis, d, rb.tail.headD 0] m₃ with e | ⟨r₄, m₄⟩
  · exact fun hG => ErrClaim.bind_left (CoreSpecE.of_callE (s₀ := ⟨m₃, Locals.init []⟩)
      ((hG.knot n (Nat.le_refl _)).whnfCore F _ _ dn vis fe M₃ eb mode 1 d _ hF hn
        ⟨hS₃, hs.mode4, hs.eb_mode⟩ e₂.resOk.2) c4)
  have e₄ := CoreSpec.of_callW (s₀ := ⟨m₃, Locals.init []⟩)
    ((hk n (Nat.le_refl _)).whnfCore F _ _ dn vis fe M₃ eb mode 1 d _ hF hn
      ⟨hS₃, hs.mode4, hs.eb_mode⟩ e₂.resOk.2) (callW_of_callE c4)
  simp only [u2E.k_whnf_core_2]
  refine RefE.bind_core (w := id) e₄ (fun M₄ hS₄ _ => ?_)
  exact dq_tail hp hc (fun _ => rfl) (fun _ => rfl) n hk F hF hn ⟨m₄, Locals.init []⟩ _ dn vis fe M₄
    eb mode d _ _ ⟨hS₄, hs.mode4, hs.eb_mode⟩ e₃.resOk e₄.resOk hd

/-! ## `lds_same` -/

/-- Equal hints, as the twin's `lazyDeltaStep` does it: the same-head spine shortcut at equal
regular hints, else both unfolds. -/
def sameT (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (a b : EIdx)
    (ha hb : ConLeche.ReducibilityHint) : AM DeltaStepA := do
  let sch ← sameConstHeads a b
  let sp ← if ConLeche.ReducibilityHint.sameRegular ha hb && sch then defeqSpine r fe depth a b
    else pure false
  if sp then pure .eq
  else unfold2T mode r fe depth a b

/-- **`lds_same`'s model, both outcomes** (generated; `same_const_heads` lifted, `defeq_spine` and
`lds_unfold2` by their unified models). -/
l_model smE_spec (p : Prog) (hf : p.lookup "lds_same" = some ldsSameL)
    (hu : p.lookup "lds_unfold2" = some ldsUnfold2L) (hq : p.lookup "delta_quick" = some deltaQuickL)
    (h1 : p.lookup "defeq_spine" = some defeqSpineL) (h2 : p.lookup "defeq_spine2" = some defeqSpine2L)
    (hc : p.lookup "spine_cmp" = some spineCmpL) (hr : p.lookup "defeq_list_rev" = some defeqListRevL)
  fns [hf ↦ smE list]
  specs [callW_spec p n "same_const_heads", spE_spec p h1 h2 hc hr n, u2E_spec p hu hq n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

theorem sameRegular_w (ka ha kb hb : Word) :
    ConLeche.ReducibilityHint.sameRegular (decHintW ka ha) (decHintW kb hb) =
      decide (2 ≤ ka ∧ 2 ≤ kb ∧ ha = hb) := by
  have e : ∀ k : Word, (2 ≤ k) ↔ (k ≠ 0 ∧ k ≠ 1) := by
    intro k
    have h0 : (k = 0) ↔ k.toNat = 0 := ⟨fun h => h ▸ rfl, fun h => UInt64.toNat_inj.mp (by simpa using h)⟩
    have h1 : (k = 1) ↔ k.toNat = 1 := ⟨fun h => h ▸ rfl, fun h => UInt64.toNat_inj.mp (by simpa using h)⟩
    have h2 : (2 : Word).toNat = 2 := rfl
    rw [UInt64.le_iff_toNat_le, h2, ne_eq, ne_eq, h0, h1]; omega
  unfold decHintW
  by_cases a0 : ka = 0 <;> by_cases a1 : ka = 1 <;> by_cases b0 : kb = 0 <;> by_cases b1 : kb = 1 <;>
    simp [a0, a1, b0, b1, ConLeche.ReducibilityHint.sameRegular, e] <;>
    (try (rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
          exact ⟨UInt64.toNat_inj.mp, fun h => h ▸ rfl⟩))

/-- **`lds_same` refines `sameT`, both outcomes**, at the decoded hints: the errors are
`defeq_spine`'s and `lds_unfold2`'s. -/
theorem sm_ref (p : Prog) (hp : LazyProg p) (hc : LazyCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a b ka ha kb hb : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hwa : HW a)
    (hwb : HW b) (hd : d.toNat < 2 ^ 63) :
    RefE (KnotNvG p n) (smE p (n + 1) s₀.mem mode vis d a b ka ha kb hb)
      (sameT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)
        (decHintW ka ha) (decHintW kb hb)) a₀ (CorePost decDS dn s₀.mem vis fe M eb Res3) := by
  have hS := hs.rel
  unfold sameT
  simp only [smE]
  rcases c1 : callW p n "same_const_heads" [a, b] s₀.mem with _ | ⟨r₁, m₁⟩
  · rw [liftE_none, smE.k_same_const_heads.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]; simp only [smE.k_same_const_heads]
  obtain ⟨k, rfl⟩ := callW_succ c1
  have e₁ := CoreSpec.of_callW (sameConstHeads_refines p hp.mid.leaf k s₀ a₀ dn vis fe M eb a b hS hwa hwb) c1
  refine RefE.bind_core (w := id) e₁ (fun M₁ hS₁ _ => ?_)
  rw [sameRegular_w]
  -- the unfold arm
  have unf : ∀ (m₂ : Mem) (M₂ : ModeMaps) (a₂ : AState), CoreS dn m₂ a₂ vis fe M₂ eb →
      RefE (KnotNvG p (k + 1)) (smE.j1 p (k + 1) mode vis d a b 0 m₂)
        (unfold2T (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) a₂
        (CorePost decDS dn m₂ vis fe M₂ eb Res3) := by
    intro m₂ M₂ a₂ hS₂
    rw [smE.j1, ite_eq_right (fun h => h rfl)]
    exact RefE.tail_relist3 (fun _ => rfl) (fun _ => rfl) (fun hG => hG.mono (by omega))
      (u2_ref p hp hc k (hk.mono (by omega)) F (by omega) (by omega) ⟨m₂, Locals.init []⟩ a₂ dn vis
        fe M₂ eb mode d a b ⟨hS₂, hs.mode4, hs.eb_mode⟩ hwa hwb hd)
  by_cases hcnd : 2 ≤ ka ∧ 2 ≤ kb ∧ ha = hb ∧ r₁.headD 0 ≠ 0
  · rw [ite_eq_left hcnd]
    have hsch : (decide (2 ≤ ka ∧ 2 ≤ kb ∧ ha = hb) && decBool r₁) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq, hcnd.1, hcnd.2.1, hcnd.2.2.1, true_and,
        decBool_t hcnd.2.2.2]
    simp only [hsch, ↓reduceIte]
    refine RefE.bind_coreE (w := id) (fun _ => rfl) (fun hG => hG.knot.mono (by omega))
      (sp_ref p hp.spine k (hk.mono (by omega)) F (by omega) (by omega) ⟨m₁, Locals.init []⟩ _
        dn vis fe M₁ eb mode d a b ⟨hS₁, hs.mode4, hs.eb_mode⟩ hwa hwb)
      (fun r₂ m₂ _ _ M₂ hS₂ _ => ?_)
    simp only [smE.k_defeq_spine]
    by_cases h2 : r₂.headD 0 ≠ 0
    · rw [smE.j1, ite_eq_left h2, decBool_t h2]
      exact RefE.ret rfl (CorePost.ret hS₂ rfl ⟨hw1, hw0, hw0⟩)
    have h2' : r₂.headD 0 = 0 := by simpa using h2
    rw [h2', decBool_f h2']
    exact unf _ _ _ hS₂
  · rw [ite_eq_right hcnd]
    have hsch : (decide (2 ≤ ka ∧ 2 ≤ kb ∧ ha = hb) && decBool r₁) = false := by
      by_cases hz : r₁.headD 0 = 0
      · rw [decBool_f hz]; simp
      · have : ¬ (2 ≤ ka ∧ 2 ≤ kb ∧ ha = hb) := fun h => hcnd ⟨h.1, h.2.1, h.2.2, hz⟩
        simp [this]
    simp only [hsch, Bool.false_eq_true, ↓reduceIte, pure_bind]
    exact unf _ _ _ hS₁

/-! ## `lds_both` -/

/-- Both heads unfoldable, as the twin's `lazyDeltaStep` does it: the hints decide the side. -/
def bothT (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (a b : EIdx) :
    AM DeltaStepA := do
  let ha ← headHint fe a
  let hb ← headHint fe b
  if ConLeche.ReducibilityHint.lt hb ha then ldsOneT mode r fe depth true a b
  else if ConLeche.ReducibilityHint.lt ha hb then ldsOneT mode r fe depth false a b
  else sameT mode r fe depth a b ha hb

/-- **`lds_both`'s model, both outcomes** (generated; `head_hint`, `hint_lt` lifted, the arms by
their unified models). -/
l_model boE_spec (p : Prog) (hf : p.lookup "lds_both" = some ldsBothL)
    (hl : p.lookup "lds_left" = some ldsLeftL) (hr' : p.lookup "lds_right" = some ldsRightL)
    (hs : p.lookup "lds_same" = some ldsSameL)
    (hu : p.lookup "lds_unfold2" = some ldsUnfold2L) (hq : p.lookup "delta_quick" = some deltaQuickL)
    (h1 : p.lookup "defeq_spine" = some defeqSpineL) (h2 : p.lookup "defeq_spine2" = some defeqSpine2L)
    (hc : p.lookup "spine_cmp" = some spineCmpL) (hr : p.lookup "defeq_list_rev" = some defeqListRevL)
  fns [hf ↦ boE list]
  specs [callW_spec p n "head_hint", callW_spec p n "hint_lt", llE_spec p hl hq n, lrE_spec p hr' hq n,
    smE_spec p hs hu hq h1 h2 hc hr n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **`lds_both` refines `bothT`, both outcomes**: the errors are the arms'. -/
theorem bo_ref (p : Prog) (hp : LazyProg p) (hc : LazyCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) (hd : d.toNat < 2 ^ 63) :
    RefE (KnotNvG p n) (boE p (n + 1) s₀.mem mode vis d a b)
      (bothT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) a₀
      (CorePost decDS dn s₀.mem vis fe M eb Res3) := by
  have hS := hs.rel
  unfold bothT
  simp only [boE]
  rcases c1 : callW p n "head_hint" [vis, a] s₀.mem with _ | ⟨ra, m₁⟩
  · rw [liftE_none, boE.k_head_hint.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]; simp only [boE.k_head_hint]
  obtain ⟨k, rfl⟩ := callW_succ c1
  have e₁ := CoreSpec.of_callW (headHint_refines p hp.mid.leaf k s₀ a₀ dn vis fe M eb a hS ha) c1
  refine RefE.bind_core (w := id) e₁ (fun M₁ hS₁ _ => ?_)
  rcases c2 : callW p (k + 1) "head_hint" [vis, b] m₁ with _ | ⟨rb, m₂⟩
  · rw [liftE_none, boE.k_head_hint_2.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]; simp only [boE.k_head_hint_2]
  have e₂ := CoreSpec.of_callW (s₀ := ⟨m₁, Locals.init []⟩)
    (headHint_refines p hp.mid.leaf k _ _ dn vis fe M₁ eb b hS₁ hb) c2
  refine RefE.bind_core (w := id) e₂ (fun M₂ hS₂ _ => ?_)
  have hdh : ∀ r : List Word, decHintR r = decHintW (r.headD 0) (r.tail.headD 0) := fun _ => rfl
  rw [hdh ra, hdh rb]
  rcases c3 : callW p (k + 1) "hint_lt" [rb.headD 0, rb.tail.headD 0, ra.headD 0, ra.tail.headD 0] m₂
    with _ | ⟨rl, m₃⟩
  · rw [liftE_none, boE.k_hint_lt.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]; simp only [boE.k_hint_lt]
  obtain ⟨t₃, ht₃, hm₃, -, hlt₁, -⟩ := triple_of_callW (s₀ := ⟨m₂, Locals.init []⟩)
    (hintLt_refines p hp.mid.leaf k ⟨m₂, Locals.init []⟩ _ _ _ _) c3
  have hm₃' : m₃ = m₂ := by rw [← ht₃, hm₃]
  subst hm₃'
  by_cases h1 : rl.headD 0 ≠ 0
  · rw [ite_eq_left h1]
    have hl : ConLeche.ReducibilityHint.lt (decHintW (rb.headD 0) (rb.tail.headD 0))
        (decHintW (ra.headD 0) (ra.tail.headD 0)) = true := by rw [← hlt₁]; exact decBool_t h1
    simp only [hl, ↓reduceIte]
    exact RefE.tail_relist3 (fun _ => rfl) (fun _ => rfl) (fun hG => hG.mono (by omega))
      (ll_ref p hp hc k (hk.mono (by omega)) F (by omega) (by omega) ⟨m₃, Locals.init []⟩ _ dn vis fe
        M₂ eb mode d a b ⟨hS₂, hs.mode4, hs.eb_mode⟩ ha hb hd)
  rw [ite_eq_right h1]
  have h1' : rl.headD 0 = 0 := by simpa using h1
  have hl : ConLeche.ReducibilityHint.lt (decHintW (rb.headD 0) (rb.tail.headD 0))
      (decHintW (ra.headD 0) (ra.tail.headD 0)) = false := by rw [← hlt₁]; exact decBool_f h1'
  simp only [hl, Bool.false_eq_true, ↓reduceIte]
  rcases c5 : callW p (k + 1) "hint_lt" [ra.headD 0, ra.tail.headD 0, rb.headD 0, rb.tail.headD 0] m₃
    with _ | ⟨rl₂, m₅⟩
  · rw [liftE_none, boE.k_hint_lt_2.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]; simp only [boE.k_hint_lt_2]
  obtain ⟨t₅, ht₅, hm₅, -, hlt₂, -⟩ := triple_of_callW (s₀ := ⟨m₃, Locals.init []⟩)
    (hintLt_refines p hp.mid.leaf k ⟨m₃, Locals.init []⟩ _ _ _ _) c5
  have hm₅' : m₅ = m₃ := by rw [← ht₅, hm₅]
  subst hm₅'
  by_cases h2 : rl₂.headD 0 ≠ 0
  · rw [ite_eq_left h2]
    have hl2 : ConLeche.ReducibilityHint.lt (decHintW (ra.headD 0) (ra.tail.headD 0))
        (decHintW (rb.headD 0) (rb.tail.headD 0)) = true := by rw [← hlt₂]; exact decBool_t h2
    simp only [hl2, ↓reduceIte]
    exact RefE.tail_relist3 (fun _ => rfl) (fun _ => rfl) (fun hG => hG.mono (by omega))
      (lr_ref p hp hc k (hk.mono (by omega)) F (by omega) (by omega) ⟨m₅, Locals.init []⟩ _ dn vis fe
        M₂ eb mode d a b ⟨hS₂, hs.mode4, hs.eb_mode⟩ ha hb hd)
  rw [ite_eq_right h2]
  have h2' : rl₂.headD 0 = 0 := by simpa using h2
  have hl2 : ConLeche.ReducibilityHint.lt (decHintW (ra.headD 0) (ra.tail.headD 0))
      (decHintW (rb.headD 0) (rb.tail.headD 0)) = false := by rw [← hlt₂]; exact decBool_f h2'
  simp only [hl2, Bool.false_eq_true, ↓reduceIte]
  exact RefE.tail_relist3 (fun _ => rfl) (fun _ => rfl) (fun hG => hG.mono (by omega))
    (sm_ref p hp hc k (hk.mono (by omega)) F (by omega) (by omega) ⟨m₅, Locals.init []⟩ _ dn vis fe
      M₂ eb mode d a b _ _ _ _ ⟨hS₂, hs.mode4, hs.eb_mode⟩ ha hb hd)

/-! ## `lazy_delta_step` -/

theorem lazyDeltaStep_eq (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (a b : EIdx) : lazyDeltaStep mode r fe depth a b = (do
      let ua ← unfoldableHead fe a
      let ub ← unfoldableHead fe b
      match ua, ub with
      | false, false => pure .unknown
      | true, false =>
        match ← tryUnfoldProjApp r depth b with
        | some b₂ => deltaQuick mode r depth a b₂
        | none => ldsOneT mode r fe depth true a b
      | false, true =>
        match ← tryUnfoldProjApp r depth a with
        | some a₂ => deltaQuick mode r depth a₂ b
        | none => ldsOneT mode r fe depth false a b
      | true, true => bothT mode r fe depth a b) := rfl

/-- **`lazy_delta_step`'s model, both outcomes** (generated; `unfoldable_head` lifted, the other
callees by their unified models). -/
l_model ldsE_spec (p : Prog) (hf : p.lookup "lazy_delta_step" = some lazyDeltaStepL)
    (hbo : p.lookup "lds_both" = some ldsBothL)
    (ht : p.lookup "try_unfold_proj_app" = some tryUnfoldProjAppL)
    (hl : p.lookup "lds_left" = some ldsLeftL) (hr' : p.lookup "lds_right" = some ldsRightL)
    (hs : p.lookup "lds_same" = some ldsSameL)
    (hu : p.lookup "lds_unfold2" = some ldsUnfold2L) (hq : p.lookup "delta_quick" = some deltaQuickL)
    (h1 : p.lookup "defeq_spine" = some defeqSpineL) (h2 : p.lookup "defeq_spine2" = some defeqSpine2L)
    (hc : p.lookup "spine_cmp" = some spineCmpL) (hr : p.lookup "defeq_list_rev" = some defeqListRevL)
  fns [hf ↦ ldsE list]
  specs [callW_spec p n "unfoldable_head", tupaE_spec p ht n, dqE_spec p hq n, llE_spec p hl hq n,
    lrE_spec p hr' hq n, boE_spec p hbo hl hr' hs hu hq h1 h2 hc hr n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **`lazy_delta_step` refines `lazyDeltaStep`, both outcomes**: the errors are
`try_unfold_proj_app`'s, `delta_quick`'s and the unfolding arms'. -/
theorem lds_ref (p : Prog) (hp : LazyProg p) (hc : LazyCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) (hd : d.toNat < 2 ^ 63) :
    RefE (KnotNvG p n) (ldsE p (n + 1) s₀.mem mode vis d a b)
      (lazyDeltaStep (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) a₀
      (CorePost decDS dn s₀.mem vis fe M eb Res3) := by
  have hS := hs.rel
  rw [lazyDeltaStep_eq]
  simp only [ldsE]
  rcases c1 : callW p n "unfoldable_head" [vis, a] s₀.mem with _ | ⟨ra, m₁⟩
  · rw [liftE_none, ldsE.k_unfoldable_head.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]; simp only [ldsE.k_unfoldable_head]
  obtain ⟨k, rfl⟩ := callW_succ c1
  have e₁ := CoreSpec.of_callW (unfoldableHead_refines p hp.mid.leaf k s₀ a₀ dn vis fe M eb a hS ha) c1
  refine RefE.bind_core (w := id) e₁ (fun M₁ hS₁ _ => ?_)
  rcases c2 : callW p (k + 1) "unfoldable_head" [vis, b] m₁ with _ | ⟨rb, m₂⟩
  · rw [liftE_none, ldsE.k_unfoldable_head_2.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]; simp only [ldsE.k_unfoldable_head_2]
  have e₂ := CoreSpec.of_callW (s₀ := ⟨m₁, Locals.init []⟩)
    (unfoldableHead_refines p hp.mid.leaf k _ _ dn vis fe M₁ eb b hS₁ hb) c2
  refine RefE.bind_core (w := id) e₂ (fun M₂ hS₂ _ => ?_)
  have hs₂ : SlotPre ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode := ⟨hS₂, hs.mode4, hs.eb_mode⟩
  by_cases h00 : ra.headD 0 = 0 ∧ rb.headD 0 = 0
  · rw [ite_eq_left h00, decBool_f h00.1, decBool_f h00.2]
    exact RefE.ret rfl (CorePost.ret hS₂ rfl ⟨hw3, hw0, hw0⟩)
  rw [ite_eq_right h00]
  by_cases hb0 : rb.headD 0 = 0
  · have ha0 : ra.headD 0 ≠ 0 := fun h => h00 ⟨h, hb0⟩
    rw [ite_eq_left hb0, decBool_t ha0, decBool_f hb0]
    refine RefE.bind_coreE (w := id) (fun _ => rfl) (fun hG => hG.knot.mono (by omega))
      (tupa_ref p hp.mid k (hk.mono (by omega)) F _ _ dn vis fe M₂ eb mode d b (by omega)
        (by omega) hs₂ hb)
      (fun rt m₃ _ hP M₃ hS₃ _ => ?_)
    simp only [ldsE.k_try_unfold_proj_app]
    by_cases ht : rt.headD 0 ≠ 0
    · rw [ite_eq_left ht, decOptR_some ht]
      exact dq_tail hp hc (fun _ => rfl) (fun _ => rfl) (k + 1) hk F hF hn ⟨m₃, Locals.init []⟩ _ dn
        vis fe M₃ eb mode d a _ ⟨hS₃, hs.mode4, hs.eb_mode⟩ ha hP.resOk.2 hd
    rw [ite_eq_right ht, decOptR_none (by simpa using ht)]
    exact RefE.tail_relist3 (fun _ => rfl) (fun _ => rfl) (fun hG => hG.mono (by omega))
      (ll_ref p hp hc k (hk.mono (by omega)) F (by omega) (by omega) ⟨m₃, Locals.init []⟩ _ dn vis fe
        M₃ eb mode d a b ⟨hS₃, hs.mode4, hs.eb_mode⟩ ha hb hd)
  rw [ite_eq_right hb0]
  by_cases ha0 : ra.headD 0 = 0
  · rw [ite_eq_left ha0, decBool_f ha0, decBool_t hb0]
    refine RefE.bind_coreE (w := id) (fun _ => rfl) (fun hG => hG.knot.mono (by omega))
      (tupa_ref p hp.mid k (hk.mono (by omega)) F _ _ dn vis fe M₂ eb mode d a (by omega)
        (by omega) hs₂ ha)
      (fun rt m₃ _ hP M₃ hS₃ _ => ?_)
    simp only [ldsE.k_try_unfold_proj_app_2]
    by_cases ht : rt.headD 0 ≠ 0
    · rw [ite_eq_left ht, decOptR_some ht]
      exact dq_tail hp hc (fun _ => rfl) (fun _ => rfl) (k + 1) hk F hF hn ⟨m₃, Locals.init []⟩ _ dn
        vis fe M₃ eb mode d _ b ⟨hS₃, hs.mode4, hs.eb_mode⟩ hP.resOk.2 hb hd
    rw [ite_eq_right ht, decOptR_none (by simpa using ht)]
    exact RefE.tail_relist3 (fun _ => rfl) (fun _ => rfl) (fun hG => hG.mono (by omega))
      (lr_ref p hp hc k (hk.mono (by omega)) F (by omega) (by omega) ⟨m₃, Locals.init []⟩ _ dn vis fe
        M₃ eb mode d a b ⟨hS₃, hs.mode4, hs.eb_mode⟩ ha hb hd)
  rw [ite_eq_right ha0, decBool_t ha0, decBool_t hb0]
  exact RefE.tail_relist3 (fun _ => rfl) (fun _ => rfl) (fun hG => hG.mono (by omega))
    (bo_ref p hp hc k (hk.mono (by omega)) F (by omega) (by omega) ⟨m₂, Locals.init []⟩ _ dn vis fe
      M₂ eb mode d a b hs₂ ha hb hd)

/-- **`lazy_delta_step` refines `lazyDeltaStep`** at the knot (`lds_ref`'s ok half). -/
@[refines ConRon.Arena.lazyDeltaStep]
theorem lazyDeltaStep_refines (p : Prog) (hp : LazyProg p) (hc : LazyCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) (hd : d.toNat < 2 ^ 63) :
    CoreSpec p (n + 1) "lazy_delta_step" [mode, vis, d, a, b]
      (lazyDeltaStep (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b))
      decDS s₀ a₀ dn vis fe M eb Res3 :=
  RefE.coreSpec (ldsE_spec p hp.step hp.both hp.mid.tupa hp.left hp.right hp.same hp.unfold2 hp.mid.dq
    hp.spine.sp hp.spine.sp2 hp.spine.cmp hp.spine.rev (n + 1) s₀ mode vis d a b)
    (lds_ref p hp hc n hk F hF hn s₀ a₀ dn vis fe M eb mode d a b hs ha hb hd)

end L.Arena
