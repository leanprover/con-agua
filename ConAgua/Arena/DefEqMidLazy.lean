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
acceleration `lazy_nat`, the step), its loop `lazyDeltaLoop`.

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

section llK
variable (p : Prog) (n : Nat) (mode vis d a b : Word) (left : Bool)

def llK3 (res : Option (List Word × Mem)) : Option (Word × Word × Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => some (r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, m)

def llK2 (res : Option (List Word × Mem)) : Option (Word × Word × Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => llK3 (callW p n "delta_quick"
      (if left then [mode, vis, d, r.headD 0, b] else [mode, vis, d, a, r.headD 0]) m)

def llK1 (res : Option (List Word × Mem)) : Option (Word × Word × Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if r.headD 0 = 0 then some (3, 0, 0, m)
    else llK2 p n mode vis d a b left (callW p n "whnf_core" [mode, 1, vis, d, r.tail.headD 0] m)

variable (r : List Word) (m : Mem)
theorem llK3_s : llK3 (some (r, m)) = some (r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, m) := rfl
theorem llK2_l : llK2 p n mode vis d a b true (some (r, m)) =
    llK3 (callW p n "delta_quick" [mode, vis, d, r.headD 0, b] m) := rfl
theorem llK2_r : llK2 p n mode vis d a b false (some (r, m)) =
    llK3 (callW p n "delta_quick" [mode, vis, d, a, r.headD 0] m) := rfl
theorem llK1_z (h : r.headD 0 = 0) : llK1 p n mode vis d a b left (some (r, m)) = some (3, 0, 0, m) := by
  simp only [llK1, h, ↓reduceIte]
theorem llK1_nz (h : r.headD 0 ≠ 0) : llK1 p n mode vis d a b left (some (r, m)) =
    llK2 p n mode vis d a b left (callW p n "whnf_core" [mode, 1, vis, d, r.tail.headD 0] m) := by
  simp only [llK1, h, ↓reduceIte]
end llK

theorem ldsLeft_spec (p : Prog) (hp : LazyProg p) (n : Nat) (s₀ : St) (mode vis d a b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "lds_left" [mode, vis, d, a, b]
    ⦃fun r s' => LocEq s' s₀ ∧ llK1 p n mode vis d a b true
      (callW p n "unfold_definition" [vis, a] s₀.mem) =
      some (r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.left]
  simp only [callFn, ldsLeftL]
  sym (gen := 80) (instances := 5000) only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "unfold_definition",
      callW_spec p n "whnf_core", callW_spec p n "delta_quick"] <;>
    finish [llK1_z, llK1_nz, llK2_l, llK3_s, St.setLocs_mem']

theorem ldsRight_spec (p : Prog) (hp : LazyProg p) (n : Nat) (s₀ : St) (mode vis d a b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "lds_right" [mode, vis, d, a, b]
    ⦃fun r s' => LocEq s' s₀ ∧ llK1 p n mode vis d a b false
      (callW p n "unfold_definition" [vis, b] s₀.mem) =
      some (r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.right]
  simp only [callFn, ldsRightL]
  sym (gen := 80) (instances := 5000) only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "unfold_definition",
      callW_spec p n "whnf_core", callW_spec p n "delta_quick"] <;>
    finish [llK1_z, llK1_nz, llK2_r, llK3_s, St.setLocs_mem']

theorem res3_eq {r r' : List Word} (h1 : r'.headD 0 = r.headD 0) (h2 : r'.tail.headD 0 = r.tail.headD 0)
    (h3 : r'.tail.tail.headD 0 = r.tail.tail.headD 0) (h : Res3 r') : Res3 r :=
  ⟨h1 ▸ h.1, h2 ▸ h.2.1, h3 ▸ h.2.2⟩

theorem decDS_eq {r r' : List Word} (h1 : r'.headD 0 = r.headD 0) (h2 : r'.tail.headD 0 = r.tail.headD 0)
    (h3 : r'.tail.tail.headD 0 = r.tail.tail.headD 0) : decDS r' = decDS r := by
  simp only [decDS, h1, h2, h3]

/-- **The model of `lds_left`/`lds_right` refines `ldsOneT`** at the knot. -/
theorem llK1_ref {p : Prog} (hp : LazyProg p) (hc : LazyCallees p) (n : Nat) (hk : KnotUpTo p n)
    (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (m m' : Mem) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word)
    (left : Bool) (hS : CoreS dn m a₀ vis fe M eb) (hmode : mode < 4) (heb : eb = (mode >>> 1) &&& 1)
    (ha : HW a) (hb : HW b) (hd : d.toNat < 2 ^ 63) (r : List Word)
    (hW : llK1 p n mode vis d a b left (callW p n "unfold_definition" [vis, if left then a else b] m) =
      some (r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, m')) :
    CoreRef (ldsOneT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat left (decE a) (decE b))
      a₀ decDS dn m vis fe M eb r m' Res3 := by
  cases hc1 : callW p n "unfold_definition" [vis, if left then a else b] m with
  | none => rw [hc1] at hW; cases hW
  | some q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [hc1] at hW
  have e₁ := CoreSpec.of_callW (s₀ := ⟨m, Locals.init []⟩)
    (hc.unfold n ⟨m, Locals.init []⟩ a₀ dn vis fe M eb _ hS (by cases left <;> assumption)) hc1
  have key : CoreRef ((unfoldDefinition fe (decE (if left then a else b))) >>= fun o => match o with
      | some e₂ => do
        let e₃ ← (coreKnot (decMode mode) fe id F).whnfCore true d.toNat e₂
        if left then deltaQuick (decMode mode) (coreKnot (decMode mode) fe id F) d.toNat e₃ (decE b)
        else deltaQuick (decMode mode) (coreKnot (decMode mode) fe id F) d.toNat (decE a) e₃
      | none => pure .unknown) a₀ decDS dn m vis fe M eb r m' Res3 := by
    refine coreRef_bind e₁ (fun M₁ hS₁ => ?_)
    by_cases h0 : r₁.headD 0 = 0
    · rw [llK1_z (h := h0), Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq] at hW
      obtain ⟨g1, g2, g3, hm⟩ := hW
      rw [decOptR_none h0, ← hm]
      exact coreRef_ret hS₁ (by simp only [decDS, ← g1]; rfl) (res3_of hw3 hw0 hw0 g1 g2 g3)
    rw [llK1_nz (h := h0)] at hW
    rw [decOptR_some h0]
    refine coreRef_callK hW rfl
        ((hk n (Nat.le_refl _)).whnfCore F _ _ dn vis fe M₁ eb mode 1 d _ hF hn ⟨hS₁, hmode, heb⟩ e₁.2.2.2.2)
      fun r₂ m₂ hW e₂ M₂ hS₂ => ?_
    have hw₂ : HW (r₂.headD 0) := e₂.2.2.2
    cases left
    · rw [llK2_r] at hW
      cases hc3 : callW p n "delta_quick" [mode, vis, d, a, r₂.headD 0] m₂ with
      | none => rw [hc3] at hW; cases hW
      | some q =>
      obtain ⟨r₃, m₃⟩ := q
      rw [hc3, llK3_s, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq] at hW
      obtain ⟨g1, g2, g3, hm⟩ := hW
      obtain ⟨k, rfl⟩ := callW_succ hc3
      have e₃ := CoreSpec.of_callW (s₀ := ⟨m₂, Locals.init []⟩)
        (deltaQuick_refines p hp.mid k (quickUpTo hp hc hk k (by omega)) F _ _ dn vis fe M₂ eb mode d
          a (r₂.headD 0) (by omega) (by omega) ⟨hS₂, hmode, heb⟩ ha hw₂ hd) hc3
      rw [← hm]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact coreRef_redec e₃ (decDS_eq g1 g2 g3) (res3_eq g1 g2 g3 e₃.2.2.2)
    · rw [llK2_l] at hW
      cases hc3 : callW p n "delta_quick" [mode, vis, d, r₂.headD 0, b] m₂ with
      | none => rw [hc3] at hW; cases hW
      | some q =>
      obtain ⟨r₃, m₃⟩ := q
      rw [hc3, llK3_s, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq] at hW
      obtain ⟨g1, g2, g3, hm⟩ := hW
      obtain ⟨k, rfl⟩ := callW_succ hc3
      have e₃ := CoreSpec.of_callW (s₀ := ⟨m₂, Locals.init []⟩)
        (deltaQuick_refines p hp.mid k (quickUpTo hp hc hk k (by omega)) F _ _ dn vis fe M₂ eb mode d
          (r₂.headD 0) b (by omega) (by omega) ⟨hS₂, hmode, heb⟩ hw₂ hb hd) hc3
      rw [← hm]
      simp only [↓reduceIte]
      exact coreRef_redec e₃ (decDS_eq g1 g2 g3) (res3_eq g1 g2 g3 e₃.2.2.2)
  cases left <;> exact key

/-- **`lds_left` refines the left unfolding of `lazyDeltaStep`.** -/
theorem ldsLeft_refines (p : Prog) (hp : LazyProg p) (hc : LazyCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) (hd : d.toNat < 2 ^ 63) :
    CoreSpec p (n + 1) "lds_left" [mode, vis, d, a, b]
      (ldsOneT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat true (decE a) (decE b))
      decDS s₀ a₀ dn vis fe M eb Res3 := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun (ldsLeft_spec p hp n s₀ mode vis d a b)
  subst hs0
  exact ⟨hloc, llK1_ref hp hc n hk F hF hn _ _ a₀ dn vis fe M eb mode d a b true hs.rel hs.mode4
    hs.eb_mode ha hb hd r hW⟩

/-- **`lds_right` refines the right unfolding of `lazyDeltaStep`.** -/
theorem ldsRight_refines (p : Prog) (hp : LazyProg p) (hc : LazyCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) (hd : d.toNat < 2 ^ 63) :
    CoreSpec p (n + 1) "lds_right" [mode, vis, d, a, b]
      (ldsOneT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat false (decE a) (decE b))
      decDS s₀ a₀ dn vis fe M eb Res3 := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun (ldsRight_spec p hp n s₀ mode vis d a b)
  subst hs0
  exact ⟨hloc, llK1_ref hp hc n hk F hF hn _ _ a₀ dn vis fe M eb mode d a b false hs.rel hs.mode4
    hs.eb_mode ha hb hd r hW⟩

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

/-- **`lds_unfold2` is its model `uW`** (generated). -/
l_model ldsUnfold2_spec (p : Prog) (hp : LazyProg p)
  fns [hp.unfold2 ↦ uW tuple]
  specs [callW_spec p n "unfold_definition", callW_spec p n "whnf_core", callW_spec p n "delta_quick"]
  grind [arena_grind] simp [St.setLocs_mem']

/-- **`lds_unfold2` refines `unfold2T`** at the knot. -/
theorem ldsUnfold2_refines (p : Prog) (hp : LazyProg p) (hc : LazyCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) (hd : d.toNat < 2 ^ 63) :
    CoreSpec p (n + 1) "lds_unfold2" [mode, vis, d, a, b]
      (unfold2T (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b))
      decDS s₀ a₀ dn vis fe M eb Res3 := by
  refine CoreSpec.of_model (ldsUnfold2_spec p hp (n + 1) s₀ mode vis d a b)
    fun r s' hW => ?_
  rw [uW.arm1] at hW
  have hS := hs.rel
  unfold unfold2T
  refine coreRef_callK hW rfl (hc.unfold n _ a₀ dn vis fe M eb a hS ha)
    fun ra m₁ hW e₁ M₁ hS₁ => ?_
  rw [uW.k_unfold_definition.arm1] at hW
  refine coreRef_callK hW rfl (hc.unfold n _ _ dn vis fe M₁ eb b hS₁ hb)
    fun rb m₂ hW e₂ M₂ hS₂ => ?_
  by_cases h0 : ra.headD 0 = 0 ∨ rb.headD 0 = 0
  · rw [uW.k_unfold_definition_2.arm1 (hc1 := h0), Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq] at hW
    obtain ⟨g1, g2, g3, hm⟩ := hW
    rw [← hm]
    rcases h0 with h0 | h0
    · rw [decOptR_none h0]
      exact coreRef_ret hS₂ (by simp only [decDS, ← g1]; rfl) (res3_of hw3 hw0 hw0 g1 g2 g3)
    · rw [decOptR_none h0]
      cases decOptR ra <;>
        exact coreRef_ret hS₂ (by simp only [decDS, ← g1]; rfl) (res3_of hw3 hw0 hw0 g1 g2 g3)
  rw [uW.k_unfold_definition_2.arm2 (hc1 := h0)] at hW
  have ha0 : ra.headD 0 ≠ 0 := fun h => h0 (.inl h)
  have hb0 : rb.headD 0 ≠ 0 := fun h => h0 (.inr h)
  rw [decOptR_some ha0, decOptR_some hb0]
  refine coreRef_callK hW rfl
      ((hk n (Nat.le_refl _)).whnfCore F _ _ dn vis fe M₂ eb mode 1 d _ hF hn ⟨hS₂, hs.mode4, hs.eb_mode⟩ e₁.2.2.2.2)
    fun r₃ m₃ hW e₃ M₃ hS₃ => ?_
  rw [uW.k_whnf_core.arm1] at hW
  refine coreRef_callK hW rfl
      ((hk n (Nat.le_refl _)).whnfCore F _ _ dn vis fe M₃ eb mode 1 d _ hF hn ⟨hS₃, hs.mode4, hs.eb_mode⟩ e₂.2.2.2.2)
    fun r₄ m₄ hW e₄ M₄ hS₄ => ?_
  rw [uW.k_whnf_core_2.arm1] at hW
  cases hc5 : callW p n "delta_quick" [mode, vis, d, r₃.headD 0, r₄.headD 0] m₄ with
  | none => rw [hc5] at hW; cases hW
  | some q =>
  obtain ⟨r₅, m₅⟩ := q
  rw [hc5, uW.k_delta_quick.arm1, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq] at hW
  obtain ⟨g1, g2, g3, hm⟩ := hW
  obtain ⟨k, rfl⟩ := callW_succ hc5
  have e₅ := CoreSpec.of_callW (s₀ := ⟨m₄, Locals.init []⟩)
    (deltaQuick_refines p hp.mid k (quickUpTo hp hc hk k (by omega)) F _ _ dn vis fe M₄ eb mode d
      _ _ (by omega) (by omega) ⟨hS₄, hs.mode4, hs.eb_mode⟩ e₃.2.2.2 e₄.2.2.2 hd) hc5
  rw [← hm]
  exact coreRef_redec e₅ (decDS_eq g1 g2 g3) (res3_eq g1 g2 g3 e₅.2.2.2)

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

/-- **`lds_same` is its model `smW`** (generated). -/
l_model ldsSame_spec (p : Prog) (hp : LazyProg p)
  fns [hp.same ↦ smW tuple]
  specs [callW_spec p n "same_const_heads", callW_spec p n "defeq_spine", callW_spec p n "lds_unfold2"]
  grind [arena_grind] simp [St.setLocs_mem']

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

/-- **`lds_same` refines `sameT`** at the knot, at the decoded hints. -/
theorem ldsSame_refines (p : Prog) (hp : LazyProg p) (hc : LazyCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a b ka ha kb hb : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hwa : HW a)
    (hwb : HW b) (hd : d.toNat < 2 ^ 63) :
    CoreSpec p (n + 1) "lds_same" [mode, vis, d, a, b, ka, ha, kb, hb]
      (sameT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)
        (decHintW ka ha) (decHintW kb hb)) decDS s₀ a₀ dn vis fe M eb Res3 := by
  refine CoreSpec.of_model (ldsSame_spec p hp (n + 1) s₀ mode vis d a b ka ha kb hb)
    fun r s' hW => ?_
  rw [smW.arm1] at hW
  have hS := hs.rel
  unfold sameT
  cases hc1 : callW p n "same_const_heads" [a, b] s₀.mem with
  | none => rw [hc1] at hW; cases hW
  | some q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [hc1] at hW
  obtain ⟨k, rfl⟩ := callW_succ hc1
  have e₁ := CoreSpec.of_callW (sameConstHeads_refines p hp.mid.leaf k s₀ a₀ dn vis fe M eb a b hS hwa hwb) hc1
  refine coreRef_bindS e₁ (fun M₁ hS₁ _ => ?_)
  rw [sameRegular_w]
  -- the unfold arm
  have unf : ∀ (m₂ : Mem) (M₂ : ModeMaps) (a₂ : AState), CoreS dn m₂ a₂ vis fe M₂ eb →
      smW.j1 p (k + 1) mode vis d a b 0 m₂ = some (r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, s'.mem) →
      CoreRef (unfold2T (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b))
        a₂ decDS dn m₂ vis fe M₂ eb r s'.mem Res3 := by
    intro m₂ M₂ a₂ hS₂ h
    rw [smW.j1.arm2 (hc1 := rfl)] at h
    cases hc3 : callW p (k + 1) "lds_unfold2" [mode, vis, d, a, b] m₂ with
    | none => rw [hc3] at h; cases h
    | some q =>
    obtain ⟨r₃, m₃⟩ := q
    rw [hc3, smW.k_lds_unfold2.arm1, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq] at h
    obtain ⟨g1, g2, g3, hm⟩ := h
    have e₃ := CoreSpec.of_callW (s₀ := ⟨m₂, Locals.init []⟩)
      (ldsUnfold2_refines p hp hc k (hk.mono (by omega)) F (by omega) (by omega) _ a₂ dn vis fe M₂ eb
        mode d a b ⟨hS₂, hs.mode4, hs.eb_mode⟩ hwa hwb hd) hc3
    rw [← hm]
    exact coreRef_redec e₃ (decDS_eq g1 g2 g3) (res3_eq g1 g2 g3 e₃.2.2.2)
  by_cases hcnd : 2 ≤ ka ∧ 2 ≤ kb ∧ ha = hb ∧ r₁.headD 0 ≠ 0
  · rw [smW.k_same_const_heads.arm1 (hc1 := hcnd)] at hW
    have hsch : (decide (2 ≤ ka ∧ 2 ≤ kb ∧ ha = hb) && decBool r₁) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq, hcnd.1, hcnd.2.1, hcnd.2.2.1, true_and,
        decBool_t hcnd.2.2.2]
    simp only [hsch, ↓reduceIte]
    refine coreRef_callK hW rfl
        (defeqSpine_refines p hp.spine hc.store k (hk.mono (by omega)) F (by omega) (by omega) _ _ dn vis fe M₁ eb mode d a b ⟨hS₁, hs.mode4, hs.eb_mode⟩ hwa hwb)
      fun r₂ m₂ hW e₂ M₂ hS₂ => ?_
    rw [smW.k_defeq_spine.arm1] at hW
    by_cases h2 : r₂.headD 0 ≠ 0
    · rw [smW.j1.arm1 (hc1 := h2), Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq] at hW
      obtain ⟨g1, g2, g3, hm⟩ := hW
      rw [decBool_t h2, ← hm]
      exact coreRef_ret hS₂ (by simp only [decDS, ← g1]; rfl) (res3_of hw1 hw0 hw0 g1 g2 g3)
    have h2' : r₂.headD 0 = 0 := by simpa using h2
    rw [h2'] at hW
    rw [decBool_f h2']
    exact unf _ _ _ hS₂ hW
  · rw [smW.k_same_const_heads.arm2 (hc1 := hcnd)] at hW
    have hsch : (decide (2 ≤ ka ∧ 2 ≤ kb ∧ ha = hb) && decBool r₁) = false := by
      by_cases hz : r₁.headD 0 = 0
      · rw [decBool_f hz]; simp
      · have : ¬ (2 ≤ ka ∧ 2 ≤ kb ∧ ha = hb) := fun h => hcnd ⟨h.1, h.2.1, h.2.2, hz⟩
        simp [this]
    simp only [hsch, Bool.false_eq_true, ↓reduceIte, pure_bind]
    exact unf _ _ _ hS₁ hW

/-! ## `lds_both` -/

/-- Both heads unfoldable, as the twin's `lazyDeltaStep` does it: the hints decide the side. -/
def bothT (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (a b : EIdx) :
    AM DeltaStepA := do
  let ha ← headHint fe a
  let hb ← headHint fe b
  if ConLeche.ReducibilityHint.lt hb ha then ldsOneT mode r fe depth true a b
  else if ConLeche.ReducibilityHint.lt ha hb then ldsOneT mode r fe depth false a b
  else sameT mode r fe depth a b ha hb

/-- **`lds_both` is its model `bothW`** (generated). Five callees on the longest path: the
default budget runs out. -/
l_model ldsBoth_spec (p : Prog) (hp : LazyProg p)
  fns [hp.both ↦ bothW tuple]
  specs [callW_spec p n "head_hint", callW_spec p n "hint_lt", callW_spec p n "lds_left",
    callW_spec p n "lds_right", callW_spec p n "lds_same"]
  grind [arena_grind] heartbeats 1000000 simp [St.setLocs_mem']

/-- **`lds_both` refines `bothT`** at the knot. -/
theorem ldsBoth_refines (p : Prog) (hp : LazyProg p) (hc : LazyCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) (hd : d.toNat < 2 ^ 63) :
    CoreSpec p (n + 1) "lds_both" [mode, vis, d, a, b]
      (bothT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b))
      decDS s₀ a₀ dn vis fe M eb Res3 := by
  refine CoreSpec.of_model (ldsBoth_spec p hp (n + 1) s₀ mode vis d a b)
    fun r s' hW => ?_
  rw [bothW.arm1] at hW
  have hS := hs.rel
  unfold bothT
  cases hc1 : callW p n "head_hint" [vis, a] s₀.mem with
  | none => rw [hc1, bothW.k_head_hint.none] at hW; cases hW
  | some q =>
  obtain ⟨ra, m₁⟩ := q
  rw [hc1, bothW.k_head_hint.arm1] at hW
  obtain ⟨k, rfl⟩ := callW_succ hc1
  have e₁ := CoreSpec.of_callW (headHint_refines p hp.mid.leaf k s₀ a₀ dn vis fe M eb a hS ha) hc1
  refine coreRef_bind e₁ (fun M₁ hS₁ => ?_)
  refine coreRef_callK hW rfl (headHint_refines p hp.mid.leaf k _ _ dn vis fe M₁ eb b hS₁ hb)
    fun rb m₂ hW e₂ M₂ hS₂ => ?_
  rw [bothW.k_head_hint_2.arm1] at hW
  -- the arms after the hints
  have arm : ∀ (f : FnName) (args : List Word) (m₃ : Mem) (T : AM DeltaStepA) (a₂ : AState),
      bothW.k_lds_left p (callW p (k + 1) f args m₃) = some (r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, s'.mem) →
      (∀ r₄ m₄, callW p (k + 1) f args m₃ = some (r₄, m₄) →
        CoreRef T a₂ decDS dn m₃ vis fe M₂ eb r₄ m₄ Res3) →
      CoreRef T a₂ decDS dn m₃ vis fe M₂ eb r s'.mem Res3 := by
    intro f args m₃ T a₂ h hT
    cases hc4 : callW p (k + 1) f args m₃ with
    | none => rw [hc4, bothW.k_lds_left.none] at h; cases h
    | some q =>
    obtain ⟨r₄, m₄⟩ := q
    rw [hc4, bothW.k_lds_left.arm1, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq] at h
    obtain ⟨g1, g2, g3, hm⟩ := h
    have e := hT r₄ m₄ hc4
    rw [← hm]
    exact coreRef_redec e (decDS_eq g1 g2 g3) (res3_eq g1 g2 g3 e.2.2.2)
  cases hc3 : callW p (k + 1) "hint_lt" [rb.headD 0, rb.tail.headD 0, ra.headD 0, ra.tail.headD 0] m₂ with
  | none => rw [hc3, bothW.k_hint_lt.none] at hW; cases hW
  | some q =>
  obtain ⟨rl, m₃⟩ := q
  rw [hc3] at hW
  obtain ⟨t₃, ht₃, hm₃, -, hlt₁, -⟩ := triple_of_callW (s₀ := ⟨m₂, Locals.init []⟩)
    (hintLt_refines p hp.mid.leaf k ⟨m₂, Locals.init []⟩ _ _ _ _) hc3
  have hm₃' : m₃ = m₂ := by rw [← ht₃, hm₃]
  subst hm₃'
  have hdh : ∀ r : List Word, decHintR r = decHintW (r.headD 0) (r.tail.headD 0) := fun _ => rfl
  rw [hdh ra, hdh rb]
  by_cases h1 : rl.headD 0 ≠ 0
  · rw [bothW.k_hint_lt.arm1 (hc1 := h1)] at hW
    have hl : ConLeche.ReducibilityHint.lt (decHintW (rb.headD 0) (rb.tail.headD 0))
        (decHintW (ra.headD 0) (ra.tail.headD 0)) = true := by rw [← hlt₁]; exact decBool_t h1
    simp only [hl, ↓reduceIte]
    exact arm _ _ _ _ _ hW (fun r₄ m₄ hc4 => CoreSpec.of_callW (s₀ := ⟨m₃, Locals.init []⟩)
      (ldsLeft_refines p hp hc k (hk.mono (by omega)) F (by omega) (by omega) _ _ dn vis fe M₂ eb
        mode d a b ⟨hS₂, hs.mode4, hs.eb_mode⟩ ha hb hd) hc4)
  have h1' : rl.headD 0 = 0 := by simpa using h1
  rw [bothW.k_hint_lt.arm2 (hc1 := h1')] at hW
  have hl : ConLeche.ReducibilityHint.lt (decHintW (rb.headD 0) (rb.tail.headD 0))
      (decHintW (ra.headD 0) (ra.tail.headD 0)) = false := by rw [← hlt₁]; exact decBool_f h1'
  simp only [hl, Bool.false_eq_true, ↓reduceIte]
  cases hc5 : callW p (k + 1) "hint_lt" [ra.headD 0, ra.tail.headD 0, rb.headD 0, rb.tail.headD 0] m₃ with
  | none => rw [hc5, bothW.k_hint_lt_2.none] at hW; cases hW
  | some q =>
  obtain ⟨rl₂, m₅⟩ := q
  rw [hc5] at hW
  obtain ⟨t₅, ht₅, hm₅, -, hlt₂, -⟩ := triple_of_callW (s₀ := ⟨m₃, Locals.init []⟩)
    (hintLt_refines p hp.mid.leaf k ⟨m₃, Locals.init []⟩ _ _ _ _) hc5
  have hm₅' : m₅ = m₃ := by rw [← ht₅, hm₅]
  subst hm₅'
  by_cases h2 : rl₂.headD 0 ≠ 0
  · rw [bothW.k_hint_lt_2.arm1 (hc1 := h2)] at hW
    have hl2 : ConLeche.ReducibilityHint.lt (decHintW (ra.headD 0) (ra.tail.headD 0))
        (decHintW (rb.headD 0) (rb.tail.headD 0)) = true := by rw [← hlt₂]; exact decBool_t h2
    simp only [hl2, ↓reduceIte]
    exact arm _ _ _ _ _ hW (fun r₄ m₄ hc4 => CoreSpec.of_callW (s₀ := ⟨m₅, Locals.init []⟩)
      (ldsRight_refines p hp hc k (hk.mono (by omega)) F (by omega) (by omega) _ _ dn vis fe M₂ eb
        mode d a b ⟨hS₂, hs.mode4, hs.eb_mode⟩ ha hb hd) hc4)
  have h2' : rl₂.headD 0 = 0 := by simpa using h2
  rw [bothW.k_hint_lt_2.arm2 (hc1 := h2')] at hW
  have hl2 : ConLeche.ReducibilityHint.lt (decHintW (ra.headD 0) (ra.tail.headD 0))
      (decHintW (rb.headD 0) (rb.tail.headD 0)) = false := by rw [← hlt₂]; exact decBool_f h2'
  simp only [hl2, Bool.false_eq_true, ↓reduceIte]
  exact arm _ _ _ _ _ hW (fun r₄ m₄ hc4 => CoreSpec.of_callW (s₀ := ⟨m₅, Locals.init []⟩)
    (ldsSame_refines p hp hc k (hk.mono (by omega)) F (by omega) (by omega) _ _ dn vis fe M₂ eb
      mode d a b _ _ _ _ ⟨hS₂, hs.mode4, hs.eb_mode⟩ ha hb hd) hc4)

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

/-- **`lazy_delta_step` is its model `ldsStepW`** (generated). Four callees on the longest path,
five arms. -/
l_model lazyDeltaStep_spec (p : Prog) (hp : LazyProg p)
  fns [hp.step ↦ ldsStepW tuple]
  specs [callW_spec p n "unfoldable_head", callW_spec p n "try_unfold_proj_app",
    callW_spec p n "delta_quick", callW_spec p n "lds_left", callW_spec p n "lds_right",
    callW_spec p n "lds_both"]
  grind [arena_grind] heartbeats 1000000 simp [St.setLocs_mem']

/-- **`lazy_delta_step` refines `lazyDeltaStep`** at the knot. -/
@[refines ConRon.Arena.lazyDeltaStep]
theorem lazyDeltaStep_refines (p : Prog) (hp : LazyProg p) (hc : LazyCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) (hd : d.toNat < 2 ^ 63) :
    CoreSpec p (n + 1) "lazy_delta_step" [mode, vis, d, a, b]
      (lazyDeltaStep (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b))
      decDS s₀ a₀ dn vis fe M eb Res3 := by
  refine CoreSpec.of_model (lazyDeltaStep_spec p hp (n + 1) s₀ mode vis d a b)
    fun r s' hW => ?_
  rw [ldsStepW.arm1] at hW
  have hS := hs.rel
  rw [lazyDeltaStep_eq]
  cases hc1 : callW p n "unfoldable_head" [vis, a] s₀.mem with
  | none => rw [hc1] at hW; cases hW
  | some q =>
  obtain ⟨ra, m₁⟩ := q
  rw [hc1, ldsStepW.k_unfoldable_head.arm1] at hW
  obtain ⟨k, rfl⟩ := callW_succ hc1
  have e₁ := CoreSpec.of_callW (unfoldableHead_refines p hp.mid.leaf k s₀ a₀ dn vis fe M eb a hS ha) hc1
  refine coreRef_bind e₁ (fun M₁ hS₁ => ?_)
  refine coreRef_callK hW rfl (unfoldableHead_refines p hp.mid.leaf k _ _ dn vis fe M₁ eb b hS₁ hb)
    fun rb m₂ hW e₂ M₂ hS₂ => ?_
  have arm : ∀ (f : FnName) (args : List Word) (m₃ : Mem) (T : AM DeltaStepA) (a₂ : AState)
      (M₃ : ModeMaps),
      ldsStepW.k_delta_quick p (callW p (k + 1) f args m₃) = some (r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, s'.mem) →
      (∀ r₄ m₄, callW p (k + 1) f args m₃ = some (r₄, m₄) →
        CoreRef T a₂ decDS dn m₃ vis fe M₃ eb r₄ m₄ Res3) →
      CoreRef T a₂ decDS dn m₃ vis fe M₃ eb r s'.mem Res3 := by
    intro f args m₃ T a₂ M₃ h hT
    cases hc4 : callW p (k + 1) f args m₃ with
    | none => rw [hc4] at h; cases h
    | some q =>
    obtain ⟨r₄, m₄⟩ := q
    rw [hc4, ldsStepW.k_delta_quick.arm1, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq] at h
    obtain ⟨g1, g2, g3, hm⟩ := h
    have e := hT r₄ m₄ hc4
    rw [← hm]
    exact coreRef_redec e (decDS_eq g1 g2 g3) (res3_eq g1 g2 g3 e.2.2.2)
  by_cases h00 : ra.headD 0 = 0 ∧ rb.headD 0 = 0
  · rw [ldsStepW.k_unfoldable_head_2.arm1 (hc1 := h00), Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq] at hW
    obtain ⟨g1, g2, g3, hm⟩ := hW
    rw [decBool_f h00.1, decBool_f h00.2, ← hm]
    exact coreRef_ret hS₂ (by simp only [decDS, ← g1]; rfl) (res3_of hw3 hw0 hw0 g1 g2 g3)
  by_cases hb0 : rb.headD 0 = 0
  · have ha0 : ra.headD 0 ≠ 0 := fun h => h00 ⟨h, hb0⟩
    rw [ldsStepW.k_unfoldable_head_2.arm2 (hc1 := h00) (hc2 := hb0)] at hW
    rw [decBool_t ha0, decBool_f hb0]
    refine coreRef_callK hW rfl
        (tryUnfoldProjApp_refines p hp.mid k (hk.mono (by omega)) F _ _ dn vis fe M₂ eb mode d b (by omega) (by omega) ⟨hS₂, hs.mode4, hs.eb_mode⟩ hb)
      fun rt m₃ hW e₃ M₃ hS₃ => ?_
    by_cases ht : rt.headD 0 ≠ 0
    · rw [ldsStepW.k_try_unfold_proj_app.arm1 (hc1 := ht)] at hW
      rw [decOptR_some ht]
      exact arm _ _ _ _ _ _ hW (fun r₄ m₄ hc4 => CoreSpec.of_callW (s₀ := ⟨m₃, Locals.init []⟩)
        (deltaQuick_refines p hp.mid k (quickUpTo hp hc hk k (by omega)) F _ _ dn vis fe M₃ eb mode d
          a _ (by omega) (by omega) ⟨hS₃, hs.mode4, hs.eb_mode⟩ ha e₃.2.2.2.2 hd) hc4)
    have ht' : rt.headD 0 = 0 := by simpa using ht
    rw [ldsStepW.k_try_unfold_proj_app.arm2 (hc1 := ht')] at hW
    rw [decOptR_none ht']
    exact arm _ _ _ _ _ _ hW (fun r₄ m₄ hc4 => CoreSpec.of_callW (s₀ := ⟨m₃, Locals.init []⟩)
      (ldsLeft_refines p hp hc k (hk.mono (by omega)) F (by omega) (by omega) _ _ dn vis fe M₃ eb
        mode d a b ⟨hS₃, hs.mode4, hs.eb_mode⟩ ha hb hd) hc4)
  by_cases ha0 : ra.headD 0 = 0
  · rw [ldsStepW.k_unfoldable_head_2.arm3 (hc1 := h00) (hc2 := hb0) (hc3 := ha0)] at hW
    rw [decBool_f ha0, decBool_t hb0]
    refine coreRef_callK hW rfl
        (tryUnfoldProjApp_refines p hp.mid k (hk.mono (by omega)) F _ _ dn vis fe M₂ eb mode d a (by omega) (by omega) ⟨hS₂, hs.mode4, hs.eb_mode⟩ ha)
      fun rt m₃ hW e₃ M₃ hS₃ => ?_
    by_cases ht : rt.headD 0 ≠ 0
    · rw [ldsStepW.k_try_unfold_proj_app_2.arm1 (hc1 := ht)] at hW
      rw [decOptR_some ht]
      exact arm _ _ _ _ _ _ hW (fun r₄ m₄ hc4 => CoreSpec.of_callW (s₀ := ⟨m₃, Locals.init []⟩)
        (deltaQuick_refines p hp.mid k (quickUpTo hp hc hk k (by omega)) F _ _ dn vis fe M₃ eb mode d
          _ b (by omega) (by omega) ⟨hS₃, hs.mode4, hs.eb_mode⟩ e₃.2.2.2.2 hb hd) hc4)
    have ht' : rt.headD 0 = 0 := by simpa using ht
    rw [ldsStepW.k_try_unfold_proj_app_2.arm2 (hc1 := ht')] at hW
    rw [decOptR_none ht']
    exact arm _ _ _ _ _ _ hW (fun r₄ m₄ hc4 => CoreSpec.of_callW (s₀ := ⟨m₃, Locals.init []⟩)
      (ldsRight_refines p hp hc k (hk.mono (by omega)) F (by omega) (by omega) _ _ dn vis fe M₃ eb
        mode d a b ⟨hS₃, hs.mode4, hs.eb_mode⟩ ha hb hd) hc4)
  rw [ldsStepW.k_unfoldable_head_2.arm4 (hc1 := fun h => ha0 h.1) (hc2 := hb0) (hc3 := ha0)] at hW
  rw [decBool_t ha0, decBool_t hb0]
  exact arm _ _ _ _ _ _ hW (fun r₄ m₄ hc4 => CoreSpec.of_callW (s₀ := ⟨m₂, Locals.init []⟩)
    (ldsBoth_refines p hp hc k (hk.mono (by omega)) F (by omega) (by omega) _ _ dn vis fe M₂ eb
      mode d a b ⟨hS₂, hs.mode4, hs.eb_mode⟩ ha hb hd) hc4)

end L.Arena
