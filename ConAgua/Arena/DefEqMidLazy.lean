import ConAgua.Arena.DefEqMidSpine

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
  reduceNat : ∀ n, ReduceNatSpec p n
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
    cases hc2 : callW p n "whnf_core" [mode, 1, vis, d, r₁.tail.headD 0] m₁ with
    | none => rw [hc2] at hW; cases hW
    | some q =>
    obtain ⟨r₂, m₂⟩ := q
    rw [hc2] at hW
    have e₂ := CoreSpec.of_callW (s₀ := ⟨m₁, Locals.init []⟩)
      ((hk n (Nat.le_refl _)).whnfCore F _ _ dn vis fe M₁ eb mode 1 d _ hF hn ⟨hS₁, hmode, heb⟩
        e₁.2.2.2.2) hc2
    have h1t : ((1 : Word) != 0) = true := rfl
    rw [h1t] at e₂
    refine coreRef_bind e₂ (fun M₂ hS₂ => ?_)
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

end L.Arena
