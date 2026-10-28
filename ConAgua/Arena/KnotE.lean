import ConAgua.Arena.Verdict

/-!
# The knot's error half: the five slots' verdict claims

`KnotOK p n` (`WhnfBase.lean`) says each of the knot's five slots (`whnf_core`, `whnf`, `infer`,
`infer_io`, `defeq`) refines the twin's slot when it returns. `KnotOKE p n` is the error half: a
call of a slot that fails with an abort of class `1` or `2` claims that the twin's slot fails with
an error of that class (`CoreSpecE`), from the same start and under the same hypotheses.

The ok knot is proved for every fuel (`knot_all`); the error knot is proved by the same induction
on the L fuel (`knotE_upTo`): at fuel `0` every call fails with class `0` (`CoreSpecE.zero`), and
a body at fuel `n + 1` uses the ok knot and the error knot up to `n` (`KnotStepE`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- `whnf_core`'s error claim. -/
def WhnfCoreSlotE (p : Prog) (n : Nat) : Prop :=
  ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode cheap d e : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe M eb mode →
    HW e →
    CoreSpecE p n "whnf_core" [mode, cheap, vis, d, e]
      ((coreKnot (decMode mode) fe id F).whnfCore (cheap != 0) d.toNat (decE e)) s₀ a₀

/-- `whnf`'s error claim. -/
def WhnfSlotE (p : Prog) (n : Nat) : Prop :=
  ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d e : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe M eb mode → HW e →
    CoreSpecE p n "whnf" [mode, vis, d, e] ((coreKnot (decMode mode) fe id F).whnf d.toNat (decE e)) s₀ a₀

/-- `infer`'s error claim. -/
def InferSlotE (p : Prog) (n : Nat) : Prop :=
  ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d e : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe M eb mode → HW e →
    CoreSpecE p n "infer" [mode, vis, d, e] ((coreKnot (decMode mode) fe id F).infer d.toNat (decE e)) s₀ a₀

/-- `infer_io`'s error claim. -/
def InferIOSlotE (p : Prog) (n : Nat) : Prop :=
  ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d e : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe M eb mode → HW e →
    CoreSpecE p n "infer_io" [mode, vis, d, e]
      ((coreKnot (decMode mode) fe id F).inferIO d.toNat (decE e)) s₀ a₀

/-- `defeq`'s error claim. -/
def DefeqSlotE (p : Prog) (n : Nat) : Prop :=
  ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d x y : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe M eb mode → HW x →
    HW y →
    CoreSpecE p n "defeq" [mode, vis, d, x, y]
      ((coreKnot (decMode mode) fe id F).defeq d.toNat (decE x) (decE y)) s₀ a₀

/-- **The knot's error half at L fuel `n`**: every slot. -/
structure KnotOKE (p : Prog) (n : Nat) : Prop where
  whnfCore : WhnfCoreSlotE p n
  whnf : WhnfSlotE p n
  infer : InferSlotE p n
  inferIO : InferIOSlotE p n
  defeq : DefeqSlotE p n

/-- The error half at every L fuel up to `n`. -/
def KnotUpToE (p : Prog) (n : Nat) : Prop := ∀ k, k ≤ n → KnotOKE p k

theorem KnotUpToE.mono {p : Prog} {n m : Nat} (h : KnotUpToE p n) (hm : m ≤ n) : KnotUpToE p m :=
  fun k hk => h k (Nat.le_trans hk hm)

/-- **At fuel `0`** every call fails with class `0`. -/
theorem knotE_zero (p : Prog) : KnotOKE p 0 where
  whnfCore := fun _ s₀ a₀ _ _ _ _ _ _ _ _ _ _ _ _ _ => CoreSpecE.zero p _ _ _ s₀ a₀
  whnf := fun _ s₀ a₀ _ _ _ _ _ _ _ _ _ _ _ _ => CoreSpecE.zero p _ _ _ s₀ a₀
  infer := fun _ s₀ a₀ _ _ _ _ _ _ _ _ _ _ _ _ => CoreSpecE.zero p _ _ _ s₀ a₀
  inferIO := fun _ s₀ a₀ _ _ _ _ _ _ _ _ _ _ _ _ => CoreSpecE.zero p _ _ _ s₀ a₀
  defeq := fun _ s₀ a₀ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => CoreSpecE.zero p _ _ _ s₀ a₀

/-- What the error knot's step needs: the five bodies at `n + 1` from the ok knot (every fuel)
and the error knot up to `n`. -/
def KnotStepE (p : Prog) : Prop :=
  ∀ n, KnotUpTo p n → KnotUpToE p n → KnotOKE p (n + 1)

/-- **The error knot at every fuel**, from its step. -/
theorem knotE_upTo {p : Prog} (hk : ∀ n, KnotUpTo p n) (hs : KnotStepE p) (n : Nat) :
    KnotUpToE p n := by
  induction n with
  | zero => intro k hk0; obtain rfl : k = 0 := by omega
            exact knotE_zero p
  | succ n ih =>
    intro k hkn
    by_cases h : k ≤ n
    · exact ih k h
    · obtain rfl : k = n + 1 := by omega
      exact hs n (hk n) ih

/-! ## A core function's two halves from one refinement

A unified model (`l_model … unified`) of a function of the knot's family refines the twin with
the post `CorePost` (the relation after the run, the result's decoding and validity); its ok half
is the `CoreSpec` (`CoreSpec.of_refE`), its error half the `CoreSpecE` (`RefE.coreSpecE`). -/

/-- **What a core function gives besides the twin's result `y` and state `a'`** (from `m₀`, the
results `r` and the memory `m`): `CoreRef`'s conjuncts after the run. -/
structure CorePost {α : Type} (dec : List Word → α) (dn : NIdx → Option ConLeche.Name) (m₀ : Mem)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb : Word) (ok : List Word → Prop) (r : List Word)
    (m : Mem) (y : α) (a' : AState) : Prop where
  after : CoreAfter dn m₀ m a' vis fe M eb
  res : y = dec r
  ok : ok r

/-- A `CoreRef` from the twin's ok run and the post. -/
theorem CorePost.coreRef {α : Type} [Inhabited α] {T : AM α} {a₀ a' : AState} {y : α}
    {dec : List Word → α} {dn : NIdx → Option ConLeche.Name} {m₀ m : Mem} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} {ok : List Word → Prop} {r : List Word}
    (hrun : T.run a₀ = .ok (y, a')) (h : CorePost dec dn m₀ vis fe M eb ok r m y a') :
    CoreRef T a₀ dec dn m₀ vis fe M eb r m ok := by
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hok, hst ▸ h.after, hres ▸ h.res, h.ok⟩

/-- A `CorePost` from a `CoreRef` (a callee's ok half). -/
theorem CoreRef.post {α : Type} [Inhabited α] {T : AM α} {a₀ : AState}
    {dec : List Word → α} {dn : NIdx → Option ConLeche.Name} {m₀ m : Mem} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} {ok : List Word → Prop} {r : List Word}
    (h : CoreRef T a₀ dec dn m₀ vis fe M eb r m ok) :
    T.run a₀ = .ok (AM.res T a₀, AM.st T a₀) ∧
      CorePost dec dn m₀ vis fe M eb ok r m (AM.res T a₀) (AM.st T a₀) :=
  ⟨AM.run_of_ok _ _ h.1, h.2.1, h.2.2.1, h.2.2.2⟩

/-- `RefE` reads the twin only through its run from `a`. -/
theorem RefE.of_run_eq {α β : Type} {G : Prop} {x : Except Err α} {T T' : AM β} {a a' : AState}
    {R : α → β → AState → Prop} (h : T.run a = T'.run a') (h' : RefE G x T' a' R) :
    RefE G x T a R := by
  cases x with
  | ok v => obtain ⟨y, a₁, hy, hR⟩ := h'; exact ⟨y, a₁, h.trans hy, hR⟩
  | error e => exact fun hG hk => by obtain ⟨ce, hce, hc⟩ := h' hG hk; exact ⟨ce, h ▸ hce, hc⟩

/-- A weaker post. -/
theorem RefE.mono {α β : Type} {G : Prop} {x : Except Err α} {T : AM β} {a : AState}
    {R R' : α → β → AState → Prop} (h : RefE G x T a R) (hR : ∀ v y a', R v y a' → R' v y a') :
    RefE G x T a R' := by
  cases x with
  | ok v => obtain ⟨y, a₁, hy, hr⟩ := h; exact ⟨y, a₁, hy, hR _ _ _ hr⟩
  | error e => exact h

/-- A leaf: the twin returns at the start's state, the relation holds there. -/
theorem CorePost.ret {α : Type} {dec : List Word → α} {dn : NIdx → Option ConLeche.Name} {m : Mem}
    {a : AState} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word} {ok : List Word → Prop}
    {r : List Word} {y : α} (hS : CoreS dn m a vis fe M eb) (hy : y = dec r) (hr : ok r) :
    CorePost dec dn m vis fe M eb ok r m y a :=
  ⟨⟨M, hS, KeptAll.refl _ _, StackKept.refl _⟩, hy, hr⟩

/-- **A core callee's ok run, then the rest**, both outcomes: the rest from the callee's state,
at any maps of the relation there, the stack kept across the callee. -/
theorem RefE.bind_core {α β γ : Type} [Inhabited γ] {G : Prop} {x : Except Err α} {T₁ : AM γ}
    {f : γ → AM β} {a₀ : AState} {dec₁ : List Word → γ} {dec : List Word → β}
    {dn : NIdx → Option ConLeche.Name} {m₀ m₁ : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps}
    {eb : Word} {r₁ : List Word} {ok₁ ok : List Word → Prop} {w : α → List Word × Mem}
    (h₁ : CoreRef T₁ a₀ dec₁ dn m₀ vis fe M eb r₁ m₁ ok₁)
    (h₂ : ∀ M', CoreS dn m₁ (AM.st T₁ a₀) vis fe M' eb → StackKept m₀ m₁ →
      RefE G x (f (dec₁ r₁)) (AM.st T₁ a₀)
        (fun v y a' => CorePost dec dn m₁ vis fe M' eb ok (w v).1 (w v).2 y a')) :
    RefE G x (T₁ >>= f) a₀ (fun v y a' => CorePost dec dn m₀ vis fe M eb ok (w v).1 (w v).2 y a') := by
  obtain ⟨M', hS, hK, hSt⟩ := h₁.2.1
  exact RefE.bind_right (by rw [AM.run_of_ok _ _ h₁.1, h₁.2.2.1])
    ((h₂ M' hS hSt).mono fun _ _ _ h => ⟨CoreAfter.comp hK hSt h.after, h.res, h.ok⟩)

/-- **The ok half of a unified core function** as its `CoreSpec`: `w` reads the model's ok value
back as the results and the memory. -/
theorem CoreSpec.of_refE {α β : Type} [Inhabited β] {p : Prog} {n : Nat} {f : FnName}
    {args : List Word} {s₀ : St} {Gs G : Prop} {fx : Except Err α} {V : List Word → St → α}
    {T : AM β} {a₀ : AState} {dec : List Word → β} {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} {ok : List Word → Prop} {w : α → List Word × Mem}
    (hs : ⦃fun s => s = s₀⦄ invoke p (exec p n) f args
      ⦃fun r s' => LocEq s' s₀ ∧ fx = .ok (V r s'); fun ε => Gs → ε.cls ≠ 0 → fx = .error ε⦄)
    (h : RefE G fx T a₀ (fun v y a' => CorePost dec dn s₀.mem vis fe M eb ok (w v).1 (w v).2 y a'))
    (hw : ∀ r s', (w (V r s')).2 = s'.mem ∧ dec (w (V r s')).1 = dec r ∧ (ok (w (V r s')).1 → ok r)) :
    CoreSpec p n f args T dec s₀ a₀ dn vis fe M eb ok := by
  refine L.M.triple_of_run fun _ r s' hp hr => ?_
  obtain ⟨hl, y, a', hrun, hR⟩ := L.M.of_run (P := fun s => s = s₀) hp hr (RefE.triple hs h)
  obtain ⟨hm, hd, ho⟩ := hw r s'
  exact ⟨hl, CorePost.coreRef hrun ⟨hm ▸ hR.after, hR.res.trans hd, ho hR.ok⟩⟩

end L.Arena
