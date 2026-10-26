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

end L.Arena
