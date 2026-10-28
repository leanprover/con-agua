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

/-! ## Error claims through equal or failing runs -/

/-- The twin computations agree on the run from `a`. -/
theorem ErrClaim.of_run_eqW {α : Type} {T T' : AM α} {a a' : AState} {e : Err}
    (h : T.run a = T'.run a') (h' : ErrClaim T' a' e) : ErrClaim T a e := fun hk => by
  obtain ⟨ce, hce, hc⟩ := h' hk
  exact ⟨ce, h ▸ hce, hc⟩

/-- The twin's run from `a` fails where `T'`'s from `a'` does. -/
theorem ErrClaim.of_run_err {α β : Type} {T : AM α} {T' : AM β} {a a' : AState} {e : Err}
    (h : ∀ ce, T'.run a' = .error ce → T.run a = .error ce) (h' : ErrClaim T' a' e) :
    ErrClaim T a e := fun hk => by
  obtain ⟨ce, hce, hc⟩ := h' hk
  exact ⟨ce, h ce hce, hc⟩

/-! ## Unified refinements of core functions

A core function's unified refinement (`RefE`, `Verdict.lean`) relates its model's value `(r, m)`
to the twin's run by `CorePost`: what `CoreRef` says besides the twin's ok run. Its halves come
from the call's run through the model's spec: the ok spec (`RefE.coreSpec`), the `CoreRef` of a
callee's run (`RefE.coreRefW`), the error spec (`RefE.coreSpecE`). -/

/-- What a core function's run `v = (r, m)` from `m₀` gives besides the twin's result `y` and
final state `a'`: the relation after it, the result words decoded, their validity. -/
structure CorePost {α : Type} (dec : List Word → α) (dn : NIdx → Option ConLeche.Name) (m₀ : Mem)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb : Word) (ok : List Word → Prop)
    (v : List Word × Mem) (y : α) (a' : AState) : Prop where
  after : CoreAfter dn m₀ v.2 a' vis fe M eb
  res : y = dec v.1
  valid : ok v.1

section corePost
open Std.WP
variable {α : Type} [Inhabited α] {T : AM α} {a : AState} {dec : List Word → α}
  {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word}
  {ok : List Word → Prop} {G Gs : Prop} {p : Prog} {n : Nat} {f : FnName} {args : List Word}
  {s₀ : St} {fx : Except Err (List Word × Mem)}

theorem CorePost.coreRef {m₀ m : Mem} {r : List Word} {y : α} {a' : AState}
    (hT : T.run a = .ok (y, a')) (h : CorePost dec dn m₀ vis fe M eb ok (r, m) y a') :
    CoreRef T a dec dn m₀ vis fe M eb r m ok := by
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hT
  exact ⟨hok, hst ▸ h.after, hres.trans h.res, h.valid⟩

/-- The ok half as the core spec of the call. -/
theorem RefE.coreSpec
    (hs : ⦃fun s => s = s₀⦄ invoke p (exec p n) f args
      ⦃fun r s' => LocEq s' s₀ ∧ fx = .ok (r, s'.mem); fun ε => Gs → ε.cls ≠ 0 → fx = .error ε⦄)
    (h : RefE G fx T a (CorePost dec dn s₀.mem vis fe M eb ok)) :
    CoreSpec p n f args T dec s₀ a dn vis fe M eb ok :=
  L.M.triple_of_run fun _ _ _ hp hr => by
    obtain ⟨hl, _, _, hT, hR⟩ := L.M.of_run' (P := fun s => s = s₀) hp hr (RefE.triple hs h)
    exact ⟨hl, hR.coreRef hT⟩

/-- The ok half at a callee's run (`callW`, the ok models' reading of a call). -/
theorem RefE.coreRefW
    (hs : ⦃fun s => s = s₀⦄ invoke p (exec p n) f args
      ⦃fun r s' => LocEq s' s₀ ∧ fx = .ok (r, s'.mem); fun ε => Gs → ε.cls ≠ 0 → fx = .error ε⦄)
    (h : RefE G fx T a (CorePost dec dn s₀.mem vis fe M eb ok)) {r : List Word} {m' : Mem}
    (hc : callW p n f args s₀.mem = some (r, m')) :
    CoreRef T a dec dn s₀.mem vis fe M eb r m' ok := by
  obtain ⟨s', rfl, -, y, a', hT, hR⟩ := RefE.run_okW hs h hc
  exact hR.coreRef hT

end corePost

end L.Arena
