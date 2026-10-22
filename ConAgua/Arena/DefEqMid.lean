import ConAgua.Arena.DefEqLeaves2
import ConAgua.Arena.InferLeaves

/-!
# Refinements of `DefEq.lean`'s middle layer (lane `defeq`, helper `defeq-mid`)

The callW pattern (`WhnfCoreRefine.lean`, `InferLeaves.lean`): a word model of each function with
its callees through their runs (`callW`), in the continuation shape (`…K (callW …)`: the run is an
argument of the model, one arm lemma per outcome), the L spec by `vcgen` + `finish`, the
refinement from the callees' specs, sequenced by `coreRef_bind`.

Functions whose callees include the knot's slots refine their twins at `coreKnot (decMode mode) fe
id F` for `F ≥ n`, where `n` is the L fuel of the callee calls (`KnotUpTo`/`DefeqSlot` at `n`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## Sequencing -/

/-- **A core run, then the rest of a `do` block on its decoded result.** -/
theorem coreRef_bind {α β : Type} [Inhabited α] [Inhabited β] {T₁ : AM α} {f : α → AM β}
    {a₀ : AState} {dec₁ : List Word → α} {dec : List Word → β} {dn : NIdx → Option ConLeche.Name}
    {m₀ m₁ m : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word} {r₁ r : List Word}
    {ok₁ ok : List Word → Prop}
    (h₁ : CoreRef T₁ a₀ dec₁ dn m₀ vis fe M eb r₁ m₁ ok₁)
    (h₂ : ∀ M', CoreS dn m₁ (AM.st T₁ a₀) vis fe M' eb →
      CoreRef (f (dec₁ r₁)) (AM.st T₁ a₀) dec dn m₁ vis fe M' eb r m ok) :
    CoreRef (T₁ >>= f) a₀ dec dn m₀ vis fe M eb r m ok := by
  refine coreRef_then h₁ h₂ ?_
  rw [StateT.run_bind, AM.run_of_ok _ _ h₁.1, h₁.2.2.1]; rfl

/-- **A pure result** under the relation. -/
theorem coreRef_ret {α : Type} [Inhabited α] {a : AState} {dec : List Word → α}
    {dn : NIdx → Option ConLeche.Name} {m : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps}
    {eb : Word} {r : List Word} {v : α} {ok : List Word → Prop} (hS : CoreS dn m a vis fe M eb)
    (hv : v = dec r) (hr : ok r) : CoreRef (pure v) a dec dn m vis fe M eb r m ok :=
  ⟨trivial, ⟨M, hS, KeptAll.refl _ _, StackKept.refl _⟩, hv, hr⟩

theorem resH_zero : ResH [0] := hw0
theorem resH_one : ResH [1] := hw1

theorem decBool_t {r : List Word} (h : r.headD 0 ≠ 0) : decBool r = true := by
  simp only [decBool, bne_iff_ne]; exact h

theorem decBool_f {r : List Word} (h : r.headD 0 = 0) : decBool r = false := by
  simp only [decBool, h, bne_self_eq_false]

/-! ## The program -/

/-- The lookups of this file. -/
structure DefEqMidProg (p : Prog) : Prop where
  noFvars : p.lookup "defeq_no_fvars" = some defeqNoFvarsL
  foldOk : p.lookup "lazy_fold_ok" = some lazyFoldOkL

/-! ## `defeq_no_fvars` -/

/-- The model past the second `has_fvar` run. -/
def noFvarsK2 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m₂) => some (if r.headD 0 = 0 then 1 else 0, m₂)

/-- The model past the first `has_fvar` run. -/
def noFvarsK (p : Prog) (n : Nat) (b : Word) (res : Option (List Word × Mem)) :
    Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m₁) => if r.headD 0 ≠ 0 then some (0, m₁) else noFvarsK2 (callW p n "has_fvar" [b] m₁)

section nf
variable (p : Prog) (n : Nat) (b : Word) (r : List Word) (m₁ : Mem)

theorem noFvarsK_t (h : r.headD 0 ≠ 0) : noFvarsK p n b (some (r, m₁)) = some (0, m₁) := by
  simp only [noFvarsK, h, ne_eq, not_false_eq_true, ↓reduceIte]
theorem noFvarsK_f (h : r.headD 0 = 0) :
    noFvarsK p n b (some (r, m₁)) = noFvarsK2 (callW p n "has_fvar" [b] m₁) := by
  simp only [noFvarsK, h, ne_eq, not_true_eq_false, ↓reduceIte]
theorem noFvarsK2_some : noFvarsK2 (some (r, m₁)) = some (if r.headD 0 = 0 then 1 else 0, m₁) := rfl

end nf

theorem defeqNoFvars_spec (p : Prog) (hp : DefEqMidProg p) (n : Nat) (s₀ : St) (a b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "defeq_no_fvars" [a, b]
    ⦃fun r s' => LocEq s' s₀ ∧
      noFvarsK p n b (callW p n "has_fvar" [a] s₀.mem) = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.noFvars]
  simp only [callFn, defeqNoFvarsL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "has_fvar"] <;>
    finish [noFvarsK_t, noFvarsK_f, noFvarsK2_some]

/-- **`defeq_no_fvars` refines `defeqNoFvars`**, from `has_fvar`'s spec. -/
@[refines ConRon.Arena.defeqNoFvars]
theorem defeqNoFvars_refines (p : Prog) (hp : DefEqMidProg p) (hf : HasFvarOK p) (n : Nat)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb a b : Word) (hS : CoreS dn s₀.mem a₀ vis fe M eb) (ha : HW a) (hb : HW b) :
    CoreSpec p (n + 1) "defeq_no_fvars" [a, b] (defeqNoFvars (decE a) (decE b)) decBool s₀ a₀ dn
      vis fe M eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun (defeqNoFvars_spec p hp n s₀ a b)
  subst hs0
  refine ⟨hloc, ?_⟩
  cases hc : callW p n "has_fvar" [a] s.mem with
  | none => rw [hc] at hW; simp [noFvarsK] at hW
  | some q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [hc] at hW
  have h₁ := CoreSpec.of_callW (hf n s a₀ dn vis fe M eb a hS ha) hc
  refine coreRef_bind h₁ (fun M₁ hS₁ => ?_)
  by_cases h0 : r₁.headD 0 ≠ 0
  · rw [noFvarsK_t p n b r₁ m₁ h0, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, rfl⟩ := hW
    rw [decBool_t h0]
    exact coreRef_ret hS₁ (by rw [decBool, ← hr]; rfl) (by unfold ResH; rw [← hr]; exact hw0)
  have h0' : r₁.headD 0 = 0 := by simpa using h0
  rw [noFvarsK_f p n b r₁ m₁ h0'] at hW
  rw [decBool_f h0']
  simp only [Bool.false_eq_true, ↓reduceIte]
  cases hc2 : callW p n "has_fvar" [b] m₁ with
  | none => rw [hc2] at hW; simp [noFvarsK2] at hW
  | some q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [hc2, noFvarsK2_some, Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, rfl⟩ := hW
  have h₂ := CoreSpec.of_callW (s₀ := ⟨m₁, Locals.init []⟩)
    (hf n _ _ dn vis fe M₁ eb b hS₁ hb) hc2
  refine coreRef_bind h₂ (fun M₂ hS₂ => coreRef_ret hS₂ ?_ (resH_of hw1 hw0 hr))
  simp only [decBool, ← hr]
  generalize r₂.headD 0 = w
  by_cases hz : w = 0 <;> simp [hz]

/-! ## `lazy_fold_ok` -/

/-- The model of `lazy_fold_ok`. -/
def lazyFoldOkW (p : Prog) (n : Nat) (m : Mem) (mode a b : Word) : Option (Word × Mem) :=
  if (mode >>> 1) &&& 1 ≠ 0 then some (1, m) else call1W p n "defeq_no_fvars" [a, b] m

theorem lazyFoldOkW_e (p : Prog) (n : Nat) (m : Mem) (mode a b : Word) (h : (mode >>> 1) &&& 1 ≠ 0) :
    lazyFoldOkW p n m mode a b = some (1, m) := by
  simp only [lazyFoldOkW, h, ne_eq, not_false_eq_true, ↓reduceIte]

theorem lazyFoldOkW_p (p : Prog) (n : Nat) (m : Mem) (mode a b : Word) (h : (mode >>> 1) &&& 1 = 0) :
    lazyFoldOkW p n m mode a b = call1W p n "defeq_no_fvars" [a, b] m := by
  simp only [lazyFoldOkW, h, ne_eq, not_true_eq_false, ↓reduceIte]

theorem lazyFoldOk_spec (p : Prog) (hp : DefEqMidProg p) (n : Nat) (s₀ : St) (mode a b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "lazy_fold_ok" [mode, a, b]
    ⦃fun r s' => LocEq s' s₀ ∧ lazyFoldOkW p n s₀.mem mode a b = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.foldOk]
  simp only [callFn, lazyFoldOkL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "defeq_no_fvars"] <;>
    finish [lazyFoldOkW_e, lazyFoldOkW_p, call1W_some]

theorem mode_eager_bit (mode : Word) (h : mode < 4) :
    (decMode mode).eager = decide ((mode >>> 1) &&& 1 ≠ 0) := by
  rcases mode_cases mode h with rfl | rfl | rfl | rfl <;> decide

/-- **`lazy_fold_ok` refines `lazyFoldOk`**, from `has_fvar`'s spec. -/
@[refines ConRon.Arena.lazyFoldOk]
theorem lazyFoldOk_refines (p : Prog) (hp : DefEqMidProg p) (hf : HasFvarOK p) (n : Nat)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode a b : Word) (hS : CoreS dn s₀.mem a₀ vis fe M eb) (hm : mode < 4)
    (ha : HW a) (hb : HW b) :
    CoreSpec p (n + 2) "lazy_fold_ok" [mode, a, b] (lazyFoldOk (decMode mode) (decE a) (decE b))
      decBool s₀ a₀ dn vis fe M eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (lazyFoldOk_spec p hp (n + 1) s₀ mode a b)
  subst hs0
  refine ⟨hloc, ?_⟩
  have he := mode_eager_bit mode hm
  by_cases h0 : (mode >>> 1) &&& 1 ≠ 0
  · rw [lazyFoldOkW_e p _ _ mode a b h0, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm'⟩ := hW
    rw [← hm']
    simp only [lazyFoldOk, he, h0, ne_eq, not_false_eq_true, decide_true, ↓reduceIte]
    exact coreRef_ret hS (by rw [decBool, ← hr]; rfl) (by unfold ResH; rw [← hr]; exact hw1)
  have h0' : (mode >>> 1) &&& 1 = 0 := by simpa using h0
  rw [lazyFoldOkW_p p _ _ mode a b h0'] at hW
  simp only [lazyFoldOk, he, h0', ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
    ↓reduceIte]
  exact CoreSpec.of_call1W (s₀ := ⟨s.mem, Locals.init []⟩)
    (defeqNoFvars_refines p hp hf n _ a₀ dn vis fe M eb a b hS ha hb)
    (fun r r' h => by simp only [decBool, h]) hW

end L.Arena
