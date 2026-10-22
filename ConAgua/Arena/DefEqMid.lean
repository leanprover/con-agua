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
  leaf : DefEqLeafProg p
  bts : p.lookup "bool_true_shortcut" = some boolTrueShortcutL
  tupa : p.lookup "try_unfold_proj_app" = some tryUnfoldProjAppL

/-- A run that succeeded had fuel. -/
theorem callW_succ {p : Prog} {n : Nat} {f : FnName} {vs : List Word} {m m' : Mem} {r : List Word}
    (h : callW p n f vs m = some (r, m')) : ∃ k, n = k + 1 := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ k => exact ⟨k, rfl⟩

theorem call1W_succ {p : Prog} {n : Nat} {f : FnName} {vs : List Word} {m m' : Mem} {w : Word}
    (h : call1W p n f vs m = some (w, m')) : ∃ k, n = k + 1 := by
  cases n with
  | zero => simp [call1W, callW_zero] at h
  | succ k => exact ⟨k, rfl⟩

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

/-! ## `bool_true_shortcut` -/

/-- The model of `bool_true_shortcut` past `whnf`'s run. -/
def btsK (p : Prog) (n : Nat) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m₁) => call1W p n "is_bool_true" [r.headD 0] m₁

theorem btsK_some (p : Prog) (n : Nat) (r : List Word) (m₁ : Mem) :
    btsK p n (some (r, m₁)) = call1W p n "is_bool_true" [r.headD 0] m₁ := rfl

theorem boolTrueShortcut_spec (p : Prog) (hp : DefEqMidProg p) (n : Nat) (s₀ : St) (mode vis d a : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "bool_true_shortcut" [mode, vis, d, a]
    ⦃fun r s' => LocEq s' s₀ ∧
      btsK p n (callW p n "whnf" [mode, vis, d, a] s₀.mem) = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.bts]
  simp only [callFn, boolTrueShortcutL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "whnf",
      callW_spec p n "is_bool_true"] <;>
    finish [btsK_some, call1W_some]

/-- **`bool_true_shortcut` refines `boolTrueShortcut`** at the knot. -/
@[refines ConRon.Arena.boolTrueShortcut]
theorem boolTrueShortcut_refines (p : Prog) (hp : DefEqMidProg p) (n : Nat) (hk : KnotUpTo p n)
    (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d a : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) :
    CoreSpec p (n + 1) "bool_true_shortcut" [mode, vis, d, a]
      (boolTrueShortcut (coreKnot (decMode mode) fe id F) d.toNat (decE a)) decBool s₀ a₀ dn vis
      fe M eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (boolTrueShortcut_spec p hp n s₀ mode vis d a)
  subst hs0
  refine ⟨hloc, ?_⟩
  cases hc : callW p n "whnf" [mode, vis, d, a] s.mem with
  | none => rw [hc] at hW; simp [btsK] at hW
  | some q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [hc, btsK_some] at hW
  have h₁ := CoreSpec.of_callW ((hk n (Nat.le_refl _)).whnf F s a₀ dn vis fe M eb mode d a hF hn hs ha) hc
  refine coreRef_bind h₁ (fun M₁ hS₁ => ?_)
  obtain ⟨k, rfl⟩ := call1W_succ hW
  exact CoreSpec.of_call1W (s₀ := ⟨m₁, Locals.init []⟩)
    (isBoolTrue_refines p hp.leaf k _ _ dn vis fe M₁ eb _ hS₁ h₁.2.2.2)
    (fun r r' h => by simp only [decBool, h]) hW

/-! ## `try_unfold_proj_app` -/

/-- The model of `try_unfold_proj_app` past `whnf_core`'s run. -/
def tupaK2 (e : Word) (res : Option (List Word × Mem)) : Option (Word × Word × Mem) :=
  match res with
  | none => none
  | some (r, m₂) => if r.headD 0 = e then some (0, 0, m₂) else some (1, r.headD 0, m₂)

/-- The model of `try_unfold_proj_app` past `head_is_proj`'s run. -/
def tupaK (p : Prog) (n : Nat) (mode vis d e : Word) (res : Option (List Word × Mem)) :
    Option (Word × Word × Mem) :=
  match res with
  | none => none
  | some (r, m₁) =>
    if r.headD 0 = 0 then some (0, 0, m₁)
    else tupaK2 e (callW p n "whnf_core" [mode, 0, vis, d, e] m₁)

section tupa
variable (p : Prog) (n : Nat) (mode vis d e : Word) (r : List Word) (m₁ : Mem)

theorem tupaK_z (h : r.headD 0 = 0) : tupaK p n mode vis d e (some (r, m₁)) = some (0, 0, m₁) := by
  simp only [tupaK, h, ↓reduceIte]
theorem tupaK_nz (h : r.headD 0 ≠ 0) : tupaK p n mode vis d e (some (r, m₁)) =
    tupaK2 e (callW p n "whnf_core" [mode, 0, vis, d, e] m₁) := by
  simp only [tupaK, h, ↓reduceIte]
theorem tupaK2_eq (h : r.headD 0 = e) : tupaK2 e (some (r, m₁)) = some (0, 0, m₁) := by
  simp only [tupaK2, h, ↓reduceIte]
theorem tupaK2_ne (h : r.headD 0 ≠ e) : tupaK2 e (some (r, m₁)) = some (1, r.headD 0, m₁) := by
  simp only [tupaK2, h, ↓reduceIte]

end tupa

theorem tryUnfoldProjApp_spec (p : Prog) (hp : DefEqMidProg p) (n : Nat) (s₀ : St) (mode vis d e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "try_unfold_proj_app" [mode, vis, d, e]
    ⦃fun r s' => LocEq s' s₀ ∧ tupaK p n mode vis d e (callW p n "head_is_proj" [e] s₀.mem) =
      some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.tupa]
  simp only [callFn, tryUnfoldProjAppL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "head_is_proj",
      callW_spec p n "whnf_core"] <;>
    finish [tupaK_z, tupaK_nz, tupaK2_eq, tupaK2_ne]

theorem decE_beq_eq (x y : Word) (hx : HW x) (hy : HW y) : (decE x == decE y) = decide (x = y) :=
  decI_beq x y hx hy

theorem resW_of (x y : Word) (r : List Word) (hx : HW x) (hy : HW y) (h1 : x = r.headD 0)
    (h2 : y = r.tail.headD 0) : ResW r := ⟨h1 ▸ hx, h2 ▸ hy⟩

/-- **`try_unfold_proj_app` refines `tryUnfoldProjApp`** at the knot. -/
@[refines ConRon.Arena.tryUnfoldProjApp]
theorem tryUnfoldProjApp_refines (p : Prog) (hp : DefEqMidProg p) (n : Nat) (hk : KnotUpTo p n)
    (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d e : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (he : HW e) :
    CoreSpec p (n + 1) "try_unfold_proj_app" [mode, vis, d, e]
      (tryUnfoldProjApp (coreKnot (decMode mode) fe id F) d.toNat (decE e)) decOptR s₀ a₀ dn vis
      fe M eb ResW := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (tryUnfoldProjApp_spec p hp n s₀ mode vis d e)
  subst hs0
  refine ⟨hloc, ?_⟩
  cases hc : callW p n "head_is_proj" [e] s.mem with
  | none => rw [hc] at hW; simp [tupaK] at hW
  | some q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [hc] at hW
  obtain ⟨k, rfl⟩ := callW_succ hc
  have h₁ := CoreSpec.of_callW (headIsProj_refines p hp.leaf k s a₀ dn vis fe M eb e hs.rel he) hc
  refine coreRef_bind h₁ (fun M₁ hS₁ => ?_)
  by_cases h0 : r₁.headD 0 = 0
  · rw [tupaK_z _ _ _ _ _ _ _ _ h0, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hr2, hm⟩ := hW
    rw [decBool_f h0, ← hm]
    exact coreRef_ret hS₁ (by simp only [decOptR, decOpt, ← hr, ↓reduceIte])
      (resW_of _ _ r hw0 hw0 hr hr2)
  rw [tupaK_nz _ _ _ _ _ _ _ _ h0] at hW
  rw [decBool_t h0]
  simp only [↓reduceIte]
  cases hc2 : callW p (k + 1) "whnf_core" [mode, 0, vis, d, e] m₁ with
  | none => rw [hc2] at hW; simp [tupaK2] at hW
  | some q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [hc2] at hW
  have h₂ := CoreSpec.of_callW (s₀ := ⟨m₁, Locals.init []⟩)
    ((hk (k + 1) (Nat.le_refl _)).whnfCore F _ _ dn vis fe M₁ eb mode 0 d e hF hn
      ⟨hS₁, hs.mode4, hs.eb_mode⟩ he) hc2
  have hf0 : ((0 : Word) != 0) = false := rfl
  rw [hf0] at h₂
  refine coreRef_bind h₂ (fun M₂ hS₂ => ?_)
  have hw2 : HW (r₂.headD 0) := h₂.2.2.2
  simp only [decH, decE_beq_eq _ _ hw2 he]
  by_cases h3 : r₂.headD 0 = e
  · rw [tupaK2_eq (h := h3), Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hr2, hm⟩ := hW
    rw [← hm]
    simp only [h3, decide_true, ↓reduceIte]
    exact coreRef_ret hS₂ (by simp only [decOptR, decOpt, ← hr, ↓reduceIte])
      (resW_of _ _ r hw0 hw0 hr hr2)
  · rw [tupaK2_ne (h := h3), Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hr2, hm⟩ := hW
    rw [← hm]
    simp only [h3, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact coreRef_ret hS₂ (by simp only [decOptR, decOpt, ← hr, ← hr2]; rfl)
      (resW_of _ _ r hw1 hw2 hr hr2)

end L.Arena
