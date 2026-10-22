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
  dq : p.lookup "delta_quick" = some deltaQuickL
  off : p.lookup "defeq_offset" = some defeqOffsetL
  lamsInner : p.lookup "defeq_lams_inner" = some defeqLamsInnerL

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

/-! ## Result decodings -/

/-- An `Option Bool` result: `(flag, v)`. -/
def decOB (r : List Word) : Option Bool :=
  if r.headD 0 = 0 then none else some (r.tail.headD 0 != 0)

instance : Inhabited DeltaStepA := ⟨.unknown⟩
instance : Inhabited LazyResA := ⟨.verdict false⟩

/-- A `DeltaStepA` result: `(k, a, b)`, `k` = `0` `.cont a b`, `1` `.eq`, `2` `.diff`, `3`
`.unknown`. -/
def decDS (r : List Word) : DeltaStepA :=
  if r.headD 0 = 0 then .cont (decE (r.tail.headD 0)) (decE (r.tail.tail.headD 0))
  else if r.headD 0 = 1 then .eq
  else if r.headD 0 = 2 then .diff
  else .unknown

/-- A `LazyResA` result: `(k, a, b)`, `k` = `0` `.verdict false`, `1` `.verdict true`, `2`
`.unknown a b`. -/
def decLR (r : List Word) : LazyResA :=
  if r.headD 0 = 0 then .verdict false
  else if r.headD 0 = 1 then .verdict true
  else .unknown (decE (r.tail.headD 0)) (decE (r.tail.tail.headD 0))

/-- Three result words below `2^32`. -/
def Res3 (r : List Word) : Prop := HW (r.headD 0) ∧ HW (r.tail.headD 0) ∧ HW (r.tail.tail.headD 0)

/-- `quick_defeq(mode, vis, d, a, b)` refines `quickDefEq` at the knot (the shape of a slot; a
hypothesis until `quickDefeq_refines`, `DefEqMidQuick.lean`; the depth leaves room for the binder
descents). -/
def QuickDefeqSpec (p : Prog) (n : Nat) : Prop :=
  ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d x y : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe M eb mode →
    HW x → HW y → d.toNat < 2 ^ 63 →
    CoreSpec p n "quick_defeq" [mode, vis, d, x, y]
      (quickDefEq (decMode mode) (coreKnot (decMode mode) fe id F) d.toNat (decE x) (decE y)) decOB
      s₀ a₀ dn vis fe M eb ResW

/-! ## `delta_quick` -/

/-- The model of `delta_quick` past `quick_defeq`'s run. -/
def dqK (a b : Word) (res : Option (List Word × Mem)) : Option (Word × Word × Word × Mem) :=
  match res with
  | none => none
  | some (r, m₁) =>
    if r.headD 0 = 0 then some (0, a, b, m₁)
    else if r.tail.headD 0 ≠ 0 then some (1, 0, 0, m₁) else some (2, 0, 0, m₁)

section dqs
variable (a b : Word) (r : List Word) (m₁ : Mem)
theorem dqK_n (h : r.headD 0 = 0) : dqK a b (some (r, m₁)) = some (0, a, b, m₁) := by
  simp only [dqK, h, ↓reduceIte]
theorem dqK_t (h : r.headD 0 ≠ 0) (h2 : r.tail.headD 0 ≠ 0) :
    dqK a b (some (r, m₁)) = some (1, 0, 0, m₁) := by
  simp only [dqK, h, h2, ↓reduceIte, ne_eq, not_false_eq_true]
theorem dqK_f (h : r.headD 0 ≠ 0) (h2 : r.tail.headD 0 = 0) :
    dqK a b (some (r, m₁)) = some (2, 0, 0, m₁) := by
  simp only [dqK, h, h2, ↓reduceIte, ne_eq, not_true_eq_false]
end dqs

theorem deltaQuick_spec (p : Prog) (hp : DefEqMidProg p) (n : Nat) (s₀ : St) (mode vis d a b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "delta_quick" [mode, vis, d, a, b]
    ⦃fun r s' => LocEq s' s₀ ∧ dqK a b (callW p n "quick_defeq" [mode, vis, d, a, b] s₀.mem) =
      some (r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.dq]
  simp only [callFn, deltaQuickL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "quick_defeq"] <;>
    finish [dqK_n, dqK_t, dqK_f]

theorem res3_of {x y z : Word} {r : List Word} (hx : HW x) (hy : HW y) (hz : HW z)
    (h1 : x = r.headD 0) (h2 : y = r.tail.headD 0) (h3 : z = r.tail.tail.headD 0) : Res3 r :=
  ⟨h1 ▸ hx, h2 ▸ hy, h3 ▸ hz⟩

theorem hw2 : HW 2 := by unfold HW; decide
theorem hw3 : HW 3 := by unfold HW; decide

/-- **`delta_quick` refines `deltaQuick`** at the knot, from `quick_defeq`'s spec. -/
@[refines ConRon.Arena.deltaQuick]
theorem deltaQuick_refines (p : Prog) (hp : DefEqMidProg p) (n : Nat) (hq : QuickDefeqSpec p n)
    (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d a b : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) (hd : d.toNat < 2 ^ 63) :
    CoreSpec p (n + 1) "delta_quick" [mode, vis, d, a, b]
      (deltaQuick (decMode mode) (coreKnot (decMode mode) fe id F) d.toNat (decE a) (decE b)) decDS
      s₀ a₀ dn vis fe M eb Res3 := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (deltaQuick_spec p hp n s₀ mode vis d a b)
  subst hs0
  refine ⟨hloc, ?_⟩
  cases hc : callW p n "quick_defeq" [mode, vis, d, a, b] s.mem with
  | none => rw [hc] at hW; simp [dqK] at hW
  | some q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [hc] at hW
  have h₁ := CoreSpec.of_callW (hq F s a₀ dn vis fe M eb mode d a b hF hn hs ha hb hd) hc
  refine coreRef_bind h₁ (fun M₁ hS₁ => ?_)
  by_cases h0 : r₁.headD 0 = 0
  · rw [dqK_n (h := h0), Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hr2, hr3, hm⟩ := hW
    have hd : decOB r₁ = none := by simp only [decOB, h0, ↓reduceIte]
    rw [hd, ← hm]
    exact coreRef_ret hS₁ (by simp only [decDS, ← hr, ← hr2, ← hr3, ↓reduceIte])
      (res3_of hw0 ha hb hr hr2 hr3)
  by_cases h2 : r₁.tail.headD 0 ≠ 0
  · rw [dqK_t (h := h0) (h2 := h2), Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq,
      Prod.mk.injEq] at hW
    obtain ⟨hr, hr2, hr3, hm⟩ := hW
    have hd : decOB r₁ = some true := by
      simp only [decOB, h0, ↓reduceIte, Option.some.injEq]; exact decBool_t (r := r₁.tail) h2
    rw [hd, ← hm]
    exact coreRef_ret hS₁ (by simp only [decDS, ← hr]; rfl) (res3_of hw1 hw0 hw0 hr hr2 hr3)
  · have h2' : r₁.tail.headD 0 = 0 := by simpa using h2
    rw [dqK_f (h := h0) (h2 := h2'), Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq,
      Prod.mk.injEq] at hW
    obtain ⟨hr, hr2, hr3, hm⟩ := hW
    have hd : decOB r₁ = some false := by
      simp only [decOB, h0, ↓reduceIte, Option.some.injEq]; exact decBool_f (r := r₁.tail) h2'
    rw [hd, ← hm]
    exact coreRef_ret hS₁ (by simp only [decDS, ← hr]; rfl) (res3_of hw2 hw0 hw0 hr hr2 hr3)

/-! ## `defeq_offset` -/

/-- `nat_pred(e)` refines `natPred?` with both result words valid handles (`ResW`).
`natPred_refines` (`DefEqLeaves2.lean`) proves the `ResH` form only: the interned predecessor
literal's word is not known to be below `2^32` there (lane `store`'s `intern_lit` spec does not
say it). A hypothesis here. -/
def NatPredW (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb e : Word), CoreS dn s₀.mem a₀ vis fe M eb → HW e →
    CoreSpec p n "nat_pred" [e] (natPred? (decE e)) decOptR s₀ a₀ dn vis fe M eb ResW

section offK
variable (p : Prog) (n : Nat) (mode vis d a b : Word)

/-- After `defeq`. -/
def offK5 (res : Option (List Word × Mem)) : Option (Word × Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => some (1, r.headD 0, m)

/-- After `nat_pred(b)`. -/
def offK4 (x : Word) (res : Option (List Word × Mem)) : Option (Word × Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if r.headD 0 = 0 then some (0, 0, m)
    else offK5 (callW p n "defeq" [mode, vis, d, x, r.tail.headD 0] m)

/-- After `nat_pred(a)`. -/
def offK3 (res : Option (List Word × Mem)) : Option (Word × Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if r.headD 0 = 0 then some (0, 0, m)
    else offK4 p n mode vis d (r.tail.headD 0) (callW p n "nat_pred" [b] m)

/-- After `is_nat_zero(b)`. -/
def offK2 (za : Word) (res : Option (List Word × Mem)) : Option (Word × Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if za ≠ 0 ∧ r.headD 0 ≠ 0 then some (1, 1, m)
    else if a >>> 28 = 8 ∧ b >>> 28 = 8 then some (0, 0, m)
    else offK3 p n mode vis d b (callW p n "nat_pred" [a] m)

/-- The model of `defeq_offset` past `is_nat_zero(a)`. -/
def offK1 (res : Option (List Word × Mem)) : Option (Word × Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => offK2 p n mode vis d a b (r.headD 0) (callW p n "is_nat_zero" [b] m)

variable (r : List Word) (m : Mem) (x za : Word)

theorem offK5_s : offK5 (some (r, m)) = some (1, r.headD 0, m) := rfl
theorem offK4_z (h : r.headD 0 = 0) : offK4 p n mode vis d x (some (r, m)) = some (0, 0, m) := by
  simp only [offK4, h, ↓reduceIte]
theorem offK4_nz (h : r.headD 0 ≠ 0) : offK4 p n mode vis d x (some (r, m)) =
    offK5 (callW p n "defeq" [mode, vis, d, x, r.tail.headD 0] m) := by
  simp only [offK4, h, ↓reduceIte]
theorem offK3_z (h : r.headD 0 = 0) : offK3 p n mode vis d b (some (r, m)) = some (0, 0, m) := by
  simp only [offK3, h, ↓reduceIte]
theorem offK3_nz (h : r.headD 0 ≠ 0) : offK3 p n mode vis d b (some (r, m)) =
    offK4 p n mode vis d (r.tail.headD 0) (callW p n "nat_pred" [b] m) := by
  simp only [offK3, h, ↓reduceIte]
theorem offK2_zz (h : za ≠ 0 ∧ r.headD 0 ≠ 0) :
    offK2 p n mode vis d a b za (some (r, m)) = some (1, 1, m) := by
  simp only [offK2, h, ↓reduceIte, ne_eq, not_false_eq_true, and_self]
theorem offK2_ll (h : ¬ (za ≠ 0 ∧ r.headD 0 ≠ 0)) (h2 : a >>> 28 = 8 ∧ b >>> 28 = 8) :
    offK2 p n mode vis d a b za (some (r, m)) = some (0, 0, m) := by
  simp only [offK2, h, h2, ↓reduceIte, and_self]
theorem offK2_go (h : ¬ (za ≠ 0 ∧ r.headD 0 ≠ 0)) (h2 : ¬ (a >>> 28 = 8 ∧ b >>> 28 = 8)) :
    offK2 p n mode vis d a b za (some (r, m)) = offK3 p n mode vis d b (callW p n "nat_pred" [a] m) := by
  simp only [offK2, h, h2, ↓reduceIte]
theorem offK1_s : offK1 p n mode vis d a b (some (r, m)) =
    offK2 p n mode vis d a b (r.headD 0) (callW p n "is_nat_zero" [b] m) := rfl

end offK

theorem defeqOffset_spec (p : Prog) (hp : DefEqMidProg p) (n : Nat) (s₀ : St) (mode vis d a b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "defeq_offset" [mode, vis, d, a, b]
    ⦃fun r s' => LocEq s' s₀ ∧ offK1 p n mode vis d a b (callW p n "is_nat_zero" [a] s₀.mem) =
      some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.off]
  simp only [callFn, defeqOffsetL]
  -- Five calls in a row: the `LocEq` chain to the last call's arguments is deeper than the
  -- default generation bound (`gen` is depth, not search).
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "is_nat_zero",
      callW_spec p n "nat_pred", callW_spec p n "defeq"] <;>
    finish (gen := 30) [offK1_s, offK2_zz, offK2_ll, offK2_go, offK3_z, offK3_nz, offK4_z, offK4_nz, offK5_s]

theorem decOptR_some {r : List Word} (h : r.headD 0 ≠ 0) : decOptR r = some (decE (r.tail.headD 0)) := by
  simp only [decOptR, decOpt, h, ↓reduceIte]

theorem decOptR_none {r : List Word} (h : r.headD 0 = 0) : decOptR r = none := by
  simp only [decOptR, decOpt, h, ↓reduceIte]

theorem resW_00 {r : List Word} {m m' : Mem} (h : some ((0 : Word), (0 : Word), m) = some (r.headD 0, r.tail.headD 0, m')) :
    ResW r ∧ decOB r = none ∧ m' = m := by
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨⟨h1 ▸ hw0, h2 ▸ hw0⟩, by simp only [decOB, ← h1, ↓reduceIte], h3.symm⟩

/-- **`defeq_offset` refines `defeqOffset`** at the knot. -/
@[refines ConRon.Arena.defeqOffset]
theorem defeqOffset_refines (p : Prog) (hp : DefEqMidProg p) (hnp : NatPredW p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) :
    CoreSpec p (n + 1) "defeq_offset" [mode, vis, d, a, b]
      (defeqOffset (coreKnot (decMode mode) fe id F) d.toNat (decE a) (decE b)) decOB s₀ a₀ dn vis
      fe M eb ResW := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (defeqOffset_spec p hp n s₀ mode vis d a b)
  subst hs0
  refine ⟨hloc, ?_⟩
  unfold defeqOffset
  cases hc1 : callW p n "is_nat_zero" [a] s.mem with
  | none => rw [hc1] at hW; cases hW
  | some q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [hc1, offK1_s] at hW
  obtain ⟨k, rfl⟩ := callW_succ hc1
  have h₁ := CoreSpec.of_callW (isNatZero_refines p hp.leaf k s a₀ dn vis fe M eb a hs.rel ha) hc1
  refine coreRef_bind h₁ (fun M₁ hS₁ => ?_)
  cases hc2 : callW p (k + 1) "is_nat_zero" [b] m₁ with
  | none => rw [hc2] at hW; cases hW
  | some q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [hc2] at hW
  have h₂ := CoreSpec.of_callW (s₀ := ⟨m₁, Locals.init []⟩)
    (isNatZero_refines p hp.leaf k _ _ dn vis fe M₁ eb b hS₁ hb) hc2
  refine coreRef_bind h₂ (fun M₂ hS₂ => ?_)
  by_cases hzz : r₁.headD 0 ≠ 0 ∧ r₂.headD 0 ≠ 0
  · rw [offK2_zz (h := hzz), Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hW
    obtain ⟨h1, h2, hm⟩ := hW
    rw [decBool_t hzz.1, decBool_t hzz.2, ← hm]
    exact coreRef_ret hS₂ (by rw [decOB, ← h1, ← h2]; rfl) ⟨h1 ▸ hw1, h2 ▸ hw1⟩
  have hzb : (decBool r₁ && decBool r₂) = false := by
    by_cases h : r₁.headD 0 = 0
    · rw [decBool_f h]; rfl
    · have h' : r₂.headD 0 = 0 := Classical.byContradiction fun h' => hzz ⟨h, h'⟩
      rw [decBool_f h']; simp
  simp only [hzb, Bool.false_eq_true, ↓reduceIte, tag_beq_lit a ha, tag_beq_lit b hb,
    Bool.and_eq_true, decide_eq_true_eq]
  by_cases hll : a >>> 28 = 8 ∧ b >>> 28 = 8
  · rw [offK2_ll (h := hzz) (h2 := hll)] at hW
    obtain ⟨hw, hd, hm⟩ := resW_00 hW
    simp only [hll, and_self, ↓reduceIte, hm]
    exact coreRef_ret hS₂ hd.symm hw
  simp only [hll, ↓reduceIte]
  rw [offK2_go (h := hzz) (h2 := hll)] at hW
  cases hc3 : callW p (k + 1) "nat_pred" [a] m₂ with
  | none => rw [hc3] at hW; cases hW
  | some q =>
  obtain ⟨r₃, m₃⟩ := q
  rw [hc3] at hW
  have h₃ := CoreSpec.of_callW (s₀ := ⟨m₂, Locals.init []⟩)
    (hnp (k + 1) _ _ dn vis fe M₂ eb a hS₂ ha) hc3
  refine coreRef_bind h₃ (fun M₃ hS₃ => ?_)
  by_cases h3 : r₃.headD 0 = 0
  · rw [offK3_z (h := h3)] at hW
    obtain ⟨hw, hd, hm⟩ := resW_00 hW
    rw [decOptR_none h3, hm]
    exact coreRef_ret hS₃ hd.symm hw
  rw [offK3_nz (h := h3)] at hW
  rw [decOptR_some h3]
  cases hc4 : callW p (k + 1) "nat_pred" [b] m₃ with
  | none => rw [hc4] at hW; cases hW
  | some q =>
  obtain ⟨r₄, m₄⟩ := q
  rw [hc4] at hW
  have h₄ := CoreSpec.of_callW (s₀ := ⟨m₃, Locals.init []⟩)
    (hnp (k + 1) _ _ dn vis fe M₃ eb b hS₃ hb) hc4
  refine coreRef_bind h₄ (fun M₄ hS₄ => ?_)
  by_cases h4 : r₄.headD 0 = 0
  · rw [offK4_z (h := h4)] at hW
    obtain ⟨hw, hd, hm⟩ := resW_00 hW
    rw [decOptR_none h4, hm]
    exact coreRef_ret hS₄ hd.symm hw
  rw [offK4_nz (h := h4)] at hW
  rw [decOptR_some h4]
  cases hc5 : callW p (k + 1) "defeq" [mode, vis, d, r₃.tail.headD 0, r₄.tail.headD 0] m₄ with
  | none => rw [hc5] at hW; cases hW
  | some q =>
  obtain ⟨r₅, m₅⟩ := q
  rw [hc5, offK5_s, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq] at hW
  obtain ⟨h1, h2, hm⟩ := hW
  have h₅ := CoreSpec.of_callW (s₀ := ⟨m₄, Locals.init []⟩)
    ((hk (k + 1) (Nat.le_refl _)).defeq F _ _ dn vis fe M₄ eb mode d _ _ hF hn
      ⟨hS₄, hs.mode4, hs.eb_mode⟩ h₃.2.2.2.2 h₄.2.2.2.2) hc5
  refine coreRef_bind h₅ (fun M₅ hS₅ => ?_)
  rw [← hm]
  refine coreRef_ret hS₅ ?_ ⟨h1 ▸ hw1, h2 ▸ h₅.2.2.2⟩
  simp only [decOB, decBool, ← h1, ← h2]; rfl

/-! ## `defeq_lams_inner` -/

section liK
variable (p : Prog) (n : Nat) (mode vis d b₁ b₂ : Word)

/-- After `infer(b₂)`. -/
def liK3 (t₁ : Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => call1W p n "defeq" [mode, vis, d + 1, t₁, r.headD 0] m

/-- After `infer(b₁)`. -/
def liK2 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => liK3 p n mode vis d (r.headD 0) (callW p n "infer" [mode, vis, d + 1, b₂] m)

/-- The model of `defeq_lams_inner` past the bodies' `defeq`. -/
def liK1 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if r.headD 0 = 0 then some (0, m)
    else if mode &&& 1 = 0 then liK2 p n mode vis d b₂ (callW p n "infer" [mode, vis, d + 1, b₁] m)
    else some (1, m)

variable (r : List Word) (m : Mem) (t₁ : Word)
theorem liK3_s : liK3 p n mode vis d t₁ (some (r, m)) =
    call1W p n "defeq" [mode, vis, d + 1, t₁, r.headD 0] m := rfl
theorem liK2_s : liK2 p n mode vis d b₂ (some (r, m)) =
    liK3 p n mode vis d (r.headD 0) (callW p n "infer" [mode, vis, d + 1, b₂] m) := rfl
theorem liK1_z (h : r.headD 0 = 0) : liK1 p n mode vis d b₁ b₂ (some (r, m)) = some (0, m) := by
  simp only [liK1, h, ↓reduceIte]
theorem liK1_v (h : r.headD 0 ≠ 0) (hv : mode &&& 1 = 0) : liK1 p n mode vis d b₁ b₂ (some (r, m)) =
    liK2 p n mode vis d b₂ (callW p n "infer" [mode, vis, d + 1, b₁] m) := by
  simp only [liK1, h, hv, ↓reduceIte]
theorem liK1_t (h : r.headD 0 ≠ 0) (hv : mode &&& 1 ≠ 0) :
    liK1 p n mode vis d b₁ b₂ (some (r, m)) = some (1, m) := by
  simp only [liK1, h, hv, ↓reduceIte]

end liK

theorem defeqLamsInner_spec (p : Prog) (hp : DefEqMidProg p) (n : Nat) (s₀ : St) (mode vis d b₁ b₂ : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "defeq_lams_inner" [mode, vis, d, b₁, b₂]
    ⦃fun r s' => LocEq s' s₀ ∧ liK1 p n mode vis d b₁ b₂
      (callW p n "defeq" [mode, vis, d + 1, b₁, b₂] s₀.mem) = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.lamsInner]
  simp only [callFn, defeqLamsInnerL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "defeq",
      callW_spec p n "infer"] <;>
    finish [liK1_z, liK1_v, liK1_t, liK2_s, liK3_s, call1W_some]

theorem mode_verified (mode : Word) (h : mode < 4) :
    (decMode mode).verifiedChecks = decide (mode &&& 1 = 0) := by
  rcases mode_cases mode h with rfl | rfl | rfl | rfl <;> decide

/-- **`defeq_lams_inner` refines `defeqLamsInner`** at the knot (the depth `d + 1` does not wrap). -/
@[refines ConRon.Arena.defeqLamsInner]
theorem defeqLamsInner_refines (p : Prog) (hp : DefEqMidProg p) (n : Nat) (hk : KnotUpTo p n)
    (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d b₁ b₂ : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hd : d.toNat + 1 < 2 ^ 64) (h₁ : HW b₁) (h₂ : HW b₂) :
    CoreSpec p (n + 1) "defeq_lams_inner" [mode, vis, d, b₁, b₂]
      (defeqLamsInner (decMode mode) (coreKnot (decMode mode) fe id F) d.toNat (decE b₁) (decE b₂))
      decBool s₀ a₀ dn vis fe M eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (defeqLamsInner_spec p hp n s₀ mode vis d b₁ b₂)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hd1 : (d + 1).toNat = d.toNat + 1 := by
    rw [UInt64.toNat_add]; simp only [UInt64.toNat_one]; omega
  have K := hk n (Nat.le_refl _)
  unfold defeqLamsInner
  cases hc1 : callW p n "defeq" [mode, vis, d + 1, b₁, b₂] s.mem with
  | none => rw [hc1] at hW; cases hW
  | some q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [hc1] at hW
  have e₁ := CoreSpec.of_callW (K.defeq F s a₀ dn vis fe M eb mode (d + 1) b₁ b₂ hF hn hs h₁ h₂) hc1
  rw [hd1] at e₁
  refine coreRef_bind e₁ (fun M₁ hS₁ => ?_)
  by_cases h0 : r₁.headD 0 = 0
  · rw [liK1_z (h := h0), Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    rw [decBool_f h0, ← hm]
    exact coreRef_ret hS₁ (by rw [decBool, ← hr]; rfl) (by unfold ResH; rw [← hr]; exact hw0)
  rw [decBool_t h0]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, mode_verified mode hs.mode4,
    decide_eq_true_eq]
  by_cases hv : mode &&& 1 = 0
  · rw [liK1_v (h := h0) (hv := hv)] at hW
    simp only [hv, ↓reduceIte]
    cases hc2 : callW p n "infer" [mode, vis, d + 1, b₁] m₁ with
    | none => rw [hc2] at hW; cases hW
    | some q =>
    obtain ⟨r₂, m₂⟩ := q
    rw [hc2, liK2_s] at hW
    have e₂ := CoreSpec.of_callW (s₀ := ⟨m₁, Locals.init []⟩)
      (K.infer F _ _ dn vis fe M₁ eb mode (d + 1) b₁ hF hn ⟨hS₁, hs.mode4, hs.eb_mode⟩ h₁) hc2
    rw [hd1] at e₂
    refine coreRef_bind e₂ (fun M₂ hS₂ => ?_)
    cases hc3 : callW p n "infer" [mode, vis, d + 1, b₂] m₂ with
    | none => rw [hc3] at hW; cases hW
    | some q =>
    obtain ⟨r₃, m₃⟩ := q
    rw [hc3, liK3_s] at hW
    have e₃ := CoreSpec.of_callW (s₀ := ⟨m₂, Locals.init []⟩)
      (K.infer F _ _ dn vis fe M₂ eb mode (d + 1) b₂ hF hn ⟨hS₂, hs.mode4, hs.eb_mode⟩ h₂) hc3
    rw [hd1] at e₃
    refine coreRef_bind e₃ (fun M₃ hS₃ => ?_)
    have e₄ := CoreSpec.of_call1W (s₀ := ⟨m₃, Locals.init []⟩)
      (K.defeq F _ _ dn vis fe M₃ eb mode (d + 1) _ _ hF hn ⟨hS₃, hs.mode4, hs.eb_mode⟩
        e₂.2.2.2 e₃.2.2.2) (fun r r' h => by simp only [decBool, h]) hW
    rw [hd1] at e₄
    exact e₄
  · rw [liK1_t (h := h0) (hv := hv), Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    simp only [hv, ↓reduceIte, ← hm]
    exact coreRef_ret hS₁ (by rw [decBool, ← hr]; rfl) (by unfold ResH; rw [← hr]; exact hw1)

end L.Arena
