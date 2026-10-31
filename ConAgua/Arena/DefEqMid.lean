import ConAgua.Arena.DefEqLeaves2
import ConAgua.Arena.InferLeaves
import ConAgua.Arena.DefEqLeaves
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.WhnfCoreProj
import ConAgua.Verdict.WhnfModels7E

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
  rw [StateT.run_bind, AM.run_of_ok _ _ h₁.run, h₁.res]; rfl

/-- **A pure result** under the relation. -/
theorem coreRef_ret {α : Type} [Inhabited α] {a : AState} {dec : List Word → α}
    {dn : NIdx → Option ConLeche.Name} {m : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps}
    {eb : Word} {r : List Word} {v : α} {ok : List Word → Prop} (hS : CoreS dn m a vis fe M eb)
    (hv : v = dec r) (hr : ok r) : CoreRef (pure v) a dec dn m vis fe M eb r m ok :=
  ⟨trivial, ⟨M, hS, KeptAll.refl _ _, StackKept.refl _⟩, hv, hr⟩

/-- **A refinement from the model spec**: the L spec says the model `P` holds of the run; the
refinement follows from `P` at the final state. -/
theorem CoreSpec.of_model {α : Type} [Inhabited α] {p : Prog} {n : Nat} {f : FnName}
    {args : List Word} {T : AM α} {dec : List Word → α} {s₀ : St} {a₀ : AState}
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word}
    {ok : List Word → Prop} {P : List Word → St → Prop}
    (hspec : ⦃fun s => s = s₀⦄ invoke p (exec p n) f args ⦃fun r s' => LocEq s' s₀ ∧ P r s'; ⊤⦄)
    (h : ∀ r s', P r s' → CoreRef T a₀ dec dn s₀.mem vis fe M eb r s'.mem ok) :
    CoreSpec p n f args T dec s₀ a₀ dn vis fe M eb ok :=
  L.M.triple_of_run fun _ _ _ hs hrun => by
    obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs hrun hspec
    exact ⟨hloc, h _ _ hW⟩

/-- **One callee of a continuation model, then the rest**: the model `K` past the callee's run
(`K none = none`), the callee's spec, the rest under the relation after it. -/
theorem coreRef_callK {α β γ : Type} [Inhabited α] [Inhabited β]
    {K : Option (List Word × Mem) → Option γ} {v : γ} {p : Prog} {n : Nat} {f : FnName}
    {args : List Word} {m m' : Mem} {T₁ : AM α} {g : α → AM β} {a₀ : AState}
    {dec₁ : List Word → α} {dec : List Word → β} {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} {r : List Word} {ok₁ ok : List Word → Prop}
    (hW : K (callW p n f args m) = some v) (hn : K none = none)
    (hspec : CoreSpec p n f args T₁ dec₁ ⟨m, Locals.init []⟩ a₀ dn vis fe M eb ok₁)
    (h : ∀ r₁ m₁, K (some (r₁, m₁)) = some v → CoreRef T₁ a₀ dec₁ dn m vis fe M eb r₁ m₁ ok₁ →
      ∀ M₁, CoreS dn m₁ (AM.st T₁ a₀) vis fe M₁ eb →
        CoreRef (g (dec₁ r₁)) (AM.st T₁ a₀) dec dn m₁ vis fe M₁ eb r m' ok) :
    CoreRef (T₁ >>= g) a₀ dec dn m vis fe M eb r m' ok := by
  cases hc : callW p n f args m with
  | none => rw [hc, hn] at hW; cases hW
  | some q =>
    obtain ⟨r₁, m₁⟩ := q
    rw [hc] at hW
    have e := CoreSpec.of_callW hspec hc
    exact coreRef_bind e (h r₁ m₁ hW e)

/-- **The last callee of a continuation model**: its result is the model's, re-decoded. -/
theorem coreRef_callLast {α γ : Type} [Inhabited α]
    {K : Option (List Word × Mem) → Option γ} {v : γ} {p : Prog} {n : Nat} {f : FnName}
    {args : List Word} {m m' : Mem} {T : AM α} {a₀ : AState} {dec₁ dec : List Word → α}
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word}
    {r : List Word} {ok₁ ok : List Word → Prop}
    (hW : K (callW p n f args m) = some v) (hn : K none = none)
    (hspec : CoreSpec p n f args T dec₁ ⟨m, Locals.init []⟩ a₀ dn vis fe M eb ok₁)
    (h : ∀ r₁ m₁, K (some (r₁, m₁)) = some v → m₁ = m' ∧ dec₁ r₁ = dec r ∧ (ok₁ r₁ → ok r)) :
    CoreRef T a₀ dec dn m vis fe M eb r m' ok := by
  cases hc : callW p n f args m with
  | none => rw [hc, hn] at hW; cases hW
  | some q =>
    obtain ⟨r₁, m₁⟩ := q
    rw [hc] at hW
    have e := CoreSpec.of_callW hspec hc
    obtain ⟨rfl, hd, hok⟩ := h r₁ m₁ hW
    exact ⟨e.run, e.after, e.res.trans hd, hok e.resOk⟩

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

/-- **`defeq_no_fvars` is its model `noFvW`** (generated). -/
l_model defeqNoFvars_spec (p : Prog) (hp : DefEqMidProg p)
  fns [hp.noFvars ↦ noFvW]
  specs [callW_spec p n "has_fvar"]
  grind [arena_grind]

/-- **`defeq_no_fvars` refines `defeqNoFvars`**, from `has_fvar`'s spec. -/
@[refines ConRon.Arena.defeqNoFvars]
theorem defeqNoFvars_refines (p : Prog) (hp : DefEqMidProg p) (hf : HasFvarOK p) (n : Nat)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb a b : Word) (hS : CoreS dn s₀.mem a₀ vis fe M eb) (ha : HW a) (hb : HW b) :
    CoreSpec p (n + 1) "defeq_no_fvars" [a, b] (defeqNoFvars (decE a) (decE b)) decBool s₀ a₀ dn
      vis fe M eb := by
  refine CoreSpec.of_model (defeqNoFvars_spec p hp (n + 1) s₀ a b) fun r s hW => ?_
  rw [noFvW.arm1] at hW
  refine coreRef_callK hW rfl (hf n _ a₀ dn vis fe M eb a hS ha) fun r₁ m₁ hW _ M₁ hS₁ => ?_
  by_cases h0 : r₁.headD 0 ≠ 0
  · rw [noFvW.k_has_fvar.arm1 (hc1 := h0), Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, rfl⟩ := hW
    rw [decBool_t h0]
    exact coreRef_ret hS₁ (by rw [decBool, ← hr]; rfl) (by unfold ResH; rw [← hr]; exact hw0)
  have h0' : r₁.headD 0 = 0 := by simpa using h0
  rw [noFvW.k_has_fvar.arm2 (hc1 := h0')] at hW
  rw [decBool_f h0']
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine coreRef_callK hW rfl (hf n _ _ dn vis fe M₁ eb b hS₁ hb) fun r₂ m₂ hW _ M₂ hS₂ => ?_
  rw [noFvW.k_has_fvar_2.arm1, Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, rfl⟩ := hW
  refine coreRef_ret hS₂ ?_ (resH_of hw1 hw0 hr)
  simp only [decBool, ← hr]
  generalize r₂.headD 0 = w
  by_cases hz : w = 0 <;> simp [hz]

/-! ## `lazy_fold_ok` -/

/-- **`lazy_fold_ok` is its model `lazyFoldOkW`** (generated). -/
l_model lazyFoldOk_spec (p : Prog) (hp : DefEqMidProg p)
  fns [hp.foldOk ↦ lazyFoldOkW]
  specs [callW_spec p n "defeq_no_fvars"]
  grind [arena_grind]

theorem mode_eager_bit (mode : Word) (h : mode < 4) :
    (decMode mode).eager = decide ((mode >>> 1) &&& 1 ≠ 0) := by
  rcases mode_cases mode h with rfl | rfl | rfl | rfl <;> decide

/-- **`lazy_fold_ok` refines `lazyFoldOk`**, from `has_fvar`'s spec. -/
@[refines ConRon.Arena.lazyFoldOk]
theorem lazyFoldOk_refines (p : Prog) (hp : DefEqMidProg p) (hf : HasFvarOK p) (n : Nat)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode a b : Word) (hS : CoreS dn s₀.mem a₀ vis fe M eb) (hm : mode < 4)
    (ha : HW a) (hb : HW b) :
    CoreSpec p (n + 1) "lazy_fold_ok" [mode, a, b] (lazyFoldOk (decMode mode) (decE a) (decE b))
      decBool s₀ a₀ dn vis fe M eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (lazyFoldOk_spec p hp (n + 1) s₀ mode a b)
  subst hs0
  refine ⟨hloc, ?_⟩
  have he := mode_eager_bit mode hm
  by_cases h0 : (mode >>> 1) &&& 1 ≠ 0
  · rw [lazyFoldOkW.arm1 (hc1 := h0), Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm'⟩ := hW
    rw [← hm']
    simp only [lazyFoldOk, he, h0, ne_eq, not_false_eq_true, decide_true, ↓reduceIte]
    exact coreRef_ret hS (by rw [decBool, ← hr]; rfl) (by unfold ResH; rw [← hr]; exact hw1)
  have h0' : (mode >>> 1) &&& 1 = 0 := by simpa using h0
  rw [lazyFoldOkW.arm2 (hc1 := h0')] at hW
  change call1W p _ _ _ _ = _ at hW
  simp only [lazyFoldOk, he, h0', ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
    ↓reduceIte]
  obtain ⟨n, rfl⟩ := call1W_succ hW
  exact CoreSpec.of_call1W (s₀ := ⟨s.mem, Locals.init []⟩)
    (defeqNoFvars_refines p hp hf n _ a₀ dn vis fe M eb a b hS ha hb)
    (fun r r' h => by simp only [decBool, h]) hW

/-! ## `bool_true_shortcut` -/

/-- **`bool_true_shortcut` refines `boolTrueShortcut`, both outcomes**: the errors are the `whnf`
slot's. -/
theorem bts_ref (p : Prog) (hp : DefEqMidProg p) (n : Nat) (hk : KnotUpTo p n)
    (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d a : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) :
    RefE (KnotUpToE p n) (btsE p (n + 1) s₀.mem mode vis d a)
      (boolTrueShortcut (coreKnot (decMode mode) fe id F) d.toNat (decE a)) a₀
      (CorePost decBool dn s₀.mem vis fe M eb ResH) := by
  simp only [btsE]
  unfold boolTrueShortcut
  cases n with
  | zero => exact RefE.callE_zero fun _ => btsE.k_whnf.none ..
  | succ k =>
  refine RefE.bind_callE (fun _ => btsE.k_whnf.none ..) ((hk _ (Nat.le_refl _)).whnf F s₀ a₀ dn vis fe M eb
    mode d a hF hn hs ha) (fun (hG : KnotUpToE p (k + 1)) => (hG _ (Nat.le_refl _)).whnf F s₀ a₀ dn vis fe
      M eb mode d a hF hn hs ha) fun r1 m1 _ h₁ => RefE.after_core (w := id) h₁ fun M₁ hS₁ _ => ?_
  simp only [btsE.k_whnf]
  rw [← bind_pure (isBoolTrue _)]
  refine RefE.bind_callW (fun _ => btsE.k_is_bool_true.none ..) (isBoolTrue_refines p hp.leaf k
    ⟨m1, Locals.init []⟩ _ dn vis fe M₁ eb _ hS₁ h₁.resOk) fun _ _ _ h₂ => ?_
  exact RefE.ret rfl ⟨h₂.after, rfl, h₂.resOk⟩

/-- **`bool_true_shortcut` refines `boolTrueShortcut`** at the knot (`bts_ref`'s ok half). -/
@[refines ConRon.Arena.boolTrueShortcut]
theorem boolTrueShortcut_refines (p : Prog) (hp : DefEqMidProg p) (n : Nat) (hk : KnotUpTo p n)
    (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d a : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) :
    CoreSpec p (n + 1) "bool_true_shortcut" [mode, vis, d, a]
      (boolTrueShortcut (coreKnot (decMode mode) fe id F) d.toNat (decE a)) decBool s₀ a₀ dn vis
      fe M eb :=
  RefE.coreSpec (btsE_spec p hp.bts (n + 1) s₀ mode vis d a)
    (bts_ref p hp n hk F s₀ a₀ dn vis fe M eb mode d a hF hn hs ha)

/-! ## `try_unfold_proj_app` -/

theorem decE_beq_eq (x y : Word) (hx : HW x) (hy : HW y) : (decE x == decE y) = decide (x = y) :=
  decI_beq x y hx hy

theorem resW_of (x y : Word) (r : List Word) (hx : HW x) (hy : HW y) (h1 : x = r.headD 0)
    (h2 : y = r.tail.headD 0) : ResW r := ⟨h1 ▸ hx, h2 ▸ hy⟩

/-- **`try_unfold_proj_app` refines `tryUnfoldProjApp`, both outcomes**: the errors are the
`whnf_core` slot's. -/
theorem tupa_ref (p : Prog) (hp : DefEqMidProg p) (n : Nat) (hk : KnotUpTo p n)
    (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d e : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (he : HW e) :
    RefE (KnotUpToE p n) (tupaE p (n + 1) s₀.mem mode vis d e)
      (tryUnfoldProjApp (coreKnot (decMode mode) fe id F) d.toNat (decE e)) a₀
      (CorePost decOptR dn s₀.mem vis fe M eb ResW) := by
  simp only [tupaE]
  unfold tryUnfoldProjApp
  cases n with
  | zero => rw [callW_zero, liftE_none, tupaE.k_head_is_proj.none]; exact RefE.of_cls0 (by simp)
  | succ k =>
  refine RefE.bind_callW (fun _ => tupaE.k_head_is_proj.none ..) (headIsProj_refines p hp.leaf k s₀ a₀ dn
    vis fe M eb e hs.rel he) fun r₁ m₁ _ h₁ => RefE.after_core (w := id) h₁ fun M₁ hS₁ _ => ?_
  by_cases h0 : r₁.headD 0 = 0
  · rw [tupaE.k_head_is_proj.arm1 _ _ _ _ _ _ _ _ h0, decBool_f h0]
    exact RefE.ret rfl (CorePost.ret hS₁ (by simp only [decOptR, decOpt]; rfl) (resW_of _ _ _ hw0 hw0 rfl rfl))
  rw [tupaE.k_head_is_proj.arm2 _ _ _ _ _ _ _ _ h0, decBool_t h0]
  simp only [↓reduceIte]
  refine RefE.bind_callE (fun _ => tupaE.k_whnf_core.none ..) ((hk (k + 1) (Nat.le_refl _)).whnfCore F
    ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode 0 d e hF hn ⟨hS₁, hs.mode4, hs.eb_mode⟩ he)
    (fun (hG : KnotUpToE p (k + 1)) => (hG (k + 1) (Nat.le_refl _)).whnfCore F ⟨m₁, Locals.init []⟩ _ dn
      vis fe M₁ eb mode 0 d e hF hn ⟨hS₁, hs.mode4, hs.eb_mode⟩ he)
    fun r₂ m₂ _ h₂ => RefE.after_core (w := id) h₂ fun M₂ hS₂ _ => ?_
  have hw2 : HW (r₂.headD 0) := h₂.resOk
  simp only [decH, decE_beq_eq _ _ hw2 he]
  by_cases h3 : r₂.headD 0 = e
  · rw [tupaE.k_whnf_core.arm1 _ _ _ _ h3]
    simp only [h3, decide_true, ↓reduceIte]
    exact RefE.ret rfl (CorePost.ret hS₂ (by simp only [decOptR, decOpt]; rfl) (resW_of _ _ _ hw0 hw0 rfl rfl))
  · rw [tupaE.k_whnf_core.arm2 _ _ _ _ h3]
    simp only [h3, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact RefE.ret rfl (CorePost.ret hS₂ (by simp only [decOptR, decOpt]; rfl) (resW_of _ _ _ hw1 hw2 rfl rfl))

/-- **`try_unfold_proj_app` refines `tryUnfoldProjApp`** at the knot (`tupa_ref`'s ok half). -/
@[refines ConRon.Arena.tryUnfoldProjApp]
theorem tryUnfoldProjApp_refines (p : Prog) (hp : DefEqMidProg p) (n : Nat) (hk : KnotUpTo p n)
    (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d e : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (he : HW e) :
    CoreSpec p (n + 1) "try_unfold_proj_app" [mode, vis, d, e]
      (tryUnfoldProjApp (coreKnot (decMode mode) fe id F) d.toNat (decE e)) decOptR s₀ a₀ dn vis
      fe M eb ResW :=
  RefE.coreSpec (tupaE_spec p hp.tupa (n + 1) s₀ mode vis d e)
    (tupa_ref p hp n hk F s₀ a₀ dn vis fe M eb mode d e hF hn hs he)

/-! ## Result decodings -/

/-- An `Option Bool` result: `(flag, v)`. -/
def decOB (r : List Word) : Option Bool :=
  if r.headD 0 = 0 then none else some (r.tail.headD 0 != 0)


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

/-- `quick_defeq`'s error claim at fuel `n` (the shape of `QuickDefeqSpec`). -/
def QuickDefeqWE (p : Prog) (n : Nat) : Prop :=
  ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d x y : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe M eb mode →
    HW x → HW y → d.toNat < 2 ^ 63 →
    CoreSpecE p n "quick_defeq" [mode, vis, d, x, y]
      (quickDefEq (decMode mode) (coreKnot (decMode mode) fe id F) d.toNat (decE x) (decE y)) s₀ a₀

/-- **The knot's slots up to fuel `n` and the verdict closure**: what the errors of the `defeq`
family's pieces that call the slots and lifted callees claim from (`peel_*`, `lams_*`,
`quick_*`). -/
structure KnotNvG (p : Prog) (n : Nat) : Prop where
  knot : KnotUpToE p n
  nv : closedNV p L.Checker.nvFns = true

theorem KnotNvG.mono {p : Prog} {n n' : Nat} (h : KnotNvG p n) (hn : n' ≤ n) : KnotNvG p n' :=
  ⟨h.knot.mono hn, h.nv⟩

/-! ## `delta_quick` -/

theorem res3_of {x y z : Word} {r : List Word} (hx : HW x) (hy : HW y) (hz : HW z)
    (h1 : x = r.headD 0) (h2 : y = r.tail.headD 0) (h3 : z = r.tail.tail.headD 0) : Res3 r :=
  ⟨h1 ▸ hx, h2 ▸ hy, h3 ▸ hz⟩

theorem hw2 : HW 2 := by unfold HW; decide
theorem hw3 : HW 3 := by unfold HW; decide

/-- **`delta_quick` refines `deltaQuick`, both outcomes**: the errors are `quick_defeq`'s. -/
theorem dq_ref (p : Prog) (n : Nat) (hq : QuickDefeqSpec p n)
    (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d a b : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) (hd : d.toNat < 2 ^ 63) :
    RefE (QuickDefeqWE p n) (dqE p (n + 1) s₀.mem mode vis d a b)
      (deltaQuick (decMode mode) (coreKnot (decMode mode) fe id F) d.toNat (decE a) (decE b)) a₀
      (CorePost decDS dn s₀.mem vis fe M eb Res3) := by
  simp only [dqE]
  unfold deltaQuick
  refine RefE.bind_callE (fun _ => dqE.k_quick_defeq.none ..) (hq F s₀ a₀ dn vis fe M eb mode d a b hF hn hs
    ha hb hd) (fun (hqE : QuickDefeqWE p n) => hqE F s₀ a₀ dn vis fe M eb mode d a b hF hn hs ha hb hd)
    fun r₁ m₁ _ h₁ => RefE.after_core (w := id) h₁ fun M₁ hS₁ _ => ?_
  by_cases h0 : r₁.headD 0 = 0
  · rw [dqE.k_quick_defeq.arm1 _ _ _ _ _ h0, show decOB r₁ = none by simp only [decOB, h0, ↓reduceIte]]
    exact RefE.ret rfl (CorePost.ret hS₁ (by simp only [decDS]; rfl) ⟨hw0, ha, hb⟩)
  by_cases h2 : r₁.tail.headD 0 ≠ 0
  · rw [dqE.k_quick_defeq.arm2 _ _ _ _ _ h0 h2, show decOB r₁ = some true by
      simp only [decOB, h0, ↓reduceIte, Option.some.injEq]; exact decBool_t (r := r₁.tail) h2]
    exact RefE.ret rfl (CorePost.ret hS₁ (by simp only [decDS]; rfl) ⟨hw1, hw0, hw0⟩)
  · have h2' : r₁.tail.headD 0 = 0 := by simpa using h2
    rw [dqE.k_quick_defeq.arm3 _ _ _ _ _ h0 h2', show decOB r₁ = some false by
      simp only [decOB, h0, ↓reduceIte, Option.some.injEq]; exact decBool_f (r := r₁.tail) h2']
    exact RefE.ret rfl (CorePost.ret hS₁ (by simp only [decDS]; rfl) ⟨hw2, hw0, hw0⟩)

/-- **`delta_quick` refines `deltaQuick`** at the knot, from `quick_defeq`'s spec (`dq_ref`'s ok
half). -/
@[refines ConRon.Arena.deltaQuick]
theorem deltaQuick_refines (p : Prog) (hp : DefEqMidProg p) (n : Nat) (hq : QuickDefeqSpec p n)
    (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d a b : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) (hd : d.toNat < 2 ^ 63) :
    CoreSpec p (n + 1) "delta_quick" [mode, vis, d, a, b]
      (deltaQuick (decMode mode) (coreKnot (decMode mode) fe id F) d.toNat (decE a) (decE b)) decDS
      s₀ a₀ dn vis fe M eb Res3 :=
  RefE.coreSpec (dqE_spec p hp.dq (n + 1) s₀ mode vis d a b)
    (dq_ref p n hq F s₀ a₀ dn vis fe M eb mode d a b hF hn hs ha hb hd)

/-! ## `defeq_offset` -/

/-- `nat_pred(e)` refines `natPred?` with both result words valid handles (`ResW`).
`natPred_refines` (`DefEqLeaves2.lean`) proves the `ResH` form only: the interned predecessor
literal's word is not known to be below `2^32` there (lane `store`'s `intern_lit` spec does not
say it). A hypothesis here. -/
def NatPredW (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb e : Word), CoreS dn s₀.mem a₀ vis fe M eb → HW e →
    CoreSpec p n "nat_pred" [e] (natPred? (decE e)) decOptR s₀ a₀ dn vis fe M eb ResW

/-- **`defeq_offset`'s model, both outcomes** (generated; `is_nat_zero` and `nat_pred` lifted, the
`defeq` slot through its run). -/
l_model offE_spec (p : Prog) (hf : p.lookup "defeq_offset" = some defeqOffsetL)
  fns [hf ↦ offE list]
  specs [callW_spec p n "is_nat_zero", callW_spec p n "nat_pred"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

theorem decOptR_some {r : List Word} (h : r.headD 0 ≠ 0) : decOptR r = some (decE (r.tail.headD 0)) := by
  simp only [decOptR, decOpt, h, ↓reduceIte]

theorem decOptR_none {r : List Word} (h : r.headD 0 = 0) : decOptR r = none := by
  simp only [decOptR, decOpt, h, ↓reduceIte]

/-- **`defeq_offset` refines `defeqOffset`, both outcomes**: the errors are the `defeq` slot's. -/
theorem off_ref (p : Prog) (hp : DefEqMidProg p) (hnp : NatPredW p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) :
    RefE (KnotUpToE p n) (offE p (n + 1) s₀.mem mode vis d a b)
      (defeqOffset (coreKnot (decMode mode) fe id F) d.toNat (decE a) (decE b)) a₀
      (CorePost decOB dn s₀.mem vis fe M eb ResW) := by
  unfold defeqOffset
  simp only [offE]
  cases n with
  | zero => rw [callW_zero, liftE_none, offE.k_is_nat_zero.none]; exact RefE.of_cls0 (by simp)
  | succ k =>
  refine RefE.bind_callW (fun _ => rfl) (isNatZero_refines p hp.leaf k s₀ a₀ dn vis fe M eb a hs.rel ha)
    fun r₁ m₁ _ h₁ => RefE.after_core (w := id) h₁ fun M₁ hS₁ _ => ?_
  dsimp only [offE.k_is_nat_zero]
  refine RefE.bind_callW (fun _ => rfl) (isNatZero_refines p hp.leaf k ⟨m₁, Locals.init []⟩ _ dn vis fe M₁
    eb b hS₁ hb) fun r₂ m₂ _ h₂ => RefE.after_core (w := id) h₂ fun M₂ hS₂ _ => ?_
  dsimp only [offE.k_is_nat_zero_2]
  by_cases hzz : r₁.headD 0 ≠ 0 ∧ r₂.headD 0 ≠ 0
  · rw [ite_eq_left hzz, decBool_t hzz.1, decBool_t hzz.2]
    exact RefE.ret rfl (CorePost.ret hS₂ rfl ⟨hw1, hw1⟩)
  rw [ite_eq_right hzz]
  have hzb : (decBool r₁ && decBool r₂) = false := by
    by_cases h : r₁.headD 0 = 0
    · rw [decBool_f h]; rfl
    · have h' : r₂.headD 0 = 0 := Classical.byContradiction fun h' => hzz ⟨h, h'⟩
      rw [decBool_f h']; simp
  simp only [hzb, Bool.false_eq_true, ↓reduceIte, decE_tag_lit_beq a ha, decE_tag_lit_beq b hb,
    Bool.and_eq_true, decide_eq_true_eq]
  by_cases hll : tagW a = 8 ∧ tagW b = 8
  · rw [ite_eq_left hll]
    simp only [hll, and_self, ↓reduceIte]
    exact RefE.ret rfl (CorePost.ret hS₂ rfl ⟨hw0, hw0⟩)
  rw [ite_eq_right hll]
  simp only [hll, ↓reduceIte]
  refine RefE.bind_callW (fun _ => rfl) (hnp (k + 1) ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb a hS₂ ha)
    fun r₃ m₃ _ h₃ => RefE.after_core (w := id) h₃ fun M₃ hS₃ _ => ?_
  dsimp only [offE.k_nat_pred]
  by_cases h3 : r₃.headD 0 = 0
  · rw [ite_eq_left h3, decOptR_none h3]
    exact RefE.ret rfl (CorePost.ret hS₃ rfl ⟨hw0, hw0⟩)
  rw [ite_eq_right h3, decOptR_some h3]
  refine RefE.bind_callW (fun _ => rfl) (hnp (k + 1) ⟨m₃, Locals.init []⟩ _ dn vis fe M₃ eb b hS₃ hb)
    fun r₄ m₄ _ h₄ => RefE.after_core (w := id) h₄ fun M₄ hS₄ _ => ?_
  dsimp only [offE.k_nat_pred_2]
  by_cases h4 : r₄.headD 0 = 0
  · rw [ite_eq_left h4, decOptR_none h4]
    exact RefE.ret rfl (CorePost.ret hS₄ rfl ⟨hw0, hw0⟩)
  rw [ite_eq_right h4, decOptR_some h4]
  have hs₄ : SlotPre ⟨m₄, Locals.init []⟩ _ dn vis fe M₄ eb mode := ⟨hS₄, hs.mode4, hs.eb_mode⟩
  refine RefE.bind_callE (fun _ => rfl) ((hk (k + 1) (Nat.le_refl _)).defeq F _ _ dn vis fe M₄ eb mode d _ _
    hF hn hs₄ h₃.resOk.2 h₄.resOk.2) (fun (hG : KnotUpToE p (k + 1)) => (hG (k + 1) (Nat.le_refl _)).defeq
      F _ _ dn vis fe M₄ eb mode d _ _ hF hn hs₄ h₃.resOk.2 h₄.resOk.2)
    fun r₅ m₅ _ h₅ => RefE.after_core (w := id) h₅ fun M₅ hS₅ _ => ?_
  exact RefE.ret rfl (CorePost.ret hS₅ (by simp only [decOB, decBool]; rfl) ⟨hw1, h₅.resOk⟩)

/-- **`defeq_offset` refines `defeqOffset`** at the knot (`off_ref`'s ok half). -/
@[refines ConRon.Arena.defeqOffset]
theorem defeqOffset_refines (p : Prog) (hp : DefEqMidProg p) (hnp : NatPredW p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) :
    CoreSpec p (n + 1) "defeq_offset" [mode, vis, d, a, b]
      (defeqOffset (coreKnot (decMode mode) fe id F) d.toNat (decE a) (decE b)) decOB s₀ a₀ dn vis
      fe M eb ResW :=
  RefE.coreSpec (offE_spec p hp.off (n + 1) s₀ mode vis d a b)
    (off_ref p hp hnp n hk F s₀ a₀ dn vis fe M eb mode d a b hF hn hs ha hb)

/-! ## `defeq_lams_inner` -/

/-- **`defeq_lams_inner`'s model, both outcomes** (generated; the `defeq` and `infer` slots through
their runs). -/
l_model liE_spec (p : Prog) (hf : p.lookup "defeq_lams_inner" = some defeqLamsInnerL)
  fns [hf ↦ liE list]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_tagE] unified

theorem mode_verified (mode : Word) (h : mode < 4) :
    (decMode mode).verifiedChecks = decide (mode &&& 1 = 0) := by
  rcases mode_cases mode h with rfl | rfl | rfl | rfl <;> decide

/-- **`defeq_lams_inner` refines `defeqLamsInner`, both outcomes** (the depth `d + 1` does not
wrap): the errors are the `defeq` and `infer` slots'. -/
theorem li_ref (p : Prog) (n : Nat) (hk : KnotUpTo p n)
    (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d b₁ b₂ : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hd : d.toNat + 1 < 2 ^ 64) (h₁ : HW b₁) (h₂ : HW b₂) :
    RefE (KnotUpToE p n) (liE p (n + 1) s₀.mem mode vis d b₁ b₂)
      (defeqLamsInner (decMode mode) (coreKnot (decMode mode) fe id F) d.toNat (decE b₁) (decE b₂))
      a₀ (CorePost decBool dn s₀.mem vis fe M eb ResH) := by
  have hd1 : (d + 1).toNat = d.toNat + 1 := by
    rw [UInt64.toNat_add]; simp only [UInt64.toNat_one]; omega
  have K := hk n (Nat.le_refl _)
  have hS := hs.rel
  unfold defeqLamsInner
  simp only [liE]
  rw [← hd1]
  refine RefE.bind_callE (fun _ => rfl) (K.defeq F s₀ a₀ dn vis fe M eb mode (d + 1) b₁ b₂ hF hn hs h₁ h₂)
    (fun (hG : KnotUpToE p n) => (hG n (Nat.le_refl _)).defeq F s₀ a₀ dn vis fe M eb mode (d + 1) b₁ b₂ hF
      hn hs h₁ h₂) fun r₁ m₁ _ e₁ => RefE.after_core (w := id) e₁ fun M₁ hS₁ _ => ?_
  dsimp only [liE.k_defeq]
  by_cases h0 : r₁.headD 0 = 0
  · rw [ite_eq_left h0, decBool_f h0]
    exact RefE.ret rfl (CorePost.ret hS₁ rfl resH_zero)
  rw [ite_eq_right h0, decBool_t h0]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, mode_verified mode hs.mode4,
    decide_eq_true_eq]
  by_cases hv : mode &&& 1 = 0
  case neg =>
    rw [ite_eq_right hv]
    simp only [hv, ↓reduceIte]
    exact RefE.ret rfl (CorePost.ret hS₁ rfl resH_one)
  rw [ite_eq_left hv]
  simp only [hv, ↓reduceIte]
  have hs₁ : SlotPre ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode := ⟨hS₁, hs.mode4, hs.eb_mode⟩
  refine RefE.bind_callE (fun _ => rfl) (K.infer F _ _ dn vis fe M₁ eb mode (d + 1) b₁ hF hn hs₁ h₁)
    (fun (hG : KnotUpToE p n) => (hG n (Nat.le_refl _)).infer F _ _ dn vis fe M₁ eb mode (d + 1) b₁ hF hn
      hs₁ h₁) fun r₂ m₂ _ e₂ => RefE.after_core (w := id) e₂ fun M₂ hS₂ _ => ?_
  dsimp only [liE.k_infer]
  have hs₂ : SlotPre ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode := ⟨hS₂, hs.mode4, hs.eb_mode⟩
  refine RefE.bind_callE (fun _ => rfl) (K.infer F _ _ dn vis fe M₂ eb mode (d + 1) b₂ hF hn hs₂ h₂)
    (fun (hG : KnotUpToE p n) => (hG n (Nat.le_refl _)).infer F _ _ dn vis fe M₂ eb mode (d + 1) b₂ hF hn
      hs₂ h₂) fun r₃ m₃ _ e₃ => RefE.after_core (w := id) e₃ fun M₃ hS₃ _ => ?_
  dsimp only [liE.k_infer_2]
  have hs₃ : SlotPre ⟨m₃, Locals.init []⟩ _ dn vis fe M₃ eb mode := ⟨hS₃, hs.mode4, hs.eb_mode⟩
  rw [← bind_pure (CoreFnsA.defeq _ _ _ _)]
  refine RefE.bind_callE (fun _ => rfl) (K.defeq F _ _ dn vis fe M₃ eb mode (d + 1) _ _ hF hn hs₃ e₂.resOk
    e₃.resOk) (fun (hG : KnotUpToE p n) => (hG n (Nat.le_refl _)).defeq F _ _ dn vis fe M₃ eb mode (d + 1)
      _ _ hF hn hs₃ e₂.resOk e₃.resOk) fun _ _ _ e₄ => ?_
  exact RefE.ret rfl ⟨e₄.after, rfl, e₄.resOk⟩

/-- **`defeq_lams_inner` refines `defeqLamsInner`** at the knot (`li_ref`'s ok half). -/
@[refines ConRon.Arena.defeqLamsInner]
theorem defeqLamsInner_refines (p : Prog) (hp : DefEqMidProg p) (n : Nat) (hk : KnotUpTo p n)
    (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d b₁ b₂ : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hd : d.toNat + 1 < 2 ^ 64) (h₁ : HW b₁) (h₂ : HW b₂) :
    CoreSpec p (n + 1) "defeq_lams_inner" [mode, vis, d, b₁, b₂]
      (defeqLamsInner (decMode mode) (coreKnot (decMode mode) fe id F) d.toNat (decE b₁) (decE b₂))
      decBool s₀ a₀ dn vis fe M eb :=
  RefE.coreSpec (liE_spec p hp.lamsInner (n + 1) s₀ mode vis d b₁ b₂)
    (li_ref p n hk F s₀ a₀ dn vis fe M eb mode d b₁ b₂ hF hn hs hd h₁ h₂)

end L.Arena
