import ConAgua.Verdict.InferLeavesE
import ConAgua.Arena.InferBodyDisp
import ConAgua.Arena.IndTwin

/-!
# Error refinements of the inference arms (lane `verdicts-b`, helper `k1`)

The verdict claims (`CoreSpecE`, `Arena/Verdict.lean`) of `ensure_sort` (the pilot of the brief),
the stage entries `ensure_sort_core` and `infer_type_core` (in the shape of `DeclValE`'s
`CoreStubsE`), and the straight-line arms of the inference bodies: `infer_lit`, `infer_let`,
`infer_lam_io`, `infer_forall_io`, `infer_spine_arg`. Each mirrors its ok refinement: a callee's
error is its own claim (the knot's slots from `KnotUpToE`, `ensure_sort`'s, `defeq_arg`'s as a
hypothesis), an ok callee run is the ok refinement's, a reject site is the twin's `fail`. Every
callee outside the verdict closure claims nothing (`nvFns`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace L.Arena

/-! ## The kit for core runs -/

/-- **A core run that succeeded, then the claim of the rest** (`coreRef_bind`'s error half). -/
theorem ErrClaim.bind_ref {α β : Type} [Inhabited α] {T₁ : AM α} {T₂ : α → AM β} {a₀ : AState}
    {dec₁ : List Word → α} {dn : NIdx → Option ConLeche.Name} {m₀ m₁ : Mem} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} {r₁ : List Word} {ok₁ : List Word → Prop} {e : Err}
    (h₁ : CoreRef T₁ a₀ dec₁ dn m₀ vis fe M eb r₁ m₁ ok₁)
    (h₂ : ErrClaim (T₂ (dec₁ r₁)) (AM.st T₁ a₀) e) : ErrClaim (T₁ >>= T₂) a₀ e :=
  ErrClaim.bind_right (by rw [AM.run_of_ok _ _ h₁.1, h₁.2.2.1]) h₂

theorem tag_sort_ne (h : Word) (hh : HW h) (hg : h >>> 28 ≠ 2) :
    ((decE h).tag == ETag.sort) = false := by
  rw [decE_tag h hh]
  have h16 : (h >>> 28).toNat < 16 := by
    rw [UInt64.toNat_shiftRight]; simp [Nat.shiftRight_eq_div_pow]; unfold HW at hh; omega
  simp only [beq_eq_false_iff_ne, ne_eq]
  intro heq
  apply hg
  have := congrArg UInt32.toNat heq
  simp [ETag.sort, Nat.shiftRight_eq_div_pow] at this
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_shiftRight]; simp [Nat.shiftRight_eq_div_pow]; unfold HW at hh; omega

/-! ## `ensure_sort` -/

l_model ensureSort_specE (p : Prog) (hf : p.lookup "ensure_sort" = some ensureSortL)
  fns [hf ↦ ensureSortE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  finish [tierW, idxW] heartbeats 400000 errors

/-- `ensure_sort`'s error claim (the error half of `EnsureSortSpec`). -/
def EnsureSortSpecE (p : Prog) (n : Nat) : Prop :=
  ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d e : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe M eb mode →
    HW e →
    CoreSpecE p n "ensure_sort" [mode, vis, d, e]
      (ensureSort (coreKnot (decMode mode) fe id F) fe d.toNat (decE e)) s₀ a₀

/-- **`ensure_sort`'s verdicts**: `whnf`'s errors are its slot's, a non-sort rejects. -/
theorem ensureSort_refinesE (p : Prog) (hp : InferLeafProg p) (n : Nat) (hk : KnotUpTo p n)
    (hkE : KnotUpToE p n) : EnsureSortSpecE p (n + 1) := by
  intro F s₀ a₀ dn vis fe M eb mode d e hF hn hs he
  refine CoreSpecE.of_runs fun er hc => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (ensureSort_specE p hp.ensureSort (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d e) hc (Err.code_ne_of_cls hk0)
  simp only [ensureSortE] at hW
  cases h1 : callE p n "whnf" [mode, vis, d, e] s₀.mem with
  | error e1 =>
    rw [h1, ensureSortE.k_whnf.none] at hW
    cases hW
    exact ErrClaim.bind_left (CoreSpecE.of_callE
      ((hkE n (Nat.le_refl _)).whnf F s₀ a₀ dn vis fe M eb mode d e (by omega) (by omega) hs he) h1)
  | ok q =>
    obtain ⟨r₁, m₁⟩ := q
    rw [h1] at hW
    have h₁ := CoreSpec.of_callW ((hk n (Nat.le_refl _)).whnf F s₀ a₀ dn vis fe M eb mode d e
      (by omega) (by omega) hs he) (callW_of_callE h1)
    by_cases g1 : r₁.headD 0 >>> 28 ≠ 2
    · rw [ensureSortE.k_whnf.abort1 p r₁ m₁ g1] at hW
      cases hW
      have ht : ((decH r₁).tag == ETag.sort) = false := tag_sort_ne _ h₁.2.2.2 g1
      refine ErrClaim.bind_ref h₁ ?_
      show ErrClaim (if (decH r₁).tag == ETag.sort then _ else _) _ _
      rw [ht]
      exact ErrClaim.fail _ _ rfl
    · simp only [ensureSortE.k_whnf, g1, ↓reduceIte] at hW
      split at hW
      · cases hW; exact ErrClaim.of_cls0 rfl
      split at hW
      · cases hW; exact ErrClaim.of_cls0 rfl
      · cases hW

/-- `ensure_sort` at every L fuel up to `n`. -/
theorem ensureSortSpecE_of_knot (p : Prog) (hp : InferLeafProg p) :
    ∀ n, KnotUpTo p n → KnotUpToE p n → EnsureSortSpecE p n
  | 0, _, _ => fun _ s₀ a₀ _ _ _ _ _ _ _ _ _ _ _ _ => CoreSpecE.zero p _ _ _ s₀ a₀
  | n + 1, hk, hkE => ensureSort_refinesE p hp n (hk.mono (by omega)) (hkE.mono (by omega))

/-! ## The stage entries `infer_type_core`, `ensure_sort_core` (`CoreStubsE`'s shape) -/

l_model inferTypeCore_specE (p : Prog) (hf : p.lookup "infer_type_core" = some inferTypeCoreL)
  fns [hf ↦ inferTypeCoreE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  finish [tierW, idxW] heartbeats 400000 errors

l_model ensureSortCore_specE (p : Prog) (hf : p.lookup "ensure_sort_core" = some ensureSortCoreL)
  fns [hf ↦ ensureSortCoreE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  finish [tierW, idxW] heartbeats 400000 errors

local notation "V" => ConLeche.CheckMode.verified

theorem inferTypeCore_eq (fe : IFEnv) (F d : Nat) (t : Word) :
    inferTypeCore V fe F d (decI t) = (coreKnot (decMode 0) fe id F).infer d (decE t) := rfl

theorem ensureSortCore_eq (fe : IFEnv) (F d : Nat) (t : Word) :
    ensureSortCore V fe F d (decI t) = ensureSort (coreKnot (decMode 0) fe id F) fe d (decE t) := rfl

/-- **`infer_type_core`'s verdicts under `StageT`** (`CoreStubsE.inferTypeCore`): the `infer`
slot's at the verified mode. -/
theorem inferTypeCore_refinesE (p : Prog) (hp : KnotEntryProg p) (hKE : ∀ n, KnotOKE p n) :
    ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {m : Mem} {a : AState}, L.Ind.StageT dn vis fe m a → ∀ (dep t : Word), L.Ind.H t →
    ∀ e, callE p n "infer_type_core" [vis, dep, t] m = .error e →
      ErrClaim (inferTypeCore V fe checkFuel dep.toNat (decI t)) a e := by
  intro n hn dn vis fe m a hS dep t ht er hc
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  cases n with
  | zero =>
    obtain ⟨e', he', h0⟩ := callE_zero p "infer_type_core" [vis, dep, t] m
    rw [hc] at he'; cases he'; exact absurd h0 hk0
  | succ k =>
  have hW := triple_of_callE_err (inferTypeCore_specE p hp.inferTypeCore (k + 1)
    ⟨m, Locals.init []⟩ vis dep t) hc (Err.code_ne_of_cls hk0)
  simp only [inferTypeCoreE] at hW
  obtain ⟨M, hC⟩ := hS.core
  cases h1 : callE p k "infer" [0, vis, dep, t] m with
  | error e1 =>
    rw [h1, inferTypeCoreE.k_infer.none] at hW
    cases hW
    rw [inferTypeCore_eq]
    exact CoreSpecE.of_callE (s₀ := ⟨m, Locals.init []⟩) ((hKE k).infer checkFuel ⟨m, Locals.init []⟩ a
      dn vis fe M 0 0 dep t (L.Ind.stage_fuel hn) (by omega) (slotPre_zero hC) (L.Ind.hw_of_h ht)) h1
  | ok q => rw [h1] at hW; simp [inferTypeCoreE.k_infer] at hW

/-- **`ensure_sort_core`'s verdicts under `StageT`** (`CoreStubsE.ensureSortCore`):
`ensure_sort`'s at the verified mode. -/
theorem ensureSortCore_refinesE (p : Prog) (hp : KnotEntryProg p) (hl : InferLeafProg p)
    (hK : ∀ n, KnotOK p n) (hKE : ∀ n, KnotOKE p n) :
    ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {m : Mem} {a : AState}, L.Ind.StageT dn vis fe m a → ∀ (dep t : Word), L.Ind.H t →
    ∀ e, callE p n "ensure_sort_core" [vis, dep, t] m = .error e →
      ErrClaim (ensureSortCore V fe checkFuel dep.toNat (decI t)) a e := by
  intro n hn dn vis fe m a hS dep t ht er hc
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  cases n with
  | zero =>
    obtain ⟨e', he', h0⟩ := callE_zero p "ensure_sort_core" [vis, dep, t] m
    rw [hc] at he'; cases he'; exact absurd h0 hk0
  | succ k =>
  have hW := triple_of_callE_err (ensureSortCore_specE p hp.ensureSortCore (k + 1)
    ⟨m, Locals.init []⟩ vis dep t) hc (Err.code_ne_of_cls hk0)
  simp only [ensureSortCoreE] at hW
  obtain ⟨M, hC⟩ := hS.core
  cases h1 : callE p k "ensure_sort" [0, vis, dep, t] m with
  | error e1 =>
    rw [h1, ensureSortCoreE.k_ensure_sort.none] at hW
    cases hW
    rw [ensureSortCore_eq]
    exact CoreSpecE.of_callE (s₀ := ⟨m, Locals.init []⟩) (ensureSortSpecE_of_knot p hl k
      (fun j _ => hK j) (fun j _ => hKE j) checkFuel ⟨m, Locals.init []⟩ a dn vis fe M 0 0 dep t
      (L.Ind.stage_fuel hn) (by omega) (slotPre_zero hC) (L.Ind.hw_of_h ht)) h1
  | ok q => rw [h1] at hW; simp [ensureSortCoreE.k_ensure_sort] at hW
end L.Arena
