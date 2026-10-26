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
/-! ## The callees' error claims (hypotheses, discharged by other lanes' proofs) -/

/-- The callees of the inference arms outside the verdict closure. -/
theorem inferArmsE_nv : ∀ f ∈ ["nat_lit_supported", "str_lit_supported", "pin_at", "const_e",
    "intern_fvar", "inst1", "inst_list", "infer_lam_result", "intern_imax", "intern_sort",
    "intern_succ", "e_view", "head_and_args", "ar_entry", "mk_forall", "in_find", "in_put",
    "io_find", "io_put"], f ∈ L.Checker.nvFns := by
  decide +kernel

/-- **`defeq_arg`'s error claim** at the knot (the error half of `defeqArg_any`; it reads the
`defeq` and `defeq_e` slots). -/
def DefeqArgE (p : Prog) : Prop :=
  ∀ n, KnotUpTo p n → KnotUpToE p n → ∀ (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a ta ty : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe M eb mode → HW a →
    HW ta → HW ty →
    CoreSpecE p n "defeq_arg" [mode, vis, d, a, ta, ty]
      (defeqArg (coreKnot (decMode mode) fe id F) d.toNat (decE a) (decE ta) (decE ty)) s₀ a₀

/-- **The callees' error claims the inference bodies take** (the error half of `InferCallees`):
every callee outside the verdict closure claims nothing (`nv`), `infer_proj`'s
(`inferProj_refinesE'`, `InferLeavesE.lean`), `defeq_arg`'s. -/
structure InferCalleesE (p : Prog) : Prop where
  nv : closedNV p L.Checker.nvFns = true
  proj : InferProjOKE p
  defeqArg : DefeqArgE p

/-! ## `infer_lit` -/

l_model inferLit_specE (p : Prog) (hf : p.lookup "infer_lit" = some inferLitL)
  fns [hf ↦ inferLitE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  finish [tierW, idxW] heartbeats 400000 errors

/-- The pin and `const_e` after a passed support test claim nothing. -/
theorem inferLitE_pin {α : Type} {T : AM α} {a : AState} (p : Prog)
    (hnv : closedNV p L.Checker.nvFns = true) (n : Nat) (k : Word) (m₁ : Mem) (er : Err)
    (hW : inferLitE.k_pin_at p n (callE p n "pin_at" [k] m₁) = .error er) : ErrClaim T a er := by
  cases h2 : callE p n "pin_at" [k] m₁ with
  | error e2 =>
    rw [h2, inferLitE.k_pin_at.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (inferArmsE_nv "pin_at" (by simp)) h2
  | ok q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [h2] at hW; simp only [inferLitE.k_pin_at] at hW
  cases h3 : callE p n "const_e" [r₂.headD 0] m₂ with
  | error e3 =>
    rw [h3, inferLitE.k_const_e.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (inferArmsE_nv "const_e" (by simp)) h3
  | ok q => rw [h3] at hW; simp [inferLitE.k_const_e] at hW

/-- **`infer_lit`'s verdicts**: a `Nat` literal without its basis rejects, a `String` literal
without its support declines; the support tests, the pin and `const_e` claim nothing. -/
theorem inferLit_refinesE (p : Prog) (hp : InferLeafProg p) (hc : InferLitCallees p)
    (hnv : closedNV p L.Checker.nvFns = true) (n : Nat)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb e : Word) (l : ConLeche.Literal) (hS : CoreS dn s₀.mem a₀ vis fe M eb)
    (he : HW e) (hg : e >>> 28 = 8) (hv : a₀.store.view (decE e) = some (.lit l)) :
    CoreSpecE p (n + 1) "infer_lit" [vis, e] (inferLitT fe l) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (inferLit_specE p hp.inferLit (n + 1) ⟨s₀.mem, Locals.init []⟩
    vis e) hc0 (Err.code_ne_of_cls hk0)
  simp only [inferLitE] at hW
  split at hW
  · cases hW; exact ErrClaim.of_cls0 rfl
  rename_i h1
  split at hW
  · cases hW; exact ErrClaim.of_cls0 rfl
  rename_i h2
  obtain ⟨k, hk, hrel⟩ := view_lit_f s₀.mem a₀ hS.arena.1 e he ⟨h1, by simpa using h2⟩ hg
  rw [hv] at hk
  have hl : l = k.l := by simpa using hk
  subst hl
  obtain ⟨l⟩ := k
  split at hW
  · rename_i h3
    cases l with
    | strVal str => simp [RecRel, StrRec, h3] at hrel
    | natVal N =>
    cases hc1 : callE p n "nat_lit_supported" [vis] s₀.mem with
    | error e1 =>
      rw [hc1, inferLitE.k_nat_lit_supported.none] at hW; cases hW
      exact ErrClaim.of_callE_nv hnv (inferArmsE_nv "nat_lit_supported" (by simp)) hc1
    | ok q =>
    obtain ⟨r₁, m₁⟩ := q
    rw [hc1] at hW
    have h₁ := CoreSpec.of_callW (hc.natLitSup n ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe M eb hS)
      (callW_of_callE hc1)
    by_cases h0 : r₁.headD 0 = 0
    · simp only [inferLitE.k_nat_lit_supported, h0, ↓reduceIte] at hW
      cases hW
      have hdb : decBool r₁ = false := by simp only [decBool, h0]; rfl
      simp only [inferLitT]
      refine ErrClaim.bind_ref h₁ ?_
      simp only [hdb, Bool.false_eq_true, ↓reduceIte]
      exact ErrClaim.fail _ _ rfl
    · simp only [inferLitE.k_nat_lit_supported, h0, ↓reduceIte] at hW
      exact inferLitE_pin p hnv n 1 m₁ er hW
  · rename_i h3
    cases l with
    | natVal N => simp [RecRel, NatRec, h3] at hrel
    | strVal str =>
    cases hc1 : callE p n "str_lit_supported" [vis] s₀.mem with
    | error e1 =>
      rw [hc1, inferLitE.k_str_lit_supported.none] at hW; cases hW
      exact ErrClaim.of_callE_nv hnv (inferArmsE_nv "str_lit_supported" (by simp)) hc1
    | ok q =>
    obtain ⟨r₁, m₁⟩ := q
    rw [hc1] at hW
    have h₁ := CoreSpec.of_callW (hc.strLitSup n ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe M eb hS)
      (callW_of_callE hc1)
    by_cases h0 : r₁.headD 0 = 0
    · simp only [inferLitE.k_str_lit_supported, h0, ↓reduceIte] at hW
      cases hW
      have hdb : decBool r₁ = false := by simp only [decBool, h0]; rfl
      simp only [inferLitT]
      refine ErrClaim.bind_ref h₁ ?_
      simp only [hdb, Bool.false_eq_true, ↓reduceIte]
      exact ErrClaim.fail _ _ rfl
    · simp only [inferLitE.k_str_lit_supported, h0, ↓reduceIte] at hW
      exact inferLitE_pin p hnv n 5 m₁ er hW

/-! ## `infer_spine_arg` -/

l_model inferSpineArg_specE (p : Prog) (hf : p.lookup "infer_spine_arg" = some inferSpineArgL)
  fns [hf ↦ inferSpineArgE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  finish [tierW, idxW] heartbeats 400000 errors

/-- **`infer_spine_arg`'s verdicts**: the argument's type (the `infer` slot), `defeq_arg`'s, a
mismatch rejects. -/
theorem inferSpineArg_refinesE (p : Prog) (hp : InferLeafProg p) (hkp : KnotProg p)
    (hq : SpineFProg p) (he : IsEagerReduceH p) (hda : DefeqArgE p) (n : Nat) (hk : KnotUpTo p n)
    (hkE : KnotUpToE p n) (F : Nat)
    (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a dom : Word)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hdom : HW dom) :
    CoreSpecE p (n + 1) "infer_spine_arg" [mode, vis, d, a, dom]
      (inferSpineArgT (coreKnot (decMode mode) fe id F) d.toNat (decE a) (decE dom)) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (inferSpineArg_specE p hq.arg (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d a dom) hc0 (Err.code_ne_of_cls hk0)
  simp only [inferSpineArgE] at hW
  cases hc1 : callE p n "infer" [mode, vis, d, a] s₀.mem with
  | error e1 =>
    rw [hc1, inferSpineArgE.k_infer.none] at hW; cases hW
    exact ErrClaim.bind_left (CoreSpecE.of_callE
      ((hkE n (Nat.le_refl _)).infer F s₀ a₀ dn vis fe M eb mode d a hF hn hs ha) hc1)
  | ok q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [hc1] at hW; simp only [inferSpineArgE.k_infer] at hW
  have h₁ := CoreSpec.of_callW ((hk n (Nat.le_refl _)).infer F s₀ a₀ dn vis fe M eb mode d a hF hn hs ha)
    (callW_of_callE hc1)
  obtain ⟨M₁, hS₁, -, -⟩ := h₁.2.1
  refine ErrClaim.bind_ref h₁ ?_
  cases hc2 : callE p n "defeq_arg" [mode, vis, d, a, r₁.headD 0, dom] m₁ with
  | error e2 =>
    rw [hc2, inferSpineArgE.k_defeq_arg.none] at hW; cases hW
    exact ErrClaim.bind_left (CoreSpecE.of_callE (s₀ := ⟨m₁, Locals.init []⟩)
      (hda n hk hkE F ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode d a (r₁.headD 0) dom hF hn
        ⟨hS₁, hs.mode4, hs.eb_mode⟩ ha h₁.2.2.2 hdom) hc2)
  | ok q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [hc2] at hW
  have h₂ := CoreSpec.of_callW (defeqArg_any p hp hkp he n hk F ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb
    mode d a (r₁.headD 0) dom hF hn ⟨hS₁, hs.mode4, hs.eb_mode⟩ ha h₁.2.2.2 hdom) (callW_of_callE hc2)
  by_cases h0 : r₂.headD 0 = 0
  · simp only [inferSpineArgE.k_defeq_arg, h0, ↓reduceIte] at hW
    cases hW
    have hdb : decBool r₂ = false := by simp only [decBool, h0]; rfl
    refine ErrClaim.bind_ref h₂ ?_
    simp only [hdb, Bool.not_false, ↓reduceIte]
    exact ErrClaim.fail _ _ rfl
  · simp only [inferSpineArgE.k_defeq_arg, h0, ↓reduceIte] at hW; cases hW

/-! ## `infer_lam_io` -/

l_model inferLamIO_specE (p : Prog) (hf : p.lookup "infer_lam_io" = some inferLamIOL)
  fns [hf ↦ inferLamIOE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  finish [tierW, idxW] heartbeats 400000 errors

/-- **`infer_lam_io`'s verdicts**: the body's type (the `infer_io` slot at `d + 1`); the rest
claims nothing. -/
theorem inferLamIO_refinesE (p : Prog) (hb : InferBodyProg p) (hnv : closedNV p L.Checker.nvFns = true)
    (hi1 : Inst1OK p) (n : Nat) (hkE : KnotUpToE p n) (F : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d ty body : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hty : HW ty) (hbody : HW body) :
    CoreSpecE p (n + 1) "infer_lam_io" [mode, vis, d, ty, body]
      (inferLamIOT (CoreFnsA.ioView (coreKnot (decMode mode) fe id F)) d.toNat (decE ty) (decE body))
      s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (inferLamIO_specE p hb.inferLamIO (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d ty body) hc0 (Err.code_ne_of_cls hk0)
  simp only [inferLamIOE] at hW
  split at hW
  · cases hW; exact ErrClaim.of_cls0 rfl
  rename_i hd
  have hd1 := toNat_succ_of_ne hd
  cases hc1 : callE p n "intern_fvar" [d, ty] s₀.mem with
  | error e1 =>
    rw [hc1, inferLamIOE.k_intern_fvar.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (inferArmsE_nv "intern_fvar" (by simp)) hc1
  | ok q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [hc1] at hW; simp only [inferLamIOE.k_intern_fvar] at hW
  obtain ⟨s₁, hs₁, -, hfv⟩ := triple_of_callW (internFVar_spec p hb.fvf hb.fvp hb.fvi n s₀ d ty)
    (callW_of_callE hc1)
  rw [hs₁] at hfv
  have h₁ := internFVar_core hs.rel d ty hty r₁ hfv
  obtain ⟨M₁, hS₁, -, -⟩ := h₁.2.1
  refine ErrClaim.bind_ref h₁ ?_
  cases hc2 : callE p n "inst1" [body, r₁.headD 0, 0] m₁ with
  | error e2 =>
    rw [hc2, inferLamIOE.k_inst1.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (inferArmsE_nv "inst1" (by simp)) hc2
  | ok q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [hc2] at hW; simp only [inferLamIOE.k_inst1] at hW
  have h₂ := CoreSpec.of_callW (hi1 n ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb body (r₁.headD 0) 0 hS₁
    hbody h₁.2.2.2) (callW_of_callE hc2)
  obtain ⟨M₂, hS₂, -, -⟩ := h₂.2.1
  refine ErrClaim.bind_ref h₂ ?_
  cases hc3 : callE p n "infer_io" [mode, vis, d + 1, r₂.headD 0] m₂ with
  | error e3 =>
    rw [hc3, inferLamIOE.k_infer_io.none] at hW; cases hW
    have h3 := CoreSpecE.of_callE (s₀ := ⟨m₂, Locals.init []⟩) ((hkE n (Nat.le_refl _)).inferIO F
      ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode (d + 1) (r₂.headD 0) hF hn ⟨hS₂, hs.mode4, hs.eb_mode⟩
      h₂.2.2.2) hc3
    rw [hd1] at h3
    exact ErrClaim.bind_left h3
  | ok q =>
  obtain ⟨r₃, m₃⟩ := q
  rw [hc3] at hW; simp only [inferLamIOE.k_infer_io] at hW
  cases hc4 : callE p n "infer_lam_result" [ty, r₃.headD 0, d] m₃ with
  | error e4 =>
    rw [hc4, inferLamIOE.k_infer_lam_result.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (inferArmsE_nv "infer_lam_result" (by simp)) hc4
  | ok q => rw [hc4] at hW; simp [inferLamIOE.k_infer_lam_result] at hW

/-! ## `infer_let` -/

l_model inferLet_specE (p : Prog) (hf : p.lookup "infer_let" = some inferLetL)
  fns [hf ↦ inferLetE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 simp [tierW, idxW] errors

/-- **`infer_let`'s verdicts**: the slots' (`infer`, `defeq`), `ensure_sort`'s, a value of another
type rejects; `inst1` claims nothing. -/
theorem inferLet_refinesE (p : Prog) (hp : InferLeafProg p) (hb : InferBodyProg p)
    (hnv : closedNV p L.Checker.nvFns = true) (hi1 : Inst1OK p) (n : Nat) (hk : KnotUpTo p n)
    (hkE : KnotUpToE p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d ty v b : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode)
    (hty : HW ty) (hv : HW v) (hbb : HW b) :
    CoreSpecE p (n + 1) "infer_let" [mode, vis, d, ty, v, b]
      (inferLetT (coreKnot (decMode mode) fe id F) fe d.toNat (decE ty) (decE v) (decE b)) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (inferLet_specE p hb.inferLet (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d ty v b) hc0 (Err.code_ne_of_cls hk0)
  simp only [inferLetE] at hW
  have hK := hk n (Nat.le_refl _)
  have hKE := hkE n (Nat.le_refl _)
  have hes := ensureSortSpec_of_knot p hp n hk
  have hesE := ensureSortSpecE_of_knot p hp n hk hkE
  simp only [inferLetT]
  cases hc1 : callE p n "infer" [mode, vis, d, ty] s₀.mem with
  | error e1 =>
    rw [hc1, inferLetE.k_infer.none] at hW; cases hW
    exact ErrClaim.bind_left (CoreSpecE.of_callE (hKE.infer F s₀ a₀ dn vis fe M eb mode d ty hF hn hs hty) hc1)
  | ok q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [hc1] at hW; simp only [inferLetE.k_infer] at hW
  have h₁ := CoreSpec.of_callW (hK.infer F s₀ a₀ dn vis fe M eb mode d ty hF hn hs hty) (callW_of_callE hc1)
  obtain ⟨M₁, hS₁, -, -⟩ := h₁.2.1
  refine ErrClaim.bind_ref h₁ ?_
  cases hc2 : callE p n "ensure_sort" [mode, vis, d, r₁.headD 0] m₁ with
  | error e2 =>
    rw [hc2, inferLetE.k_ensure_sort.none] at hW; cases hW
    exact ErrClaim.bind_left (CoreSpecE.of_callE (s₀ := ⟨m₁, Locals.init []⟩) (hesE F _ _ dn vis fe M₁ eb
      mode d (r₁.headD 0) hF hn ⟨hS₁, hs.mode4, hs.eb_mode⟩ h₁.2.2.2) hc2)
  | ok q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [hc2] at hW; simp only [inferLetE.k_ensure_sort] at hW
  have h₂ := CoreSpec.of_callW (hes F ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode d (r₁.headD 0) hF hn
    ⟨hS₁, hs.mode4, hs.eb_mode⟩ h₁.2.2.2) (callW_of_callE hc2)
  obtain ⟨M₂, hS₂, -, -⟩ := h₂.2.1
  refine ErrClaim.bind_ref h₂ ?_
  cases hc3 : callE p n "infer" [mode, vis, d, v] m₂ with
  | error e3 =>
    rw [hc3, inferLetE.k_infer_2.none] at hW; cases hW
    exact ErrClaim.bind_left (CoreSpecE.of_callE (s₀ := ⟨m₂, Locals.init []⟩) (hKE.infer F _ _ dn vis fe
      M₂ eb mode d v hF hn ⟨hS₂, hs.mode4, hs.eb_mode⟩ hv) hc3)
  | ok q =>
  obtain ⟨r₃, m₃⟩ := q
  rw [hc3] at hW; simp only [inferLetE.k_infer_2] at hW
  have h₃ := CoreSpec.of_callW (hK.infer F ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode d v hF hn
    ⟨hS₂, hs.mode4, hs.eb_mode⟩ hv) (callW_of_callE hc3)
  obtain ⟨M₃, hS₃, -, -⟩ := h₃.2.1
  refine ErrClaim.bind_ref h₃ ?_
  cases hc4 : callE p n "defeq" [mode, vis, d, r₃.headD 0, ty] m₃ with
  | error e4 =>
    rw [hc4, inferLetE.k_defeq.none] at hW; cases hW
    exact ErrClaim.bind_left (CoreSpecE.of_callE (s₀ := ⟨m₃, Locals.init []⟩) (hKE.defeq F _ _ dn vis fe
      M₃ eb mode d (r₃.headD 0) ty hF hn ⟨hS₃, hs.mode4, hs.eb_mode⟩ h₃.2.2.2 hty) hc4)
  | ok q =>
  obtain ⟨r₄, m₄⟩ := q
  rw [hc4] at hW
  have h₄ := CoreSpec.of_callW (hK.defeq F ⟨m₃, Locals.init []⟩ _ dn vis fe M₃ eb mode d (r₃.headD 0) ty
    hF hn ⟨hS₃, hs.mode4, hs.eb_mode⟩ h₃.2.2.2 hty) (callW_of_callE hc4)
  obtain ⟨M₄, hS₄, -, -⟩ := h₄.2.1
  refine ErrClaim.bind_ref h₄ ?_
  by_cases h0 : r₄.headD 0 = 0
  · simp only [inferLetE.k_defeq, h0, ↓reduceIte] at hW
    cases hW
    have hdb : decBool r₄ = false := by simp only [decBool, h0]; rfl
    simp only [hdb, Bool.not_false, ↓reduceIte]
    exact ErrClaim.fail _ _ rfl
  simp only [inferLetE.k_defeq, h0, ↓reduceIte] at hW
  have hdb : decBool r₄ = true := by simp only [decBool, bne_iff_ne]; exact h0
  simp only [hdb, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases hc5 : callE p n "inst1" [b, v, 0] m₄ with
  | error e5 =>
    rw [hc5, inferLetE.k_inst1.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (inferArmsE_nv "inst1" (by simp)) hc5
  | ok q =>
  obtain ⟨r₅, m₅⟩ := q
  rw [hc5] at hW; simp only [inferLetE.k_inst1] at hW
  have h₅ := CoreSpec.of_callW (hi1 n ⟨m₄, Locals.init []⟩ _ dn vis fe M₄ eb b v 0 hS₄ hbb hv)
    (callW_of_callE hc5)
  obtain ⟨M₅, hS₅, -, -⟩ := h₅.2.1
  refine ErrClaim.bind_ref h₅ ?_
  cases hc6 : callE p n "infer" [mode, vis, d, r₅.headD 0] m₅ with
  | error e6 =>
    rw [hc6, inferLetE.k_infer_3.none] at hW; cases hW
    exact CoreSpecE.of_callE (s₀ := ⟨m₅, Locals.init []⟩) (hKE.infer F _ _ dn vis fe M₅ eb mode d
      (r₅.headD 0) hF hn ⟨hS₅, hs.mode4, hs.eb_mode⟩ h₅.2.2.2) hc6
  | ok q => rw [hc6] at hW; simp [inferLetE.k_infer_3] at hW

/-! ## `infer_forall_io` -/

l_model inferForallIO_specE (p : Prog) (hf : p.lookup "infer_forall_io" = some inferForallIOL)
  fns [hf ↦ inferForallIOE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 simp [tierW, idxW] errors

/-- **`infer_forall_io`'s verdicts**: the slots' (`infer_io` twice, `whnf`), `ensure_sort`'s, a
domain type that is no sort rejects; the interning and `inst1` claim nothing. -/
theorem inferForallIO_refinesE (p : Prog) (hp : InferLeafProg p) (hb : InferBodyProg p)
    (hnv : closedNV p L.Checker.nvFns = true) (hi1 : Inst1OK p) (n : Nat) (hk : KnotUpTo p n)
    (hkE : KnotUpToE p n) (F : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d ty body : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hty : HW ty) (hbody : HW body) :
    CoreSpecE p (n + 1) "infer_forall_io" [mode, vis, d, ty, body]
      (inferForallIOT (CoreFnsA.ioView (coreKnot (decMode mode) fe id F)) fe d.toNat (decE ty)
        (decE body)) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (inferForallIO_specE p hb.inferForallIO (n + 1)
    ⟨s₀.mem, Locals.init []⟩ mode vis d ty body) hc0 (Err.code_ne_of_cls hk0)
  simp only [inferForallIOE] at hW
  split at hW
  · cases hW; exact ErrClaim.of_cls0 rfl
  rename_i hd
  have hd1 := toNat_succ_of_ne hd
  have hK := hk n (Nat.le_refl _)
  have hKE := hkE n (Nat.le_refl _)
  have hesE := ensureSortSpecE_of_knot p hp n hk hkE
  simp only [inferForallIOT]
  cases hc1 : callE p n "infer_io" [mode, vis, d, ty] s₀.mem with
  | error e1 =>
    rw [hc1, inferForallIOE.k_infer_io.none] at hW; cases hW
    exact ErrClaim.bind_left (CoreSpecE.of_callE (hKE.inferIO F s₀ a₀ dn vis fe M eb mode d ty hF hn hs
      hty) hc1)
  | ok q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [hc1] at hW; simp only [inferForallIOE.k_infer_io] at hW
  have h₁ := CoreSpec.of_callW (hK.inferIO F s₀ a₀ dn vis fe M eb mode d ty hF hn hs hty)
    (callW_of_callE hc1)
  obtain ⟨M₁, hS₁, -, -⟩ := h₁.2.1
  refine ErrClaim.bind_ref h₁ ?_
  cases hc2 : callE p n "whnf" [mode, vis, d, r₁.headD 0] m₁ with
  | error e2 =>
    rw [hc2, inferForallIOE.k_whnf.none] at hW; cases hW
    exact ErrClaim.bind_left (CoreSpecE.of_callE (s₀ := ⟨m₁, Locals.init []⟩) (hKE.whnf F _ _ dn vis fe
      M₁ eb mode d (r₁.headD 0) hF hn ⟨hS₁, hs.mode4, hs.eb_mode⟩ h₁.2.2.2) hc2)
  | ok q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [hc2] at hW
  have h₂ := CoreSpec.of_callW (hK.whnf F ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode d (r₁.headD 0)
    hF hn ⟨hS₁, hs.mode4, hs.eb_mode⟩ h₁.2.2.2) (callW_of_callE hc2)
  obtain ⟨M₂, hS₂, -, -⟩ := h₂.2.1
  refine ErrClaim.bind_ref h₂ ?_
  simp only [inferForallIOE.k_whnf] at hW
  by_cases g1 : r₂.headD 0 >>> 28 ≠ 2
  · rw [ite_eq_left g1] at hW; cases hW
    simp only [show decH r₂ = decE (r₂.headD 0) from rfl, tag_sort_ne _ h₂.2.2.2 g1,
      Bool.false_eq_true, ↓reduceIte]
    exact ErrClaim.fail _ _ rfl
  rw [ite_eq_right g1] at hW
  split at hW
  · cases hW; exact ErrClaim.of_cls0 rfl
  rename_i g2
  split at hW
  · cases hW; exact ErrClaim.of_cls0 rfl
  rename_i g3
  have hg : r₂.headD 0 >>> 28 = 2 := by simpa using g1
  obtain ⟨hv, hu⟩ := L.Ind.view_sort_f m₂ _ hS₂.arena.1 (r₂.headD 0) h₂.2.2.2 ⟨g2, by simpa using g3⟩ hg
  have htag : ((decH r₂).tag == ETag.sort) = true := tag_sort_beq _ h₂.2.2.2 hg
  simp only [htag, ↓reduceIte]
  refine ErrClaim.bind_right (view_run _ _ _ hv) ?_
  cases hc3 : callE p n "intern_fvar" [d, ty] m₂ with
  | error e3 =>
    rw [hc3, inferForallIOE.k_intern_fvar.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (inferArmsE_nv "intern_fvar" (by simp)) hc3
  | ok q =>
  obtain ⟨r₃, m₃⟩ := q
  rw [hc3] at hW; simp only [inferForallIOE.k_intern_fvar] at hW
  obtain ⟨s₃, hs₃, -, hfv⟩ := triple_of_callW
    (internFVar_spec p hb.fvf hb.fvp hb.fvi n ⟨m₂, Locals.init []⟩ d ty) (callW_of_callE hc3)
  rw [hs₃] at hfv
  have h₃ := internFVar_core hS₂ d ty hty r₃ hfv
  obtain ⟨M₃, hS₃, -, -⟩ := h₃.2.1
  refine ErrClaim.bind_ref h₃ ?_
  cases hc4 : callE p n "inst1" [body, r₃.headD 0, 0] m₃ with
  | error e4 =>
    rw [hc4, inferForallIOE.k_inst1.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (inferArmsE_nv "inst1" (by simp)) hc4
  | ok q =>
  obtain ⟨r₄, m₄⟩ := q
  rw [hc4] at hW; simp only [inferForallIOE.k_inst1] at hW
  have h₄ := CoreSpec.of_callW (hi1 n ⟨m₃, Locals.init []⟩ _ dn vis fe M₃ eb body (r₃.headD 0) 0 hS₃
    hbody h₃.2.2.2) (callW_of_callE hc4)
  obtain ⟨M₄, hS₄, -, -⟩ := h₄.2.1
  refine ErrClaim.bind_ref h₄ ?_
  cases hc5 : callE p n "infer_io" [mode, vis, d + 1, r₄.headD 0] m₄ with
  | error e5 =>
    rw [hc5, inferForallIOE.k_infer_io_2.none] at hW; cases hW
    have h5 := CoreSpecE.of_callE (s₀ := ⟨m₄, Locals.init []⟩) (hKE.inferIO F _ _ dn vis fe M₄ eb mode
      (d + 1) (r₄.headD 0) hF hn ⟨hS₄, hs.mode4, hs.eb_mode⟩ h₄.2.2.2) hc5
    rw [hd1] at h5
    exact ErrClaim.bind_left h5
  | ok q =>
  obtain ⟨r₅, m₅⟩ := q
  rw [hc5] at hW; simp only [inferForallIOE.k_infer_io_2] at hW
  have h₅ := CoreSpec.of_callW (hK.inferIO F ⟨m₄, Locals.init []⟩ _ dn vis fe M₄ eb mode (d + 1)
    (r₄.headD 0) hF hn ⟨hS₄, hs.mode4, hs.eb_mode⟩ h₄.2.2.2) (callW_of_callE hc5)
  rw [hd1] at h₅
  obtain ⟨M₅, hS₅, -, -⟩ := h₅.2.1
  refine ErrClaim.bind_ref h₅ ?_
  cases hc6 : callE p n "ensure_sort" [mode, vis, d + 1, r₅.headD 0] m₅ with
  | error e6 =>
    rw [hc6, inferForallIOE.k_ensure_sort.none] at hW; cases hW
    have h6 := CoreSpecE.of_callE (s₀ := ⟨m₅, Locals.init []⟩) (hesE F _ _ dn vis fe M₅ eb mode (d + 1)
      (r₅.headD 0) hF hn ⟨hS₅, hs.mode4, hs.eb_mode⟩ h₅.2.2.2) hc6
    rw [hd1] at h6
    exact ErrClaim.bind_left h6
  | ok q =>
  obtain ⟨r₆, m₆⟩ := q
  rw [hc6] at hW; simp only [inferForallIOE.k_ensure_sort] at hW
  cases hc7 : callE p n "intern_imax" [_, r₆.headD 0] m₆ with
  | error e7 =>
    rw [hc7, inferForallIOE.k_intern_imax.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (inferArmsE_nv "intern_imax" (by simp)) hc7
  | ok q =>
  obtain ⟨r₇, m₇⟩ := q
  rw [hc7] at hW; simp only [inferForallIOE.k_intern_imax] at hW
  cases hc8 : callE p n "intern_sort" [r₇.headD 0] m₇ with
  | error e8 =>
    rw [hc8, inferForallIOE.k_intern_sort.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (inferArmsE_nv "intern_sort" (by simp)) hc8
  | ok q => rw [hc8] at hW; simp [inferForallIOE.k_intern_sort] at hW

end L.Arena
