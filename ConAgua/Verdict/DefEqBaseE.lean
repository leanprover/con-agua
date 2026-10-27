import ConAgua.Checker.NoVerdictFns
import ConAgua.Arena.DefEqMid
import ConAgua.Arena.Verdict
import ConAgua.Checker.NoVerdictTree

/-!
# The defeq family's error claims: the kit (lane `verdicts-b`, helper `k3`)

Two facts the error refinements of the knot's `defeq` family use on every step:

* `ErrClaim.bind_core`: the first step of a twin `>>=` is a callee that ran ok (its `CoreRef`, from
  the callee's ok refinement): the error claim of the rest, from every state related after it, is
  the claim of the whole (the error twin of `coreRef_bind`).
* `ErrClaim.of_callE_zero`: a call at L fuel `0` fails with class `0` and claims nothing.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- **The error claim past a callee's ok run** (the error twin of `coreRef_bind`). -/
theorem ErrClaim.bind_core {α β : Type} [Inhabited α] {T₁ : AM α} {f : α → AM β} {a₀ : AState}
    {dec₁ : List Word → α} {dn : NIdx → Option ConLeche.Name} {m₀ m₁ : Mem} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} {r₁ : List Word} {ok₁ : List Word → Prop} {e : Err}
    (h₁ : CoreRef T₁ a₀ dec₁ dn m₀ vis fe M eb r₁ m₁ ok₁)
    (h₂ : ∀ M', CoreS dn m₁ (AM.st T₁ a₀) vis fe M' eb → ErrClaim (f (dec₁ r₁)) (AM.st T₁ a₀) e) :
    ErrClaim (T₁ >>= f) a₀ e := by
  obtain ⟨M', hS, -, -⟩ := h₁.2.1
  exact ErrClaim.bind_right (by rw [AM.run_of_ok _ _ h₁.1, h₁.2.2.1]) (h₂ M' hS)

/-- `ErrClaim.bind_core`, also passing the stack kept across the callee's run. -/
theorem ErrClaim.bind_coreS {α β : Type} [Inhabited α] {T₁ : AM α} {f : α → AM β} {a₀ : AState}
    {dec₁ : List Word → α} {dn : NIdx → Option ConLeche.Name} {m₀ m₁ : Mem} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} {r₁ : List Word} {ok₁ : List Word → Prop} {e : Err}
    (h₁ : CoreRef T₁ a₀ dec₁ dn m₀ vis fe M eb r₁ m₁ ok₁)
    (h₂ : ∀ M', CoreS dn m₁ (AM.st T₁ a₀) vis fe M' eb → StackKept m₀ m₁ →
      ErrClaim (f (dec₁ r₁)) (AM.st T₁ a₀) e) :
    ErrClaim (T₁ >>= f) a₀ e := by
  obtain ⟨M', hS, -, hSt⟩ := h₁.2.1
  exact ErrClaim.bind_right (by rw [AM.run_of_ok _ _ h₁.1, h₁.2.2.1]) (h₂ M' hS hSt)

/-- A call at L fuel `0` fails with class `0`: it claims nothing. -/
theorem ErrClaim.of_callE_zero {α : Type} {T : AM α} {a : AState} {p : Prog} {f : FnName}
    {args : List Word} {m : Mem} {e : Err} (h : callE p 0 f args m = .error e) : ErrClaim T a e := by
  obtain ⟨e', h', h0⟩ := callE_zero p f args m
  rw [h] at h'; cases h'
  exact ErrClaim.of_cls0 h0

/-- A failing call: at fuel `0` it claims nothing, else the claim at `k + 1`. -/
theorem ErrClaim.of_callE_succ {α : Type} {T : AM α} {a : AState} {p : Prog} {n : Nat} {f : FnName}
    {args : List Word} {m : Mem} {e : Err} (hc : callE p n f args m = .error e)
    (h : ∀ k, n = k + 1 → callE p (k + 1) f args m = .error e → ErrClaim T a e) : ErrClaim T a e := by
  cases n with
  | zero => exact ErrClaim.of_callE_zero hc
  | succ k => exact h k rfl hc

/-- An ok call has positive fuel. -/
theorem callE_succ {p : Prog} {n : Nat} {f : FnName} {vs : List Word} {m m' : Mem} {r : List Word}
    (h : callE p n f vs m = .ok (r, m')) : ∃ k, n = k + 1 :=
  callW_succ (callW_of_callE h)

/-- `if` in the twin, both ways at once. -/
theorem ErrClaim.ite {α : Type} {c : Prop} [Decidable c] {x y : AM α} {a : AState} {e : Err}
    (h1 : c → ErrClaim x a e) (h2 : ¬ c → ErrClaim y a e) : ErrClaim (if c then x else y) a e := by
  by_cases hc : c
  · exact ErrClaim.ite_pos hc (h1 hc)
  · exact ErrClaim.ite_neg hc (h2 hc)

/-- The twin computations have the same run (a run lemma of the twin's match, a loop's step). -/
theorem ErrClaim.congr_run {α : Type} {T T' : AM α} {a a' : AState} {e : Err}
    (h : T.run a = T'.run a') (h' : ErrClaim T' a' e) : ErrClaim T a e := fun hk => by
  obtain ⟨ce, hce, hc⟩ := h' hk
  exact ⟨ce, h.trans hce, hc⟩

/-- **A tail call's continuation**: it passes the callee's error on and maps every ok run to an
ok result, so a failing result is the callee's own failure. -/
theorem tailE {β γ : Type} {K : Except Err γ → Except Err β} {x : Except Err γ} {er : Err}
    (hn : ∀ ε, K (.error ε) = .error ε) (ho : ∀ q, ∃ v, K (.ok q) = .ok v) (h : K x = .error er) :
    x = .error er := by
  cases x with
  | error e => rw [hn] at h; cases h; rfl
  | ok q => obtain ⟨v, hv⟩ := ho q; rw [hv] at h; cases h

/-- The defeq family's callees outside the verdict closure. -/
def defeqNVList : List FnName :=
  ["de_find", "de_put", "is_bool_true", "has_fvar", "head_is_proj", "lvls_eq_c", "lvl_eq_c",
   "pin_word", "pin_at", "str_lit_supported", "str_lit_ctor", "get_app_args", "get_app_fn",
   "inst_list", "lams_inst", "peel_push", "spine_head", "same_const_heads", "head_hint", "hint_lt",
   "unfoldable_head", "lazy_fold_ok", "is_eager_reduce", "unfold_definition", "lit_eq", "e_view",
   "is_nat_zero", "nat_pred", "lam_pair", "intern_fvar", "inst1", "inst_list"]

theorem defeqNV : ∀ f ∈ defeqNVList, f ∈ L.Checker.nvFns :=
  _root_.L.Checker.nv_sub (by decide +kernel)

/-- A callee of the list fails with class `0`: its failure claims nothing. -/
theorem ErrClaim.of_nv {α : Type} {T : AM α} {a : AState} {p : Prog}
    (hp : closedNV p L.Checker.nvFns = true) {f : FnName} (hf : f ∈ defeqNVList) {n : Nat}
    {vs : List Word} {m : Mem} {e : Err} (h : callE p n f vs m = .error e) : ErrClaim T a e :=
  ErrClaim.of_callE_nv hp (defeqNV f hf) h

end L.Arena
