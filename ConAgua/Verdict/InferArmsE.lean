module

public import ConAgua.Arena.IndTwin
public import ConAgua.Arena.InferBodyDisp

@[expose] public section
/-!
# Error claims of the inference family's entries

The error halves of the unified refinements of the stage entries `infer_type_core` and
`ensure_sort_core` (`itc_ref`, `esc_ref`), in `CoreStubsE`'s shape (`StageT`), and the error
claims the knot's `infer` slots take of their callees (`InferCalleesE`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

/-! ## The stage entries `infer_type_core`, `ensure_sort_core` (`CoreStubsE`'s shape) -/

local notation "V" => ConLeche.CheckMode.verified

/-- **`infer_type_core`'s verdicts under `StageT`** (`CoreStubsE.inferTypeCore`): the `infer`
slot's at the verified mode (`itc_ref`'s error half). -/
theorem inferTypeCore_refinesE (p : Prog) (hp : KnotEntryProg p) (hK : ∀ n, KnotOK p n)
    (hKE : ∀ n, KnotOKE p n) :
    ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {m : Mem} {a : AState}, L.Ind.StageT dn vis fe m a → ∀ (dep t : Word), L.Ind.H t →
    ∀ e, callE p n "infer_type_core" [vis, dep, t] m = .error e →
      ErrClaim (inferTypeCore V fe checkFuel dep.toNat (decI t)) a e := by
  intro n hn dn vis fe m a hS dep t ht er hc
  obtain _ | k := n
  · obtain ⟨e', he', h0⟩ := callE_zero p _ _ m
    rw [hc] at he'; cases he'; exact ErrClaim.of_cls0 h0
  obtain ⟨M, hC⟩ := hS.core
  exact RefE.run_err (itcE_spec p hp.inferTypeCore (k + 1) ⟨m, Locals.init []⟩ vis dep t) trivial
    (hKE k).infer (itc_ref p k (hK k).infer checkFuel ⟨m, Locals.init []⟩ a dn vis fe M dep t
      (L.Ind.stage_fuel hn) (by omega) hC (L.Ind.hw_of_h ht)) hc

/-- **`ensure_sort_core`'s verdicts under `StageT`** (`CoreStubsE.ensureSortCore`):
`ensure_sort`'s at the verified mode (`esc_ref`'s error half). -/
theorem ensureSortCore_refinesE (p : Prog) (hp : KnotEntryProg p) (hl : InferLeafProg p)
    (hK : ∀ n, KnotOK p n) (hKE : ∀ n, KnotOKE p n) :
    ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {m : Mem} {a : AState}, L.Ind.StageT dn vis fe m a → ∀ (dep t : Word), L.Ind.H t →
    ∀ e, callE p n "ensure_sort_core" [vis, dep, t] m = .error e →
      ErrClaim (ensureSortCore V fe checkFuel dep.toNat (decI t)) a e := by
  intro n hn dn vis fe m a hS dep t ht er hc
  obtain _ | k := n
  · obtain ⟨e', he', h0⟩ := callE_zero p _ _ m
    rw [hc] at he'; cases he'; exact ErrClaim.of_cls0 h0
  obtain ⟨M, hC⟩ := hS.core
  exact RefE.run_err (escE_spec p hp.ensureSortCore (k + 1) ⟨m, Locals.init []⟩ vis dep t) trivial
    (ensureSortSpecE_of_knot p hl k (fun j _ => hK j) (fun j _ => hKE j))
    (esc_ref p k (ensureSortSpec_of_knot p hl k (fun j _ => hK j)) checkFuel ⟨m, Locals.init []⟩ a dn
      vis fe M dep t (L.Ind.stage_fuel hn) (by omega) hC (L.Ind.hw_of_h ht)) hc

/-! ## The callees' error claims -/

/-- **The callees' error claims the inference bodies take** (the error half of `InferCallees`):
every callee outside the verdict closure claims nothing (`nv`), `infer_proj`'s
(`inferProj_refinesE'`, `InferLeavesE.lean`). -/
structure InferCalleesE (p : Prog) : Prop where
  nv : closedNV p L.Checker.nvFns = true
  proj : InferProjOKE p

end L.Arena
