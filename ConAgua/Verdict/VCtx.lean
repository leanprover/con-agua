import ConAgua.Arena.IndTwin
import ConAgua.Verdict.UnresolvedE

/-!
# What the error claims assume about the program

The error half of a unified refinement (`RefE`, `Arena/Verdict.lean`) holds under an assumption
`G` about the program that only the error arms use, so that the ok half and the ok refinements up
the call chain need nothing new. `G` is the weakest of these that the error arms need:

* `True`: the function's only errors are its own aborts;
* `closedNV p nvFns = true`: its callees with errors are outside the verdict closure (lifted, their
  errors of class `0`) or unified with this `G`;
* `CoreStubsE p`: the core stubs' claims (`infer_type_core`, `ensure_sort_core`,
  `is_def_eq_core`) and nothing lifted;
* `VerdictCtx p`: both; `VerdictCtxU p`: also `unresolved_consts_error`'s program (`UceProg`,
  with `str_lit_supported`'s refinement, a semantic fact);
* a family's own named-field structure where the claims of callees not migrated yet, or of the
  knot (`KnotUpToE`), are needed (`CvgCtx`, `M2CCtxE`, `PeelG`, …).

A caller passes its own `G`'s fields (`hG.nv`, `hG.core`, `hG.toVerdictCtx`).
-/

open ConRon.Arena

namespace L.Arena

open L.Ind

local notation "V" => ConLeche.CheckMode.verified

/-- **The core stubs' error claims under `StageT`**: the error halves of `KnotStageProg`'s
`inferTypeCore_sim`, `ensureSortCore_sim`, `isDefEqCore_sim`. -/
structure CoreStubsE (p : Prog) : Prop where
  inferTypeCore : ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {m : Mem} {a : AState}, StageT dn vis fe m a → ∀ (dep t : Word), H t →
    ∀ e, callE p n "infer_type_core" [vis, dep, t] m = .error e →
      ErrClaim (inferTypeCore V fe checkFuel dep.toNat (decI t)) a e
  ensureSortCore : ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {m : Mem} {a : AState}, StageT dn vis fe m a → ∀ (dep t : Word), H t →
    ∀ e, callE p n "ensure_sort_core" [vis, dep, t] m = .error e →
      ErrClaim (ensureSortCore V fe checkFuel dep.toNat (decI t)) a e
  isDefEqCore : ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {m : Mem} {a : AState}, StageT dn vis fe m a → ∀ (dep x y : Word), H x → H y →
    ∀ e, callE p n "is_def_eq_core" [vis, dep, x, y] m = .error e →
      ErrClaim (isDefEqCore V fe checkFuel dep.toNat (decI x) (decI y)) a e

/-- **What the error claims assume about the program**: the no-verdict functions closed, the core
stubs' claims. -/
structure VerdictCtx (p : Prog) : Prop where
  nv : closedNV p L.Checker.nvFns = true
  core : CoreStubsE p

/-- `VerdictCtx` with `unresolved_consts_error`'s program (the consts-resolve sites'
`uce_errClaim_hi`). -/
structure VerdictCtxU (p : Prog) : Prop extends VerdictCtx p where
  uce : UceProg p

end L.Arena
