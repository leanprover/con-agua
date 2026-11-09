module

import ConAgua.Arena.InferProj2
public import ConAgua.Arena.InferBodyDisp
public import ConAgua.Arena.InferProj
public import ConAgua.Arena.WhnfProjRefine

@[expose] public section

/-!
# Error claims of `infer_const`, `infer_proj`

The verdict claims (`CoreSpecE`, `Arena/Verdict.lean`) of two leaves of the inference bodies, the
error halves of their unified refinements (`inferConst_ref`, `Arena/InferLeaves.lean`; `ip_ref`
over `ipa_ref`, `Arena/InferProj2.lean`, `Arena/InferProj.lean`):

* `inferConst_refinesE`: `infer_const` against `inferConstT`;
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- **`infer_const(vis, n, us)`'s verdicts** (`inferConst_ref`'s error half). -/
theorem inferConst_refinesE (p : Prog) (hp : InferLeafProg p) (hct : ConstTyAtOK p)
    (hnv : closedNV p L.Checker.nvFns = true) (n : Nat)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb nm us : Word) (hS : CoreS dn s₀.mem a₀ vis fe M eb) (hnm : HW nm)
    (hus : HW us) :
    CoreSpecE p (n + 1) "infer_const" [vis, nm, us] (inferConstT fe (decI nm) (decI us)) s₀ a₀ :=
  RefE.coreSpecE (inferConstE_spec p hp.inferConst hp.lsNode (n + 1) s₀ vis nm us) hnv hnv
    (inferConst_ref p hp hct n s₀ a₀ dn vis fe M eb nm us hS hnm hus)


end L.Arena
