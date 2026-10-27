module

meta import ConAgua.L.Semantics
meta import ConAgua.Arena.Store
public import ConAgua.Arena.LiftL
import all ConAgua.Arena.LiftL
import ConAgua.Census.Attr
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
public import ConAgua.L.ModelGen
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# `liftLooseBVars`: the first walk that interns its results

con-ron's `lift_loose_bvars_go` (Lean twin `liftLooseBVarsGo`, `Arena/ExprOps.lean:668`) and its
entry `lift_loose_bvars_fast` (`liftLooseBVarsFast`): bump every loose bound variable `≥ c` by
`amount`, memoized per `(node, cutoff)` in `liftC`, rebuilding the term through the store.

`lift_go(h, c, k, fu)` (`k` the amount, `fu` the twin's `fuel` as a counter), as
the twin's dispatcher:
* `abort` at `fu = 0` (the twin throws), the arms called at `fu - 1`;
* the **cutoff**: `der_b(h)` (the range field of the derived word, `ExprMk.lean`); if it is below
  `satRange` and at most `c`, return `h`;
* the **view** checks (scratch tier, the tier's count; the twin's `view` fails there), then per tag:
  `bvar i`: `i < c` returns `h`, else `intern_bvar(i + k)` (an `abort` where `i + k` wraps);
  `fvar`, `sort`, `const`, `lit`: `h`; the compound tags call their arm.
* the **arms** `lift_app`, `lift_lam`, `lift_forall`, `lift_let`, `lift_proj` (the twin's
  `liftArmApp`, …): probe the memo `lf_find(h, c)`; on a hit return the value; else walk the
  children (a binder's body and `letE`'s body at `c + 1`), rebuild with `mk_*`, probe again and
  `lf_put`.

`lift_entry(h, k, c, f)` is `liftLooseBVarsFast f k c h`: `lf_clear(); r := lift_go(h, c, k, f); lf_clear()`.
The memo is the library's (`lfSch`: array 41, `CTL[42]`, `CTL[43]`), keys `(h, c)`.

The models `liftW`/`lift*W`, their continuations `lift*W.kᵢ`, their guarded equations
`lift*W.armᵢ` and the specs `liftGo_spec` are generated from the L text (`LiftL.lean`) by
`l_model` (`L/ModelGen.lean`).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-! ## The models and the specs (generated) -/

/-- **`lift_go` and its arms are their models** `liftW`, `liftAppW`, …, at every fuel. -/
l_model liftGo_spec (p : Prog) (hp : LiftProg p)
  fns [(hp.get "lift_go") ↦ liftW, (hp.get "lift_app") ↦ liftAppW, (hp.get "lift_lam") ↦ liftLamW, (hp.get "lift_forall") ↦ liftForallW,
    (hp.get "lift_let") ↦ liftLetW, (hp.get "lift_proj") ↦ liftProjW]
  specs [derB_spec p (hp.get "der_b") n, internBVar_spec p (hp.get "bvar_find") (hp.get "bvar_push") (hp.get "intern_bvar") n,
    memoFindG_spec lfSch p _ (hp.get "lf_find") n, memoPutG_spec lfSch p _ (hp.get "lf_put") n,
    mkApp_spec p (hp.get "der_b") (hp.get "app_find") (hp.get "app_push") (hp.get "intern_app") (hp.get "mk_app") n,
    mkLam_spec p (hp.get "der_b") (hp.get "lam_find") (hp.get "lam_push") (hp.get "intern_lam") (hp.get "mk_lam") n,
    mkForall_spec p (hp.get "der_b") (hp.get "forall_find") (hp.get "forall_push") (hp.get "intern_forall") (hp.get "mk_forall") n,
    mkLet_spec p (hp.get "der_b") (hp.get "letE_find") (hp.get "letE_push") (hp.get "intern_letE") (hp.get "mk_let") n,
    mkProj_spec p (hp.get "der_b") (hp.get "proj_find") (hp.get "proj_push") (hp.get "intern_proj") (hp.get "mk_proj") n]
  grind [arena_grind] fold [tierW, idxW]
  extra [evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  finish [tierW, idxW] gen 20 heartbeats 1000000

end L.Arena
