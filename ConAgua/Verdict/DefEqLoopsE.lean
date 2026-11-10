module

import ConAgua.Arena.DefEqMidLoops
public import ConAgua.Arena.DefEqStuckWith
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr

@[expose] public section

/-!
# The `defeq` loops' error claims: `defeq_lst`, `defeq_list_rev`

The error halves of the unified refinements of `defeq_lst`, `defeq_list_rev`
(`DefEqMidLoops.lean`): a failure is an iteration's `defeq` slot call's (`KnotUpToE`), after the
earlier iterations' ok runs.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## `defeq_lst` -/

/-- **`defeq_lst`'s error claim** (`DefeqLstWE`, `defeqLst_ref`'s error half). -/
theorem defeqLst_refinesE (p : Prog) (hp : p.lookup "defeq_lst" = some defeqLstL) : DefeqLstWE p :=
  fun n hk hkE F hF hn s₀ a₀ dn vis fe M eb mode d ao an bo bn xs ys hs hx hy hxt hyt =>
    RefE.coreSpecE (defeqLst_specE p hp (n + 1) s₀ mode vis d ao an bo bn) trivial hkE
      (defeqLst_ref p n hk F hF hn s₀ a₀ dn vis fe M eb mode d ao an bo bn hs xs.toList ys.toList
        (by simpa using hx) (by simpa using hy) hxt hyt)

/-! ## `defeq_list_rev` -/

/-- **`defeq_list_rev`'s error claim** (`defeqListRev_ref`'s error half). -/
theorem defeqListRev_refinesE (p : Prog) (hp : p.lookup "defeq_list_rev" = some defeqListRevL)
    (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d ao an bo bn : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode)
    (xs ys : List EIdx) (hx : SpineR s₀.mem ao an xs.toArray) (hy : SpineR s₀.mem bo bn ys.toArray)
    (hxt : ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat)
    (hyt : bo.toNat + bn.toNat ≤ (spTop s₀.mem).toNat) :
    CoreSpecE p (n + 1) "defeq_list_rev" [mode, vis, d, ao, an, bo, bn]
      (defEqList (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat xs.reverse ys.reverse) s₀ a₀ :=
  RefE.coreSpecE (defeqListRev_specE p hp (n + 1) s₀ mode vis d ao an bo bn) trivial hkE
    (defeqListRev_ref p n hk F hF hn s₀ a₀ dn vis fe M eb mode d ao an bo bn hs xs ys hx hy hxt hyt)

end L.Arena
