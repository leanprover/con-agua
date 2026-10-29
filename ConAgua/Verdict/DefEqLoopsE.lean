import ConAgua.Arena.DefEqMidLoops
import ConAgua.Arena.DefEqStuckWith
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr

/-!
# The `defeq` loops' error claims: `defeq_lst`, `defeq_list_rev`, `defeq_list`

The error halves of the unified refinements of `defeq_lst`, `defeq_list_rev`
(`DefEqMidLoops.lean`) and `defeq_list` (`WhnfIotaRefine2.lean`): a failure is an iteration's
`defeq` slot call's (`KnotUpToE`), after the earlier iterations' ok runs.
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
      (defEqList (coreKnot (decMode mode) fe id F) fe d.toNat xs.reverse ys.reverse) s₀ a₀ :=
  RefE.coreSpecE (defeqListRev_specE p hp (n + 1) s₀ mode vis d ao an bo bn) trivial hkE
    (defeqListRev_ref p n hk F hF hn s₀ a₀ dn vis fe M eb mode d ao an bo bn hs xs ys hx hy hxt hyt)

end L.Arena

/-! ## `defeq_list` (`WhnfIota.lean`'s) -/

namespace L.Arena

/-- **`defeq_list`'s error claim** (`defeqList_ref`'s error half). -/
theorem defeqList_refinesE (p : Prog) (hp : IotaProg' p) :
    ∀ (n : Nat), KnotUpTo p n → KnotUpToE p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d ao an bo bn : Word) (aas bs : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 →
    SpineN s₀.mem ao an aas → SpineN s₀.mem bo bn bs →
    (an ≠ 0 → ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat) →
    (bn ≠ 0 → bo.toNat + bn.toNat ≤ (spTop s₀.mem).toNat) →
    CoreSpecE p (n + 1) "defeq_list" [mode, vis, d, ao, an, bo, bn]
      (defEqList (coreKnot (decMode mode) fe id F) fe d.toNat aas.toList bs.toList) s₀ a₀ :=
  fun n hk hkE F hnF hn62 s₀ a₀ dn vis fe MM eb mode d ao an bo bn aas bs hS hm4 hebm hsa hsb hta htb =>
    RefE.coreSpecE (defeqList_specE p hp.defeqList (n + 1) s₀ mode vis d ao an bo bn) trivial hkE
      (defeqList_ref p n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d ao an bo bn aas bs hS hm4 hebm hsa
        hsb hta htb)

end L.Arena
