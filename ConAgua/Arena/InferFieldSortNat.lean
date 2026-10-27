import ConAgua.Arena.DefEqMid
import ConAgua.Arena.WhnfDeltaRefine3
import ConAgua.Arena.DefEqLeaves2

/-!
# `NatPredW` from `natPred_refines` (lane `defeq2`)

`natPred_refines` (`DefEqLeaves2.lean`) posts `ResW` given `LitInternHW` (an interned `lit`
handle word is below `2^32`), which `WhnfDeltaRefine3.lean`'s `internW_hw` proves; that file is
not imported by `DefEqLeaves2.lean` (it would pull in the whnf walks), so the two meet here.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

theorem litInternHW : LitInternHW := fun m a o l w m' hR hI => internW_hw m a hR o l w m' hI

/-- **`NatPredW` is a theorem** (fuel `0`: every L call fails). -/
theorem natPredW_of (p : Prog) (hp : NatPredProg p) : NatPredW p
  | 0, s₀, a₀, dn, vis, fe, M, eb, e, _, _ => by
    unfold CoreSpec
    rw [invoke_eq _ hp.np]
    simp only [callFn]
    vcgen [exec] <;> grind
  | n + 1, s₀, a₀, dn, vis, fe, M, eb, e, hS, he =>
    natPred_refines p hp litInternHW n s₀ a₀ dn vis fe M eb e hS he

end L.Arena
