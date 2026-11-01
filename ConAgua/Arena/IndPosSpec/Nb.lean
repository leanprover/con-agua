module

import ConAgua.Arena.IndPosSpec.UnW
public import ConAgua.Arena.IndPosSpec.NbLook
public import ConAgua.Arena.IndPosSpec.NbKeyK2

@[expose] public section

/-!
# Nb

`whnfWalkFuel_spec'`.
-/


/-! # `IndPos2`, the `nestPos` block (lane `indproofs2`, helper `pos2`): the L side — every
function of the block refines its word model, by one induction on the exec fuel. -/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Leaf callees at any exec fuel -/

theorem whnfWalkFuel_spec' (p : Prog) (L : NbLook p) (n : Nat) (s₀ : St) (e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "whnf_walk_fuel" [e]
    ⦃fun r s' => LocEq s' s₀ ∧ wfWf n s₀.mem e = some ([r.headD 0], s'.mem); ⊤⦄ := by
  match n with
  | 0 => exact triple_post (invoke_exec0 p _ _ s₀) (fun _ _ h => h.elim)
  | 1 =>
    rw [invoke_eq _ L.hwf]; simp only [callFn, whnfWalkFuel]
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, invoke_exec0 p] <;> grind
  | n + 2 =>
    refine triple_post (whnfWalkFuel_spec p L.ct.cr.rx.hl.hv L.hdf L.hdp L.hdg L.hdn L.hdc L.hdd L.hwf n s₀ e) ?_
    rintro r s' ⟨h1, h2⟩
    exact ⟨h1, by simp [wfWf, h2]⟩


end L.Ind

end
