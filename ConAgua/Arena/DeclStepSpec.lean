import ConAgua.Arena.DeclBase
import ConAgua.Arena.DeclStep

/-!
# The specs of phase A's step and phase B's check (`install_step_go`, `check_value_group`)

The two callees of the declaration loop's skeleton (`Checker.lean`) that `DeclStep.lean`
translates, with the specs the skeleton is proved from.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false

namespace L.Arena

open L.Front (DECL DLP DeclsR)

section specs
variable (mode : ConLeche.CheckMode) (pins : List INatOpPinSet) (dn : NIdx → Option ConLeche.Name)
  (ds : Array IDeclaration) (p : Prog)

theorem installStepGo_spec (hm : mode = .verified) :
    ∀ (n : Nat) (s₀ : St) (a₀ : AState) (vis : Word) (fe : IFEnv) (pend : Array PendingCheck)
      (i : Word) (hi : i.toNat < ds.size), LoopR dn s₀.mem a₀ vis fe pend ds →
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "install_step_go" [i, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (installStepGo mode pins fe (dsAt ds i)) a₀ ∧
      LoopR dn s'.mem (AM.st (installStepGo mode pins fe (dsAt ds i)) a₀) (r.headD 0)
        (AM.res (installStepGo mode pins fe (dsAt ds i)) a₀).1 pend ds ∧
      (AM.res (installStepGo mode pins fe (dsAt ds i)) a₀).2 =
        vgOut s'.mem (r.tail.headD 0) (r.tail.tail.headD 0) ∧
      (r.tail.headD 0 ≠ 0 → (AM.res (installStepGo mode pins fe (dsAt ds i)) a₀).2 ≠ none); ⊤⦄ :=
  sorry

theorem checkValueGroup_spec (hm : mode = .verified) :
    ∀ (n : Nat) (s₀ : St) (a₀ : AState) (vis : Word) (fe : IFEnv) (pend : Array PendingCheck)
      (g : Word) (vg : ValueGroup), decVG (erecP s₀.mem) g.toNat = some vg →
      LoopR dn s₀.mem a₀ vis fe pend ds →
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_value_group" [vis, g]
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok (checkValueGroup mode fe vg) a₀ ∧
      LoopR dn s'.mem (AM.st (checkValueGroup mode fe vg) a₀) vis fe pend ds; ⊤⦄ := sorry

end specs

end L.Arena
