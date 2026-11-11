module

public import ConAgua.Arena.RecCheckSpec.TaGoWMfr
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
public import ConAgua.Arena.RecClassSpec.MnW
import ConAgua.Arena.RecCheckSpec.EraseFVarTys

@[expose] public section

/-!
# Tpd

`ta_specF`: the spec of `target_abs` at any fuel.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

theorem ta_specF (p : Prog) (L : TaLook p) (n : Nat) (s₀ : St) (no nl lvls ho hl e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_abs" [no, nl, lvls, ho, hl, e]
    ⦃fun r s' => LocEq s' s₀ ∧ taF n s₀.mem no nl lvls ho hl e = some (r.headD 0, s'.mem); ⊤⦄ := by
  cases n with
  | zero => exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
  | succ n => exact targetAbs_spec p L n s₀ no nl lvls ho hl e

end L.Ind

end
