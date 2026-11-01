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

`tcp_specF`, `ta_specF`: the specs of `target_canon_params` and `target_abs` at any fuel.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

theorem tcp_specF (p : Prog) (L : RcLook p) (n : Nat) (s₀ : St) (pfo pfl e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_canon_params" [pfo, pfl, e]
    ⦃fun r s' => LocEq s' s₀ ∧ tcpF n s₀.mem pfo pfl e = some (r, s'.mem); ⊤⦄ := by
  cases n with
  | zero => exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
  | succ n => exact targetCanonParams_spec p L.rx L.r3 L.tcp n s₀ pfo pfl e

theorem ta_specF (p : Prog) (L : TaLook p) (n : Nat) (s₀ : St) (no nl lvls ho hl e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_abs" [no, nl, lvls, ho, hl, e]
    ⦃fun r s' => LocEq s' s₀ ∧ taF n s₀.mem no nl lvls ho hl e = some (r.headD 0, s'.mem); ⊤⦄ := by
  cases n with
  | zero => exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
  | succ n => exact targetAbs_spec p L n s₀ no nl lvls ho hl e

end L.Ind

end
