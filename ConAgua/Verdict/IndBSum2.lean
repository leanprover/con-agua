import ConAgua.Arena.ConstsResolveFRefine2
import ConAgua.Arena.IndTwin
import ConRon.Bridge.Inductives.SumInstall
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr

/-!
# `check_constant_val`'s error claim in the shape part B takes (`CcvE`)

The declaration family discharges it (`ccvE_of`, `IndArmE.lean`).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- **`check_constant_val`'s error claim** (the hypotheses of `checkConstantVal_refinesT`; the
declaration family discharges it). -/
def CcvE (p : Prog) : Prop :=
  ∀ {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (n : Nat), n ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (q : Word) (cv : IConstantVal), StageT dn vis fe s₀.mem a₀ →
    decCV (erecP s₀.mem) q.toNat = some cv → q.toNat + 3 < 2 ^ 64 →
    (∃ ks, cv.levelParams.mapM (denoteN a₀.store.ns) = some ks) → L.Stubs.CrOK s₀.mem →
    CoreSpecE p n "check_constant_val" [vis, q] (checkConstantVal V fe cv) s₀ a₀

end L.Ind
