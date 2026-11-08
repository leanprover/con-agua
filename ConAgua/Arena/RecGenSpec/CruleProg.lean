module

public import ConAgua.Arena.IndRealCrF
public import ConAgua.Arena.IndRealWalk
public import ConAgua.Arena.RecGen

@[expose] public section

/-!
# CruleProg

`StageR.restrict`, `StageR.unrestrict`, `CruleProg`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Shared pieces -/

/-- The stage relation at a smaller view of the same index. -/
theorem StageR.restrict {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem}
    {a : AState} (h : StageR vis fe m a) (k : Word) : StageR k (fe.restrictTo k.toNat) m a := by
  sorry

/-- Back from a smaller view (`fe`'s own view is `vis`). -/
theorem StageR.unrestrict {dn : NIdx → Option ConLeche.Name} {vis k : Word} {fe : IFEnv} {m : Mem}
    {a : AState} (h : StageR k (fe.restrictTo k.toNat) m a) (hv : fe.visibleBelow = vis.toNat) :
    StageR vis fe m a := by
  sorry

/-! ## `class_rule_ok` -/

end L.Ind

end
