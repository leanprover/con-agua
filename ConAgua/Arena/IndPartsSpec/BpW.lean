module

public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConRon.Bridge.Grind
import all ConAgua.Arena.IndParts

@[expose] public section

/-!
# BpW

The `blockShape?` chain's imports, gathered (`blockParts?` is gone from the twin and L).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

end L.Ind

end
