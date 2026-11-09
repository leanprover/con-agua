module

import ConAgua.Arena.IndPartsSpec.Bf
import ConAgua.Arena.IndPartsSpec.BrsW
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConRon.Bridge.Grind
public import ConAgua.Arena.IndPartsSpec.BlockRecNamesUnreserved
public import ConAgua.Arena.IndPartsSpec.IndPartsProg5
public import ConAgua.Arena.IndPartsSpec.PlW
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
