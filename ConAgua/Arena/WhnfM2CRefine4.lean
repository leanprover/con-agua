module

import ConAgua.Arena.WhnfM2CRefine3
import ConAgua.Arena.RefWalk
import ConAgua.Arena.WhnfCoreRefine
import ConAgua.Arena.WhnfIotaRefine3
import ConAgua.Arena.DefEqStuckGo
import all ConAgua.Arena.WhnfM2C
public import ConAgua.Arena.WhnfM2CRefine2
import ConAgua.Arena.WhnfDeltaRefine

@[expose] public section

/-!
# `major_to_ctor`: refinements of the η arm (`m2c_eta`, `m2c_eta2`)
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

section etaarm
variable (p : Prog) (hp : M2CProg' p) (hc : IotaCallees p) (hE : ErecPKept p)
  (hcc : ProjCallees p) (hpr : PropReadProg p) (hilp : InstLPOK p)
include hp hc hcc hpr hilp


end etaarm

end L.Arena
