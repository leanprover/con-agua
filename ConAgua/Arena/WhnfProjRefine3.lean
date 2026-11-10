module

import ConAgua.Arena.WhnfProjRefine2
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.Arena.WhnfIotaRefine2
import Std.WP.Triple.SpecLemmas
public import ConAgua.Arena.WhnfIotaRefine
public import ConAgua.Arena.WhnfProjRefine
import all ConAgua.Arena.WhnfProj

@[expose] public section

/-!
# `tower_slots_all` refines `towerSlotsAll` on the real `find_proj`

(The file's `fire_ok` refinement went with `IProjEntry.fireOk`, con-leche's task #480.)
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-- **`tower_slots_all` refines `towerSlotsAll`**, on the real `find_proj`. -/
@[refines ConRon.Arena.towerSlotsAll]
theorem towerSlotsAll_refines (p : Prog) (hp : IotaProg' p) (hq : ProjProg p) :
    TowerSlotsAllOK p :=
  towerSlotsAll_refines' p hp (findProj_refines p hq) (projFound p hq)

end L.Arena
