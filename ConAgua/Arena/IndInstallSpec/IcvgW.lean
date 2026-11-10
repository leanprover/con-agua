module

public import ConAgua.Arena.IndInstallSpec.Icvg
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.Arena.RecStab
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.IndInstall

@[expose] public section

/-!
# IcvgW

`RecsB.grow`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified


theorem RecsB.grow {m m' : Mem} {pp : Word} (h : RecsB m pp) (hg : IWGrow m m') (h3 : pp.toNat + 3 < iwTop m) :
    RecsB m' pp := by
  intro o l ho hl
  rw [iwN_grow hg (by omega)] at ho
  rw [iwN_grow hg h3] at hl
  exact Nat.le_trans (h o l ho hl) hg.iw

end L.Ind

end
