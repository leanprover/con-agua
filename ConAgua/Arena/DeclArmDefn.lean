module

import ConAgua.Arena.DeclStepSpec
import ConAgua.Arena.Verdict
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.Arena.DeclPins
public import ConAgua.Arena.DeclCvg
public import ConAgua.Rom.PinSets

@[expose] public section

/-!
# The variant records across the definition arm's steps (lane `decls3`)

The pin gate reads the pin variants `rom_pin_sets()` lists, so its refinement (`cdmp_ref`) takes
lane `romload`'s `PinSetsR m pins`, which the arm (`cdf_ref`, `DeclDefnT.lean`) carries from its
entry to the gate (`PinSetsR.step`: the records are below `EREC`'s top and `CTL[150]`, `CTL[151]`
are not in a step's write set).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

open L.Ind
open L.Rom (PinSetsR PinSetR SliceR HdrR)
open L.Front (DECL DLP DeclsF DeclAt CVAt dw)

local notation "V" => ConLeche.CheckMode.verified

/-! ## The variant records across a step -/

/-- A frame of the step's write set keeps the variant list. -/
theorem PinSetsR.step {m m' : Mem} {ips : List INatOpPinSet} (h : PinSetsR m ips)
    (hg : IWGrow m m') (hf : MemFrame stepA stepC m m') : PinSetsR m' ips :=
  PinSetsR.grow h (IWGrow.recGrow hg) (hf.ctl _ step_pins.1) (hf.ctl _ step_pins.2)

end L.Arena
