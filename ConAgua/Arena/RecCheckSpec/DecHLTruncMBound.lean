module

public import ConAgua.Arena.IndDecStab
import ConAgua.Arena.IndInstallSpec.DomsW
import ConRon.Bridge.Grind
public import ConAgua.Arena.IndRealSpine

@[expose] public section

/-!
# DecHLTruncMBound

`TmpProg`, `decHL_truncM_bound`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## `target_major_pins` -/

/-- The lookups `target_major_pins` needs. -/
structure TmpProg (p : Prog) : Prop where
  ad : AdF p
  tpt : p.lookup "target_pin_tys" = some targetPinTys
  cf : p.lookup "const_find" = some constFind
  cp : p.lookup "const_push" = some constPush
  ic : p.lookup "intern_const" = some internConst
  tmp : p.lookup "target_major_pins" = some targetMajorPins

/-- A non-empty slice decoded below the tops ends below the top. -/
theorem decHL_truncM_bound {k : IdxKind} {m : Mem} {o l : Nat} {xs : List (Idx k)}
    (h : decHL (truncM m) o l = some xs) (hl : l ≠ 0) : o + l ≤ iwTop m := by
  sorry

end L.Ind

end
