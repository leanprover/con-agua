import ConAgua.Arena.IndDecStab
import ConAgua.Arena.IndInstallSpec.DomsW

/-!
# DecHLTruncMBound

`tmpK4`, `TmpProg`, `decHL_truncM_bound`.
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

def tmpK4 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m4) => some ([], m4)

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
  have := decHL_getI h (l - 1) (by omega)
  simp only [iwH, hd?] at this
  cases hw : (iwA (truncM m))[o + (l - 1)]? with
  | none => simp [hw] at this
  | some w =>
    have := (truncM_iw_get hw).1
    omega

end L.Ind

end
