module

public import ConAgua.Arena.RecClassSpec.RuProg

@[expose] public section

/-!
# CrsProg

`CrsProg`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- The lookups `class_rules_ok` needs. -/
structure CrsProg (p : Prog) : Prop where
  ru : RuProg p
  alloc : p.lookup "iw_alloc" = some iwAlloc
  copy : p.lookup "iw_copy" = some iwCopy
  cons : p.lookup "sl_cons" = some slCons
  slGet : p.lookup "sl_get" = some slGet
  paramFind : p.lookup "param_find" = some paramFind
  paramPush : p.lookup "param_push" = some paramPush
  internParam : p.lookup "intern_param" = some internParam
  plGo : p.lookup "param_levels_go" = some paramLevelsGoL
  pl : p.lookup "param_levels" = some paramLevelsL
  il : IlF p
  crs : p.lookup "class_rules_ok" = some classRulesOkL
  one : p.lookup "class_rules_ok_one" = some classRulesOkOne

/-! ## The `abstract1` memo across a rule's check -/

end L.Ind

end
