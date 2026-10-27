import ConAgua.Arena.RecClassSpec.RuProg
import ConAgua.Arena.RecGenSpec.CrsK6
import ConAgua.Arena.RecGenSpec.FlushStage

/-!
# CrsProg

`cr1W`, `CrsProg`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- **The model of `class_rules_ok_one`.** -/
noncomputable def cr1W (cR : CallM) : Nat → Mem → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _ => none
  | n + 1, m, visT, visR, g, cvR, x, gen =>
    if (rdW (m.arr64 IW) g + rdW (m.arr64 IW) (g + 8)) + rdW (m.arr64 IW) (x + 1) < (rdW (m.arr64 IW) g + rdW (m.arr64 IW) (g + 8)) then none
    else cr1K (cruleW cR n m visT visR cvR ((rdW (m.arr64 IW) g + rdW (m.arr64 IW) (g + 8)) + rdW (m.arr64 IW) (x + 1)) gen)

/-- The lookups `class_rules_ok` needs. -/
structure CrsProg (p : Prog) : Prop where
  ru : RuProg p
  cr : CruleProg p
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
