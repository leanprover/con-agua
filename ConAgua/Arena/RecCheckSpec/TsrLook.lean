import ConAgua.Arena.RecCheckSpec.ArfW
import ConAgua.Arena.RecCheckSpec.RcLook

/-!
# TsrLook

`TsrLook`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- The lookups of `tgt_stored_rules`. -/
structure TsrLook (p : Prog) : Prop where
  rc : RcLook p
  arf : ArfLook p
  ea : p.lookup "erec_alloc" = some erecAlloc
  srg : p.lookup "sum_rules_go" = some sumRulesGoL
  sr : p.lookup "sum_rules" = some sumRulesL
  rrb : RrbF p
  efg : p.lookup "er_from_iw_go" = some erFromIwGo
  ef : p.lookup "er_from_iw" = some erFromIw
  ic : p.lookup "iw_copy" = some iwCopy
  sc : p.lookup "sl_cons" = some slCons
  trn : p.lookup "tgt_rule_nested" = some tgtRuleNested
  tsrm : p.lookup "tgt_stored_rules_remap" = some tgtStoredRulesRemap
  tsr : p.lookup "tgt_stored_rules" = some tgtStoredRules

end L.Ind

end
