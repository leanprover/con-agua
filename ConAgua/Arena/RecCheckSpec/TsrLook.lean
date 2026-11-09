module

public import ConAgua.Arena.RecCheckSpec.ArfW
public import ConAgua.Arena.RecCheckSpec.RcLook
public import ConAgua.Arena.IndReal

@[expose] public section

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
  efg : p.lookup "er_from_iw_go" = some erFromIwGo
  ef : p.lookup "er_from_iw" = some erFromIw
  ic : p.lookup "iw_copy" = some iwCopy
  sc : p.lookup "sl_cons" = some slCons
  trn : p.lookup "generated_rule_nested" = some generatedRuleNested
  tsrm : p.lookup "generated_rules_remap" = some generatedRulesRemap
  tsr : p.lookup "generated_rules" = some generatedRules

end L.Ind

end
