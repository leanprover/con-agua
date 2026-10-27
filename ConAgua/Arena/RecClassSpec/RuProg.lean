import ConAgua.Arena.RecClassSpec.PbProg

/-!
# RuProg

`RuProg`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Lookups, `find_slot`, `pvars_go` -/

/-- The lookups `class_gen_rule` needs. -/
structure RuProg (p : Prog) : Prop extends PbProg p where
  lf : p.lookup "lam_find" = some lamFind
  lp : p.lookup "lam_push" = some lamPush
  il : p.lookup "intern_lam" = some internLamL
  mkl : p.lookup "mk_lam" = some mkLam
  cl : p.lookup "close_lams" = some closeLams
  cro : p.lookup "class_rec_of" = some classRecOf
  fsg : p.lookup "class_gen_rule_find_slot_go" = some classGenRuleFindSlotGo
  fs : p.lookup "class_gen_rule_find_slot" = some classGenRuleFindSlot
  pv : p.lookup "class_gen_rule_pvars_go" = some classGenRulePvarsGo
  c1c : p.lookup "class_gen_rule_call1_close" = some classGenRuleCall1Close
  c1t : p.lookup "class_gen_rule_call1_tail" = some classGenRuleCall1Tail
  c1 : p.lookup "class_gen_rule_call1" = some classGenRuleCall1
  cg : p.lookup "class_gen_rule_calls_go" = some classGenRuleCallsGo
  rc : p.lookup "class_gen_rule_close" = some classGenRuleClose
  rb : p.lookup "class_gen_rule_body" = some classGenRuleBody
  ru : p.lookup "class_gen_rule" = some classGenRule

end L.Ind

end
