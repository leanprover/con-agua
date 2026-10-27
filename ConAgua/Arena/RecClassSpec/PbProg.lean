import ConAgua.Arena.RecClassSpec.MnProg

/-!
# PbProg

`PbProg`, `rec2IsMot`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- The lookups `class_gen_prefix_binders` needs. -/
structure PbProg (p : Prog) : Prop extends MnProg p where
  fcg : p.lookup "class_gen_prefix_binders_find_ctor_go" = some classGenPrefixBindersFindCtorGo
  fc : p.lookup "class_gen_prefix_binders_find_ctor" = some classGenPrefixBindersFindCtor
  psg : p.lookup "class_gen_prefix_binders_slots_go" = some classGenPrefixBindersSlotsGo
  psm : p.lookup "class_gen_prefix_binders_slot_motive" = some classGenPrefixBindersSlotMotive
  psn : p.lookup "class_gen_prefix_binders_slot_minor" = some classGenPrefixBindersSlotMinor
  pb : p.lookup "class_gen_prefix_binders" = some classGenPrefixBinders

/-! ## The slot walk -/

/-- A motive slot. -/
def rec2IsMot : ClassSlot → Bool
  | .motive _ => true
  | _ => false

end L.Ind

end
