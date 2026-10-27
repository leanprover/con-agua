import ConAgua.Arena.RecClassSpec.GtProg

/-!
# MnProg

`MnProg`, `decIHO`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `class_gen_minor_ty_ih1_close`, `_ih1_tail`, `_ih1` -/

/-- The lookups `class_gen_minor_ty` needs. -/
structure MnProg (p : Prog) : Prop extends GtProg p where
  ihp : p.lookup "class_gen_ih_parts" = some classGenIhParts
  cons : p.lookup "sl_cons" = some slCons
  tpd : p.lookup "target_pi_doms_with" = some targetPiDomsWith
  it : p.lookup "class_gen_minor_ty_ih1_tail" = some classGenMinorTyIh1Tail
  icl : p.lookup "class_gen_minor_ty_ih1_close" = some classGenMinorTyIh1Close
  i1 : p.lookup "class_gen_minor_ty_ih1" = some classGenMinorTyIh1
  isg : p.lookup "class_gen_minor_ty_ihs_go" = some classGenMinorTyIhsGo
  c2 : p.lookup "class_gen_minor_ty_concl2" = some classGenMinorTyConcl2
  mcl : p.lookup "class_gen_minor_ty_close" = some classGenMinorTyClose
  cc : p.lookup "class_gen_minor_ty_concl" = some classGenMinorTyConcl
  bd : p.lookup "class_gen_minor_ty_body" = some classGenMinorTyBody
  mnci : p.lookup "class_gen_minor_ci" = some classGenMinorCi
  mn : p.lookup "class_gen_minor_ty" = some classGenMinorTy

/-- `class_gen_minor_ty_ihs_go`'s result. -/
def decIHO (m' : Mem) (r : List Word) : Option (List EIdx) → Prop
  | none => r.headD 0 = 0
  | some ihs => r.headD 0 = 1 ∧ decHL m' (r.tail.headD 0).toNat (r.tail.tail.headD 0).toNat = some ihs ∧
      (r.tail.headD 0).toNat + (r.tail.tail.headD 0).toNat ≤ iwTop m'

end L.Ind

end
