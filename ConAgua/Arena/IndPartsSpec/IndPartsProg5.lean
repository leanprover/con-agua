import ConAgua.Arena.IndPartsSpec.Bsp
import ConAgua.Arena.IndRealPartsC1

/-!
# IndPartsProg5

`bbW`, `IndPartsProg5`, `bshW`.
-/

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- **The model of `block_shape_build`** (at exec fuel `n + 4`). -/
def bbW (c : CallM) (n : Nat) (m : Mem) (nPd cto ctl cso csl rso rsl : Word) : Option (List Word × Mem) :=
  bbH1 c n nPd cto ctl cso csl rso rsl (rdW (m.arr64 IW) cto) (bsnW (n + 3) m cto ctl)

/-- **The program bundle of `blockShape?`.** -/
structure IndPartsProg5 (p : Prog) : Prop extends IndPartsProg4 p where
  resFrom : p.lookup "reserved_from" = some reservedFrom
  resCont : p.lookup "reserved_contains" = some reservedContains
  erCopy : p.lookup "er_copy" = some erCopy
  erToIw : p.lookup "er_to_iw" = some erToIw
  slEq : p.lookup "sl_eq" = some slEq
  slGetD : p.lookup "sl_getd" = some slGetD
  pinWord : p.lookup "pin_word" = some pinWordL
  rec4 : p.lookup "rec4" = some rec4
  slGet : p.lookup "sl_get" = some slGet
  paramFind : p.lookup "param_find" = some paramFind
  paramPush : p.lookup "param_push" = some paramPush
  internParam : p.lookup "intern_param" = some internParam
  plGo : p.lookup "param_levels_go" = some paramLevelsGoL
  pl : p.lookup "param_levels" = some paramLevelsL
  il : IlF p
  namesOf : p.lookup "block_shape_names_of" = some blockShapeNamesOf
  pinsF : p.lookup "block_shape_pins_formers" = some blockShapePinsFormers
  pinsR : p.lookup "block_shape_pins_recs" = some blockShapePinsRecs
  pinsC : p.lookup "block_shape_pins_ctors" = some blockShapePinsCtors
  pinsOk : p.lookup "block_shape_pins_ok" = some blockShapePinsOk
  sort : p.lookup "block_shape_result_sort" = some blockShapeResultSort
  ctorsOf : p.lookup "block_shape_ctors_of" = some blockShapeCtorsOf
  membersOf : p.lookup "block_shape_members_of" = some blockShapeMembersOf
  rhssOf : p.lookup "block_shape_rhss_of" = some blockShapeRhssOf
  recsOf : p.lookup "block_shape_recs_of" = some blockShapeRecsOf
  large : p.lookup "block_shape_large" = some blockShapeLarge
  pack : p.lookup "block_shape_pack" = some blockShapePack
  sealF : p.lookup "block_shape_seal" = some blockShapeSeal
  fin : p.lookup "block_shape_fin" = some blockShapeFin
  tail : p.lookup "block_shape_tail" = some blockShapeTail
  build : p.lookup "block_shape_build" = some blockShapeBuild
  shape : p.lookup "block_shape" = some blockShape
  parts : p.lookup "block_parts" = some blockParts
  na : NaF p

end L.Ind

end

end

section

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `block_shape`, `block_parts` -/

/-- **The model of `block_shape`** (at exec fuel `n + 5`). -/
def bshW (c : CallM) (n : Nat) (m : Mem) (nPd off l : Word) : Option (List Word × Mem) :=
  match bsW (n + 4) m off l with
  | none => none
  | some (r1, m1) =>
    if r1.headD 0 = 0 then some ([0, 0], m1)
    else if rdW (m1.arr64 IW) (r1.tail.headD 0 + 1) = 0 ∨ rdW (m1.arr64 IW) (r1.tail.headD 0 + 5) = 0 then
      some ([0, 0], m1)
    else bgoK3 (bbW c n m1 nPd (rdW (m1.arr64 IW) (r1.tail.headD 0)) (rdW (m1.arr64 IW) (r1.tail.headD 0 + 1))
      (rdW (m1.arr64 IW) (r1.tail.headD 0 + 2)) (rdW (m1.arr64 IW) (r1.tail.headD 0 + 3))
      (rdW (m1.arr64 IW) (r1.tail.headD 0 + 4)) (rdW (m1.arr64 IW) (r1.tail.headD 0 + 5)))

end L.Ind

end

end
