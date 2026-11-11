module

public import ConAgua.Arena.IndPartsSpec.Bsp
import ConAgua.Arena.IndSumSpec.Row
import ConAgua.L.ModelGen
import all ConAgua.Arena.IndParts

@[expose] public section

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
  rec7 : p.lookup "rec7" = some rec7
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
  recsOf : p.lookup "block_shape_recs_of" = some blockShapeRecsOf
  large : p.lookup "block_shape_large" = some blockShapeLarge
  pack : p.lookup "block_shape_pack" = some blockShapePack
  sealF : p.lookup "block_shape_seal" = some blockShapeSeal
  fin : p.lookup "block_shape_fin" = some blockShapeFin
  tail : p.lookup "block_shape_tail" = some blockShapeTail
  build : p.lookup "block_shape_build" = some blockShapeBuild
  shape : p.lookup "block_shape" = some blockShape
  na : NaF p

/-- **The model of `block_shape_fin`** (at exec fuel `n + 2`). -/
l_model bf_spec (p : Prog) (hP : IndPartsProg5 p)
  fns [hP.fin ↦ bfW list]
  specs [bct_spec p hP.alloc hP.copy hP.cons hP.rec2 hP.ctorsOf (n + 1),
      plW_spec p hP.alloc hP.copy hP.cons hP.slGet hP.paramFind hP.paramPush hP.internParam hP.plGo hP.pl hP.il (n + 1),
      bg_spec p hP.toIndPartsProg hP.view hP.find hP.midx hP.cmem hP.gone hP.rec2 hP.ggo hP.groups n,
      bmo_spec p hP.alloc hP.copy hP.cons hP.rec5 hP.membersOf (n + 1),
      brs_spec p hP.toIndPartsProg4 hP.rec7 hP.recsOf (n + 1),
      bsl_spec p hP.toIndPartsProg4 hP.erCopy hP.erToIw hP.slEq hP.large (n + 1),
      bseal_spec p hP.na hP.alloc hP.pack hP.sealF (n + 1)]
  grind [arena_grind, ind_grind] pfuel 2

/-- **The model of `block_shape_tail`** (at exec fuel `n + 3`). -/
l_model bt_spec (p : Prog) (hP : IndPartsProg5 p) (c : CallM) (hc : CallSpec p c)
  fns [hP.tail ↦ btW list]
  specs [bso_spec p hP.view hP.pinWord hP.slGetD hP.sort hP.strip (n + 2), pinWord_specV p hP.pinWord (n + 2),
      hc (n + 2) "lvl_eq_c", bf_spec p hP n]
  grind [arena_grind, ind_grind] fold [erRd] pfuel 3

/-- After `block_shape_pins_ok`. -/
def bbH4 (c : CallM) (n : Nat) (nPd cto ctl cso csl rso rsl no nl io il lo ll : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) =>
    if r.headD 0 = 0 then some ([0, 0], m)
    else bgoK3 (btW c n m nPd cto ctl cso csl rso rsl no nl io il lo ll)

/-- After `er_to_iw`. -/
def bbH3 (c : CallM) (n : Nat) (nPd cto ctl cso csl rso rsl no nl io il : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => bbH4 c n nPd cto ctl cso csl rso rsl no nl io il (r.headD 0) (r.tail.headD 0)
      (bpoW (n + 2) m nPd cto ctl (r.headD 0) (r.tail.headD 0) rso rsl cso csl)

/-- After `block_member_counts`. -/
def bbH2 (c : CallM) (n : Nat) (nPd cto ctl cso csl rso rsl cvT0 no nl : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) =>
    if r.headD 0 = 0 then some ([0, 0], m)
    else bbH3 c n nPd cto ctl cso csl rso rsl no nl (r.tail.headD 0) (r.tail.tail.headD 0)
      (erToIwW (n + 3) m (erRd m (cvT0 + 1)) (erRd m (cvT0 + 2)))

/-- After `block_shape_names_of`. -/
def bbH1 (c : CallM) (n : Nat) (nPd cto ctl cso csl rso rsl cvT0 : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => bbH2 c n nPd cto ctl cso csl rso rsl cvT0 (r.headD 0) (r.tail.headD 0)
      (bmcW (n + 2) m nPd ctl csl (r.headD 0) (r.tail.headD 0) rso rsl cto ctl)

section arms
variable (c : CallM) (n : Nat) (nPd cto ctl cso csl rso rsl cvT0 : Word) (m : Mem) (r : List Word)
  (no nl io il lo ll s z : Word)
theorem bbH4_fail (h : r.headD 0 = 0) : bbH4 c n nPd cto ctl cso csl rso rsl no nl io il lo ll (some (r, m)) =
    some ([0, 0], m) := by simp only [bbH4]; exact ite_eq_left h
theorem bbH4_ok (h : ¬ r.headD 0 = 0) : bbH4 c n nPd cto ctl cso csl rso rsl no nl io il lo ll (some (r, m)) =
    bgoK3 (btW c n m nPd cto ctl cso csl rso rsl no nl io il lo ll) := by simp only [bbH4]; exact ite_eq_right h
theorem bbH3_some : bbH3 c n nPd cto ctl cso csl rso rsl no nl io il (some (r, m)) =
    bbH4 c n nPd cto ctl cso csl rso rsl no nl io il (r.headD 0) (r.tail.headD 0)
      (bpoW (n + 2) m nPd cto ctl (r.headD 0) (r.tail.headD 0) rso rsl cso csl) := rfl
theorem bbH1_some : bbH1 c n nPd cto ctl cso csl rso rsl cvT0 (some (r, m)) =
    bbH2 c n nPd cto ctl cso csl rso rsl cvT0 (r.headD 0) (r.tail.headD 0)
      (bmcW (n + 2) m nPd ctl csl (r.headD 0) (r.tail.headD 0) rso rsl cto ctl) := rfl
end arms
attribute [ind_grind] bbH4_fail bbH4_ok bbH3_some bbH1_some

/-- **The model of `block_shape_build`** (at exec fuel `n + 4`). -/
def bbW (c : CallM) (n : Nat) (m : Mem) (nPd cto ctl cso csl rso rsl : Word) : Option (List Word × Mem) :=
  bbH1 c n nPd cto ctl cso csl rso rsl (rdW (m.arr64 IW) cto) (bsnW (n + 3) m cto ctl)

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
