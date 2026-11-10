module

public import ConAgua.Arena.IndRealIlpN
public import ConAgua.Arena.RecCheckSpec.PtrNamesWDec
public import ConAgua.Arena.IndPartsSpec.SetEqW
public import ConAgua.Arena.IndReal
import ConAgua.L.ModelGen
import all ConAgua.Arena.RecCheck

@[expose] public section

/-!
# RpLook

`RpLook`, `rpN0`, `rpAux`, `rpSetOk`, `namesTwin`, the generated `tpnW` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The lookups -/

/-- The program bundle of `target_rec_pins` and its callees. -/
structure RpLook (p : Prog) : Prop extends IndPartsProg3 p where
  erCopy : p.lookup "er_copy" = some erCopy
  rna : NaF p
  erToIw : p.lookup "er_to_iw" = some erToIw
  slEq : p.lookup "sl_eq" = some slEq
  lpsOne : p.lookup "block_rec_lps_one" = some blockRecLpsOne
  lpsGo : p.lookup "block_rec_lps_ok_go" = some blockRecLpsOkGo
  lps : p.lookup "block_shape_lps" = some blockShapeLps
  lpsOk : p.lookup "block_rec_lps_ok" = some blockRecLpsOk
  unres : p.lookup "block_rec_names_unreserved" = some blockRecNamesUnreserved
  rrn : RrnF p
  soa : p.lookup "block_rec_split_own_aux" = some blockRecSplitOwnAux
  wan : p.lookup "block_rec_want_aux_names" = some blockRecWantAuxNames
  nri : NriF p
  pnc : p.lookup "ptr_names_copy" = some ptrNamesCopy
  pln : p.lookup "ptr_list_names" = some ptrListNames
  nodup : p.lookup "sl_nodup" = some slNodup
  nco : p.lookup "num_ctors_of" = some numCtorsOf
  acc : p.lookup "block_shape_ctors_copy" = some blockShapeCtorsCopy
  acg : p.lookup "block_shape_all_ctors_go" = some blockShapeAllCtorsGo
  ac : p.lookup "block_shape_all_ctors" = some blockShapeAllCtors
  names : p.lookup "target_rec_pins_names" = some targetRecPinsNames
  psplit : p.lookup "target_rec_pins_split" = some targetRecPinsSplit
  pins : p.lookup "target_rec_pins" = some targetRecPins

/-! ## Guards: the L code aborts where the twin fails -/

/-! ## The twin's name pins, as one test -/

/-- `n₀`: member 0's name, `.anonymous` (interned) at no member. -/
def rpN0 (p : BlockShape) : AM NIdx :=
  match p.members with
  | [] => internNNode .anonymous
  | ms :: _ => pure ms.cvT.name

/-- The auxiliary recursors. -/
def rpAux (p : BlockShape) : List RecShape := p.recs.filter fun rc => !(rc.tgt < p.k)

/-- The set test of the auxiliary names. -/
def rpSetOk (gotAux wantAux : List NIdx) : Bool :=
  gotAux.length == wantAux.length && wantAux.all (gotAux.contains ·) && gotAux.all (wantAux.contains ·)

/-- **The twin's name pins** (`targetRecPins` between the member name set and the split): the
auxiliary names as a set, then no two recursors sharing a name. -/
def namesTwin (p : BlockShape) : AM Bool := do
  let n₀ ← rpN0 p
  let wantAux ← (List.range (rpAux p).length).mapM fun i => internNNode (.str n₀ s!"rec_{i + 1}")
  if rpSetOk ((rpAux p).map (·.cvR.name)) wantAux then pure (nameNodup (p.recs.map (·.cvR.name)))
  else pure false

/-- **`target_rec_pins_names` is its model `tpnW`** (generated; body fuel `n`). -/
l_model tpn_spec (p : Prog) (hp : p.lookup "target_rec_pins_names" = some targetRecPinsNames)
  fns [hp ↦ tpnW list]
  specs [callW_spec p n "intern_nanon", callW_spec p n "block_rec_want_aux_names",
    callW_spec p n "ptr_list_names", callW_spec p n "sl_set_eq", callW_spec p n "sl_nodup"]
  grind [arena_grind, ind_grind] finish [rdW_eq, erRd] gen 20 pfuel

end L.Ind

end
