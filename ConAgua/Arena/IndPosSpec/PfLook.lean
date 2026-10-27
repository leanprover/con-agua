import ConAgua.Arena.IndPosSpec.CtxFields
import ConAgua.Arena.IndPosSpec.PiBWStage
import ConAgua.Arena.IndSumSpec7

/-!
# PfLook

`NSB`, `NfsB`, `nestedW`, `cfK3`, `cfK2`, `hkW` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The walk's state, below the tops -/

/-- A `NestState` record at `p`: decoded below the tops, its three slices below the top. -/
structure NSB (m : Mem) (p : Word) (NS : NestState) : Prop where
  dec : DecB (fun m => decNS m p.toNat) m NS
  b0 : (rdW (m.arr64 IW) p).toNat + (rdW (m.arr64 IW) (p + 1)).toNat ≤ iwTop m
  b2 : (rdW (m.arr64 IW) (p + 2)).toNat + (rdW (m.arr64 IW) (p + 3)).toNat ≤ iwTop m
  b4 : (rdW (m.arr64 IW) (p + 4)).toNat + (rdW (m.arr64 IW) (p + 5)).toNat ≤ iwTop m

/-- A `NestCtorNf` slice decoded below the tops. -/
def NfsB (m : Mem) (o l : Nat) (xs : List NestCtorNf) : Prop := DecB (fun m => decPL m (decNCN m) o l) m xs

end L.Ind

namespace L.Ind

open L.Arena

/-! ## `nest_cont_new_finish`: the group cached when closed, the active list restored -/

/-- The kind word of `.nested (kb != 0)`. -/
def nestedW (kb : Word) : Word := 4 + 8 * (if kb ≠ 0 then 1 else 0)

def cfK3 (kb : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (q, m3) => some ([nestedW kb, q], m3)
def cfK2 (ns2 aO aL kb : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m2) => cfK3 kb (posRecW m2 [r.headD 0, r.tail.headD 0, aO, aL, rdW (m2.arr64 IW) (ns2 + 4),
      rdW (m2.arr64 IW) (ns2 + 5)])
end L.Ind

namespace L.Ind

open L.Arena

/-! ## `nest_pos_hole_kind`, `nest_pos_fvar` -/

/-- The model of `nest_pos_hole_kind(ctx, kb, i)` (memory unchanged). -/
def hkW (m : Mem) (ctx kb i : Word) : Option Word :=
  if i < nhiW m ctx 0 then
    (if 1152921504606846976 ≤ i - rdW (m.arr64 IW) (ctx + 4) then none
     else if kb = 0 then some (1 + 8 * (i - rdW (m.arr64 IW) (ctx + 4)))
     else some (2 + 8 * (i - rdW (m.arr64 IW) (ctx + 4))))
  else some 3

def hkWf : Nat → Mem → Word → Word → Word → Option Word
  | 0, _, _, _, _ => none
  | _ + 1, m, ctx, kb, i => hkW m ctx kb i

/-- The twin's field kind of a hole `i`. -/
def holeKind (c : NestCtx) (kb i : Nat) : NestFieldKind :=
  if i < c.hiAt 0 then (if kb == 0 then .recursive (i - c.nP) else .reflexive (i - c.nP)) else .inProgress

end L.Ind

namespace L.Ind

open L.Arena

def p2pfK3 (k : Nat) (ctx kb i aL dL2 : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m3) =>
    if aL + dL2 < aL then none
    else if aL + dL2 ≠ r.headD 0 then none
    else match hkWf k m3 ctx kb i with
      | none => none
      | some w => some ([w], m3)
/-- The lookups of `nest_pos_fvar`. -/
structure PfLook (p : Prog) : Prop where
  ha : p.lookup "iw_alloc" = some iwAlloc
  h2 : p.lookup "rec2" = some rec2
  h4 : p.lookup "rec4" = some rec4
  hrg : p.lookup "nest_ctx_root_holes_go" = some nestCtxRootHolesGo
  hr : p.lookup "nest_ctx_root_holes" = some nestCtxRootHoles
  hc : p.lookup "iw_copy" = some iwCopy
  hap : p.lookup "sl_append" = some slAppend
  hha : p.lookup "nest_hole_at" = some nestHoleAt
  no : NoLook p
  hoa : p.lookup "nest_occ_any" = some nestOccAnyL
  na : NaLook p
  hh : p.lookup "nest_ctx_hi_at" = some nestCtxHiAt
  hk : p.lookup "nest_pos_hole_kind" = some nestPosHoleKindL
  hp : p.lookup "nest_pos_fvar" = some nestPosFvarL

end L.Ind

namespace L.Ind

open L.Arena

/-- The `.fvar` arm of `nestPos`, its result kind to `K` (the twin's text). -/
def pfK {β : Type} (fe : IFEnv) (ctx : NestCtx) (prog : List NestHole) (kb hi i : Nat) (args : List EIdx)
    (K : NestFieldKind → AM β) : AM β :=
  match ConRon.Arena.nestHoleAt ctx prog i with
  | none => fail nestNonValid
  | some h => do
    if ← args.anyM (fun x => ConRon.Arena.nestOcc ctx.names ctx.nP hi x) then fail nestNonValid
    else do
      let ar ← ConRon.Arena.nestArity fe h.key.cname
      if args.length + h.key.ds.length == ar then K (holeKind ctx kb i) else fail nestNonValid

end L.Ind

namespace L.Ind

open L.Arena

/-! ## `nest_ctors_u4`: a non-ordinary field read later -/

def ustWf : Nat → Mem → Word → Word → Word → Option (Word × Mem)
  | n + 2, m, cty, nP, j => ustW n m cty nP j
  | _, _, _, _, _ => none

/-- The lookups of `struct_used_later`. -/
structure UslLook (p : Prog) : Prop where
  hv : p.lookup "e_view" = some eView
  hf : p.lookup "hb_find" = some (memoFindG hbSch)
  hput : p.lookup "hb_put" = some (memoPutG hbSch)
  hins : p.lookup "has_loose_b_var_b_ins" = some hasLooseBVarBInsL
  hgo : p.lookup "has_loose_b_var_b_go" = some hasLooseBVarBGoL
  hbp : BvbProg p
  hst : StripProg p
  hcl : p.lookup "hb_clear" = some (memoClearG hbSch)
  hfast : p.lookup "has_loose_b_var_b_fast" = some hasLooseBVarBFastL
  hp : p.lookup "struct_used_later" = some structUsedLaterL

end L.Ind

namespace L.Ind

open L.Arena

/-- The twin's U4 test at field `i`. -/
def u4F (ks : List NestFieldKind) (closed : EIdx) (i : Nat) : AM Bool :=
  if (ks[i]?.map (· == .ordinary)).getD true then pure false else structUsedLater closed 0 i

end L.Ind

namespace L.Ind

open L.Arena

/-! ## `nest_ctors_res_ok`: the result headed by a hole, hole-free indices -/

def roK2 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m3) => some ([if r.headD 0 = 0 then 1 else 0], m3)
/-- The twin's result check of `nestCtors`, the rest to `K` (the twin's text). -/
def roK {β : Type} (c : NestCtx) (hi : Nat) (cur : EIdx) (K : Bool → AM β) : AM β := do
  let resOk ← do
    if ← nestResHead cur then do
      let args ← getAppArgs coreWalkFuel cur
      let occ ← args.anyM fun x => ConRon.Arena.nestOcc c.names c.nP hi x
      pure !occ
    else pure false
  K resOk

end L.Ind

namespace L.Ind

open L.Arena

/-! ## `nest_ctors_crest`: the group abstracted, typed at the frame's context -/

def p2ctK4 (cR : CallM) (k : Nat) (vis hi : Word) (crest : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m4) => match cR k "ensure_sort_core" [vis, hi, r.headD 0] m4 with
    | none => none
    | some (_, m5) => some ([crest], m5)
def p2ctK3 (cR : CallM) (k : Nat) (vis hi : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m3) =>
    if r.headD 0 = 0 then none
    else p2ctK4 cR k vis hi (r.tail.headD 0) (cR k "infer_type_core" [vis, hi, r.tail.headD 0] m3)
end L.Ind

end
