module

public import ConAgua.Arena.DeclCvg
public import ConAgua.Arena.DeclHeader
public import ConAgua.Arena.DeclRec
public import ConAgua.Arena.Verdict
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr

@[expose] public section

noncomputable section

/-!
# `checkDecl`'s value checks under the stage relation (lane `decls3`)

`ValProg` and the twin equations: `checkConstantVal` is `installHeader`, then the type's sort
(`checkConstantVal_eq`). The unified models of `check_constant_val`, `check_defn_val` and
`check_opaque_val` and their refinements are in `Verdict/DeclValsE.lean`, `check_thm_val`'s in
`Verdict/DeclValE.lean`.
-/

noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

open L.Ind

/-- The value checks' functions in a program. -/
structure ValProg (p : Prog) : Prop where
  ccv : p.lookup "check_constant_val" = some checkConstantValL
  dv : p.lookup "check_defn_val" = some checkDefnValL
  tv : p.lookup "check_thm_val" = some checkThmValL
  ov : p.lookup "check_opaque_val" = some checkOpaqueValL
  lef : p.lookup "lvl_eq_fueled" = some lvlEqFueled
  ih : IhProg p
  cvg : CvgProg p
  rcp : RecProg p

/-! ## Twin equations -/

/-- `checkConstantVal` is `installHeader`, then the type's sort. -/
theorem checkConstantVal_eq (mode : ConLeche.CheckMode) (fe : IFEnv) (cv : IConstantVal) :
    checkConstantVal mode fe cv = (do installHeader fe cv
                                      let st ← inferTypeCore mode fe checkFuel 0 cv.type
                                      let _ ← ensureSortCore mode fe checkFuel 0 st
                                      pure ()) := by
  simp only [checkConstantVal, installHeader, bind_assoc, ite_bindAM, fail_bindAM, pure_bind]

end L.Arena
