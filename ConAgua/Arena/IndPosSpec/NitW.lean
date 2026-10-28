import ConAgua.Arena.WhnfCoreProj
import ConAgua.Arena.IndPosSpec.Grow
import ConAgua.Arena.IndPosSpec.NtyW
import ConAgua.Arena.IndGrindAttr

/-!
# NitW

`ntyT`, `NtyPost`: the twin of `nest_inst_type_ty` and what its refinement gives.
-/

section

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- `nestInstType` up to the instantiated container type `ty`, then `K ty`. -/
def ntyT {β : Type} (fe : IFEnv) (key : NestKey) (K : EIdx → AM β) : AM β := do
  let cvC ← unwrapOr
    (match fe.find? key.cname with
     | some (.indInfo cv _) => some cv
     | _ => none)
    (.internal "nested positivity: container vanished")
  match ← viewLsLen key.lvls with
  | none => failDanglingLs
  | some nl =>
    if nl != cvC.levelParams.length then
      fail (.invalid "nested positivity: incorrect number of universe levels for a nested inductive datatype (official: incorrect number of universe levels)")
    else
      match ← stripPis key.ds.length cvC.type with
      | none => fail (.invalid "nested positivity: invalid nested inductive datatype, its type does not bind its parameters (official: ill-formed inductive type)")
      | some _ => do
        let tl ← instLPFast coreWalkFuel cvC.levelParams key.lvls cvC.type
        match ← ConRon.Arena.instPisWith key.ds tl with
        | none => fail (.invalid "nested positivity: invalid nested inductive datatype, its type does not bind its parameters (official: ill-formed inductive type)")
        | some ty => K ty

/-- What `nest_inst_type_ty` gives besides the twin's type `ty` (from `m`, `a`): the twin's steps,
the stage, the growth, the result word, the frames. -/
structure NtyPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (kk : NestKey)
    (m : Mem) (a : AState) (w : Word) (m' : Mem) (ty : EIdx) (a' : AState) : Prop where
  steps : ∃ cv caps q a3 a4 tl, fe.find? kk.cname = some (.indInfo cv caps) ∧
    a.store.lss.viewLen kk.lvls = some cv.levelParams.length ∧
    (stripPis kk.ds.length cv.type).run a = .ok (some q, a3) ∧
    (instLPFast coreWalkFuel cv.levelParams kk.lvls cv.type).run a3 = .ok (tl, a4) ∧
    (ConRon.Arena.instPisWith kk.ds tl).run a4 = .ok (some ty, a')
  stage : StageR dn vis fe m' a'
  grow : IWGrow m m'
  hw : H w
  dec : decI w = ty
  abs : AFr m m'
  mfr : MFr [] [] m m'

end L.Ind

end

end
