import ConAgua.Arena.IndIface

/-!
# PosBindT

`posBindT`, `walkK`.
-/

noncomputable section

open ConRon.Arena
open ConLeche (CheckMode)

namespace L.Ind

section pieces
variable (mode : CheckMode) (fe : IFEnv) (ctx : NestCtx) (fuel : Nat) (prog : List NestHole)

/-- The `Π` branch of `nestPos` (`nest_pos_bind`). -/
def posBindT (dep kb hi : Nat) (w : EIdx) (ns : NestState) : AM (NestFieldKind × EIdx × NestState) := do
  match ← viewBind w with
  | none => failDanglingE
  | some (a, b) =>
    if ← ConRon.Arena.nestOcc ctx.names ctx.nP hi a then
      fail (.invalid "nested positivity: non positive occurrence of the datatypes being declared")
    else do
      let fv ← internFVarE dep a
      let b2 ← instantiate1Fast coreWalkFuel b fv 0
      let (k, nb, ns2) ← ConRon.Arena.nestPos mode fe ctx fuel prog (dep + 1) (kb + 1) b2 ns
      let nb2 ← abstract1Fast coreWalkFuel nb dep 0
      let r ← internForallEE a nb2
      pure (k, r, ns2)

/-- The walk of one constructor's fields (`nest_ctors_walk`), the rest to `K`. -/
def walkK {β : Type} (root : Bool) (hi nF : Nat) (crest : EIdx) (ns : NestState)
    (K : List NestFieldKind → List EIdx → EIdx → NestState → EIdx → AM β) : AM β := do
  let (ks, nds, cur, ns2) ←
    if _h : root = true then do
      let fuelC ← ConRon.Arena.whnfWalkFuel crest
      ConRon.Arena.nestFields mode fe ctx fuelC prog hi nF 0 crest ns [] []
    else ConRon.Arena.nestFields mode fe ctx fuel prog hi nF 0 crest ns [] []
  let closed ← ConRon.Arena.closeTelescope nds hi cur
  K ks nds cur ns2 closed

end pieces

end L.Ind

end
