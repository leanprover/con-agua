import ConRon.Arena.Inductives.BlockInstall
import Std.Tactic.BVDecide.Normalize.Prop
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.WP.Tactic
import ConAgua.L.Examples

/-!
# LvlEqFueledSpecC

`agreeBodyAM`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- The per-member body of `checkBlockAgree` after member 0's telescope `fvs0` is opened. -/
def agreeBodyAM (fe : IFEnv) (nP : Nat) (fvs0 : List EIdx) (cvTa : IConstantVal) (s s₀ : LIdx) :
    AM Unit := do
  let tq ← unwrapOr (← openPisAtFvarsF nP cvTa.type 0)
    (.invalid "parameters of all inductive datatypes must match")
  unless tq.1.length == fvs0.length do
    fail (.invalid "parameters of all inductive datatypes must match")
  let doms ← fvarTypeDs fvs0
  ConRon.Arena.checkBlockDomsAt V fe 0 tq.1 doms nP
  unless ← liftFueled "level comparison" (← lvlEq? s s₀) do
    fail (.invalid "mutually inductive types must live in the same universe")

end L.Ind

end
