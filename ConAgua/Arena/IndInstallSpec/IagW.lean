import ConAgua.Arena.IndInstallSpec.LvlEqFueledSpecC
import ConAgua.Arena.IndRealSpine
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr

/-!
# IagW

`installIteBind`, `installAgree_cons` (the twin's `checkBlockAgree` at a member), `AgreeProg`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

theorem installIteBind {α β : Type} (c : Prop) [Decidable c] (x y : AM α) (f : α → AM β) :
    ((if c then x else y) >>= f) = if c then x >>= f else y >>= f := by
  split <;> rfl

/-- The twin's `checkBlockAgree` at a member: member 0's telescope, the member's body, the rest. -/
theorem installAgree_cons (fe : IFEnv) (nP : Nat) (cvTa₀ cvTa : IConstantVal) (s₀ s : LIdx)
    (rest : List (IConstantVal × LIdx)) :
    ConRon.Arena.checkBlockAgree V fe nP cvTa₀ s₀ ((cvTa, s) :: rest) =
      (openPisAtFvarsF nP cvTa₀.type 0 >>= fun x =>
        unwrapOr x (.internal "block: type former telescope") >>= fun tq₀ =>
        agreeBodyAM fe nP tq₀.1 cvTa s s₀ >>= fun _ =>
        ConRon.Arena.checkBlockAgree V fe nP cvTa₀ s₀ rest) := by
  simp only [ConRon.Arena.checkBlockAgree, agreeBodyAM, bind_assoc, installIteBind, pure_bind]

/-- The lookups of `check_block_agree`. -/
structure AgreeProg (p : Prog) : Prop where
  doms : p.lookup "check_block_doms_at" = some checkBlockDomsAt
  lvl : p.lookup "lvl_eq_fueled" = some lvlEqFueled
  one : p.lookup "check_block_agree_one" = some checkBlockAgreeOne
  agree : p.lookup "check_block_agree" = some checkBlockAgree
  ad : AdF p

end L.Ind

end
