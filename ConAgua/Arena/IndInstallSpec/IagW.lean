module

public import ConAgua.Arena.IndInstallSpec.LvlEqFueledSpecC
public import ConAgua.Arena.IndRealSpine
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.Arena.Verdict

@[expose] public section

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

/-- The twin's `checkBlockAgree` at a member: member 0's telescope, the member's body, the rest. -/
theorem installAgree_cons (fe : IFEnv) (nP : Nat) (cvTa₀ cvTa : IConstantVal) (s₀ s : LIdx)
    (rest : List (IConstantVal × LIdx)) :
    ConRon.Arena.checkBlockAgree V fe nP cvTa₀ s₀ ((cvTa, s) :: rest) =
      (openPisAtFvarsF nP cvTa₀.type 0 >>= fun x =>
        unwrapOr x (.internal "block: type former telescope") >>= fun tq₀ =>
        agreeBodyAM fe nP tq₀.1 cvTa s s₀ >>= fun _ =>
        ConRon.Arena.checkBlockAgree V fe nP cvTa₀ s₀ rest) := by
  simp only [ConRon.Arena.checkBlockAgree, agreeBodyAM, bind_assoc, L.Arena.ite_bindAM, pure_bind]

/-- The lookups of `check_block_agree`. -/
structure AgreeProg (p : Prog) : Prop where
  doms : p.lookup "check_block_doms_at" = some checkBlockDomsAt
  lvl : p.lookup "lvl_eq_fueled" = some lvlEqFueled
  one : p.lookup "check_block_agree_one" = some checkBlockAgreeOne
  agree : p.lookup "check_block_agree" = some checkBlockAgree
  ad : AdF p

end L.Ind

end
