import ConAgua.Arena.IndInstall
import ConAgua.Arena.WhnfBase
import ConAgua.Scan.Common
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic

/-!
# Icr

`icrK`, `icrW`, `icrK_some`, `icr_spec`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## `check_block_rec` -/

def icrK : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0], m)

/-- **The model of `check_block_rec`** (body fuel `n`). -/
def icrW (p : Prog) (n : Nat) (m : Mem) (vis pp nested pO pL tO tL rd mO mL bO bL cO cL : Word) :
    Option (List Word × Mem) :=
  icrK (callW p n "gen_rec_check" [vis, pp, nested, pO, pL, tO, tL, rd, mO, mL, cO, cL, bO, bL] m)

theorem icrK_some (r : List Word) (m : Mem) : icrK (some (r, m)) =
    some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0], m) := rfl
attribute [ind_grind] icrK_some

theorem icr_spec (p : Prog) (hp : p.lookup "check_block_rec" = some checkBlockRec) (n : Nat) (s₀ : St)
    (vis pp nested pO pL tO tL rd mO mL bO bL cO cL : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 1)) "check_block_rec"
      [vis, pp, nested, pO, pL, tO, tL, rd, mO, mL, bO, bL, cO, cL]
    ⦃fun r s' => LocEq s' s₀ ∧ icrW p n s₀.mem vis pp nested pO pL tO tL rd mO mL bO bL cO cL =
      some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkBlockRec]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "gen_rec_check"] <;>
    finish (gen := 40) (instances := 20000) [icrW]

end L.Ind

end
