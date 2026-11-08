module

public import ConAgua.Arena.IndInstall
public import ConAgua.Arena.WhnfBase
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
public import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.IndInstall

@[expose] public section

/-!
# Icp

`bpMem`, `icprK`, `icprW`, `icpr_spec`: `check_block_pass_rec`'s model (the pass's record).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `check_block_pass` -/

/-- The memory after the record's nineteen writes (`q` the allocation). -/
def bpMem (m : Mem) (q fe1 cO cL p1 aO aL sO sL kO kL nO nL pO pL rd mO mL tO tL : Word) : Mem :=
  ((((((((((((((((((m.set64 IW q fe1).set64 IW (q + 1) cO).set64 IW (q + 2) cL).set64 IW (q + 3) p1
    ).set64 IW (q + 4) aO).set64 IW (q + 5) aL).set64 IW (q + 6) sO).set64 IW (q + 7) sL
    ).set64 IW (q + 8) kO).set64 IW (q + 9) kL).set64 IW (q + 10) nO).set64 IW (q + 11) nL
    ).set64 IW (q + 12) pO).set64 IW (q + 13) pL).set64 IW (q + 14) rd).set64 IW (q + 15) mO
    ).set64 IW (q + 16) mL).set64 IW (q + 17) tO).set64 IW (q + 18) tL

/-! ### `check_block_pass_rec` -/

def icprK : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)

/-- **The model of `check_block_pass_rec(…)`** (body fuel `n`): the allocation, then the writes. -/
def icprW (p : Prog) (n : Nat) (m : Mem) (fe1 cO cL p1 aO aL sO sL kO kL nO nL pO pL rd mO mL tO tL : Word) :
    Option (List Word × Mem) :=
  match callW p n "iw_alloc" [19] m with
  | none => none
  | some (rq, m1) => some ([rq.headD 0], bpMem m1 (rq.headD 0) fe1 cO cL p1 aO aL sO sL kO kL nO nL pO pL rd
      mO mL tO tL)

set_option maxHeartbeats 1600000 in
theorem icpr_spec (p : Prog) (hp : p.lookup "check_block_pass_rec" = some checkBlockPassRec) (n : Nat)
    (s₀ : St) (fe1 cO cL p1 aO aL sO sL kO kL nO nL pO pL rd mO mL tO tL : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 1)) "check_block_pass_rec"
      [fe1, cO, cL, p1, aO, aL, sO, sL, kO, kL, nO, nL, pO, pL, rd, mO, mL, tO, tL]
    ⦃fun r s' => LocEq s' s₀ ∧ icprW p n s₀.mem fe1 cO cL p1 aO aL sO sL kO kL nO nL pO pL rd mO mL tO tL =
      some (r, s'.mem); ⊤⦄ := by
  sorry

end L.Ind
