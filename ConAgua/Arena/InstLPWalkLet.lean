import ConAgua.Arena.InstLPWalk

/-!
# The `instLP` walk: the spec of `lp_let`

The third child and the rebuild are `lp_let_tail`'s (`lpLetTail_spec`), so that this spec has
the two-child arms' shape.

Split from `InstLPWalk.lean` (the models) for build parallelism.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

section specs
variable (p : Prog) (hp : ILWProg p)
include hp

set_option maxHeartbeats 1000000 in
theorem lpLet_spec (n : Nat) (s₀ : St) (h ko kc vo vc fu : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "lp_let" [h, ko, kc, vo, vc, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ ilwLetW p n s₀.mem h ko kc vo vc fu = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.le]
  simp only [callFn, lpLet]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE,
      memoFindG_spec lpSch p _ hp.ilpf n, memoPutG_spec lpSch p _ hp.ilpp n,
      callW_spec p n "lp_go", callW_spec p n "lp_let_tail"] <;>
    finish (gen := 20) (instances := 5000) [ilwLetW, ilwProbe, msetG, tierW, idxW]
end specs

end L.Arena
