import ConAgua.Arena.InstLPWalk
import ConAgua.L.PureEval

/-!
# The `instLP` walk: the spec of `lp_let`

Split from `InstLPWalk.lean` (the models) for build parallelism.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false

namespace L.Arena

/-- `L.rd64` is `rdW` (`evalE_spec`'s reads). -/
theorem rd64_rdW (m : Mem) (a : ArrId) (i : Word) : L.rd64 m a i = rdW (m.arr64 a) i := by
  simp [L.rd64, rdW]

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
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      memoFindG_spec lpSch p _ hp.ilpf n, memoPutG_spec lpSch p _ hp.ilpp n,
      callW_spec p n "lp_go", callW_spec p n "mk_let"] <;>
    finish (gen := 20) [ilwLetW, ilwProbe, msetG, tierW, idxW]
end specs

end L.Arena
