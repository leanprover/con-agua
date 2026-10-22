import ConAgua.Arena.InstLPWalk

/-!
# The `instLP` walk: the spec of `lp_go`

Split from `InstLPWalk.lean` (the models) for build parallelism.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false

namespace L.Arena

section specs
variable (p : Prog) (hp : ILWProg p)
include hp

set_option maxHeartbeats 1000000 in
theorem lpGo_spec (n : Nat) (s₀ : St) (h ko kc vo vc fu : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "lp_go" [h, ko, kc, vo, vc, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ ilwGoW p n s₀.mem h ko kc vo vc fu = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.go]
  simp only [callFn, lpGo]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "der_b", callW_spec p n "sl_memo", callW_spec p n "sls_memo",
      callW_spec p n "intern_sort", callW_spec p n "intern_const", callW_spec p n "lp_fvar",
      callW_spec p n "lp_app", callW_spec p n "lp_lam", callW_spec p n "lp_forall",
      callW_spec p n "lp_let", callW_spec p n "lp_proj"] <;>
    finish (gen := 20) [ilwGoW, ilwDispW_sc, ilwDispW_bvar, ilwDispW_lit, ilwDispW_sort, ilwDispW_const,
      ilwDispW_fvar, ilwDispW_app, ilwDispW_lam, ilwDispW_forall, ilwDispW_let, ilwDispW_proj,
      ilwDispW_other, tierW, idxW]
end specs

end L.Arena
