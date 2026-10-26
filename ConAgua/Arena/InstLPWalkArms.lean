import ConAgua.Arena.InstLPWalk

/-!
# The `instLP` walk: the spec of the arms `lp_app`, `lp_lam`, `lp_forall`

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
theorem lpApp_spec (n : Nat) (s₀ : St) (h ko kc vo vc fu : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "lp_app" [h, ko, kc, vo, vc, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ ilwBinW APP "mk_app" p n s₀.mem h ko kc vo vc fu = some (r.headD 0, s'.mem);
      ⊤⦄ := by
  rw [invoke_eq _ hp.app]
  simp only [callFn, lpApp]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE,
      memoFindG_spec lpSch p _ hp.ilpf n, memoPutG_spec lpSch p _ hp.ilpp n,
      callW_spec p n "lp_go", callW_spec p n "mk_app"] <;>
    finish (gen := 20) [ilwBinW, ilwProbe, msetG, tierW, idxW]
set_option maxHeartbeats 1000000 in
theorem lpLam_spec (n : Nat) (s₀ : St) (h ko kc vo vc fu : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "lp_lam" [h, ko, kc, vo, vc, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ ilwBinW LAM "mk_lam" p n s₀.mem h ko kc vo vc fu = some (r.headD 0, s'.mem);
      ⊤⦄ := by
  rw [invoke_eq _ hp.lam]
  simp only [callFn, lpLam]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE,
      memoFindG_spec lpSch p _ hp.ilpf n, memoPutG_spec lpSch p _ hp.ilpp n,
      callW_spec p n "lp_go", callW_spec p n "mk_lam"] <;>
    finish (gen := 20) [ilwBinW, ilwProbe, msetG, tierW, idxW]
set_option maxHeartbeats 1000000 in
theorem lpForall_spec (n : Nat) (s₀ : St) (h ko kc vo vc fu : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "lp_forall" [h, ko, kc, vo, vc, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ ilwBinW FORALL "mk_forall" p n s₀.mem h ko kc vo vc fu = some (r.headD 0, s'.mem);
      ⊤⦄ := by
  rw [invoke_eq _ hp.fa]
  simp only [callFn, lpForall]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE,
      memoFindG_spec lpSch p _ hp.ilpf n, memoPutG_spec lpSch p _ hp.ilpp n,
      callW_spec p n "lp_go", callW_spec p n "mk_forall"] <;>
    finish (gen := 20) [ilwBinW, ilwProbe, msetG, tierW, idxW]
end specs

end L.Arena
