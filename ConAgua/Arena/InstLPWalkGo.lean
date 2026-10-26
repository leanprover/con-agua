import ConAgua.Arena.InstLPWalk
import ConAgua.L.PureEval

/-!
# The `instLP` walk: the spec of `lp_go`

Split from `InstLPWalk.lean` (the models) for build parallelism.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

private theorem getElem_toNat_rdW {a : Array Word} {x : Word} (h : x.toNat < a.size) :
    a[x.toNat] = rdW a x := (rdW_eq a x _ rfl h).symm

private theorem rd64_rdW (m : Mem) (a : ArrId) (i : Word) : L.rd64 m a i = rdW (m.arr64 a) i := by
  simp [L.rd64, rdW, Array.getD_eq_getD_getElem?]

section specs
variable (p : Prog) (hp : ILWProg p)
include hp

set_option maxHeartbeats 5000000 in
theorem lpGo_spec (n : Nat) (s₀ : St) (h ko kc vo vc fu : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "lp_go" [h, ko, kc, vo, vc, fu]
    ⦃fun r s' => LocEq s' s₀ ∧ ilwGoW p n s₀.mem h ko kc vo vc fu = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.go]
  simp only [callFn, lpGo]
  vcgen [exec, step, evalE, L.evalC_spec, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE,
    callW_spec p n "der_b", callW_spec p n "sl_memo", callW_spec p n "sls_memo",
    callW_spec p n "intern_sort", callW_spec p n "intern_const", callW_spec p n "lp_fvar",
    callW_spec p n "lp_app", callW_spec p n "lp_lam", callW_spec p n "lp_forall",
    callW_spec p n "lp_let", callW_spec p n "lp_proj"]
  all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
    Locals.init_cons_zero, Locals.init_cons_succ, Cmp.eval, BinOp.eval, Nat.reduceEqDiff,
    reduceIte, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq, Cond.pval, Expr.pval,
    Bool.and_eq_true, rd64_rdW, Expr.pval_cntE] at *)
  all_goals grind (gen := 20) [lang_grind, arena_grind, ilwGoW, ilwDispW_sc, ilwDispW_bvar, ilwDispW_lit,
    ilwDispW_sort, ilwDispW_const, ilwDispW_fvar, ilwDispW_app, ilwDispW_lam, ilwDispW_forall, ilwDispW_let,
    ilwDispW_proj, ilwDispW_other, tierW, idxW]
end specs

end L.Arena
