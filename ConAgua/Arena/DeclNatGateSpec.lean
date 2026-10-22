import ConAgua.Arena.DeclNatOpEq
import ConAgua.Arena.DeclArmDefn

/-!
# `defn_nat_gate` refines `natGateT` (lane `decls3`, helper `decls3-nat`)

The definition arm's structural-`Nat` gate: `nat_op_names`, `sl_contains`, and for a member the
guard, the stored dependencies, the stored value's equations certified at the pre-insertion view.
-/

set_option experimental.vcgen true
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind

section gate
variable {dn : NIdx → Option ConLeche.Name} {p : Prog}

def defnNatCertW (p : Prog) (k : Nat) (m : Mem) (vis w n : Word) : Option (List Word × Mem) :=
  bW (callW p k "env_find" [n, w] m) fun r6 m6 =>
  if r6.headD 0 = 0 then none else
  if rdW (m6.arr64 EREC) (r6.tail.headD 0) ≠ 1 then none else
  bW (callW p k "nat_op_equations" [0, n] m6) fun r7 m7 =>
  bW (callW p k "subst_const0_pairs" [n, rdW (m7.arr64 EREC) (r6.tail.headD 0 + 5), r7.headD 0, r7.tail.headD 0] m7)
    fun r8 m8 =>
  bW (callW p k "certify_nat_eqs" [vis, r8.headD 0, r8.tail.headD 0] m8) fun r9 m9 =>
  if r9.headD 0 = 0 then none else some ([0], m9)

set_option maxHeartbeats 6400000 in
theorem defnNatCert_specW (p : Prog) (hp : p.lookup "defn_nat_cert" = some defnNatCert) (k : Nat) (s₀ : St)
    (vis w n : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "defn_nat_cert" [vis, w, n]
    ⦃fun r s' => LocEq s' s₀ ∧ defnNatCertW p k s₀.mem vis w n = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, defnNatCert]
  vcgen [exec, step, evalE, L.evalC_spec, evalArgs, setLoc, setLocs, ld64,
    callW_spec p k "env_find", callW_spec p k "nat_op_equations", callW_spec p k "subst_const0_pairs",
    callW_spec p k "certify_nat_eqs"]
  all_goals (try simp only [Cond.pval, Expr.pval, Cmp.eval, Bool.or_eq_true, decide_eq_true_eq, rd64_eq_rdW, getElem_rdW'] at *)
  all_goals grind (gen := 20) (instances := 10000) [lang_grind, arena_grind, defnNatCertW, bW]

def defnNatGateW (p : Prog) (k : Nat) (m : Mem) (vis w n : Word) : Option (List Word × Mem) :=
  bW (callW p k "nat_op_names" [] m) fun r1 m1 =>
  bW (callW p k "sl_contains" [r1.headD 0, r1.tail.headD 0, n] m1) fun r2 m2 =>
  if r2.headD 0 = 0 then some ([0], m2) else
  bW (callW p k "nat_op_guard" [w, n] m2) fun r3 m3 =>
  bW (callW p k "nat_op_deps" [n] m3) fun r4 m4 =>
  bW (callW p k "nat_op_stored_ok_all" [w, r4.headD 0, r4.tail.headD 0] m4) fun r5 m5 =>
  if r3.headD 0 = 0 ∨ r5.headD 0 = 0 then none else
  bW (callW p k "defn_nat_cert" [vis, w, n] m5) fun r6 m6 => some ([0], m6)

set_option maxHeartbeats 6400000 in
theorem defnNatGate_specW (p : Prog) (hp : p.lookup "defn_nat_gate" = some defnNatGate) (k : Nat) (s₀ : St)
    (vis w n : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "defn_nat_gate" [vis, w, n]
    ⦃fun r s' => LocEq s' s₀ ∧ defnNatGateW p k s₀.mem vis w n = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, defnNatGate]
  vcgen [exec, step, evalE, L.evalC_spec, evalArgs, setLoc, setLocs, ld64,
    callW_spec p k "nat_op_names", callW_spec p k "sl_contains", callW_spec p k "nat_op_guard",
    callW_spec p k "nat_op_deps", callW_spec p k "nat_op_stored_ok_all", callW_spec p k "defn_nat_cert"]
  all_goals (try simp only [Cond.pval, Expr.pval, Cmp.eval, Bool.or_eq_true, decide_eq_true_eq, rd64_eq_rdW] at *)
  all_goals grind (gen := 20) (instances := 10000) [lang_grind, arena_grind, defnNatGateW, bW]

end gate

end L.Arena
