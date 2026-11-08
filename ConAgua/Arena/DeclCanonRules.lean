module

import ConAgua.Arena.DeclCanonEq
public import ConAgua.Arena.DeclCanonExpr2
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.Arena.DeclRec
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
import all ConAgua.Arena.DeclArmsCanon

@[expose] public section

/-!
# `canon_rules_eq` (lane `decls3`, helper `decls3-canon`)
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

mutual
/-- **The model of `canon_rules_eq`**. -/
def cnCrW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ => none
  | k + 1, m, po, pl, qo, ql, co, cl, fuel, o1, l1, o2, l2 =>
    if l1 = 0 ∧ l2 = 0 then some (1, m)
    else if l1 = 0 ∨ l2 = 0 then some (0, m)
    else crK0 k m po pl qo ql co cl fuel o1 l1 o2 l2
      (if ruleEqButRhsB (m.arr64 EREC) o1 o2 then 1 else 0)

/-- After `rule_eq_but_rhs`. -/
def crK0 (k : Nat) (m : Mem) (po pl qo ql co cl fuel o1 l1 o2 l2 e : Word) : Option (Word × Mem) :=
  if e = 0 then some (0, m)
  else cnCrK1 k po pl qo ql co cl fuel o1 l1 o2 l2
    (ceW k m po pl qo ql co cl fuel (rdW (m.arr64 EREC) (o1 + 8)) (rdW (m.arr64 EREC) (o2 + 8)))

/-- After `canon_expr_eq`. -/
def cnCrK1 (k : Nat) (po pl qo ql co cl fuel o1 l1 o2 l2 : Word) : Option (Word × Mem) →
    Option (Word × Mem)
  | none => none
  | some (e, m1) =>
    if e = 0 then some (0, m1)
    else cnCrW k m1 po pl qo ql co cl fuel (o1 + 11) (l1 - 1) (o2 + 11) (l2 - 1)
end

section arms
variable (k : Nat) (m m1 : Mem) (po pl qo ql co cl fuel o1 l1 o2 l2 e : Word)
theorem crW_succ : cnCrW (k + 1) m po pl qo ql co cl fuel o1 l1 o2 l2 =
    (if l1 = 0 ∧ l2 = 0 then some (1, m)
    else if l1 = 0 ∨ l2 = 0 then some (0, m)
    else crK0 k m po pl qo ql co cl fuel o1 l1 o2 l2
      (if ruleEqButRhsB (m.arr64 EREC) o1 o2 then 1 else 0)) := by rw [cnCrW]
theorem crK0_def : crK0 k m po pl qo ql co cl fuel o1 l1 o2 l2 e =
    (if e = 0 then some (0, m)
    else cnCrK1 k po pl qo ql co cl fuel o1 l1 o2 l2
      (ceW k m po pl qo ql co cl fuel (rdW (m.arr64 EREC) (o1 + 8)) (rdW (m.arr64 EREC) (o2 + 8)))) :=
  by rw [crK0]
theorem crK1_some : cnCrK1 k po pl qo ql co cl fuel o1 l1 o2 l2 (some (e, m1)) =
    (if e = 0 then some (0, m1)
    else cnCrW k m1 po pl qo ql co cl fuel (o1 + 11) (l1 - 1) (o2 + 11) (l2 - 1)) := by rw [cnCrK1]
end arms

grind_pattern [ind_grind] crW_succ => cnCrW (k + 1) m po pl qo ql co cl fuel o1 l1 o2 l2
grind_pattern [ind_grind] crK0_def => crK0 k m po pl qo ql co cl fuel o1 l1 o2 l2 e
grind_pattern [ind_grind] crK1_some => cnCrK1 k po pl qo ql co cl fuel o1 l1 o2 l2 (some (e, m1))

section specs6
variable (p : Prog) (hp : CanonProg p)
include hp

set_option maxHeartbeats 4000000 in
theorem canonRulesEq_spec (n : Nat) : ∀ (s₀ : St) (po pl qo ql co cl fuel o1 l1 o2 l2 : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "canon_rules_eq"
      [po, pl, qo, ql, co, cl, fuel, o1, l1, o2, l2]
    ⦃fun x s' => LocEq s' s₀ ∧ cnCrW n s₀.mem po pl qo ql co cl fuel o1 l1 o2 l2 = some (x.headD 0, s'.mem);
      ⊤⦄ := by
  sorry

end specs6


theorem decRules_length {a : Array Word} {o l : Nat} {xs : List IRecRule}
    (h : decRules (aread a) o l = some xs) : xs.length = l := by
  have := mapM_opt_length _ _ _ h
  simpa using this

theorem cnCrW_ok {vis : Word} {fe : IFEnv} (k : Nat) :
    ∀ (m m' : Mem) (a : AState) (po pl qo ql co cl fuel o1 l1 o2 l2 x : Word) (ps qs cs : List NIdx)
      (xs ys : List IRecRule),
    cnCrW k m po pl qo ql co cl fuel o1 l1 o2 l2 = some (x, m') → StageR vis fe m a →
    CtxR m po pl qo ql co cl ps qs cs → LitInj a → PoolSmall m →
    decRules (erecP m) o1.toNat l1.toNat = some xs → decRules (erecP m) o2.toNat l2.toNat = some ys →
    ∃ b, (ConRon.Arena.canonRulesEq ps qs cs fuel.toNat xs ys).run a = .ok (b, a) ∧
      x = (if b then 1 else 0) ∧ StageR vis fe m' a ∧ IWGrow m m' ∧ PoolSmall m' := by
  sorry

/-- **`canon_rules_eq` refines `canonRulesEq`.** -/
@[refines ConRon.Arena.canonRulesEq]
theorem canonRulesEq_refines (p : Prog) (hp : CanonProg p) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (po pl qo ql co cl fuel o1 l1 o2 l2 : Word) (ps qs cs : List NIdx)
    (xs ys : List IRecRule) :
    RefAM p "canon_rules_eq" [po, pl, qo, ql, co, cl, fuel, o1, l1, o2, l2]
      (fun m a => StageR vis fe m a ∧ CtxR m po pl qo ql co cl ps qs cs ∧ LitInj a ∧
        PoolSmall m ∧ decRules (erecP m) o1.toNat l1.toNat = some xs ∧
        decRules (erecP m) o2.toNat l2.toNat = some ys)
      (ConRon.Arena.canonRulesEq ps qs cs fuel.toNat xs ys) (CPostL dn vis fe decW0B) := by
  sorry

end L.Ind
