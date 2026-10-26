import ConAgua.Arena.DeclCanonLvl
import ConAgua.Arena.IndView

/-!
# The canonical expression comparison in L (lane `decls3`, helper `decls3-canon`)

`canon_expr_eq` against `canonExprEq`. A literal is compared by handle in L and by value in the
twin: the two agree because the expression store hash-conses literals (`LitInj`, a hypothesis).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

mutual
/-- **The model of `canon_expr_eq`**. -/
def ceW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Option (Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, po, pl, qo, ql, co, cl, fuel, a, b =>
    if fuel = 0 then none
    else ceK0 n m po pl qo ql co cl fuel a b (eViewW m a) (eViewW m b)

/-- After the two `e_view` calls. -/
def ceK0 (n : Nat) (m : Mem) (po pl qo ql co cl fuel a b : Word) (ru rv : List Word) :
    Option (Word × Mem) :=
  if ru = [] ∨ rv = [] then none
  else if ru.headD 0 ≠ rv.headD 0 then some (0, m)
  else if ru.headD 0 = 0 then some (if ru.tail.headD 0 = rv.tail.headD 0 then 1 else 0, m)
  else if ru.headD 0 = 1 then
    if ru.tail.headD 0 ≠ rv.tail.headD 0 then some (0, m)
    else ceW n m po pl qo ql co cl (fuel - 1) (ru.tail.tail.headD 0) (rv.tail.tail.headD 0)
  else if ru.headD 0 = 2 then
    ceKL n m (cnClW n m po pl qo ql co cl (fuel - 1) (ru.tail.headD 0) (rv.tail.headD 0))
  else if ru.headD 0 = 3 then
    if ru.tail.headD 0 ≠ rv.tail.headD 0 then some (0, m)
    else ceKS (lsEqW n m po pl qo ql co cl (fuel - 1) (ru.tail.tail.headD 0) (rv.tail.tail.headD 0))
  else if ru.headD 0 = 4 ∨ ru.headD 0 = 5 ∨ ru.headD 0 = 6 then
    ceK1 n po pl qo ql co cl fuel (ru.tail.tail.headD 0) (rv.tail.tail.headD 0)
      (ceW n m po pl qo ql co cl (fuel - 1) (ru.tail.headD 0) (rv.tail.headD 0))
  else if ru.headD 0 = 7 then
    ceK2 n po pl qo ql co cl fuel (ru.tail.tail.headD 0) (rv.tail.tail.headD 0)
      (ru.tail.tail.tail.headD 0) (rv.tail.tail.tail.headD 0)
      (ceW n m po pl qo ql co cl (fuel - 1) (ru.tail.headD 0) (rv.tail.headD 0))
  else if ru.headD 0 = 8 then some (if a = b then 1 else 0, m)
  else if ru.tail.headD 0 ≠ rv.tail.headD 0 ∨ ru.tail.tail.headD 0 ≠ rv.tail.tail.headD 0 then
    some (0, m)
  else ceW n m po pl qo ql co cl (fuel - 1) (ru.tail.tail.tail.headD 0) (rv.tail.tail.tail.headD 0)

/-- A level comparison's result, memory unchanged. -/
def ceKL (n : Nat) (m : Mem) : Option Word → Option (Word × Mem)
  | none => none
  | some r => some (r, m)

/-- A level-list comparison's result. -/
def ceKS : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some x => some x

/-- After the first child of a binary node. -/
def ceK1 (n : Nat) (po pl qo ql co cl fuel y y2 : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m1) =>
    if r = 0 then some (0, m1) else ceW n m1 po pl qo ql co cl (fuel - 1) y y2

/-- After the first child of a `letE`. -/
def ceK2 (n : Nat) (po pl qo ql co cl fuel y y2 z z2 : Word) : Option (Word × Mem) →
    Option (Word × Mem)
  | none => none
  | some (r, m1) =>
    if r = 0 then some (0, m1)
    else ceK3 n po pl qo ql co cl fuel z z2 (ceW n m1 po pl qo ql co cl (fuel - 1) y y2)

/-- After the second child of a `letE`. -/
def ceK3 (n : Nat) (po pl qo ql co cl fuel z z2 : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (r, m2) =>
    if r = 0 then some (0, m2) else ceW n m2 po pl qo ql co cl (fuel - 1) z z2
end


section arms
variable (n : Nat) (m m1 m2 : Mem) (po pl qo ql co cl fuel a b y y2 z z2 r : Word) (ru rv : List Word)
theorem ceW_succ : ceW (n + 1) m po pl qo ql co cl fuel a b =
    (if fuel = 0 then none else ceK0 n m po pl qo ql co cl fuel a b (eViewW m a) (eViewW m b)) := by
  rw [ceW]
theorem ceK0_def : ceK0 n m po pl qo ql co cl fuel a b ru rv =
  (if ru = [] ∨ rv = [] then none
  else if ru.headD 0 ≠ rv.headD 0 then some (0, m)
  else if ru.headD 0 = 0 then some (if ru.tail.headD 0 = rv.tail.headD 0 then 1 else 0, m)
  else if ru.headD 0 = 1 then
    if ru.tail.headD 0 ≠ rv.tail.headD 0 then some (0, m)
    else ceW n m po pl qo ql co cl (fuel - 1) (ru.tail.tail.headD 0) (rv.tail.tail.headD 0)
  else if ru.headD 0 = 2 then
    ceKL n m (cnClW n m po pl qo ql co cl (fuel - 1) (ru.tail.headD 0) (rv.tail.headD 0))
  else if ru.headD 0 = 3 then
    if ru.tail.headD 0 ≠ rv.tail.headD 0 then some (0, m)
    else ceKS (lsEqW n m po pl qo ql co cl (fuel - 1) (ru.tail.tail.headD 0) (rv.tail.tail.headD 0))
  else if ru.headD 0 = 4 ∨ ru.headD 0 = 5 ∨ ru.headD 0 = 6 then
    ceK1 n po pl qo ql co cl fuel (ru.tail.tail.headD 0) (rv.tail.tail.headD 0)
      (ceW n m po pl qo ql co cl (fuel - 1) (ru.tail.headD 0) (rv.tail.headD 0))
  else if ru.headD 0 = 7 then
    ceK2 n po pl qo ql co cl fuel (ru.tail.tail.headD 0) (rv.tail.tail.headD 0)
      (ru.tail.tail.tail.headD 0) (rv.tail.tail.tail.headD 0)
      (ceW n m po pl qo ql co cl (fuel - 1) (ru.tail.headD 0) (rv.tail.headD 0))
  else if ru.headD 0 = 8 then some (if a = b then 1 else 0, m)
  else if ru.tail.headD 0 ≠ rv.tail.headD 0 ∨ ru.tail.tail.headD 0 ≠ rv.tail.tail.headD 0 then
    some (0, m)
  else ceW n m po pl qo ql co cl (fuel - 1) (ru.tail.tail.tail.headD 0) (rv.tail.tail.tail.headD 0)) := by
  rw [ceK0]
theorem ceK1_some : ceK1 n po pl qo ql co cl fuel y y2 (some (r, m1)) =
    (if r = 0 then some (0, m1) else ceW n m1 po pl qo ql co cl (fuel - 1) y y2) := by
  rw [ceK1]
theorem ceK2_some : ceK2 n po pl qo ql co cl fuel y y2 z z2 (some (r, m1)) =
    (if r = 0 then some (0, m1)
    else ceK3 n po pl qo ql co cl fuel z z2 (ceW n m1 po pl qo ql co cl (fuel - 1) y y2)) := by
  rw [ceK2]
theorem ceK3_some : ceK3 n po pl qo ql co cl fuel z z2 (some (r, m2)) =
    (if r = 0 then some (0, m2) else ceW n m2 po pl qo ql co cl (fuel - 1) z z2) := by
  rw [ceK3]
theorem ceKL_some : ceKL n m (some r) = some (r, m) := rfl
theorem ceKS_some (x : Word × Mem) : ceKS (some x) = some x := rfl
end arms

grind_pattern [ind_grind] ceW_succ => ceW (n + 1) m po pl qo ql co cl fuel a b
grind_pattern [ind_grind] ceK0_def => ceK0 n m po pl qo ql co cl fuel a b ru rv
grind_pattern [ind_grind] ceK1_some => ceK1 n po pl qo ql co cl fuel y y2 (some (r, m1))
grind_pattern [ind_grind] ceK2_some => ceK2 n po pl qo ql co cl fuel y y2 z z2 (some (r, m1))
grind_pattern [ind_grind] ceK3_some => ceK3 n po pl qo ql co cl fuel z z2 (some (r, m2))
grind_pattern [ind_grind] ceKL_some => ceKL n m (some r)
grind_pattern [ind_grind] ceKS_some => ceKS (some x)

section specs4
variable (p : Prog) (hp : CanonProg p)
include hp

set_option maxHeartbeats 8000000 in
theorem canonExprEq_spec (n : Nat) : ∀ (s₀ : St) (po pl qo ql co cl fuel a b : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "canon_expr_eq" [po, pl, qo, ql, co, cl, fuel, a, b]
    ⦃fun r s' => LocEq s' s₀ ∧
      ceW n s₀.mem po pl qo ql co cl fuel a b = some (r.headD 0, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ po pl qo ql co cl fuel a b
    rw [invoke_eq _ (hp.get "canon_expr_eq")]; simp only [callFn, canonExprEq]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ po pl qo ql co cl fuel a b
    rw [invoke_eq _ (hp.get "canon_expr_eq")]
    simp only [callFn, canonExprEq]
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      eView_spec p (hp.get "e_view") n, canonLevelEq_spec p hp n, canonLevelsEq_spec p hp n, ih]
    all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
      List.headD_cons, List.headD_nil, List.tail_cons, List.tail_nil, init9_0, init9_1, init9_2,
      init9_3, init9_4, init9_5, init9_6, init9_7, init9_8, Cmp.eval, BinOp.eval, Nat.reduceEqDiff,
      reduceIte, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq] at *)
    all_goals grind (gen := 20) [lang_grind, arena_grind, ind_grind]

end specs4

end L.Ind
