module

public import ConAgua.Arena.Abs1Spec
meta import ConAgua.L.Semantics
meta import ConAgua.Arena.Store
import ConAgua.Census.Attr

@[expose] public section

/-!
# `hasFvarFast`: the fvar-range field read

con-ron's `hasFvarFast fuel e = (fvarB fuel e != 0)`: `ab_fvb` (`Abs1.lean`) and a compare.
`has_fvar_fast(f, e)` is the interface the declaration and inductive lanes call (`f` the twin's
fuel, passed to `ab_fvb` as the walk's depth counter); `has_fvar(e)` the knot's,
at the core's `coreWalkFuel` (`4000000000`).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- After `ab_fvb`: the range is nonzero. -/
def hfK : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (x, m₁) => some (if x ≠ 0 then 1 else 0, m₁)

theorem hfK_some (x : Word) (m₁ : Mem) : hfK (some (x, m₁)) = some (if x ≠ 0 then 1 else 0, m₁) :=
  rfl

attribute [arena_grind =] hfK_some

/-- con-ron: ConRon/Arena/ExprOps.lean:1582-1586 ConRon.Arena.hasFvarFast -/
@[l_impl ConRon.Arena.hasFvarFast]
def hasFvarFastL : FunDecl := lfn (f, e) locals (x) {
  x := call ab_fvb(e, f);
  return u64(x != 0)
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1582-1586 ConRon.Arena.hasFvarFast -/
@[l_impl ConRon.Arena.hasFvarFast]
def hasFvarL : FunDecl := lfn (e) locals (x) {
  x := call ab_fvb(e, 4000000000);
  return u64(x != 0)
}

section specs
variable (p : Prog) (hp : AbsProg p)

include hp in
theorem hasFvarFastL_spec (hpf : p.lookup "has_fvar_fast" = some hasFvarFastL) (n : Nat) (s₀ : St)
    (f e : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "has_fvar_fast" [f, e]
    ⦃fun r s' => LocEq s' s₀ ∧ hfK (fvbW n s₀.mem e f) = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hpf]
  simp only [callFn, hasFvarFastL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, abFvb_spec p hp n] <;>
    finish

include hp in
theorem hasFvarL_spec (hpf : p.lookup "has_fvar" = some hasFvarL) (n : Nat) (s₀ : St) (e : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "has_fvar" [e]
    ⦃fun r s' => LocEq s' s₀ ∧ hfK (fvbW n s₀.mem e 4000000000) = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hpf]
  simp only [callFn, hasFvarL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, abFvb_spec p hp n] <;>
    finish

end specs

end L.Arena
