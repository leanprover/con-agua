import ConAgua.Arena.DerRel

/-!
# `has_loose_bvar(h, i)`: does `h` have a loose bound variable at index `i` or above?

con-leche (and Lean4's own kernel): `Expr.hasLooseBVar e i := i < e.looseBVarRange`, read directly
off the node's cached range field — no recursion needed, because every node (L's and con-ron's
arena's alike) already carries its derived range word (`ExprMk.lean`'s `der_b`, `DerRel.lean`'s
`DerR`). Unlike the other walks in this file group, this one has no twin *arena* function to
refine against: con-ron's `has_loose_bvar_b_go`/`_memo` (`struct_parts.rs`) are a different,
inductive-types-flavoured twin, threaded through extra context (`T`) that is not part of
`ConRon.Arena.ExprOps`. So `has_loose_bvar` is refined directly against the mathematical
definition, stated over `a.store.derived`'s range field (`bvarOfData`), which `der_b` already
computes exactly (`derBW_ok`).
-/

open ConRon.Arena ConLeche
set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- **The model of `has_loose_bvar`**: `1` iff `i` is below `h`'s derived range. -/
def hasLooseBVarW (m : Mem) (h i : Word) : Word := if i < derBW m h then 1 else 0

/-- con-leche: ConLeche/Kernel/Inductives/StructParts.lean:102-115 ConLeche.Expr.hasLooseBVar -/
def hasLooseBVar : FunDecl := lfn (h, i) locals (x) {
  x := call der_b(h);
  return u64(i < x)
}

theorem hasLooseBVar_spec (p : Prog) (hd : p.lookup "der_b" = some derB)
    (hp : p.lookup "has_loose_bvar" = some hasLooseBVar) (n : Nat) (s₀ : St) (h i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "has_loose_bvar" [h, i]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ r.headD 0 = hasLooseBVarW s₀.mem h i; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, hasLooseBVar]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, derB_spec p hd n] <;>
      finish [hasLooseBVarW]

/-- **`has_loose_bvar(h, i)` is `Expr.hasLooseBVar h i`**: `i` below `h`'s loose-bvar range, i.e.
the range field of `a.store.derived (decE h)`, under `ArenaD`. -/
theorem hasLooseBVarW_ok (m : Mem) (a : AState) (hA : ArenaD m a) (h i : Word)
    (hh : h.toNat < 2 ^ 32) :
    hasLooseBVarW m h i = 1 ↔ i.toNat < (bvarOfData (a.store.derived (decE h))).toNat := by
  simp only [hasLooseBVarW, derBW_ok m a hA.1 hA.2 h hh, UInt64.lt_iff_toNat_lt]
  split <;> simp_all

end L.Arena
