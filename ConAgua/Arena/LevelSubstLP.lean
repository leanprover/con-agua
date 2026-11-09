module

public import ConAgua.Arena.LevelSubstL
public import ConAgua.Arena.WhnfBase
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.LevelGrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# The `instLP` family's own instances of lane `levels`' substitution functions

`LevelSubstL.lean`'s `lv_lookup`, `lv_substl` are generic in their arrays
(the models `lookupW KA VA`, `substLW KA VA`), but they call each other by name, and one name has
one body project-wide: lane `defeq2` binds `lv_lookup` to `lvLookupG EREC POOL` (`field_sort_zero`,
`PropRead`). The `instLP` family keeps its keys on the spine stack (`keys_push`: the record pool's
and lane `induct`'s `IW` slices share one walk), so it gets the two functions under its own names,
at fixed arrays:

* `lp_lookup` = `lvLookupG SPN POOL` renamed (model `lookupW (keyA SPN) POOL`);
* `lp_substl` = `lvSubstL` calling `lp_lookup`/`lp_substl` (model `substLW (keyA SPN) POOL`);

The models and their refinements (`lookupW_ok`, `substLW_ok`) are lane `levels`'
generic ones; only the call-level specs are restated here.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- `lv_lookup` with the keys on the spine stack and the values in the limb pool.
con-leche: ConLeche/Kernel/Level.lean:31-42 ConLeche.Level.subst -/
@[no_expose] def lpLookup : FunDecl := lfn (ko, kc, vo, vc, w) locals (f, v) {
  if kc == 0 || vc == 0 { return (0, 0) };
  if SPN.u64[ko] == w { return (1, POOL⦃vo⦄) };
  (f, v) := call lp_lookup(ko + 1, kc - 1, vo + 1, vc - 1, w);
  return (f, v)
}

/-- `lv_substl` over `lp_lookup`.
con-leche: ConLeche/Kernel/Level.lean:31-42 ConLeche.Level.subst
con-leche: ConLeche/Kernel/Level.lean:31-42 ConLeche.Level.subst.go -/
@[no_expose] def lpSubstL : FunDecl := lfn (l, ko, kc, vo, vc) locals (g, a, b, x, y, f, v) {
  (g, a, b) := call lv_node(l);
  if g == 0 { return l };
  if g == 4 {
    (f, v) := call lp_lookup(ko, kc, vo, vc, a);
    if f != 0 { return v };
    return l
  };
  x := call lp_substl(a, ko, kc, vo, vc);
  if g == 1 { x := call lh_mk(1, x, 0); return x };
  y := call lp_substl(b, ko, kc, vo, vc);
  x := call lh_mk(g, x, y);
  return x
}

section specs
variable (p : Prog) (hpl : p.lookup "lp_lookup" = some lpLookup)

include hpl in
theorem lpLookup_spec (n : Nat) : ∀ (s₀ : St) (ko kc vo vc w : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "lp_lookup" [ko, kc, vo, vc, w]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      lookupW (keyA SPN) POOL n s₀.mem ko kc vo vc w = some (r.headD 0, r.tail.headD 0); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ ko kc vo vc w; rw [invoke_eq _ hpl]; simp only [callFn, lpLookup]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ ko kc vo vc w
    rw [invoke_eq _ hpl]
    simp only [callFn, lpLookup]
    sym only [lang_grind, arena_grind, level_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;>
      finish (gen := 20)

include hpl in
theorem lpSubstL_spec (hpn : p.lookup "lv_node" = some lvNode) (hpm : p.lookup "lh_mk" = some lhMk)
    (hp : p.lookup "lp_substl" = some lpSubstL) (n : Nat) : ∀ (s₀ : St) (l ko kc vo vc : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "lp_substl" [l, ko, kc, vo, vc]
    ⦃fun r s' => LocEq s' s₀ ∧ substLW (keyA SPN) POOL n s₀.mem l ko kc vo vc = some (r.headD 0, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ l ko kc vo vc; rw [invoke_eq _ hp]; simp only [callFn, lpSubstL]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ l ko kc vo vc
    rw [invoke_eq _ hp]
    simp only [callFn, lpSubstL]
    sym only [lang_grind, arena_grind, level_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, lvNode_spec p hpn n,
        lhMk_spec p hpm n, lpLookup_spec p hpl n, ih] <;>
      finish (gen := 20)

end specs

end L.Arena
