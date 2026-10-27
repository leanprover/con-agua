import ConAgua.Arena.LevelSubstL
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.LevelGrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic

/-!
# The `instLP` family's own instances of lane `levels`' substitution functions

`LevelSubstL.lean`'s `lv_lookup`, `lv_substl`, `lv_spw`, `lv_substpw` are generic in their arrays
(the models `lookupW KA VA`, `substLW KA VA`, `spwW KA VA PA`, `substPWW KA VA PA`), but they call
each other by name, and one name has one body project-wide: lane `defeq2` binds `lv_lookup` to
`lvLookupG EREC POOL` (`field_sort_zero`, `PropRead`) and `lv_spw` to `lvSpwG LH`. The `instLP`
family keeps its keys on the spine stack (`keys_push`: the record pool's and lane `induct`'s `IW`
slices share one walk) and `caps_never_zero`'s datum names in the record pool, so it gets the same
four functions under its own names, at fixed arrays:

* `lp_lookup` = `lvLookupG SPN POOL` renamed (model `lookupW SPN POOL`);
* `lp_substl` = `lvSubstL` calling `lp_lookup`/`lp_substl` (model `substLW SPN POOL`);
* `lp_spw` = `lvSpwG EREC` calling `lp_lookup`/`lp_spw` (model `spwW SPN POOL EREC`);
* `lp_substpw` = `lvSubstPW` calling `lp_spw` (model `substPWW SPN POOL EREC`).

The models and their refinements (`lookupW_ok`, `substLW_ok`, `spwW_ok`, …) are lane `levels`'
generic ones; only the call-level specs are restated here.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- `lv_lookup` with the keys on the spine stack and the values in the limb pool.
con-leche: ConLeche/Kernel/Level.lean:31-42 ConLeche.Level.subst -/
def lpLookup : FunDecl := lfn (ko, kc, vo, vc, w) locals (f, v) {
  if kc == 0 || vc == 0 { return (0, 0) };
  if SPN.u64[ko] == w { return (1, POOL⦃vo⦄) };
  (f, v) := call lp_lookup(ko + 1, kc - 1, vo + 1, vc - 1, w);
  return (f, v)
}

/-- `lv_substl` over `lp_lookup`.
con-leche: ConLeche/Kernel/Level.lean:31-42 ConLeche.Level.subst
con-leche: ConLeche/Kernel/Level.lean:31-42 ConLeche.Level.subst.go -/
def lpSubstL : FunDecl := lfn (l, ko, kc, vo, vc) locals (g, a, b, x, y, f, v) {
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

/-- `lv_spw` over `lp_lookup`, the datum's names in the record pool.
con-leche: ConLeche/Kernel/Level.lean:199-205 ConLeche.Level.substPW -/
def lpSpw : FunDecl := lfn (po, pc, ko, kc, vo, vc) locals (f, v, x, w) {
  if pc == 0 { return 0 };
  w := EREC.u64[po];
  (f, v) := call lp_lookup(ko, kc, vo, vc, w);
  if f != 0 { x := call lv_zero(v) } else { x := call lh_push(w); x := 0 };
  if x != 0 { return 1 };
  x := call lp_spw(po + 1, pc - 1, ko, kc, vo, vc);
  return x
}

/-- `lv_substpw` over `lp_spw`.
con-leche: ConLeche/Kernel/Level.lean:199-205 ConLeche.Level.substPW -/
def lpSubstPW : FunDecl := lfn (kd, po, pc, ko, kc, vo, vc) locals (x) {
  if kd == 0 { return 1 };
  x := call lp_spw(po, pc, ko, kc, vo, vc);
  return x
}

section specs
variable (p : Prog) (hpl : p.lookup "lp_lookup" = some lpLookup)

include hpl in
theorem lpLookup_spec (n : Nat) : ∀ (s₀ : St) (ko kc vo vc w : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "lp_lookup" [ko, kc, vo, vc, w]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      lookupW SPN POOL n s₀.mem ko kc vo vc w = some (r.headD 0, r.tail.headD 0); ⊤⦄ := by
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
    ⦃fun r s' => LocEq s' s₀ ∧ substLW SPN POOL n s₀.mem l ko kc vo vc = some (r.headD 0, s'.mem); ⊤⦄ := by
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

include hpl in
theorem lpSpw_spec (hpn : p.lookup "lv_node" = some lvNode) (hpp : p.lookup "lh_push" = some lhPush)
    (hpz : p.lookup "lv_zero" = some lvZero) (hp : p.lookup "lp_spw" = some lpSpw) (n : Nat) :
    ∀ (s₀ : St) (po pc ko kc vo vc : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "lp_spw" [po, pc, ko, kc, vo, vc]
    ⦃fun r s' => LocEq s' s₀ ∧
      spwW SPN POOL EREC n s₀.mem po pc ko kc vo vc = some (r.headD 0, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ po pc ko kc vo vc; rw [invoke_eq _ hp]; simp only [callFn, lpSpw]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ po pc ko kc vo vc
    rw [invoke_eq _ hp]
    simp only [callFn, lpSpw]
    sym only [lang_grind, arena_grind, level_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, lpLookup_spec p hpl n,
        lvZero_spec p hpn hpp hpz n, lhPush_spec p hpp n, ih] <;>
      finish (gen := 20)

include hpl in
theorem lpSubstPW_spec (hpn : p.lookup "lv_node" = some lvNode)
    (hpp : p.lookup "lh_push" = some lhPush) (hpz : p.lookup "lv_zero" = some lvZero)
    (hps : p.lookup "lp_spw" = some lpSpw) (hp : p.lookup "lp_substpw" = some lpSubstPW)
    (n : Nat) (s₀ : St) (kd po pc ko kc vo vc : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "lp_substpw" [kd, po, pc, ko, kc, vo, vc]
    ⦃fun r s' => LocEq s' s₀ ∧
      substPWW SPN POOL EREC n s₀.mem kd po pc ko kc vo vc = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, lpSubstPW]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, level_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        lpSpw_spec p hpl hpn hpp hpz hps n] <;>
      finish (gen := 20) [substPWW]

end specs

end L.Arena
