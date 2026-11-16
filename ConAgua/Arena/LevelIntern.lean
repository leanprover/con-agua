module

public import ConAgua.Arena.LevelSubstLP
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.LevelGrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import ConAgua.L.ModelGen
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# Interning a level pointer back into the store: `lv_intern`, `lv_sub_int`

con-ron's level-substituting functions (`substLMemoAt`, `substLevelsAt`, `substParamLevels`,
`recFireLevels`) read a level back (`readLevelM`), run con-leche's `Level.subst` on the transient
tree and **intern the result** (`internLevel`). L has no trees: lane `levels`' `lv_substl`
(`LevelSubstL.lean`) runs `subst` on level pointers (a store handle, or a node of the scratch heap
`LH`, `LevelHeap.lean`) and returns a pointer. What is new here is the way back into the store
(finding (3) of lane `whnf`, DESIGN.md):

* `lv_intern(p)`: `internLevel l` for the level `l` the pointer `p` denotes (`LvR`), node by node
  in the twin's order (the children first, `u` before `v`), **every** node, whether `p` is a heap
  node or a store handle, as the twin re-interns the whole readback. A `param`'s name word is a
  stored name handle, re-interned by the twin as `internName` of its readback, which returns the
  handle and changes nothing (`NStoreWF`'s `consP`/`consS`).
* `lv_sub_int(u, ko, kc, vo, vc)`: a fresh heap (`CTL[192] := 0`, as `lvl_eq`), `lp_substl` with
  the keys the `EREC` name slice `(ko, kc)` and the values the `POOL` level-list slice
  `(vo, vc)`, then `lv_intern`: `internLevel (Level.subst ks vs l)`.

The keys and values arrays of lane `levels`' generic functions are fixed here, under this
family's own names (`LevelSubstLP.lean`): `lp_lookup` (keys on the spine stack, copied there by
`keys_push`, so that lane `induct`'s `IW` slices and the record pool's slices are served by one
function; values in the pool) and `lp_substl`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## `lv_intern(p)` -/

/-- con-ron: ConRon/Arena/Monad.lean:473-490 ConRon.Arena.internLevel -/
@[no_expose, l_impl ConRon.Arena.internLevel]
def lvIntern : FunDecl := lfn (p) locals (g, a, b, x, y, h) {
  (g, a, b) := call lv_node(p);
  if g == 0 {
    h := call intern_zero();
    if h >= 4294967296 { abort };
    return h
  };
  if g == 4 {
    h := call intern_param(a);
    if h >= 4294967296 { abort };
    return h
  };
  x := call lv_intern(a);
  if g == 1 {
    h := call intern_succ(x);
    if h >= 4294967296 { abort };
    return h
  };
  y := call lv_intern(b);
  if g == 2 {
    h := call intern_max(x, y);
    if h >= 4294967296 { abort };
    return h
  };
  if g != 3 { abort };
  h := call intern_imax(x, y);
  if h >= 4294967296 { abort };
  return h
}

/-- The functions `lv_intern` calls. -/
structure LvInternProg (p : Prog) : Prop where
  lv_intern : p.lookup "lv_intern" = some lvIntern
  lv_node : p.lookup "lv_node" = some lvNode
  zero_find : p.lookup "zero_find" = some zeroFind
  zero_push : p.lookup "zero_push" = some zeroPush
  intern_zero : p.lookup "intern_zero" = some internZero
  succ_find : p.lookup "succ_find" = some succFind
  succ_push : p.lookup "succ_push" = some succPush
  intern_succ : p.lookup "intern_succ" = some internSucc
  max_find : p.lookup "max_find" = some maxFind
  max_push : p.lookup "max_push" = some maxPush
  intern_max : p.lookup "intern_max" = some internMax
  imax_find : p.lookup "imax_find" = some imaxFind
  imax_push : p.lookup "imax_push" = some imaxPush
  intern_imax : p.lookup "intern_imax" = some internImax
  param_find : p.lookup "param_find" = some paramFind
  param_push : p.lookup "param_push" = some paramPush
  intern_param : p.lookup "intern_param" = some internParam

l_model lvIntern_spec (p : Prog) (hL : LvInternProg p)
  fns [hL.lv_intern ↦ lvInternW]
  specs [lvNode_spec p hL.lv_node n,
    internZero_spec p hL.zero_find hL.zero_push hL.intern_zero n,
    internSucc_spec p hL.succ_find hL.succ_push hL.intern_succ n,
    internMax_spec p hL.max_find hL.max_push hL.intern_max n,
    internImax_spec p hL.imax_find hL.imax_push hL.intern_imax n,
    internParam_spec p hL.param_find hL.param_push hL.intern_param n]
  grind [arena_grind] fold [lvG, lvA, lvB] noguard ["lv_node"]

/-! ## `lv_sub_int(u, ko, kc, vo, vc)`: substitute, then intern -/

/-- con-ron: ConRon/Arena/ExprOps.lean:2094-2109 ConRon.Arena.substLMemoAt
con-ron: ConRon/Arena/Core.lean:2391-2401 ConRon.Arena.substLevelsAt -/
@[no_expose] def lvSubInt : FunDecl := lfn (u, ko, kc, vo, vc) locals (x, h) {
  CTL.u64[192] := 0;
  x := call lp_substl(u, ko, kc, vo, vc);
  h := call lv_intern(x);
  return h
}

/-! ## `keys_push(src, l)`: a record-pool name slice onto the spine stack -/

/-- con-ron: none — the substitution's keys copied onto the spine stack (`lp_lookup`'s key array) -/
@[no_expose] def ekCopy : FunDecl := lfn (s, d, l) locals (r) {
  if l == 0 { return 0 };
  SPN.u64[d] := EREC⦃s⦄;
  r := call ek_copy(s + 1, d + 1, l - 1);
  return r
}

/-- **The model of `ek_copy`.** -/
l_model ekCopy_spec (p : Prog) (hp : p.lookup "ek_copy" = some ekCopy)
  fns [hp ↦ ekCopyW void]
  grind [arena_grind]

/-- The copy's rest is its result. -/
theorem ekCopyW_k {x : Option Mem} {m' : Mem} (h : ekCopyW.k_ek_copy x = some m') : x = some m' := by
  cases x <;> simp_all [ekCopyW.k_ek_copy.none, ekCopyW.k_ek_copy.arm1]

/-- con-ron: none — the substitution's keys copied onto the spine stack (`lp_lookup`'s key array) -/
@[no_expose] def keysPush : FunDecl := lfn (po, pc) locals (b, r) {
  b := CTL.u64[136];
  if len(SPN.u64) < b { abort };
  if len(SPN.u64) - b < pc { abort };
  r := call ek_copy(po, b, pc);
  CTL.u64[136] := b + pc;
  return b
}

/-- After the copy: the top raised. -/
def kpK (b pc : Word) : Option Mem → Option (Word × Mem)
  | none => none
  | some m₁ => some (b, m₁.set64 CTL 136 (b + pc))

@[arena_grind =] theorem kpK_some (b pc : Word) (m₁ : Mem) :
    kpK b pc (some m₁) = some (b, m₁.set64 CTL 136 (b + pc)) := by rfl

/-- **The model of `keys_push`.** -/
def keysPushW : Nat → Mem → Word → Word → Option (Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, po, pc =>
    if m.len64 SPN < spTop m then none
    else if m.len64 SPN - spTop m < pc then none
    else kpK (spTop m) pc (ekCopyW n m po (spTop m) pc)

/-- The functions `lv_sub_int` calls. -/
structure LvSubProg (p : Prog) : Prop extends LvInternProg p where
  lv_sub_int : p.lookup "lv_sub_int" = some lvSubInt
  lp_substl : p.lookup "lp_substl" = some lpSubstL
  lp_lookup : p.lookup "lp_lookup" = some lpLookup
  lh_mk : p.lookup "lh_mk" = some lhMk
  keys_push : p.lookup "keys_push" = some keysPush
  ek_copy : p.lookup "ek_copy" = some ekCopy
  ls_node : p.lookup "ls_node" = some lsNode
  lv_zero : p.lookup "lv_zero" = some lvZero
  lh_push : p.lookup "lh_push" = some lhPush

/-- **The model of `lv_sub_int`.** -/
l_model lvSubInt_spec (p : Prog) (hL : LvSubProg p)
  fns [hL.lv_sub_int ↦ lvSubIntW]
  specs [lpSubstL_spec p hL.lp_lookup hL.lv_node hL.lh_mk hL.lp_substl n,
    lvIntern_spec p hL.toLvInternProg n]
  grind [arena_grind]

section spec2
variable (p : Prog) (hL : LvSubProg p)
include hL

theorem keysPush_spec (n : Nat) (s₀ : St) (po pc : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "keys_push" [po, pc]
    ⦃fun r s' => LocEq s' s₀ ∧ keysPushW n s₀.mem po pc = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hL.keys_push]
  simp only [callFn, keysPush]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        ekCopy_spec p hL.ek_copy n] <;>
      finish [keysPushW, spTop]

end spec2

end L.Arena
