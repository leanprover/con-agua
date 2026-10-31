module

meta import ConAgua.L.Semantics
meta import ConAgua.Arena.Store
public import ConAgua.Arena.MemoLib
public import ConAgua.Arena.ExprMk
public import ConAgua.L.ModelGen
import ConAgua.Census.Attr
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# `wscopedBFast`: the memoized scope walk (lane `whnf3`)

con-ron's `wscopedBGo`/`wscopedBFast` (`Arena/ExprOps.lean:959-1048`, con-leche's `wscopedBXP`):
is every `fvar` leaf reachable from `h` (its annotation descended at the leaf's own index) below
the cursor `d`? The twin threads a walk-local `Std.HashMap (EIdx × Nat) Bool`; L keeps it in the
memo library's table at word array `WSM` (151, stamp/count `CTL[152]`/`CTL[153]`), keyed by the
handle word and the cursor word, cleared (an epoch bump) on the entry, as the twin starts from `∅`.

`ws_go(h, d, c)`: `abort` at `c = 0` (the twin's fuel exhausted), the `fvar`-range cutoff off the
derived word (`der_b`'s second result `0`: `true`), the memo probe, else `ws_node(h, d, c - 1)`
and record. `ws_node` views the handle and dispatches as the twin's arms (the `app`, binder and
`letE` arms short-circuit on a `false` child, as `wscopedBGoArm*`):

* `bvar`, `sort`, `const`, `lit`: `1`;
* `fvar idx ty`: `idx < d` ? `ws_go(ty, idx, c)` : `0`;
* `app f a`, `lam ty b`, `forallE ty b`: the first child, then (if `1`) the second;
* `letE ty v b`: the three in order, stopping at a `0`;
* `proj _ _ e`: `ws_go(e, d, c)`.

`wscoped_bfast(d, e)` is `ws_clear(); ws_go(e, d, 4000000000)` (`coreWalkFuel`).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- Its schema: array 151, stamp/count `CTL[152]`/`CTL[153]`. -/
abbrev wsSch : MemoSch := ⟨WSM, 152⟩

/-- con-ron: ConRon/Arena/ExprOps.lean:958-986 ConRon.Arena.wscopedBGo -/
@[l_impl ConRon.Arena.wscopedBGo]
def wsGo : FunDecl := lfn (h, d, c) locals (b, x, fd, j, e, r, u) {
  if c == 0 { abort };
  (b, x) := call der_b(h);
  if x == 0 { return 1 };
  (fd, j, e) := call ws_find(h, d);
  if fd != 0 { x := WSM.u64[j * 4 + 3]; if x == 0 { return 0 }; return 1 };
  r := call ws_node(h, d, c - 1);
  (fd, j, e) := call ws_find(h, d);
  u := call ws_put(h, d, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:958-986 ConRon.Arena.wscopedBGo
con-ron: ConRon/Arena/ExprOps.lean:988-994 ConRon.Arena.wscopedBGoArmApp
con-ron: ConRon/Arena/ExprOps.lean:996-1003 ConRon.Arena.wscopedBGoArmBind
con-ron: ConRon/Arena/ExprOps.lean:1005-1015 ConRon.Arena.wscopedBGoArmLet -/
@[l_impl ConRon.Arena.wscopedBGo ConRon.Arena.wscopedBGoArmApp ConRon.Arena.wscopedBGoArmBind
  ConRon.Arena.wscopedBGoArmLet]
def wsNode : FunDecl := lfn (h, d, c) locals (g, t, i, f, a, b, x) {
  g := ⟦h⟧.tag;
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if g == 0 { if BVAR⟨t⟩.count <= i { abort }; return 1 };
  if g == 1 {
    if FVAR⟨t⟩.count <= i { abort };
    f := FVAR⟨t, i⟩.i;
    a := FVAR⟨t, i⟩.ty;
    if f < d { x := call ws_go(a, f, c); return x };
    return 0
  };
  if g == 4 {
    i := ⟦h⟧.aidx;
    if APP⟨t⟩.count <= i { abort };
    f := APP⟨t, i⟩.f;
    a := APP⟨t, i⟩.a;
    x := call ws_go(f, d, c);
    if x == 0 { return 0 };
    x := call ws_go(a, d, c);
    return x
  };
  if g == 5 {
    if LAM⟨t⟩.count <= i { abort };
    f := LAM⟨t, i⟩.ty;
    a := LAM⟨t, i⟩.b;
    x := call ws_go(f, d, c);
    if x == 0 { return 0 };
    x := call ws_go(a, d, c);
    return x
  };
  if g == 6 {
    if FORALL⟨t⟩.count <= i { abort };
    f := FORALL⟨t, i⟩.ty;
    a := FORALL⟨t, i⟩.b;
    x := call ws_go(f, d, c);
    if x == 0 { return 0 };
    x := call ws_go(a, d, c);
    return x
  };
  if g == 9 {
    if PROJ⟨t⟩.count <= i { abort };
    f := PROJ⟨t, i⟩.e;
    x := call ws_go(f, d, c);
    return x
  };
  if g == 7 {
    if LET⟨t⟩.count <= i { abort };
    f := LET⟨t, i⟩.ty;
    a := LET⟨t, i⟩.v;
    b := LET⟨t, i⟩.b;
    x := call ws_go(f, d, c);
    if x == 0 { return 0 };
    x := call ws_go(a, d, c);
    if x == 0 { return 0 };
    x := call ws_go(b, d, c);
    return x
  };
  if g == 2 { if SORT⟨t⟩.count <= i { abort }; return 1 };
  if g == 3 { if CONST⟨t⟩.count <= i { abort }; return 1 };
  if g == 8 { if LIT⟨t⟩.count <= i { abort }; return 1 };
  abort
}

/-- **`ws_go` and `ws_node` are their models** `wscW`, `wsNodeW`, at every fuel. -/
l_model wsGo_spec (p : Prog) (hpd : p.lookup "der_b" = some derB)
  (hpf : p.lookup "ws_find" = some (memoFindG wsSch))
  (hps : p.lookup "ws_put" = some (memoPutG wsSch)) (hp : p.lookup "ws_go" = some wsGo)
  (hpn : p.lookup "ws_node" = some wsNode)
  fns [hp ↦ wscW, hpn ↦ wsNodeW]
  specs [derB_spec p hpd n, memoFindG_spec wsSch p _ hpf n, memoPutG_spec wsSch p _ hps n]
  grind [arena_grind] fold [tierW, idxW]
  extra [evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  finish [tierW, idxW] gen 20 heartbeats 1000000

/-! ## `wscoped_bfast(d, e)`: the entry -/

/-- **The model of `wscoped_bfast`**: clear the memo (the twin's `∅`), walk at `coreWalkFuel`. -/
def wsFastW (n : Nat) (m : Mem) (d e : Word) : Option (Word × Mem) :=
  if rdW (m.arr64 CTL) 152 + 2 = 0 then none else wscW n (mclearG wsSch m) e d 4000000000

theorem wsFastW_eq (n : Nat) (m : Mem) (d e : Word) (h0 : rdW (m.arr64 CTL) 152 + 2 ≠ 0) :
    wsFastW n m d e = wscW n (mclearG wsSch m) e d 4000000000 := by simp [wsFastW, h0]

grind_pattern [arena_grind] wsFastW_eq => wsFastW n m d e

/-- con-ron: ConRon/Arena/ExprOps.lean:1048-1052 ConRon.Arena.wscopedBFast -/
@[l_impl ConRon.Arena.wscopedBFast]
def wscopedBFastL : FunDecl := lfn (d, e) locals (r, u) {
  u := call ws_clear();
  r := call ws_go(e, d, 4000000000);
  return r
}

theorem wscopedBFast_spec (p : Prog) (hpd : p.lookup "der_b" = some derB)
    (hpf : p.lookup "ws_find" = some (memoFindG wsSch))
    (hps : p.lookup "ws_put" = some (memoPutG wsSch)) (hp : p.lookup "ws_go" = some wsGo)
    (hpn : p.lookup "ws_node" = some wsNode) (hpc : p.lookup "ws_clear" = some (memoClearG wsSch))
    (hpm : p.lookup "wscoped_bfast" = some wscopedBFastL) (n : Nat) (s₀ : St) (d e : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "wscoped_bfast" [d, e]
    ⦃fun r s' => LocEq s' s₀ ∧ wsFastW n s₀.mem d e = some (r.headD 0, s'.mem); ⊤⦄ := by
  have ih := (wsGo_spec p hpd hpf hps hp hpn n).1
  rw [invoke_eq _ hpm]
  simp only [callFn, wscopedBFastL]
  sym only [lang_grind, arena_grind] =>
    vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, memoClearG_spec wsSch p _ hpc n, ih] <;>
    finish

/-- What the specs need of the program. -/
structure WsProg (p : Prog) : Prop where
  derb : p.lookup "der_b" = some derB
  wsf : p.lookup "ws_find" = some (memoFindG wsSch)
  wsp : p.lookup "ws_put" = some (memoPutG wsSch)
  wsc : p.lookup "ws_clear" = some (memoClearG wsSch)
  wsgo : p.lookup "ws_go" = some wsGo
  wsnode : p.lookup "ws_node" = some wsNode
  wsfast : p.lookup "wscoped_bfast" = some wscopedBFastL

end L.Arena
