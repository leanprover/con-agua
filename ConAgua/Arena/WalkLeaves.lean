module

public import ConAgua.L.PureEval
meta import ConAgua.L.Semantics
meta import ConAgua.Arena.Store
public import ConAgua.Arena.ExprMk
public import ConAgua.Arena.MemoLib
import ConAgua.Census.Attr
import ConAgua.Arena.GrindAttr
public import ConAgua.L.ModelGen
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# `leafGuard`: the fabrication leaf guard (lane `whnf3`)

con-ron's `leafGuard` (`Arena/ExprOps.lean:1251-1256`, con-leche's `leafGuard`): every `fvar` leaf
reachable from the fabrication `fab` is one of the leaves of `base`. Three walks, each a twin
function with a walk-local map:

* `fl_go(h, k, c)`: `fvarLeavesGo` — the reachable `fvar` leaves of `base`, with a `seen` set (memo
  table `FLM`, array 152, `CTL[154]`/`CTL[155]`, key `(h, 0)`, inserted *before* the view, as the
  twin). The twin's accumulator `acc` (consed on the way in) is the word array `LVS` (154), two words
  `(idx, ty)` per leaf in push order, so `acc` is its first `k` entries read from the end; `fl_go`
  returns the new count. A push past the array's capacity aborts.
* `leaf_mem(k, x, y)`: `leafMem acc x y`, scanning `LVS` from entry `k - 1` down (`acc`'s order).
* `lsb_go(h, k, c)`: `leavesSubGo` — the memoized subset test against the first `k` leaves (memo
  table `LSM`, array 153, `CTL[156]`/`CTL[157]`, key `(h, 0)`), the arms short-circuiting as
  `leavesSubArm*`.

`leaf_guard(fab, base)`: the `fvar`-range cutoff on `fab`, then clear `FLM`, `fl_go(base, 0, 4·10⁹)`,
clear `LSM`, `lsb_go(fab, k, 4·10⁹)` (`coreWalkFuel`, the twin's `fuel`).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

abbrev flSch : MemoSch := ⟨FLM, 154⟩
abbrev lsbSch : MemoSch := ⟨LSM, 156⟩

/-! ## `fl_go`: the leaves of `base` -/

/-- Push the leaf `(x, y)` at entry `k`. -/
def lvsPush (m : Mem) (k x y : Word) : Mem := (m.set64 LVS (k * 2) x).set64 LVS (k * 2 + 1) y

/-- con-ron: ConRon/Arena/ExprOps.lean:1056-1083 ConRon.Arena.fvarLeavesGo -/
@[l_impl ConRon.Arena.fvarLeavesGo]
def flGo : FunDecl := lfn (h, k, c) locals (b, x, fd, j, e, u) {
  if c == 0 { abort };
  (b, x) := call der_b(h);
  if x == 0 { return k };
  (fd, j, e) := call fl_find(h, 0);
  if fd != 0 { return k };
  u := call fl_put(h, 0, 0, fd, j);
  x := call fl_node(h, k, c - 1);
  return x
}


/-- con-ron: ConRon/Arena/ExprOps.lean:1056-1083 ConRon.Arena.fvarLeavesGo
con-ron: ConRon/Arena/ExprOps.lean:1085-1092 ConRon.Arena.fvarLeavesGoArmApp
con-ron: ConRon/Arena/ExprOps.lean:1094-1101 ConRon.Arena.fvarLeavesGoArmBind
con-ron: ConRon/Arena/ExprOps.lean:1103-1111 ConRon.Arena.fvarLeavesGoArmLet -/
@[l_impl ConRon.Arena.fvarLeavesGo ConRon.Arena.fvarLeavesGoArmApp ConRon.Arena.fvarLeavesGoArmBind
  ConRon.Arena.fvarLeavesGoArmLet]
def flNode : FunDecl := lfn (h, k, c) locals (g, t, i, f, a, b, x) {
  g := ⟦h⟧.tag;
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if g == 0 { if BVAR⟨t⟩.count <= i { abort }; return k };
  if g == 1 {
    if FVAR⟨t⟩.count <= i { abort };
    if len(LVS.u64) >> 1 <= k { abort };
    f := FVAR⟨t, i⟩.i;
    a := FVAR⟨t, i⟩.ty;
    LVS.u64[k * 2] := f;
    LVS.u64[k * 2 + 1] := a;
    x := call fl_go(a, k + 1, c);
    return x
  };
  if g == 4 {
    i := ⟦h⟧.aidx;
    if APP⟨t⟩.count <= i { abort };
    f := APP⟨t, i⟩.f;
    a := APP⟨t, i⟩.a;
    x := call fl_go(f, k, c);
    x := call fl_go(a, x, c);
    return x
  };
  if g == 5 {
    if LAM⟨t⟩.count <= i { abort };
    f := LAM⟨t, i⟩.ty;
    a := LAM⟨t, i⟩.b;
    x := call fl_go(f, k, c);
    x := call fl_go(a, x, c);
    return x
  };
  if g == 6 {
    if FORALL⟨t⟩.count <= i { abort };
    f := FORALL⟨t, i⟩.ty;
    a := FORALL⟨t, i⟩.b;
    x := call fl_go(f, k, c);
    x := call fl_go(a, x, c);
    return x
  };
  if g == 9 {
    if PROJ⟨t⟩.count <= i { abort };
    f := PROJ⟨t, i⟩.e;
    x := call fl_go(f, k, c);
    return x
  };
  if g == 7 {
    if LET⟨t⟩.count <= i { abort };
    f := LET⟨t, i⟩.ty;
    a := LET⟨t, i⟩.v;
    b := LET⟨t, i⟩.b;
    x := call fl_go(f, k, c);
    x := call fl_go(a, x, c);
    x := call fl_go(b, x, c);
    return x
  };
  if g == 2 { if SORT⟨t⟩.count <= i { abort }; return k };
  if g == 3 { if CONST⟨t⟩.count <= i { abort }; return k };
  if g == 8 { if LIT⟨t⟩.count <= i { abort }; return k };
  abort
}

/-- **`fl_go` and `fl_node` are their models** `flW`, `flNodeW`, at every fuel. -/
l_model flGo_spec (p : Prog) (hpd : p.lookup "der_b" = some derB)
  (hpf : p.lookup "fl_find" = some (memoFindG flSch))
  (hps : p.lookup "fl_put" = some (memoPutG flSch)) (hp : p.lookup "fl_go" = some flGo)
  (hpn : p.lookup "fl_node" = some flNode)
  fns [hp ↦ flW, hpn ↦ flNodeW]
  specs [derB_spec p hpd n, memoFindG_spec flSch p _ hpf n, memoPutG_spec flSch p _ hps n]
  grind [arena_grind] fold [tierW, idxW]
  extra [evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  finish [tierW, idxW] gen 20 heartbeats 1000000

/-! ## `leaf_mem(k, x, y)`: membership in the first `k` leaves, newest first -/

/-- **The model of `leaf_mem`'s loop** from the cursor `j` down. -/
def lfmW (a : Array Word) (x y j : Word) : Word :=
  if j = 0 then 0
  else if rdW a ((j - 1) * 2) = x ∧ rdW a ((j - 1) * 2 + 1) = y then 1
  else lfmW a x y (j - 1)
termination_by j.toNat
decreasing_by
  have : j.toNat ≠ 0 := fun e => ‹¬ j = 0› (UInt64.toNat_inj.mp (by simpa using e))
  rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp; omega

theorem lfmW_zero (a : Array Word) (x y : Word) : lfmW a x y 0 = 0 := by rw [lfmW]; simp
theorem lfmW_hit (a : Array Word) (x y j : Word) (hj : j ≠ 0)
    (h : rdW a ((j - 1) * 2) = x ∧ rdW a ((j - 1) * 2 + 1) = y) : lfmW a x y j = 1 := by
  rw [lfmW]; simp [hj, h.1, h.2]
theorem lfmW_next (a : Array Word) (x y j : Word) (hj : j ≠ 0)
    (h : ¬ (rdW a ((j - 1) * 2) = x ∧ rdW a ((j - 1) * 2 + 1) = y)) : lfmW a x y j = lfmW a x y (j - 1) := by
  rw [lfmW]; simp only [hj, ↓reduceIte, h]

grind_pattern [arena_grind] lfmW_zero => lfmW a x y 0
grind_pattern [arena_grind] lfmW_hit => lfmW a x y j
grind_pattern [arena_grind] lfmW_next => lfmW a x y j

def lmLoop : Stmt := lblk (k, x, y, j) {
  while j != 0 {
    j := j - 1;
    if LVS.u64[j * 2] == x && LVS.u64[j * 2 + 1] == y { return 1 }
  }
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1149-1156 ConRon.Arena.leafMem -/
@[l_impl ConRon.Arena.leafMem]
def leafMemL : FunDecl := lfn (k, x, y) locals (j) {
  j := k;
  ⟪lmLoop⟫;
  return 0
}

section lm
variable (p : Prog) (hp : p.lookup "leaf_mem" = some leafMemL)

theorem lmLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n lmLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [lfmW (s₀.mem.arr64 LVS) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := lmLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;> finish

theorem lmLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) lmLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [lfmW (s₀.mem.arr64 LVS) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3)]; ⊤⦄ :=
  Triple.step_exec (lmLoop_spec p (n + 1) s₀)

include hp in
theorem leafMem_spec (n : Nat) (s₀ : St) (k x y : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "leaf_mem" [k, x, y]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ r.headD 0 = lfmW (s₀.mem.arr64 LVS) x y k; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, leafMemL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalArgs, setLoc, lmLoop_step_spec p n] <;> finish

end lm


/-! ## `lsb_go`: every leaf of `fab` among the first `k` leaves -/

/-- con-ron: ConRon/Arena/ExprOps.lean:1160-1188 ConRon.Arena.leavesSubGo -/
@[l_impl ConRon.Arena.leavesSubGo]
def lsbGo : FunDecl := lfn (h, k, c) locals (b, x, fd, j, e, r, u) {
  if c == 0 { abort };
  (b, x) := call der_b(h);
  if x == 0 { return 1 };
  (fd, j, e) := call lsb_find(h, 0);
  if fd != 0 { x := LSM.u64[j * 4 + 3]; if x == 0 { return 0 }; return 1 };
  r := call lsb_node(h, k, c - 1);
  (fd, j, e) := call lsb_find(h, 0);
  u := call lsb_put(h, 0, r, fd, j);
  return r
}

/-- con-ron: ConRon/Arena/ExprOps.lean:1160-1188 ConRon.Arena.leavesSubGo
con-ron: ConRon/Arena/ExprOps.lean:1190-1196 ConRon.Arena.leavesSubArmApp
con-ron: ConRon/Arena/ExprOps.lean:1198-1204 ConRon.Arena.leavesSubArmBind
con-ron: ConRon/Arena/ExprOps.lean:1206-1216 ConRon.Arena.leavesSubArmLet -/
@[l_impl ConRon.Arena.leavesSubGo ConRon.Arena.leavesSubArmApp ConRon.Arena.leavesSubArmBind
  ConRon.Arena.leavesSubArmLet]
def lsbNode : FunDecl := lfn (h, k, c) locals (g, t, i, f, a, b, x) {
  g := ⟦h⟧.tag;
  t := ⟦h⟧.tier;
  i := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if g == 0 { if BVAR⟨t⟩.count <= i { abort }; return 1 };
  if g == 1 {
    if FVAR⟨t⟩.count <= i { abort };
    f := FVAR⟨t, i⟩.i;
    a := FVAR⟨t, i⟩.ty;
    x := call leaf_mem(k, f, a);
    if x == 0 { return 0 };
    x := call lsb_go(a, k, c);
    return x
  };
  if g == 4 {
    i := ⟦h⟧.aidx;
    if APP⟨t⟩.count <= i { abort };
    f := APP⟨t, i⟩.f;
    a := APP⟨t, i⟩.a;
    x := call lsb_go(f, k, c);
    if x == 0 { return 0 };
    x := call lsb_go(a, k, c);
    return x
  };
  if g == 5 {
    if LAM⟨t⟩.count <= i { abort };
    f := LAM⟨t, i⟩.ty;
    a := LAM⟨t, i⟩.b;
    x := call lsb_go(f, k, c);
    if x == 0 { return 0 };
    x := call lsb_go(a, k, c);
    return x
  };
  if g == 6 {
    if FORALL⟨t⟩.count <= i { abort };
    f := FORALL⟨t, i⟩.ty;
    a := FORALL⟨t, i⟩.b;
    x := call lsb_go(f, k, c);
    if x == 0 { return 0 };
    x := call lsb_go(a, k, c);
    return x
  };
  if g == 9 {
    if PROJ⟨t⟩.count <= i { abort };
    f := PROJ⟨t, i⟩.e;
    x := call lsb_go(f, k, c);
    return x
  };
  if g == 7 {
    if LET⟨t⟩.count <= i { abort };
    f := LET⟨t, i⟩.ty;
    a := LET⟨t, i⟩.v;
    b := LET⟨t, i⟩.b;
    x := call lsb_go(f, k, c);
    if x == 0 { return 0 };
    x := call lsb_go(a, k, c);
    if x == 0 { return 0 };
    x := call lsb_go(b, k, c);
    return x
  };
  if g == 2 { if SORT⟨t⟩.count <= i { abort }; return 1 };
  if g == 3 { if CONST⟨t⟩.count <= i { abort }; return 1 };
  if g == 8 { if LIT⟨t⟩.count <= i { abort }; return 1 };
  abort
}


/-- **`lsb_go` and `lsb_node` are their models** `lsbW`, `lsbNodeW`, at every fuel. -/
l_model lsbGo_spec (p : Prog) (hpd : p.lookup "der_b" = some derB)
  (hpf : p.lookup "lsb_find" = some (memoFindG lsbSch))
  (hps : p.lookup "lsb_put" = some (memoPutG lsbSch)) (hp : p.lookup "lsb_go" = some lsbGo)
  (hpn : p.lookup "lsb_node" = some lsbNode) (hpm : p.lookup "leaf_mem" = some leafMemL)
  fns [hp ↦ lsbW, hpn ↦ lsbNodeW]
  specs [derB_spec p hpd n, memoFindG_spec lsbSch p _ hpf n, memoPutG_spec lsbSch p _ hps n,
    leafMem_spec p hpm n]
  grind [arena_grind] fold [tierW, idxW]
  extra [evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  finish [tierW, idxW] gen 20 heartbeats 1000000


/-! ## `leaf_guard(fab, base)` -/

/-- con-ron: ConRon/Arena/ExprOps.lean:1250-1261 ConRon.Arena.leafGuard
con-ron: ConRon/Arena/ExprOps.lean:1143-1147 ConRon.Arena.fvarLeavesFast -/
@[l_impl ConRon.Arena.leafGuard ConRon.Arena.fvarLeavesFast]
def leafGuardL : FunDecl := lfn (fab, base) locals (b, x, k, r, u) {
  (b, x) := call der_b(fab);
  if x == 0 { return 1 };
  u := call fl_clear();
  k := call fl_go(base, 0, 4000000000);
  u := call lsb_clear();
  r := call lsb_go(fab, k, 4000000000);
  return r
}


/-- What the specs need of the program. -/
structure LgProg (p : Prog) : Prop where
  derb : p.lookup "der_b" = some derB
  flf : p.lookup "fl_find" = some (memoFindG flSch)
  flp : p.lookup "fl_put" = some (memoPutG flSch)
  flc : p.lookup "fl_clear" = some (memoClearG flSch)
  flgo : p.lookup "fl_go" = some flGo
  flnode : p.lookup "fl_node" = some flNode
  lsf : p.lookup "lsb_find" = some (memoFindG lsbSch)
  lsp : p.lookup "lsb_put" = some (memoPutG lsbSch)
  lsc : p.lookup "lsb_clear" = some (memoClearG lsbSch)
  lsgo : p.lookup "lsb_go" = some lsbGo
  lsnode : p.lookup "lsb_node" = some lsbNode
  lm : p.lookup "leaf_mem" = some leafMemL
  lg : p.lookup "leaf_guard" = some leafGuardL


/-- **`leaf_guard` is its model** `lgW`. -/
l_model leafGuard_spec (p : Prog) (hp : LgProg p)
  fns [hp.lg ↦ lgW]
  specs [derB_spec p hp.derb n, (flGo_spec p hp.derb hp.flf hp.flp hp.flgo hp.flnode n).1,
    (lsbGo_spec p hp.derb hp.lsf hp.lsp hp.lsgo hp.lsnode hp.lm n).1,
    memoClearG_spec flSch p _ hp.flc n, memoClearG_spec lsbSch p _ hp.lsc n]
  grind [arena_grind] fold [tierW, idxW]
  finish [tierW, idxW] gen 20 heartbeats 1000000

end L.Arena
