import ConAgua.Front.IndApply
import ConAgua.Arena.DeclArmsNat
import ConAgua.L.ProgHas
import ConAgua.Arena.IndCopy
import ConAgua.Arena.WhnfBase
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import ConAgua.Arena.GrindAttr
import ConAgua.Census.Attr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen

/-!
# The ground hoist: `hoistNatOpGround` in L (lane `front3`)

The twin of `ConRon/Arena/Frontend/NatOpGround.lean` (con-leche's `Frontend/NatOpGround.lean`):
a pinned `Nat` operation's certificate is spelled over the structural `Nat` operations
(`natOpDeps`), which must be installed before it; an export that orders declarations by a DFS from
arbitrary roots can list them after it, so the prepared stream is reordered: every record a ground
of an operation at position `i` reaches through records after `i` moves just ahead of `i`.

The stream is `DECL` in the order `ord` (an `IW` slice of record indices, `preparePrelude`'s
`front ++ rest`): position `k` is the record `DECL[1 + 8 ord[k] ..]` (`ApplyDecl.lean`, kinds `1`
axiom, `2` def, `3` thm, `4` opaque, `5` quot, `6` inductive block of `DIND` constant records).

* **The name index** (`nameIndex`, `insertNames`): the memo `HNIX` (array 76, `CTL[75‥76]`),
  name handle ↦ the first position declaring it, plus one.
* **The targets** (`hoistTargetsGo`, `hoistDeps`, `hoistClosure`): `IW[tg + k] = t + 1` when
  position `k` must precede the operation at position `t`, `0` otherwise (the twin's
  `Std.HashMap Nat Nat`).
* **The closure's worklist.** The twin pops a record, skips it if it is done (already has a target
  `≤ i`), marks it and pushes the positions its constants are first declared at that lie after
  `i`. Every target is set to the current `i` and `i` only grows, so "done" is "has a target", and
  the set of records a closure marks is the set reachable from `j` through not-yet-marked records
  after `i`, whatever the order: L marks a record when it pushes it (`hoist_note`), so each record
  is pushed at most once in the whole pass and the stack (`IW[ws ..]`, `c` words) never overflows.
  The twin's fuel (`ds.size`, never exhausted: `hoistClosure_fuel_succ`) is that bound.
* **The constants of a record** (`usedConstsGo`, `usedConstsRules`, `usedConstsBlock`,
  `IDeclaration.usedConsts`): a walk over the expression DAG, each node once per record (the memo
  `HSEEN`, array 75, `CTL[73‥74]`, cleared per record, as the twin's fresh `Std.HashSet EIdx`; an
  inductive block shares one), every `const` name and `proj` structure name handed to
  `hoist_note` as it is found (the
  twin collects them into an array first and then pushes them in order; the marked set is the
  same). The walk's fuel is the twin's `coreWalkFuel` (`4000000000`), the view checks those of
  every walk (a dangling handle aborts where `view` fails).
* **The reorder** (`applyHoist`, `reorder`, `hoistKey`, `hoistLt`): the twin sorts the positions by
  the key `(t, 0, k)` (moved, target `t`) or `(k, 1, k)` (not moved); the keys are distinct, so
  the sorted order is: for each position `p`, the records moved to `p` in position order, then
  `p` itself unless it moved. L builds that order directly (a bucket list per target).
* `movedNames` (the second component of `applyHoist`, the `hoisted` receipt) is not computed:
  `preparePrelude` drops it (docs/deviations.md D30).
* Every loop is a self-recursion (the twin's own shape), so that `l_model` (`L/ModelGen.lean`)
  generates each function's word model and spec (`hoistIns_spec` … `hoistApply_spec`, at the end
  of this file); the recursions over the stream run `c` deep (the harness's stack is 1 GiB).
  `hoist_targets_go` and `hoist_nat_op_ground` call two-result callees (`nat_op_deps`), which
  `l_model` does not take yet: no model. The refinement of the models against the twin is open.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Checker

open L L.Arena L.Ind L.Front L.Front.Ind

/-- The hoist's expression visited set (one record's, or one block's). -/
abbrev HSEEN : ArrId := 75
/-- The hoist's name index: name handle ↦ the first position declaring it. -/
abbrev HNIX : ArrId := 76
abbrev hsSch : MemoSch := ⟨HSEEN, 73⟩
abbrev hnSch : MemoSch := ⟨HNIX, 75⟩

/-! ## The name index -/

/-- `hoist_ins(n, k)`: the name `n` is declared at position `k`, unless an earlier one declares it. -/
-- con-ron: ConRon/Arena/Frontend/NatOpGround.lean:120-127 ConRon.Arena.Frontend.insertNames
@[l_impl ConRon.Arena.Frontend.insertNames]
def hoistInsL : FunDecl := lfn (n, k) locals (fd, j, e0, z) {
  (fd, j, e0) := call hn_find(n, 0);
  if fd == 0 { z := call hn_put(n, 0, k + 1, fd, j) };
  return 0
}

/-- `hoist_names_go(k, o, c, q)`: the names of the block members `DIND[o + q ‥ o + c)`, declared at
position `k`. -/
-- con-ron: ConRon/Arena/Frontend/NatOpGround.lean:120-127 ConRon.Arena.Frontend.insertNames
def hoistNamesGoL : FunDecl := lfn (k, o, c, q) locals (z, r) {
  if c <= q { return 0 };
  z := call hoist_ins(DIND.u64[DIND.u64[o + q] + 1], k);
  r := call hoist_names_go(k, o, c, q + 1);
  return r
}

/-- `hoist_names(k, x)`: the names of the record at `DECL[x ..]` (`IDeclaration.names`: an
inductive block's members' names), declared at position `k`. -/
-- con-ron: ConRon/Arena/Frontend/NatOpGround.lean:120-127 ConRon.Arena.Frontend.insertNames
def hoistNamesL : FunDecl := lfn (k, x) locals (z) {
  if DECL.u64[x] != 6 {
    z := call hoist_ins(DECL.u64[x + 1], k);
    return 0
  };
  z := call hoist_names_go(k, DECL.u64[x + 2], DECL.u64[x + 3], 0);
  return 0
}

/-- `hoist_index_go(ord, c, k)`: positions `k ‥ c` into the name index. -/
-- con-ron: ConRon/Arena/Frontend/NatOpGround.lean:129-138 ConRon.Arena.Frontend.nameIndex
@[l_impl ConRon.Arena.Frontend.nameIndex]
def hoistIndexGoL : FunDecl := lfn (ord, c, k) locals (z, r) {
  if c <= k { return 0 };
  z := call hoist_names(k, 1 + 8 * IW.u64[ord + k]);
  r := call hoist_index_go(ord, c, k + 1);
  return r
}

/-- `hoist_ix(n)`: `m + 1` when the name index maps `n` to `m`, `0` when it has no entry. -/
-- con-ron: ConRon/Arena/Frontend/NatOpGround.lean:129-138 ConRon.Arena.Frontend.nameIndex
def hoistIxL : FunDecl := lfn (n) locals (fd, j, e0) {
  (fd, j, e0) := call hn_find(n, 0);
  if fd == 0 { return 0 };
  return HNIX.u64[j * 4 + 3]
}

/-! ## The closure -/

/-- `hoist_note(n, i, k, tg, ws, sp)`: record `k` (being processed for the operation at `i`)
references the name `n`: the position `m` first declaring it, if it lies after `i`, is not `k` and
has no target yet, gets target `i` and is pushed (`ws[sp] := m`); the new stack size. -/
-- con-ron: ConRon/Arena/Frontend/NatOpGround.lean:155-197 ConRon.Arena.Frontend.hoistClosure.pushOne
@[l_impl ConRon.Arena.Frontend.hoistClosure.pushOne]
def hoistNoteL : FunDecl := lfn (n, i, k, tg, ws, sp) locals (m) {
  m := call hoist_ix(n);
  if m != 0 && i + 1 < m && m != k + 1 && IW.u64[tg + m - 1] == 0 {
    IW.u64[tg + m - 1] := i + 1;
    IW.u64[ws + sp] := m - 1;
    return sp + 1
  };
  return sp
}

/-- `hoist_walk(e, i, k, tg, ws, sp, fu)`: the constants of the expression `e` (each node once,
the visited set `HSEEN`), each handed to `hoist_note`; the new stack size. The compound nodes go
to their arm (`hoist_app`, …) at fuel `fu - 1`. -/
-- con-ron: ConRon/Arena/Frontend/NatOpGround.lean:46-70 ConRon.Arena.Frontend.usedConstsGo
@[l_impl ConRon.Arena.Frontend.usedConstsGo]
def hoistWalkL : FunDecl := lfn (e, i, k, tg, ws, sp, fu) locals (fd, j, e0, z, g, t, x, r) {
  if fu == 0 { abort };
  (fd, j, e0) := call hs_find(e, 0);
  if fd != 0 { return sp };
  z := call hs_put(e, 0, 1, fd, j);
  g := e >> 28;
  t := ⟦e⟧.tier;
  x := ⟦e⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if g == 3 {
    if CONST⟨t⟩.count <= x { abort };
    r := call hoist_note(CONST⟨t, x⟩.n, i, k, tg, ws, sp);
    return r
  };
  if g == 4 { if APP⟨t⟩.count <= x { abort }; r := call hoist_app(e, i, k, tg, ws, sp, fu - 1); return r };
  if g == 5 { if LAM⟨t⟩.count <= x { abort }; r := call hoist_lam(e, i, k, tg, ws, sp, fu - 1); return r };
  if g == 6 { if FORALL⟨t⟩.count <= x { abort }; r := call hoist_forall(e, i, k, tg, ws, sp, fu - 1); return r };
  if g == 7 { if LET⟨t⟩.count <= x { abort }; r := call hoist_let(e, i, k, tg, ws, sp, fu - 1); return r };
  if g == 9 { if PROJ⟨t⟩.count <= x { abort }; r := call hoist_proj(e, i, k, tg, ws, sp, fu - 1); return r };
  if g == 1 { if FVAR⟨t⟩.count <= x { abort }; r := call hoist_fvar(e, i, k, tg, ws, sp, fu - 1); return r };
  if g == 0 { if BVAR⟨t⟩.count <= x { abort }; return sp };
  if g == 2 { if SORT⟨t⟩.count <= x { abort }; return sp };
  if g == 8 { if LIT⟨t⟩.count <= x { abort }; return sp };
  abort
}

/-- `hoist_app(e, i, k, tg, ws, sp, fu)`: `usedConstsGo`'s arm for a `app` node (the children at
fuel `fu`). -/
-- con-ron: ConRon/Arena/Frontend/NatOpGround.lean:46-70 ConRon.Arena.Frontend.usedConstsGo
def hoistAppL : FunDecl := lfn (e, i, k, tg, ws, sp, fu) locals (t, x) {
  t := ⟦e⟧.tier;
  x := ⟦e⟧.idx;
  sp := call hoist_walk(APP⟨t, x⟩.f, i, k, tg, ws, sp, fu);
  sp := call hoist_walk(APP⟨t, x⟩.a, i, k, tg, ws, sp, fu);
  return sp
}

/-- `hoist_lam(e, i, k, tg, ws, sp, fu)`: `usedConstsGo`'s arm for a `lam` node (the children at
fuel `fu`). -/
-- con-ron: ConRon/Arena/Frontend/NatOpGround.lean:46-70 ConRon.Arena.Frontend.usedConstsGo
def hoistLamL : FunDecl := lfn (e, i, k, tg, ws, sp, fu) locals (t, x) {
  t := ⟦e⟧.tier;
  x := ⟦e⟧.idx;
  sp := call hoist_walk(LAM⟨t, x⟩.ty, i, k, tg, ws, sp, fu);
  sp := call hoist_walk(LAM⟨t, x⟩.b, i, k, tg, ws, sp, fu);
  return sp
}

/-- `hoist_forall(e, i, k, tg, ws, sp, fu)`: `usedConstsGo`'s arm for a `forallE` node (the children at
fuel `fu`). -/
-- con-ron: ConRon/Arena/Frontend/NatOpGround.lean:46-70 ConRon.Arena.Frontend.usedConstsGo
def hoistForallL : FunDecl := lfn (e, i, k, tg, ws, sp, fu) locals (t, x) {
  t := ⟦e⟧.tier;
  x := ⟦e⟧.idx;
  sp := call hoist_walk(FORALL⟨t, x⟩.ty, i, k, tg, ws, sp, fu);
  sp := call hoist_walk(FORALL⟨t, x⟩.b, i, k, tg, ws, sp, fu);
  return sp
}

/-- `hoist_let(e, i, k, tg, ws, sp, fu)`: `usedConstsGo`'s arm for a `letE` node (the children at
fuel `fu`). -/
-- con-ron: ConRon/Arena/Frontend/NatOpGround.lean:46-70 ConRon.Arena.Frontend.usedConstsGo
def hoistLetL : FunDecl := lfn (e, i, k, tg, ws, sp, fu) locals (t, x) {
  t := ⟦e⟧.tier;
  x := ⟦e⟧.idx;
  sp := call hoist_walk(LET⟨t, x⟩.ty, i, k, tg, ws, sp, fu);
  sp := call hoist_walk(LET⟨t, x⟩.v, i, k, tg, ws, sp, fu);
  sp := call hoist_walk(LET⟨t, x⟩.b, i, k, tg, ws, sp, fu);
  return sp
}

/-- `hoist_proj(e, i, k, tg, ws, sp, fu)`: `usedConstsGo`'s arm for a `proj` node (the children at
fuel `fu`). -/
-- con-ron: ConRon/Arena/Frontend/NatOpGround.lean:46-70 ConRon.Arena.Frontend.usedConstsGo
def hoistProjL : FunDecl := lfn (e, i, k, tg, ws, sp, fu) locals (t, x) {
  t := ⟦e⟧.tier;
  x := ⟦e⟧.idx;
  sp := call hoist_note(PROJ⟨t, x⟩.n, i, k, tg, ws, sp);
  sp := call hoist_walk(PROJ⟨t, x⟩.e, i, k, tg, ws, sp, fu);
  return sp
}

/-- `hoist_fvar(e, i, k, tg, ws, sp, fu)`: `usedConstsGo`'s arm for a `fvar` node (the children at
fuel `fu`). -/
-- con-ron: ConRon/Arena/Frontend/NatOpGround.lean:46-70 ConRon.Arena.Frontend.usedConstsGo
def hoistFvarL : FunDecl := lfn (e, i, k, tg, ws, sp, fu) locals (t, x) {
  t := ⟦e⟧.tier;
  x := ⟦e⟧.idx;
  sp := call hoist_walk(FVAR⟨t, x⟩.ty, i, k, tg, ws, sp, fu);
  return sp
}

/-- `hoist_rules_go(k, i, tg, ws, sp, ro, rc, r)`: the right-hand sides of the recursor rules
`r ‥ rc` at `DIND[ro ..]` (eleven words each, the right-hand side at `+ 8`). -/
-- con-ron: ConRon/Arena/Frontend/NatOpGround.lean:72-82 ConRon.Arena.Frontend.usedConstsRules
@[l_impl ConRon.Arena.Frontend.usedConstsRules]
def hoistRulesGoL : FunDecl := lfn (k, i, tg, ws, sp, ro, rc, r) locals (x) {
  if rc <= r { return sp };
  sp := call hoist_walk(DIND.u64[ro + 11 * r + 8], i, k, tg, ws, sp, 4000000000);
  x := call hoist_rules_go(k, i, tg, ws, sp, ro, rc, r + 1);
  return x
}

/-- `hoist_block_go(k, i, tg, ws, sp, o, c, q)`: the block members `DIND[o + q ‥ o + c)`: each
member's type, a recursor's rules. -/
-- con-ron: ConRon/Arena/Frontend/NatOpGround.lean:84-95 ConRon.Arena.Frontend.usedConstsBlock
@[l_impl ConRon.Arena.Frontend.usedConstsBlock]
def hoistBlockGoL : FunDecl := lfn (k, i, tg, ws, sp, o, c, q) locals (p, x) {
  if c <= q { return sp };
  p := DIND.u64[o + q];
  sp := call hoist_walk(DIND.u64[p + 4], i, k, tg, ws, sp, 4000000000);
  if DIND.u64[p] == 5 {
    sp := call hoist_rules_go(k, i, tg, ws, sp, DIND.u64[p + 7], DIND.u64[p + 8], 0)
  };
  x := call hoist_block_go(k, i, tg, ws, sp, o, c, q + 1);
  return x
}

/-- `hoist_deps_of(k, i, x, tg, ws, sp)`: the constants of the record at `DECL[x ..]` (position
`k`), one visited set: the type and the value; an inductive block's members; a quotient none. The
new stack size. -/
-- con-ron: ConRon/Arena/Frontend/NatOpGround.lean:155-197 ConRon.Arena.Frontend.hoistClosure.pushDeps
-- con-ron: ConRon/Arena/Frontend/NatOpGround.lean:97-106 ConRon.Arena.Frontend.IDeclaration.usedConsts
@[l_impl ConRon.Arena.Frontend.hoistClosure.pushDeps ConRon.Arena.Frontend.IDeclaration.usedConsts]
def hoistDepsOfL : FunDecl := lfn (k, i, x, tg, ws, sp) locals (z, kd) {
  z := call hs_clear();
  kd := DECL.u64[x];
  if kd == 1 {
    sp := call hoist_walk(DECL.u64[x + 4], i, k, tg, ws, sp, 4000000000);
    return sp
  };
  if kd == 2 || kd == 3 || kd == 4 {
    sp := call hoist_walk(DECL.u64[x + 4], i, k, tg, ws, sp, 4000000000);
    sp := call hoist_walk(DECL.u64[x + 5], i, k, tg, ws, sp, 4000000000);
    return sp
  };
  if kd != 6 { return sp };
  sp := call hoist_block_go(k, i, tg, ws, sp, DECL.u64[x + 2], DECL.u64[x + 3], 0);
  return sp
}

/-- `hoist_close_go(i, ord, tg, ws, sp)`: the worklist `ws[0 ‥ sp)`: pop a position, push the
positions its constants reach (`hoist_deps_of`), until empty. -/
-- con-ron: ConRon/Arena/Frontend/NatOpGround.lean:155-197 ConRon.Arena.Frontend.hoistClosure
-- con-ron: ConRon/Arena/Frontend/NatOpGround.lean:140-145 ConRon.Arena.Frontend.hoistDone
-- con-ron: ConRon/Arena/Frontend/NatOpGround.lean:147-153 ConRon.Arena.Frontend.hoistDropDone
@[l_impl ConRon.Arena.Frontend.hoistClosure ConRon.Arena.Frontend.hoistDone
  ConRon.Arena.Frontend.hoistDropDone]
def hoistCloseGoL : FunDecl := lfn (i, ord, tg, ws, sp) locals (k, r) {
  if sp == 0 { return 0 };
  k := IW.u64[ws + sp - 1];
  sp := call hoist_deps_of(k, i, 1 + 8 * IW.u64[ord + k], tg, ws, sp - 1);
  r := call hoist_close_go(i, ord, tg, ws, sp);
  return r
}

/-- `hoist_closure(i, j, ord, tg, ws)`: position `j` (after `i`) and every position it reaches
through unmarked positions after `i` get target `i`. -/
-- con-ron: ConRon/Arena/Frontend/NatOpGround.lean:155-197 ConRon.Arena.Frontend.hoistClosure
def hoistClosureL : FunDecl := lfn (i, j, ord, tg, ws) locals (r) {
  if IW.u64[tg + j] != 0 { return 0 };
  IW.u64[tg + j] := i + 1;
  IW.u64[ws] := j;
  r := call hoist_close_go(i, ord, tg, ws, 1);
  return r
}

/-! ## The targets -/

/-- `slice_has(o, l, n, j)`: `n` in the `IW` slice `IW[o + j ‥ o + l)`. -/
-- con-ron: none — `List.contains` on an `IW` slice (`natOpNames.contains`)
def sliceHasL : FunDecl := lfn (o, l, n, j) locals (r) {
  if l <= j { return 0 };
  if IW.u64[o + j] == n { return 1 };
  r := call slice_has(o, l, n, j + 1);
  return r
}

/-- `nat_op_record(n)`: `isNatOpRecord` of a definition named `n`. -/
-- con-ron: ConRon/Arena/Frontend/NatOpGround.lean:108-116 ConRon.Arena.Frontend.isNatOpRecord
@[l_impl ConRon.Arena.Frontend.isNatOpRecord]
def natOpRecordL : FunDecl := lfn (n) locals (o1, l1, o2, l2, a, b) {
  (o1, l1) := call nat_div_mod_names();
  (o2, l2) := call nat_op_names();
  a := call slice_has(o1, l1, n, 0);
  b := call slice_has(o2, l2, n, 0);
  if a != 0 || b != 0 { return 1 };
  return 0
}

/-- `hoist_deps(i, o, l, q, ord, tg, ws)`: the grounds `IW[o + q ‥ o + l)` of the operation at
`i`: each first declared after `i` pulls its closure ahead of `i`. -/
-- con-ron: ConRon/Arena/Frontend/NatOpGround.lean:283-311 ConRon.Arena.Frontend.hoistTargetsGo.hoistDeps
@[l_impl ConRon.Arena.Frontend.hoistTargetsGo.hoistDeps]
def hoistDepsL : FunDecl := lfn (i, o, l, q, ord, tg, ws) locals (m, z, r) {
  if l <= q { return 0 };
  m := call hoist_ix(IW.u64[o + q]);
  if m != 0 && i + 1 < m { z := call hoist_closure(i, m - 1, ord, tg, ws) };
  r := call hoist_deps(i, o, l, q + 1, ord, tg, ws);
  return r
}

/-- `hoist_targets_go(ord, c, tg, ws, i)`: positions `i ‥ c`: for every pinned `Nat` operation
record (a definition named in `natDivModNames`/`natOpNames`), its grounds' closures. -/
-- con-ron: ConRon/Arena/Frontend/NatOpGround.lean:283-311 ConRon.Arena.Frontend.hoistTargetsGo
@[l_impl ConRon.Arena.Frontend.hoistTargetsGo]
def hoistTargetsGoL : FunDecl := lfn (ord, c, tg, ws, i) locals (x, n, op, o, l, z, r) {
  if c <= i { return 0 };
  x := 1 + 8 * IW.u64[ord + i];
  if DECL.u64[x] == 2 {
    n := DECL.u64[x + 1];
    op := call nat_op_record(n);
    if op != 0 {
      (o, l) := call nat_op_deps(n);
      z := call hoist_deps(i, o, l, 0, ord, tg, ws)
    }
  };
  r := call hoist_targets_go(ord, c, tg, ws, i + 1);
  return r
}

/-! ## The reorder -/

/-- `hoist_zero(o, c, k)`: `IW[o + k ‥ o + c) := 0`. -/
-- con-ron: none — L scratch-array plumbing (the twin's maps and arrays start empty)
def hoistZeroL : FunDecl := lfn (o, c, k) locals (r) {
  if c <= k { return 0 };
  IW.u64[o + k] := 0;
  r := call hoist_zero(o, c, k + 1);
  return r
}

/-- `hoist_any(tg, c, k)`: `1` if some position `k ‥ c` has a target (the map is not empty). -/
-- con-ron: ConRon/Arena/Frontend/NatOpGround.lean:366-373 ConRon.Arena.Frontend.hoistNatOpGround
def hoistAnyL : FunDecl := lfn (tg, c, k) locals (r) {
  if c <= k { return 0 };
  if IW.u64[tg + k] != 0 { return 1 };
  r := call hoist_any(tg, c, k + 1);
  return r
}

/-- `hoist_bucket(tg, c, hd, tl, nx, k)`: positions `k ‥ c` with a target `t` appended, in order,
to the list of target `t` (`hd[t]`, `tl[t]`: its first and last position `+ 1`; `nx[k]`: the next
one `+ 1`). -/
-- con-ron: ConRon/Arena/Frontend/NatOpGround.lean:322-330 ConRon.Arena.Frontend.hoistKey
-- con-ron: ConRon/Arena/Frontend/NatOpGround.lean:332-338 ConRon.Arena.Frontend.hoistLt
@[l_impl ConRon.Arena.Frontend.hoistKey ConRon.Arena.Frontend.hoistLt]
def hoistBucketL : FunDecl := lfn (tg, c, hd, tl, nx, k) locals (t, r) {
  if c <= k { return 0 };
  t := IW.u64[tg + k];
  if t != 0 {
    if IW.u64[hd + t - 1] == 0 {
      IW.u64[hd + t - 1] := k + 1
    } else {
      IW.u64[nx + IW.u64[tl + t - 1] - 1] := k + 1
    };
    IW.u64[tl + t - 1] := k + 1
  };
  r := call hoist_bucket(tg, c, hd, tl, nx, k + 1);
  return r
}

/-- `hoist_chain(ord, nx, out, q, e)`: the list from `e` (a position `+ 1`, `0` at its end): the
records to `out[q ..]`; the new `q`. -/
-- con-ron: ConRon/Arena/Frontend/NatOpGround.lean:350-357 ConRon.Arena.Frontend.reorder
def hoistChainL : FunDecl := lfn (ord, nx, out, q, e) locals (r) {
  if e == 0 { return q };
  IW.u64[out + q] := IW.u64[ord + e - 1];
  r := call hoist_chain(ord, nx, out, q + 1, IW.u64[nx + e - 1]);
  return r
}

/-- `hoist_emit(ord, c, tg, hd, nx, out, q, p)`: positions `p ‥ c` of the sorted order: the
positions moved to `p`, then `p` itself unless it moved. -/
-- con-ron: ConRon/Arena/Frontend/NatOpGround.lean:350-357 ConRon.Arena.Frontend.reorder
@[l_impl ConRon.Arena.Frontend.reorder]
def hoistEmitL : FunDecl := lfn (ord, c, tg, hd, nx, out, q, p) locals (r) {
  if c <= p { return 0 };
  q := call hoist_chain(ord, nx, out, q, IW.u64[hd + p]);
  if IW.u64[tg + p] == 0 {
    IW.u64[out + q] := IW.u64[ord + p];
    q += 1
  };
  r := call hoist_emit(ord, c, tg, hd, nx, out, q, p + 1);
  return r
}

/-- `hoist_apply(ord, c, tg)`: the positions sorted by `hoistKey` (the key `(t, 0, k)` of a
position moved to `t`, `(k, 1, k)` of one that stays; distinct keys), as a new `IW` slice of
record indices. -/
-- con-ron: ConRon/Arena/Frontend/NatOpGround.lean:359-364 ConRon.Arena.Frontend.applyHoist
@[l_impl ConRon.Arena.Frontend.applyHoist]
def hoistApplyL : FunDecl := lfn (ord, c, tg) locals (hd, tl, nx, out, z) {
  hd := call iw_alloc(c);
  tl := call iw_alloc(c);
  nx := call iw_alloc(c);
  out := call iw_alloc(c);
  z := call hoist_zero(hd, c, 0);
  z := call hoist_zero(nx, c, 0);
  z := call hoist_bucket(tg, c, hd, tl, nx, 0);
  z := call hoist_emit(ord, c, tg, hd, nx, out, 0, 0);
  return out
}

/-- `hoist_nat_op_ground(ord, c)`: the order after the hoist (`ord` itself when nothing moves). -/
-- con-ron: ConRon/Arena/Frontend/NatOpGround.lean:366-373 ConRon.Arena.Frontend.hoistNatOpGround
-- con-ron: ConRon/Arena/Frontend/NatOpGround.lean:313-318 ConRon.Arena.Frontend.hoistTargets
@[l_impl ConRon.Arena.Frontend.hoistNatOpGround ConRon.Arena.Frontend.hoistTargets]
def hoistNatOpGroundL : FunDecl := lfn (ord, c) locals (z, tg, ws, a, r) {
  z := call hn_clear();
  z := call hoist_index_go(ord, c, 0);
  tg := call iw_alloc(c);
  ws := call iw_alloc(c);
  z := call hoist_zero(tg, c, 0);
  z := call hoist_targets_go(ord, c, tg, ws, 0);
  a := call hoist_any(tg, c, 0);
  if a == 0 { return ord };
  r := call hoist_apply(ord, c, tg);
  return r
}

/-- The hoist's functions (`preludeProg` takes them). -/
def hoistProg : Prog :=
  [("hoist_ins", hoistInsL), ("hoist_names_go", hoistNamesGoL), ("hoist_names", hoistNamesL),
   ("hoist_index_go", hoistIndexGoL), ("hoist_ix", hoistIxL), ("hoist_note", hoistNoteL),
   ("hoist_walk", hoistWalkL), ("hoist_app", hoistAppL), ("hoist_lam", hoistLamL),
   ("hoist_forall", hoistForallL), ("hoist_let", hoistLetL), ("hoist_proj", hoistProjL),
   ("hoist_fvar", hoistFvarL), ("hoist_rules_go", hoistRulesGoL), ("hoist_block_go", hoistBlockGoL),
   ("hoist_deps_of", hoistDepsOfL), ("hoist_close_go", hoistCloseGoL),
   ("hoist_closure", hoistClosureL), ("hoist_deps", hoistDepsL),
   ("hoist_targets_go", hoistTargetsGoL), ("hoist_zero", hoistZeroL), ("hoist_any", hoistAnyL),
   ("hoist_bucket", hoistBucketL), ("hoist_chain", hoistChainL), ("hoist_emit", hoistEmitL),
   ("hoist_apply", hoistApplyL), ("hoist_nat_op_ground", hoistNatOpGroundL),
   ("slice_has", sliceHasL), ("nat_op_record", natOpRecordL),
   ("hs_find", memoFindG hsSch), ("hs_put", memoPutG hsSch), ("hs_clear", memoClearG hsSch),
   ("hn_find", memoFindG hnSch), ("hn_put", memoPutG hnSch), ("hn_clear", memoClearG hnSch)]

/-- The hoist's functions in a program. -/
abbrev HoistProg (p : Prog) : Prop := ProgHas p hoistProg

/-- The functions outside the hoist it calls (the `Nat` operations' names, grounds and pins,
`iw_alloc`). -/
def hoistExtProg : Prog :=
  [("nat_op_names", natOpNamesL), ("nat_div_mod_names", natDivModNamesL),
   ("nat_op_deps", natOpDepsL), ("pin_at", pinAtL), ("iw_alloc", iwAlloc),
   ("nat_op_pins", natOpPinsL), ("nat_op_pins_a", natOpPinsAL), ("nat_op_pins_b", natOpPinsBL),
   ("nat_op_pins_c", natOpPinsCL)]

/-- The functions outside the hoist in a program. -/
abbrev HoistExt (p : Prog) : Prop := ProgHas p hoistExtProg

/-! ## The name index -/

/-- **`hoist_ins` is its model `hInsW`** (generated). -/
l_model hoistIns_spec (p : Prog) (hp : HoistProg p)
  fns [hp.get "hoist_ins" ↦ hInsW]
  specs [memoFindG_spec hnSch p _ (hp.get "hn_find") n,
    memoPutG_spec hnSch p _ (hp.get "hn_put") n]
  grind [arena_grind]

/-- **`hoist_names_go` is its model `hNamesGoW`** (generated). -/
l_model hoistNamesGo_spec (p : Prog) (hp : HoistProg p)
  fns [hp.get "hoist_names_go" ↦ hNamesGoW]
  specs [hoistIns_spec p hp n]
  grind [arena_grind]

/-- **`hoist_names` is its model `hNamesW`** (generated). -/
l_model hoistNames_spec (p : Prog) (hp : HoistProg p)
  fns [hp.get "hoist_names" ↦ hNamesW]
  specs [hoistIns_spec p hp n, hoistNamesGo_spec p hp n]
  grind [arena_grind]

/-- **`hoist_index_go` is its model `hIndexGoW`** (generated). -/
l_model hoistIndexGo_spec (p : Prog) (hp : HoistProg p)
  fns [hp.get "hoist_index_go" ↦ hIndexGoW]
  specs [hoistNames_spec p hp n]
  grind [arena_grind]

/-- **`hoist_ix` is its model `hIxW`** (generated; reads only). -/
l_model hoistIx_spec (p : Prog) (hp : HoistProg p)
  fns [hp.get "hoist_ix" ↦ hIxW]
  specs [memoFindG_spec hnSch p _ (hp.get "hn_find") n]
  grind [arena_grind]

/-! ## The closure -/

/-- **`hoist_note` is its model `hNoteW`** (generated). -/
l_model hoistNote_spec (p : Prog) (hp : HoistProg p)
  fns [hp.get "hoist_note" ↦ hNoteW]
  specs [hoistIx_spec p hp n]
  grind [arena_grind] extra [L.st64]

/-- **`hoist_walk` and its arms are their models** (generated). -/
l_model hoistWalk_spec (p : Prog) (hp : HoistProg p)
  fns [hp.get "hoist_walk" ↦ hWalkW, hp.get "hoist_app" ↦ hAppW, hp.get "hoist_lam" ↦ hLamW,
    hp.get "hoist_forall" ↦ hForallW, hp.get "hoist_let" ↦ hLetW, hp.get "hoist_proj" ↦ hProjW,
    hp.get "hoist_fvar" ↦ hFvarW]
  specs [memoFindG_spec hsSch p _ (hp.get "hs_find") n,
    memoPutG_spec hsSch p _ (hp.get "hs_put") n, hoistNote_spec p hp n]
  grind [arena_grind] fold [tierW, idxW]
  extra [evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  finish [tierW, idxW] gen 20 heartbeats 1000000

/-- **`hoist_rules_go` is its model `hRulesGoW`** (generated). -/
l_model hoistRulesGo_spec (p : Prog) (hp : HoistProg p)
  fns [hp.get "hoist_rules_go" ↦ hRulesGoW]
  specs [(hoistWalk_spec p hp n).1]
  grind [arena_grind]

/-- **`hoist_block_go` is its model `hBlockGoW`** (generated). -/
l_model hoistBlockGo_spec (p : Prog) (hp : HoistProg p)
  fns [hp.get "hoist_block_go" ↦ hBlockGoW]
  specs [(hoistWalk_spec p hp n).1, hoistRulesGo_spec p hp n]
  grind [arena_grind]

/-- **`hoist_deps_of` is its model `hDepsOfW`** (generated). -/
l_model hoistDepsOf_spec (p : Prog) (hp : HoistProg p)
  fns [hp.get "hoist_deps_of" ↦ hDepsOfW]
  specs [memoClearG_spec hsSch p _ (hp.get "hs_clear") n, (hoistWalk_spec p hp n).1,
    hoistBlockGo_spec p hp n]
  grind [arena_grind]

/-- **`hoist_close_go` is its model `hCloseGoW`** (generated). -/
l_model hoistCloseGo_spec (p : Prog) (hp : HoistProg p)
  fns [hp.get "hoist_close_go" ↦ hCloseGoW]
  specs [hoistDepsOf_spec p hp n]
  grind [arena_grind]

/-- **`hoist_closure` is its model `hClosureW`** (generated). -/
l_model hoistClosure_spec (p : Prog) (hp : HoistProg p)
  fns [hp.get "hoist_closure" ↦ hClosureW]
  specs [hoistCloseGo_spec p hp n]
  grind [arena_grind] extra [L.st64]

/-- **`hoist_deps` is its model `hDepsW`** (generated). -/
l_model hoistDeps_spec (p : Prog) (hp : HoistProg p)
  fns [hp.get "hoist_deps" ↦ hDepsW]
  specs [hoistIx_spec p hp n, hoistClosure_spec p hp n]
  grind [arena_grind]

/-! ## The reorder -/

/-- **`hoist_zero` is its model `hZeroW`** (generated). -/
l_model hoistZero_spec (p : Prog) (hp : HoistProg p)
  fns [hp.get "hoist_zero" ↦ hZeroW]
  specs []
  grind [arena_grind] extra [L.st64]

/-- **`hoist_any` is its model `hAnyW`** (generated). -/
l_model hoistAny_spec (p : Prog) (hp : HoistProg p)
  fns [hp.get "hoist_any" ↦ hAnyW]
  specs []
  grind [arena_grind]

/-- **`hoist_bucket` is its model `hBucketW`** (generated). -/
l_model hoistBucket_spec (p : Prog) (hp : HoistProg p)
  fns [hp.get "hoist_bucket" ↦ hBucketW]
  specs []
  grind [arena_grind] extra [L.st64]

/-- **`hoist_chain` is its model `hChainW`** (generated). -/
l_model hoistChain_spec (p : Prog) (hp : HoistProg p)
  fns [hp.get "hoist_chain" ↦ hChainW]
  specs []
  grind [arena_grind] extra [L.st64]

/-- **`hoist_emit` is its model `hEmitW`** (generated). -/
l_model hoistEmit_spec (p : Prog) (hp : HoistProg p)
  fns [hp.get "hoist_emit" ↦ hEmitW]
  specs [hoistChain_spec p hp n]
  grind [arena_grind] extra [L.st64]

/-- **`hoist_apply` is its model `hApplyW`** (generated). -/
l_model hoistApply_spec (p : Prog) (hp : HoistProg p) (ha : p.lookup "iw_alloc" = some iwAlloc)
  fns [hp.get "hoist_apply" ↦ hApplyW]
  specs [iwAlloc_specW p ha n, hoistZero_spec p hp n, hoistBucket_spec p hp n,
    hoistEmit_spec p hp n]
  grind [arena_grind] gen 20 heartbeats 1000000

/-! ## The targets and the whole pass -/

/-- **`slice_has` is its model `hSliceHasW`** (generated; reads only). -/
l_model sliceHas_spec (p : Prog) (hp : HoistProg p)
  fns [hp.get "slice_has" ↦ hSliceHasW ro]
  specs []
  grind [arena_grind]

/-- **`nat_op_record` is its model `hNatOpRecW`** (generated). -/
l_model natOpRecord_spec (p : Prog) (hp : HoistProg p)
  fns [hp.get "nat_op_record" ↦ hNatOpRecW]
  specs [callW_spec p n "nat_div_mod_names" [], callW_spec p n "nat_op_names" [],
    sliceHas_spec p hp n]
  grind [arena_grind]

/-- **`hoist_targets_go` is its model `hTargetsGoW`** (generated). -/
l_model hoistTargetsGo_spec (p : Prog) (hp : HoistProg p)
  fns [hp.get "hoist_targets_go" ↦ hTargetsGoW]
  specs [natOpRecord_spec p hp n, fun s₀ c => callW_spec p n "nat_op_deps" [c] s₀,
    hoistDeps_spec p hp n]
  grind [arena_grind] gen 20

/-- **`hoist_nat_op_ground` is its model `hNatOpGroundW`** (generated). -/
l_model hoistNatOpGround_spec (p : Prog) (hp : HoistProg p) (hx : HoistExt p)
  fns [hp.get "hoist_nat_op_ground" ↦ hNatOpGroundW]
  specs [memoClearG_spec hnSch p _ (hp.get "hn_clear") n, hoistIndexGo_spec p hp n,
    iwAlloc_specW p (hx.get "iw_alloc") n, hoistZero_spec p hp n, hoistTargetsGo_spec p hp n,
    hoistAny_spec p hp n, hoistApply_spec p hp (hx.get "iw_alloc") n]
  grind [arena_grind] gen 20

end L.Checker
