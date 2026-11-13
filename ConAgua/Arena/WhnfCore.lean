module

public import ConAgua.Arena.WhnfSpine
public import ConAgua.Arena.Env
public import ConAgua.Arena.ErecRd

@[expose] public section

/-!
# `whnfCore`: the knot's slot (the loop and its memo policy), the step, the stuck spine, the batched β spine, projections

con-ron's head normalisation without δ (`Arena/Core.lean:2140-2395` and the knot's `whnfCore`
slot, `:3546`), in L:

| L | twin |
|---|---|
| `whnf_core(mode, cheap, vis, d, e)` | the knot's `whnfCore` slot = `whnfCoreBody` = `whnfCoreLoop … whnfCoreLoopFuel e #[] #[]` (an uncounted L loop; the pending keys a stack slice) |
| `whnf_core_lookup_at(mode, key, cheap, e)` | `whnfCoreLookupAt`, `whnfCoreLookup` (`wk`/`wc` at the mode's eager bit) |
| `whnf_core_store_chain(mode, cheap, pb, pn, pc, v)` | `whnfCoreStoreChain` |
| `whnf_core_store_keys(mode, o, n, i, v)`, `whnf_core_store_cheap_keys(…)` | `whnfCoreStoreKeys`, `whnfCoreStoreCheapKeys` |
| `whnf_core_step(mode, cheap, vis, d, h, e)` | `whnfCoreStep` (`(0, e)` done, `(1, e)` continue); its `app` arm is `whnf_stuck` or `whnf_core_app` |
| `whnf_stuck(mode, vis, d, h, e)`, `iota_target(vis, h)` | `whnfStuck`, `iotaTarget` |
| `whnf_core_app(mode, cheap, vis, d, e)` | `whnfCoreStepApp` |
| `whnf_app(mode, vis, d, v, hd, vo, vn, same, ao, an, i)` | `whnfApp`: the head's arguments `vargs` a stack slice `(vo, vn)` at the top, the spine's arguments and nodes the slices `(ao, an)`, `(ao + an, an)` |
| `beta_peel(t, a, ao, an, i)` | `betaPeel t #[a] args i` (the accumulator a stack slice) |
| `whnf_core_step_proj(mode, cheap, vis, d, e, sn, i, pe)` | `whnfCoreStepProj` |
| `reduce_proj_core(mode, vis, d, sn, i, c)` | `reduceProjCore` |
| `proj_lit_to_ctor(mode, vis, d, h)` | `projLitToCtor` |
| `proj_cert(vis, k, ao, an)` | `projCert` (with `teleArityOk` = `peel_pis`) |

Callees from elsewhere: the spine walks (`WhnfSpine.lean`), `whnf` (`WhnfDelta.lean`),
`iota_rec_at` (`WhnfIota.lean`), `env_find` (`Env.lean`), `ls_node` (lane `levels`), `mk_app`,
`intern_bvar`; stubs (`CoreCallees` below): `inst1` (`instantiate1Fast` at the exact
`coreWalkFuel` counter, which lane `exprops`' `inst_entry` does not have), `find_proj`
(`IFEnv.findProj?`: interns the table name); from
`WhnfCallees`: `inst_list`, `str_lit_stored`, `str_lit_ctor`.

The `projCertAt` mode test is `mode & 1 == 0` (`verifiedChecks`: the two verified modes).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## The L code -/

/-- The loop of `whnf_core`, named for its spec. -/
def whnfCoreLoopB : Stmt :=
    lblk (mode, cheap, vis, d, e, pb, pn, pc, g, h, hg, sh, key, safe, f, x, st, r, stb, u) {
  while 0 == 0 {
    g := ⟦e⟧.tag;
    if (657 >> g) & 1 == 0 {
      u := call whnf_core_store_chain(mode, cheap, pb, pn, pc, e);
      CTL.u64[136] := pb;
      return e
    };
    h := call get_app_fn(e);
    hg := ⟦h⟧.tag;
    sh := (334 >> hg) & 1;
    key := ((640 >> g) & 1) | (u64(g == 4) & (1 - sh));
    safe := ((128 >> g) & 1) | (u64(g == 4) & (sh | u64(hg == 5)));
    (f, x) := call whnf_core_lookup_at(mode, key, cheap, e);
    if f != 0 {
      u := call whnf_core_store_chain(mode, cheap, pb, pn, pn, x);
      CTL.u64[136] := pb;
      return x
    };
    (st, r) := call whnf_core_step(mode, cheap, vis, d, h, e);
    stb := u64(cheap == 0) & key & (u64(st != 0) | u64(g != 4) | u64(r != e));
    if stb != 0 {
      if len(SPN.u64) <= pb + pn || len(CTL.u64) <= 136 { abort };
      SPN.u64[pb + pn] := e;
      pn += 1;
      CTL.u64[136] := pb + pn
    };
    if safe == 0 { pc := pn };
    if st == 0 {
      u := call whnf_core_store_chain(mode, cheap, pb, pn, pc, r);
      CTL.u64[136] := pb;
      return r
    };
    e := r
  }
}

/-- **The knot's `whnfCore` slot: the loop** (`whnfCoreBody` = `whnfCoreLoop … whnfCoreLoopFuel e #[]
#[]`, an uncounted L loop), with the official memo policy (con-ron's #572): a stuck tag ends the
chain before any lookup (`whnfCoreStuckTag`); every other step computes the spine head `h`
(`getAppFn`), looks its term up when it is a key (`whnfCoreKey`, `whnfCoreLookupAt`: `wk` in the
cheap mode, `wc` otherwise, at the mode's eager bit), and a hit ends the chain. **The pending keys**
`pend` are the stack slice `SPN[pb, pb + pn)` at the top found at entry (`pb`), pushed as they come
(the step restores the top it found, so they survive it); the cheap keys `pendC` are its suffix
from `pc` (`pushCheapKey` either pushes where `pushKey` pushes or empties `pendC`: then `pc := pn`).
At a chain's end the keys are stored (`whnf_core_store_chain`) and the top put back. `isStuckHead`,
`whnfCoreKey`, `whnfCoreCheapSafe`, `whnfCoreStoresDone`, `pushKey`, `pushCheapKey` are inline, the tag
tests branch-free as bit masks over the tag (`657`: the tags `bvar`, `app`, `letE`, `proj` that
`whnfCoreStuckTag` rejects; `334`: `fvar`, `sort`, `const`, `forallE`, `lit`, the stuck heads; `640`:
`letE`, `proj`; `128`: `letE`), so the loop's model has few paths. A full stack aborts (a fixed
capacity), and so does a top past the stack's end at entry. -/
-- con-ron: ConRon/Arena/Core.lean:2931-2939 ConRon.Arena.whnfCoreBody
-- con-ron: ConRon/Arena/Core.lean:2892-2929 ConRon.Arena.whnfCoreLoop
-- con-ron: ConRon/Arena/Core.lean:2616-2626 ConRon.Arena.isStuckHead
-- con-ron: ConRon/Arena/Core.lean:2796-2804 ConRon.Arena.whnfCoreKey
-- con-ron: ConRon/Arena/Core.lean:2812-2819 ConRon.Arena.whnfCoreCheapSafe
-- con-ron: ConRon/Arena/Core.lean:2806-2810 ConRon.Arena.whnfCoreStoresDone
-- con-ron: ConRon/Arena/Core.lean:2821-2824 ConRon.Arena.pushKey
-- con-ron: ConRon/Arena/Core.lean:2826-2831 ConRon.Arena.pushCheapKey
-- con-ron: ConRon/Arena/Core.lean:4313-4392 ConRon.Arena.coreKnot
-- con-ron: ConRon/Arena/Core.lean:2494-2508 ConRon.Arena.whnfCoreStuckTag
@[no_expose, l_impl ConRon.Arena.whnfCoreBody ConRon.Arena.whnfCoreLoop ConRon.Arena.whnfCoreStuckTag
  ConRon.Arena.isStuckHead ConRon.Arena.whnfCoreKey ConRon.Arena.whnfCoreCheapSafe
  ConRon.Arena.whnfCoreStoresDone ConRon.Arena.pushKey ConRon.Arena.pushCheapKey
  ConRon.Arena.coreKnot]
def whnfCoreL : FunDecl :=
    lfn (mode, cheap, vis, d, e) locals (pb, pn, pc, g, h, hg, sh, key, safe, f, x, st, r, stb, u) {
  pb := CTL.u64[136];
  if len(SPN.u64) < pb { abort };
  pn := 0;
  pc := 0;
  ⟪whnfCoreLoopB⟫;
  abort
}

/-- The `app` arm of `whnf_core_step` at a head that is not its own head normal form: the batched
β spine. -/
-- con-ron: ConRon/Arena/Core.lean:2754-2765 ConRon.Arena.whnfCoreStepApp
@[no_expose, l_impl ConRon.Arena.whnfCoreStepApp]
def whnfCoreAppL : FunDecl :=
    lfn (mode, cheap, vis, d, e) locals (top, h, so, sn, v, st, r) {
  top := CTL.u64[136];
  (h, so, sn) := call get_app_spine(e);
  v := call whnf_core(mode, cheap, vis, d, h);
  (st, r) := call whnf_core_app2(mode, vis, d, v, h, so, sn);
  CTL.u64[136] := top;
  return (st, r)
}

/-- The second half of `whnf_core_app`: the reduct's spine, then the β/ι walk. -/
-- con-ron: ConRon/Arena/Core.lean:2754-2765 ConRon.Arena.whnfCoreStepApp
@[no_expose, l_impl ConRon.Arena.whnfCoreStepApp]
def whnfCoreApp2L : FunDecl := lfn (mode, vis, d, v, h, so, sn) locals (top, hd, ho, hn, st, r) {
  top := CTL.u64[136];
  (hd, ho, hn) := call head_and_args(v);
  (st, r) := call whnf_app(mode, vis, d, v, hd, ho, hn, u64(v == h), so, sn, 0);
  CTL.u64[136] := top;
  return (st, r)
}

/-- The step at the spine head `h` (the loop's `getAppFn`): an application whose head is its own
head normal form (`isStuckHead`, inline) is `whnf_stuck`'s, any other `whnf_core_app`'s. -/
-- con-ron: ConRon/Arena/Core.lean:2767-2792 ConRon.Arena.whnfCoreStep
-- con-ron: ConRon/Arena/Core.lean:2616-2626 ConRon.Arena.isStuckHead
@[no_expose, l_impl ConRon.Arena.whnfCoreStep ConRon.Arena.isStuckHead]
def whnfCoreStepL : FunDecl :=
    lfn (mode, cheap, vis, d, h, e) locals (g, t, i, hg, st, r) {
  g := ⟦e⟧.tag;
  t := ⟦e⟧.tier;
  i := ⟦e⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if g == 4 {
    i := ⟦e⟧.aidx;
    if APP⟨t⟩.count <= i { abort };
    hg := ⟦h⟧.tag;
    if (334 >> hg) & 1 != 0 {
      (st, r) := call whnf_stuck(mode, vis, d, h, e);
      return (st, r)
    };
    (st, r) := call whnf_core_app(mode, cheap, vis, d, e);
    return (st, r)
  };
  if g == 9 {
    if PROJ⟨t⟩.count <= i { abort };
    (st, r) := call whnf_core_step_proj(mode, cheap, vis, d, e, PROJ⟨t, i⟩.n,
      PROJ⟨t, i⟩.i, PROJ⟨t, i⟩.e);
    return (st, r)
  };
  if g == 7 {
    if LET⟨t⟩.count <= i { abort };
    r := call inst1(LET⟨t, i⟩.b, LET⟨t, i⟩.v, 0);
    return (1, r)
  };
  if g == 0 { if BVAR⟨t⟩.count <= i { abort }; fail R_WHNF_BEYOND_THE };
  if g == 1 { if FVAR⟨t⟩.count <= i { abort }; return (0, e) };
  if g == 2 { if SORT⟨t⟩.count <= i { abort }; return (0, e) };
  if g == 3 { if CONST⟨t⟩.count <= i { abort }; return (0, e) };
  if g == 5 { if LAM⟨t⟩.count <= i { abort }; return (0, e) };
  if g == 6 { if FORALL⟨t⟩.count <= i { abort }; return (0, e) };
  if g == 8 { if LIT⟨t⟩.count <= i { abort }; return (0, e) };
  abort
}

/-- The ι target of a spine head `h`: `(1, mI)` at a stored recursor at its own number of levels
(the twin's `some (mI + 1)`: the word is the major's index, so the length never wraps), `(0, 0)`
otherwise; a dangling handle aborts. -/
-- con-ron: ConRon/Arena/Core.lean:2628-2643 ConRon.Arena.iotaTarget
@[no_expose, l_impl ConRon.Arena.iotaTarget]
def iotaTargetL : FunDecl := lfn (vis, h) locals (t, x, f, q, lo, usl) {
  if ⟦h⟧.tag != 3 { return (0, 0) };
  t := ⟦h⟧.tier;
  x := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CONST⟨t⟩.count <= x { abort };
  (f, q) := call env_find(CONST⟨t, x⟩.n, vis);
  if f == 0 { return (0, 0) };
  if EREC⦃q⦄ != 5 { return (0, 0) };
  (lo, usl) := call ls_node(CONST⟨t, x⟩.us);
  if usl == EREC⦃q + 3⦄ { return (1, EREC⦃q + 5⦄) };
  return (0, 0)
}

/-- The stuck spine `e` at head `h`: the ι step once, at the target prefix `k + 1` of the
spine's arguments (pushed at the top by `get_app_args`, the top put back), else `e` itself. -/
-- con-ron: ConRon/Arena/Core.lean:2645-2663 ConRon.Arena.whnfStuck
@[no_expose, l_impl ConRon.Arena.whnfStuck]
def whnfStuckL : FunDecl := lfn (mode, vis, d, h, e) locals (f, k, top, ao, an, st, e2, e3) {
  (f, k) := call iota_target(vis, h);
  if f == 0 { return (0, e) };
  top := CTL.u64[136];
  (ao, an) := call get_app_args(e);
  if k < an {
    (st, e2) := call iota_rec_at(mode, vis, d, h, ao, k + 1);
    if st != 0 {
      e3 := call mk_app_n_from(e2, ao, an, k + 1);
      CTL.u64[136] := top;
      return (1, e3)
    }
  };
  CTL.u64[136] := top;
  return (0, e)
}

/-- The loop's lookup: at a key, the mode's `whnfCore` memo at `e`: `(1, x)` a hit, `(0, 0)` a miss
(`wk` in the cheap mode, `wc` otherwise, at the mode's eager bit); `(0, 0)` at a non-key. -/
-- con-ron: ConRon/Arena/Core.lean:2886-2890 ConRon.Arena.whnfCoreLookupAt
-- con-ron: ConRon/Arena/Core.lean:2880-2884 ConRon.Arena.whnfCoreLookup
@[no_expose, l_impl ConRon.Arena.whnfCoreLookupAt ConRon.Arena.whnfCoreLookup]
def whnfCoreLookupL : FunDecl := lfn (mode, key, cheap, e) locals (fd, j, dd) {
  if key == 0 { return (0, 0) };
  if cheap != 0 {
    (fd, j, dd) := call wk_find(e, ((mode >> 1) & 1) << 32);
    if fd != 0 { return (1, WKM.u64[j * 4 + 3]) };
    return (0, 0)
  };
  (fd, j, dd) := call wc_find(e, ((mode >> 1) & 1) << 32);
  if fd != 0 { return (1, WCM.u64[j * 4 + 3]) };
  return (0, 0)
}

/-- The keys `SPN[o + i, o + n)` map to `v` in the full mode's memo (`wc`, `whnfCoreSet` each). -/
-- con-ron: ConRon/Arena/Core.lean:2851-2858 ConRon.Arena.whnfCoreStoreKeys
-- con-ron: ConRon/Arena/Core.lean:2833-2840 ConRon.Arena.whnfCoreSet
@[no_expose, l_impl ConRon.Arena.whnfCoreStoreKeys ConRon.Arena.whnfCoreSet]
def whnfCoreStoreKeysL : FunDecl := lfn (mode, o, n, i, v) locals (k, fd, j, dd, u) {
  for i < n {
    k := SPN.u64[o + i];
    (fd, j, dd) := call wc_find(k, ((mode >> 1) & 1) << 32);
    u := call wc_put(k, ((mode >> 1) & 1) << 32, v, fd, j)
  };
  return 0
}

/-- The cheap keys `SPN[o + i, o + n)` map to `v` in the cheap mode's memo (`wk`,
`whnfCoreCheapSet` each). -/
-- con-ron: ConRon/Arena/Core.lean:2860-2867 ConRon.Arena.whnfCoreStoreCheapKeys
-- con-ron: ConRon/Arena/Core.lean:2842-2849 ConRon.Arena.whnfCoreCheapSet
@[no_expose, l_impl ConRon.Arena.whnfCoreStoreCheapKeys ConRon.Arena.whnfCoreCheapSet]
def whnfCoreStoreCheapKeysL : FunDecl := lfn (mode, o, n, i, v) locals (k, fd, j, dd, u) {
  for i < n {
    k := SPN.u64[o + i];
    (fd, j, dd) := call wk_find(k, ((mode >> 1) & 1) << 32);
    u := call wk_put(k, ((mode >> 1) & 1) << 32, v, fd, j)
  };
  return 0
}

/-- Store a finished chain: `pend` the slice `SPN[pb, pb + pn)`, `pendC` its suffix from `pc`. -/
-- con-ron: ConRon/Arena/Core.lean:2869-2878 ConRon.Arena.whnfCoreStoreChain
@[no_expose, l_impl ConRon.Arena.whnfCoreStoreChain]
def whnfCoreStoreChainL : FunDecl := lfn (mode, cheap, pb, pn, pc, v) locals (u) {
  if cheap != 0 { return 0 };
  if pn == 0 { return 0 };
  u := call whnf_core_store_keys(mode, pb, pn, 0, v);
  u := call whnf_core_store_cheap_keys(mode, pb + pc, pn - pc, 0, v);
  return 0
}

/-- con-ron: ConRon/Arena/Core.lean:2581-2612 ConRon.Arena.whnfApp
con-ron: ConRon/Arena/Core.lean:2457-2461 ConRon.Arena.internAppRebuilt -/
@[no_expose, l_impl ConRon.Arena.whnfApp ConRon.Arena.internAppRebuilt]
def whnfAppL : FunDecl :=
    lfn (mode, vis, d, v, hd, vo, vn, same, ao, an, i) locals (top, a, node, ap, st, e2, e3, t, x) {
  top := CTL.u64[136];
  for i < an {
    a := SPN.u64[ao + i];
    node := SPN.u64[ao + an + i];
    if ⟦v⟧.tag == 5 {
      (t, x) := node LAM⟦v⟧;
      (st, e3) := call beta_peel(LAM⟨t, x⟩.b, a, ao, an, i + 1);
      CTL.u64[136] := top;
      return (st, e3)
    };
    if same != 0 { ap := node } else { ap := call mk_app(v, a) };
    same := u64(ap == node);
    if len(SPN.u64) <= vo + vn { abort };
    SPN.u64[vo + vn] := a;
    vn += 1;
    CTL.u64[136] := vo + vn;
    if ⟦hd⟧.tag == 3 {
      (st, e2) := call iota_rec_at(mode, vis, d, hd, vo, vn);
      if st != 0 {
        e3 := call mk_app_n_from(e2, ao, an, i + 1);
        CTL.u64[136] := top;
        return (1, e3)
      }
    };
    v := ap
  };
  CTL.u64[136] := top;
  return (0, v)
}

/-- con-ron: ConRon/Arena/Core.lean:2560-2579 ConRon.Arena.betaPeel -/
@[no_expose, l_impl ConRon.Arena.betaPeel]
def betaPeelL : FunDecl := lfn (t, a, ao, an, i) locals (co, cn, tt, x, e2, e3) {
  co := CTL.u64[136];
  if len(SPN.u64) <= co { abort };
  SPN.u64[co] := a;
  cn := 1;
  CTL.u64[136] := co + 1;
  for i < an {
    if ⟦t⟧.tag != 5 {
      e2 := call inst_list(t, co, cn, 0);
      e3 := call mk_app_n_from(e2, ao, an, i);
      CTL.u64[136] := co;
      return (1, e3)
    };
    (tt, x) := node LAM⟦t⟧;
    t := LAM⟨tt, x⟩.b;
    if len(SPN.u64) <= co + cn { abort };
    SPN.u64[co + cn] := SPN.u64[ao + i];
    cn += 1;
    CTL.u64[136] := co + cn
  };
  e2 := call inst_list(t, co, cn, 0);
  CTL.u64[136] := co;
  return (1, e2)
}

/-- con-ron: ConRon/Arena/Core.lean:2741-2752 ConRon.Arena.whnfCoreStepProj -/
@[no_expose, l_impl ConRon.Arena.whnfCoreStepProj]
def whnfCoreStepProjL : FunDecl := lfn (mode, cheap, vis, d, e, sn, i, pe) locals (c, f, r) {
  if cheap != 0 { c := call whnf_core(mode, 1, vis, d, pe) } else { c := call whnf(mode, vis, d, pe) };
  (f, r) := call reduce_proj_core(mode, vis, d, sn, i, c);
  if f != 0 { return (1, r) };
  return (0, e)
}

/-- con-ron: ConRon/Arena/Core.lean:2706-2739 ConRon.Arena.reduceProjCore -/
@[no_expose, l_impl ConRon.Arena.reduceProjCore]
def reduceProjCoreL : FunDecl :=
    lfn (mode, vis, d, sn, i, c) locals (top, e1, f, q, st, r) {
  top := CTL.u64[136];
  e1 := call proj_lit_to_ctor(mode, vis, d, c);
  (f, q) := call find_proj(vis, sn, i);
  if f == 0 { return (0, 0) };
  (st, r) := call reduce_proj_head(mode, vis, e1, q, i);
  CTL.u64[136] := top;
  return (st, r)
}

/-- `reduceProjCore` from the scrutinee's head on (`q` the table record): the head must be a
constant.
con-ron: ConRon/Arena/Core.lean:2706-2739 ConRon.Arena.reduceProjCore -/
@[no_expose] def reduceProjHeadL : FunDecl :=
    lfn (mode, vis, e1, q, i) locals (hh, t, x, k, us, st, r) {
  hh := call get_app_fn(e1);
  if ⟦hh⟧.tag != 3 { return (0, 0) };
  (t, x) := node CONST⟦hh⟧;
  k := CONST⟨t, x⟩.n;
  us := CONST⟨t, x⟩.us;
  (st, r) := call reduce_proj_fire(mode, vis, e1, q, i, k, us);
  return (st, r)
}

/-- `reduceProjCore` at a constant head `k.{us}`: the arguments (pushed on the stack), the
level count, the shape conditions (the rule fires unguarded). The twin's `args.length = numParams +
numFields` (`Nat`) is tested as `nf <= an && an - nf == np`, which does not wrap; then `np + i < an`.
con-ron: ConRon/Arena/Core.lean:2706-2739 ConRon.Arena.reduceProjCore -/
@[no_expose] def reduceProjFireL : FunDecl :=
    lfn (mode, vis, e1, q, i, k, us) locals (ao, an, lo, usl, np, nf, st, r) {
  (ao, an) := call get_app_args(e1);
  (lo, usl) := call ls_node(us);
  np := EREC⦃q + ⟪Tbl.numParams⟫⦄;
  nf := EREC⦃q + ⟪Tbl.numFields⟫⦄;
  if k == EREC⦃q + ⟪Tbl.ctor⟫⦄ && i < nf && nf <= an && an - nf == np && usl == EREC⦃q + ⟪Tbl.lpsLen⟫⦄ {
    (st, r) := call reduce_proj_arg(mode, vis, k, ao, an, np + i);
    return (st, r)
  };
  return (0, 0)
}

/-- `reduceProjCore`'s fire: argument `j` of the slice `(ao, an)` (else `bvar 0`), certified at
the verified mode.
con-ron: ConRon/Arena/Core.lean:2706-2739 ConRon.Arena.reduceProjCore -/
@[no_expose] def reduceProjArgL : FunDecl :=
    lfn (mode, vis, k, ao, an, j) locals (b0, arg, ok) {
  b0 := call intern_bvar(0);
  if j < an { arg := SPN.u64[ao + j] } else { arg := b0 };
  ok := 1;
  if mode & 1 == 0 { ok := call proj_cert(vis, k, ao, an) };
  if ok != 0 { return (1, arg) };
  return (0, 0)
}

/-- con-ron: ConRon/Arena/Core.lean:2689-2696 ConRon.Arena.projCert
con-ron: ConRon/Arena/Core.lean:2698-2704 ConRon.Arena.projCertAt
con-ron: ConRon/Arena/Core.lean:2682-2687 ConRon.Arena.teleArityOk -/
@[no_expose, l_impl ConRon.Arena.projCert ConRon.Arena.projCertAt ConRon.Arena.teleArityOk]
def projCertL : FunDecl := lfn (vis, k, ao, an) locals (f, q, ok, r) {
  (f, q) := call env_find(k, vis);
  if f == 0 { return 0 };
  if EREC⦃q⦄ != 4 { return 0 };
  (ok, r) := call peel_pis(an, EREC⦃q + 4⦄);
  return u64(ok != 0)
}

/-- con-ron: ConRon/Arena/Core.lean:2228-2240 ConRon.Arena.projLitToCtor -/
@[no_expose, l_impl ConRon.Arena.projLitToCtor]
def projLitToCtorL : FunDecl := lfn (mode, vis, d, h) locals (t, x, s, c) {
  if ⟦h⟧.tag != 8 { return h };
  (t, x) := node LIT⟦h⟧;
  if LIT⟨t, x⟩.kind != 1 { return h };
  s := call str_lit_stored(vis);
  if s == 0 { return h };
  c := call str_lit_ctor(h);
  c := call whnf(mode, vis, d, c);
  return c
}

/-- What the specs need of a program: these functions and the ones they call by name. -/
structure WhnfCoreProg (p : Prog) : Prop where
  spine : SpineProg p
  core : p.lookup "whnf_core" = some whnfCoreL
  step : p.lookup "whnf_core_step" = some whnfCoreStepL
  lookup : p.lookup "whnf_core_lookup_at" = some whnfCoreLookupL
  storeKeys : p.lookup "whnf_core_store_keys" = some whnfCoreStoreKeysL
  storeCheapKeys : p.lookup "whnf_core_store_cheap_keys" = some whnfCoreStoreCheapKeysL
  storeChain : p.lookup "whnf_core_store_chain" = some whnfCoreStoreChainL
  iotaTarget : p.lookup "iota_target" = some iotaTargetL
  stuck : p.lookup "whnf_stuck" = some whnfStuckL
  lsn : p.lookup "ls_node" = some lsNode
  capp : p.lookup "whnf_core_app" = some whnfCoreAppL
  capp2 : p.lookup "whnf_core_app2" = some whnfCoreApp2L
  app : p.lookup "whnf_app" = some whnfAppL
  peel : p.lookup "beta_peel" = some betaPeelL
  sproj : p.lookup "whnf_core_step_proj" = some whnfCoreStepProjL
  rproj : p.lookup "reduce_proj_core" = some reduceProjCoreL
  rphead : p.lookup "reduce_proj_head" = some reduceProjHeadL
  rpfire : p.lookup "reduce_proj_fire" = some reduceProjFireL
  rparg : p.lookup "reduce_proj_arg" = some reduceProjArgL
  cert : p.lookup "proj_cert" = some projCertL
  plit : p.lookup "proj_lit_to_ctor" = some projLitToCtorL
  wcf : p.lookup "wc_find" = some (memoFindG wcSch)
  wcp : p.lookup "wc_put" = some (memoPutG wcSch)
  wkf : p.lookup "wk_find" = some (memoFindG wkSch)
  wkp : p.lookup "wk_put" = some (memoPutG wkSch)
  envrow : p.lookup "env_row_get" = some envRowGetL
  envfind : p.lookup "env_find" = some envFindL
  baserow : p.lookup "base_row_get" = some baseRowGetL
  bvf : p.lookup "bvar_find" = some bvarFind
  bvp : p.lookup "bvar_push" = some bvarPush
  bvi : p.lookup "intern_bvar" = some internBVar

/-! ## Stubs -/

/-- `inst1(e, v, d)` refines `instantiate1Fast coreWalkFuel e v d` (the exact counter). -/
def Inst1OK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb e v d : Word), CoreS dn s₀.mem a₀ vis fe M eb → HW e → HW v →
    CoreSpec p n "inst1" [e, v, d] (instantiate1Fast coreWalkFuel (decE e) (decE v) d.toNat) decH
      s₀ a₀ dn vis fe M eb

/-- The projection entry at field `i` of the table record at `q`, if any. -/
def decEntry (a : Nat → Option Word) (f q : Word) (i : Nat) : Option IProjEntry :=
  if f = 0 then none else (decTbl a q.toNat).map (·.entry i)

/-- `find_proj(vis, T, i)` refines `fe.findProj? T i`: `(0, _)` none, `(1, q)` the table record. -/
def FindProjOK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb T i : Word), CoreS dn s₀.mem a₀ vis fe M eb → HW T →
    CoreSpec p n "find_proj" [vis, T, i] (pure (fe.findProj? (decI T) i.toNat))
      (fun r => decEntry (erecP s₀.mem) (r.headD 0) (r.tail.headD 0) i.toNat) s₀ a₀ dn vis fe
      M eb

/-- `iota_rec_at(mode, vis, d, hd, so, sn)` refines `iotaRecAt` (`WhnfIota.lean`). -/
def IotaRecAtOK (p : Prog) (n : Nat) : Prop :=
  ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d hd so sn : Word) (xs : Array EIdx), n ≤ F → n ≤ 2 ^ 62 →
    SlotPre s₀ a₀ dn vis fe M eb mode → HW hd → SpineR s₀.mem so sn xs →
    so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat →
    CoreSpec p n "iota_rec_at" [mode, vis, d, hd, so, sn]
      (iotaRecAt (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE hd) xs xs.size)
      decOptR s₀ a₀ dn vis fe M eb ResW

/-- **`find_proj` leaves the record pool alone**; `reduce_proj_core` reads the table's words after
it. -/
def ErecKept (p : Prog) : Prop :=
  ∀ (n : Nat) (f : FnName) (vs : List Word) (m : Mem) (r : List Word) (m' : Mem),
    f = "find_proj" → callW p n f vs m = some (r, m') →
    m'.arr64 EREC = m.arr64 EREC ∧ m'.arr64 (tier1 EREC) = m.arr64 (tier1 EREC) ∧
      erRd m' = erRd m ∧ erecP m' = erecP m

/-- **`find_proj` answers a table record that decodes** (added for `reduce_proj_core`):
`FindProjOK` equates the twin's lookup with `decEntry`, which is `none` for a record that does not
decode, so it does not exclude `find_proj` answering `(1, q)` for a `q` that fails to decode (then
`reduce_proj_head` would read garbage where the twin says `none`). The record is read in the
memory the call started from (`ErecKept`: the same after it), and it is a table the environment
holds (what `StoreDen.proj` covers; lane `loopt2`). -/
def ProjFound (p : Prog) : Prop :=
  ∀ (n : Nat) (m : Mem) (a : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb T i : Word) (r : List Word) (m' : Mem), CoreS dn m a vis fe M eb →
    callW p n "find_proj" [vis, T, i] m = some (r, m') → r.headD 0 ≠ 0 →
    ∃ tbl : IProjTable, decTbl (erecP m) (r.tail.headD 0).toNat = some tbl ∧
      ∃ c, fe.findTable? c = some tbl

/-- **The projection-table callee** (`find_proj`) and their record-pool facts: what
`reduce_proj_core` and the ι side's `and_rescue_slots`/`major_to_ctor` assume of them. A part of
`CoreCallees` on its own, so that `major_to_ctor` (which `iota_rec_at` calls) does not take
`CoreCallees.iota` (helper `whnf4-knot`). -/
structure ProjCallees (p : Prog) : Prop where
  findProj : FindProjOK p
  erec : ErecKept p
  projFound : ProjFound p

/-- **The callees of this file not written here.** -/
structure CoreCallees (p : Prog) : Prop extends ProjCallees p where
  inst1 : Inst1OK p
  /-- `iota_rec_at` one level down from the knot at `n` (`WhnfIota.lean`). -/
  iota : ∀ n, KnotUpTo p n → IotaRecAtOK p (n + 1)

/-! ## The specs

Each body at L fuel `n + 1` refines the twin's body at the knot `coreKnot mode eager fe id F`, `F ≥ n`,
given the knot's slots at every fuel up to `n` (`KnotUpTo p n`). -/

section specs
variable (p : Prog) (hp : WhnfCoreProg p) (hw : WhnfCallees p) (hc : CoreCallees p)

end specs

end L.Arena
