import ConAgua.Arena.Reasons
import ConAgua.Arena.WhnfSpine
import ConAgua.Arena.Env
import ConAgua.Arena.LevelEquiv

/-!
# `whnfCore`: the knot's slot, the loop, the step, the batched β spine, projections

con-ron's head normalisation without δ (`Arena/Core.lean:2140-2395` and the knot's `whnfCore`
slot, `:3546`), in L:

| L | twin |
|---|---|
| `whnf_core(mode, cheap, vis, d, e)` | the knot's `whnfCore` slot: `whnfCoreStuckTag`, the memo (`whnfCoreCheapC` / `whnfCoreC`, at the mode's eager bit), `whnfCoreBody` |
| `whnf_core_loop(mode, cheap, vis, d, e)` | `whnfCoreBody` = `whnfCoreLoop … whnfCoreLoopFuel` (an uncounted L loop) |
| `whnf_core_step(mode, cheap, vis, d, e)` | `whnfCoreStep` (`(0, e)` done, `(1, e)` continue); its `app` arm is `whnf_core_app` |
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
(`IFEnv.findProj?`: interns the table name), `fire_ok` (`IProjEntry.fireOk`); from
`WhnfCallees`: `inst_list`, `str_lit_supported`, `str_lit_ctor`.

The `projCertAt` mode test is `mode & 1 == 0` (`verifiedChecks`: the two verified modes).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-- The cheap-mode `whnfCore` memo's slots (`wkSch`). -/
abbrev WKM : ArrId := 97
/-- The `whnfCore` memo's slots (`wcSch`). -/
abbrev WCM : ArrId := 96

/-! ## The L code -/

/-- The knot's `whnfCore` slot. -/
-- con-ron: ConRon/Arena/Core.lean:2141-2153 ConRon.Arena.whnfCoreStuckTag
@[l_impl ConRon.Arena.whnfCoreStuckTag]
def whnfCoreL : FunDecl := lfn (mode, cheap, vis, d, e) locals (g, fd, j, dd, x, u) {
  g := e >> 28;
  if g != 4 && g != 9 && g != 7 && g != 0 { return e };
  if cheap != 0 {
    (fd, j, dd) := call wk_find(e, ((mode >> 1) & 1) << 32);
    if fd != 0 { return WKM.u64[j * 4 + 3] };
    x := call whnf_core_loop(mode, 1, vis, d, e);
    (fd, j, dd) := call wk_find(e, ((mode >> 1) & 1) << 32);
    u := call wk_put(e, ((mode >> 1) & 1) << 32, x, fd, j);
    return x
  };
  (fd, j, dd) := call wc_find(e, ((mode >> 1) & 1) << 32);
  if fd != 0 { return WCM.u64[j * 4 + 3] };
  x := call whnf_core_loop(mode, 0, vis, d, e);
  (fd, j, dd) := call wc_find(e, ((mode >> 1) & 1) << 32);
  u := call wc_put(e, ((mode >> 1) & 1) << 32, x, fd, j);
  return x
}

/-- The loop of `whnf_core_loop`, named for its spec. -/
def whnfCoreLoopB : Stmt := lblk (mode, cheap, vis, d, e, st, r) {
  while 0 == 0 {
    (st, r) := call whnf_core_step(mode, cheap, vis, d, e);
    if st == 0 { return r };
    e := r
  }
}

/-- con-ron: ConRon/Arena/Core.lean:2387-2395 ConRon.Arena.whnfCoreBody
con-ron: ConRon/Arena/Core.lean:2374-2385 ConRon.Arena.whnfCoreLoop -/
@[l_impl ConRon.Arena.whnfCoreBody ConRon.Arena.whnfCoreLoop]
def whnfCoreLoopL : FunDecl := lfn (mode, cheap, vis, d, e) locals (st, r) {
  ⟪whnfCoreLoopB⟫;
  abort
}

/-- The `app` arm of `whnf_core_step` (its own function: the arms' chains of calls are proved
apart). -/
-- con-ron: ConRon/Arena/Core.lean:2345-2372 ConRon.Arena.whnfCoreStep
@[l_impl ConRon.Arena.whnfCoreStep]
def whnfCoreAppL : FunDecl :=
    lfn (mode, cheap, vis, d, e) locals (top, h, so, sn, v, st, r) {
  top := CTL.u64[136];
  (h, so, sn) := call get_app_spine(e);
  v := call whnf_core(mode, cheap, vis, d, h);
  (st, r) := call whnf_core_app2(mode, vis, d, v, h, so, sn);
  CTL.u64[136] := top;
  return (st, r)
}

/-- The second half of the `app` arm: the reduct's spine, then the β/ι walk. -/
-- con-ron: ConRon/Arena/Core.lean:2345-2372 ConRon.Arena.whnfCoreStep
@[l_impl ConRon.Arena.whnfCoreStep]
def whnfCoreApp2L : FunDecl := lfn (mode, vis, d, v, h, so, sn) locals (top, hd, ho, hn, st, r) {
  top := CTL.u64[136];
  (hd, ho, hn) := call head_and_args(v);
  (st, r) := call whnf_app(mode, vis, d, v, hd, ho, hn, u64(v == h), so, sn, 0);
  CTL.u64[136] := top;
  return (st, r)
}

/-- con-ron: ConRon/Arena/Core.lean:2345-2372 ConRon.Arena.whnfCoreStep -/
@[l_impl ConRon.Arena.whnfCoreStep]
def whnfCoreStepL : FunDecl :=
    lfn (mode, cheap, vis, d, e) locals (g, t, i, st, r) {
  g := e >> 28;
  t := ⟦e⟧.tier;
  i := ⟦e⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if g == 4 {
    if APP⟨t⟩.count <= i { abort };
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

/-- con-ron: ConRon/Arena/Core.lean:2223-2254 ConRon.Arena.whnfApp
con-ron: ConRon/Arena/Core.lean:2104-2108 ConRon.Arena.internAppRebuilt -/
@[l_impl ConRon.Arena.whnfApp ConRon.Arena.internAppRebuilt]
def whnfAppL : FunDecl :=
    lfn (mode, vis, d, v, hd, vo, vn, same, ao, an, i) locals (top, a, node, ap, st, e2, e3, t, x) {
  top := CTL.u64[136];
  while i < an {
    a := SPN.u64[ao + i];
    node := SPN.u64[ao + an + i];
    if v >> 28 == 5 {
      t := ⟦v⟧.tier;
      x := ⟦v⟧.idx;
      if t != 0 && CTL.u64[1] == 0 { abort };
      if LAM⟨t⟩.count <= x { abort };
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
    if hd >> 28 == 3 {
      (st, e2) := call iota_rec_at(mode, vis, d, hd, vo, vn);
      if st != 0 {
        e3 := call mk_app_n_from(e2, ao, an, i + 1);
        CTL.u64[136] := top;
        return (1, e3)
      }
    };
    v := ap;
    i += 1
  };
  CTL.u64[136] := top;
  return (0, v)
}

/-- con-ron: ConRon/Arena/Core.lean:2202-2221 ConRon.Arena.betaPeel -/
@[l_impl ConRon.Arena.betaPeel]
def betaPeelL : FunDecl := lfn (t, a, ao, an, i) locals (co, cn, tt, x, e2, e3) {
  co := CTL.u64[136];
  if len(SPN.u64) <= co { abort };
  SPN.u64[co] := a;
  cn := 1;
  CTL.u64[136] := co + 1;
  while i < an {
    if t >> 28 != 5 {
      e2 := call inst_list(t, co, cn, 0);
      e3 := call mk_app_n_from(e2, ao, an, i);
      CTL.u64[136] := co;
      return (1, e3)
    };
    tt := ⟦t⟧.tier;
    x := ⟦t⟧.idx;
    if tt != 0 && CTL.u64[1] == 0 { abort };
    if LAM⟨tt⟩.count <= x { abort };
    t := LAM⟨tt, x⟩.b;
    if len(SPN.u64) <= co + cn { abort };
    SPN.u64[co + cn] := SPN.u64[ao + i];
    cn += 1;
    CTL.u64[136] := co + cn;
    i += 1
  };
  e2 := call inst_list(t, co, cn, 0);
  CTL.u64[136] := co;
  return (1, e2)
}

/-- con-ron: ConRon/Arena/Core.lean:2332-2343 ConRon.Arena.whnfCoreStepProj -/
@[l_impl ConRon.Arena.whnfCoreStepProj]
def whnfCoreStepProjL : FunDecl := lfn (mode, cheap, vis, d, e, sn, i, pe) locals (c, f, r) {
  if cheap != 0 { c := call whnf_core(mode, 1, vis, d, pe) } else { c := call whnf(mode, vis, d, pe) };
  (f, r) := call reduce_proj_core(mode, vis, d, sn, i, c);
  if f != 0 { return (1, r) };
  return (0, e)
}

/-- con-ron: ConRon/Arena/Core.lean:2297-2330 ConRon.Arena.reduceProjCore -/
-- con-ron: CHANGED since 12752ca7 — `ConRon.Arena.reduceProjCore` changed; re-check the L code and its proofs, then delete this line
@[l_impl ConRon.Arena.reduceProjCore]
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
con-ron: ConRon/Arena/Core.lean:2297-2330 ConRon.Arena.reduceProjCore -/
-- con-ron: CHANGED since 12752ca7 — `ConRon.Arena.reduceProjCore` changed; re-check the L code and its proofs, then delete this line
def reduceProjHeadL : FunDecl :=
    lfn (mode, vis, e1, q, i) locals (hh, t, x, k, us, st, r) {
  hh := call get_app_fn(e1);
  if hh >> 28 != 3 { return (0, 0) };
  t := ⟦hh⟧.tier;
  x := ⟦hh⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if CONST⟨t⟩.count <= x { abort };
  k := CONST⟨t, x⟩.n;
  us := CONST⟨t, x⟩.us;
  (st, r) := call reduce_proj_fire(mode, vis, e1, q, i, k, us);
  return (st, r)
}

/-- `reduceProjCore` at a constant head `k.{us}`: the arguments (pushed on the stack), the
level count, the entry's fire check, the shape conditions. The twin's `args.length = numParams +
numFields` (`Nat`) is tested as `nf <= an && an - nf == np`, which does not wrap; then `np + i < an`.
con-ron: ConRon/Arena/Core.lean:2297-2330 ConRon.Arena.reduceProjCore -/
-- con-ron: CHANGED since 12752ca7 — `ConRon.Arena.reduceProjCore` changed; re-check the L code and its proofs, then delete this line
def reduceProjFireL : FunDecl :=
    lfn (mode, vis, e1, q, i, k, us) locals (ao, an, lo, usl, fok, np, nf, st, r) {
  (ao, an) := call get_app_args(e1);
  (lo, usl) := call ls_node(us);
  fok := call fire_ok(q, i, us);
  np := EREC.u64[q + 5];
  nf := EREC.u64[q + 7];
  if k == EREC.u64[q + 6] && i < nf && nf <= an && an - nf == np && usl == EREC.u64[q + 4] && fok != 0 {
    (st, r) := call reduce_proj_arg(mode, vis, k, ao, an, np + i);
    return (st, r)
  };
  return (0, 0)
}

/-- `reduceProjCore`'s fire: argument `j` of the slice `(ao, an)` (else `bvar 0`), certified at
the verified mode.
con-ron: ConRon/Arena/Core.lean:2297-2330 ConRon.Arena.reduceProjCore -/
-- con-ron: CHANGED since 12752ca7 — `ConRon.Arena.reduceProjCore` changed; re-check the L code and its proofs, then delete this line
def reduceProjArgL : FunDecl :=
    lfn (mode, vis, k, ao, an, j) locals (b0, arg, ok) {
  b0 := call intern_bvar(0);
  if j < an { arg := SPN.u64[ao + j] } else { arg := b0 };
  ok := 1;
  if mode & 1 == 0 { ok := call proj_cert(vis, k, ao, an) };
  if ok != 0 { return (1, arg) };
  return (0, 0)
}

/-- con-ron: ConRon/Arena/Core.lean:2280-2287 ConRon.Arena.projCert
con-ron: ConRon/Arena/Core.lean:2289-2295 ConRon.Arena.projCertAt
con-ron: ConRon/Arena/Core.lean:2273-2278 ConRon.Arena.teleArityOk -/
@[l_impl ConRon.Arena.projCert ConRon.Arena.projCertAt ConRon.Arena.teleArityOk]
def projCertL : FunDecl := lfn (vis, k, ao, an) locals (f, q, ok, r) {
  (f, q) := call env_find(k, vis);
  if f == 0 { return 0 };
  if EREC.u64[q] != 4 { return 0 };
  (ok, r) := call peel_pis(an, EREC.u64[q + 4]);
  return u64(ok != 0)
}

/-- con-ron: ConRon/Arena/Core.lean:1838-1850 ConRon.Arena.projLitToCtor -/
@[l_impl ConRon.Arena.projLitToCtor]
def projLitToCtorL : FunDecl := lfn (mode, vis, d, h) locals (t, x, s, c) {
  if h >> 28 != 8 { return h };
  t := ⟦h⟧.tier;
  x := ⟦h⟧.idx;
  if t != 0 && CTL.u64[1] == 0 { abort };
  if LIT⟨t⟩.count <= x { abort };
  if LIT⟨t, x⟩.kind != 1 { return h };
  s := call str_lit_supported(vis);
  if s == 0 { return h };
  c := call str_lit_ctor(h);
  c := call whnf(mode, vis, d, c);
  return c
}

/-- What the specs need of a program: these functions and the ones they call by name. -/
structure WhnfCoreProg (p : Prog) : Prop where
  spine : SpineProg p
  core : p.lookup "whnf_core" = some whnfCoreL
  loop : p.lookup "whnf_core_loop" = some whnfCoreLoopL
  step : p.lookup "whnf_core_step" = some whnfCoreStepL
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
  envix : p.lookup "env_ix" = some envIxL
  envrow : p.lookup "env_row_get" = some envRowGetL
  envfind : p.lookup "env_find" = some envFindL
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
def decEntry (a : Array Word) (f q : Word) (i : Nat) : Option IProjEntry :=
  if f = 0 then none else (decTbl a q.toNat).map (·.entry i)

/-- `find_proj(vis, T, i)` refines `fe.findProj? T i`: `(0, _)` none, `(1, q)` the table record. -/
def FindProjOK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb T i : Word), CoreS dn s₀.mem a₀ vis fe M eb → HW T →
    CoreSpec p n "find_proj" [vis, T, i] (fe.findProj? (decI T) i.toNat)
      (fun r => decEntry (s₀.mem.arr64 EREC) (r.headD 0) (r.tail.headD 0) i.toNat) s₀ a₀ dn vis fe
      M eb

/-- `fire_ok(q, i, us)` refines `IProjEntry.fireOk` at the entry of table record `q`. **Statement
correction** (helper `whnf4-leaves`): at a field `i` below the table's `numFields` (the twin's
`findProj?` answers no other entry) and universe arguments that are a stored `const` node's list
(the callers' `us` is; the twin reads them back when the structure is a proposition, and a
stored `const` node's list reads back, `StoreDen.constLs`), of a table the environment holds
(`StoreDen.proj`; `ProjFound` gives it for the table `find_proj` answers). -/
def FireOkOK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb q i us : Word) (tbl : IProjTable), CoreS dn s₀.mem a₀ vis fe M eb →
    HW us → decTbl (s₀.mem.arr64 EREC) q.toNat = some tbl →
    (∃ c, fe.find? c = some (.projInfo tbl)) → i.toNat < tbl.numFields →
    (∃ (h : EIdx) (c : NIdx), a₀.store.view h = some (.const c (decI us))) →
    CoreSpec p n "fire_ok" [q, i, us] ((tbl.entry i.toNat).fireOk (decI us)) decBool s₀ a₀ dn vis
      fe M eb

/-- `iota_rec_at(mode, vis, d, hd, so, sn)` refines `iotaRecAt` (`WhnfIota.lean`). -/
def IotaRecAtOK (p : Prog) (n : Nat) : Prop :=
  ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d hd so sn : Word) (xs : Array EIdx), n ≤ F → n ≤ 2 ^ 62 →
    SlotPre s₀ a₀ dn vis fe M eb mode → HW hd → SpineR s₀.mem so sn xs →
    so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat →
    CoreSpec p n "iota_rec_at" [mode, vis, d, hd, so, sn]
      (iotaRecAt (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE hd) xs xs.size)
      decOptR s₀ a₀ dn vis fe M eb ResW

/-- **`find_proj` and `fire_ok` leave the record pool alone** (they intern into the expression and
level stores); `reduce_proj_core` reads the table's words after them. -/
def ErecKept (p : Prog) : Prop :=
  ∀ (n : Nat) (f : FnName) (vs : List Word) (m : Mem) (r : List Word) (m' : Mem),
    (f = "find_proj" ∨ f = "fire_ok") → callW p n f vs m = some (r, m') →
    m'.arr64 EREC = m.arr64 EREC

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
    ∃ tbl : IProjTable, decTbl (m.arr64 EREC) (r.tail.headD 0).toNat = some tbl ∧
      ∃ c, fe.find? c = some (.projInfo tbl)

/-- **The projection-table callees** (`find_proj`, `fire_ok`) and their record-pool facts: what
`reduce_proj_core` and the ι side's `and_rescue_slots`/`major_to_ctor` assume of them. A part of
`CoreCallees` on its own, so that `major_to_ctor` (which `iota_rec_at` calls) does not take
`CoreCallees.iota` (helper `whnf4-knot`). -/
structure ProjCallees (p : Prog) : Prop where
  findProj : FindProjOK p
  fireOk : FireOkOK p
  erec : ErecKept p
  projFound : ProjFound p

/-- **The callees of this file not written here.** -/
structure CoreCallees (p : Prog) : Prop extends ProjCallees p where
  inst1 : Inst1OK p
  /-- `iota_rec_at` one level down from the knot at `n` (`WhnfIota.lean`). -/
  iota : ∀ n, KnotUpTo p n → IotaRecAtOK p (n + 1)

/-! ## The specs

Each body at L fuel `n + 1` refines the twin's body at the knot `coreKnot mode fe id F`, `F ≥ n`,
given the knot's slots at every fuel up to `n` (`KnotUpTo p n`). -/

section specs
variable (p : Prog) (hp : WhnfCoreProg p) (hw : WhnfCallees p) (hc : CoreCallees p)

end specs

end L.Arena
