import ConAgua.Arena.IndIface

/-!
# The positivity walk in L (lane `induct`, module `IndPos`)

The L translation of `vendor/con-ron/ConRon/Arena/Inductives/Positivity.lean`, from the top
through `nestCrest`: the occurrence walks (`mentionsAnyConst`, `nestOcc`), the telescope closer,
the input-derived fuel (`depth`, `whnfWalkFuel`), the container lookup (`nestContainer`,
`nestCtorEntry`), the frame records' small helpers (`NestCtx.hiAt`, `NestCtx.rootHoles`,
`nestHoleAt`), the readback walk (`replaceFVars`, its four maps' dispatch `fvMapAt`, the holes'
image `nestHoleImg`), the whole-application substitution (`replaceApps`, `phApp?`, `appHole?`,
`nestCanonSub`), and the canonical constructor abstraction (`nestPhs`, `nestCanonCrest`,
`nestCrest`). No proofs this round (DESIGN.md, lane `induct`): every function here is tagged
`@[l_impl ConRon.Arena.<T>]`; a twin function split for size shares its parent's tag.

Per-call memos (`IndIface`'s schemas): `ma_*` (`mentionsAnyGo`), `no_*` (`nestOccGo`), `dp_*`
(`depthGo`), `ra_*` (`replaceAppsGo`) are cleared once by their walk's top call; `replaceFVars`
nests inside itself (`nestHoleImg`), so its memo (`rf_*`) is BANKED instead (`rf_bank_enter` /
`rf_bank_leave`, key `k2 = g << 32` with `g = CTL.u64[219]` the current generation).
-/

namespace L.Ind

open L.Arena

/-! ## `mentionsAnyConst`: does any of `names` occur in `h`? -/

/-- `mentions_any_node(namesOff, namesLen, fuel1, g, x, y, z)`: the non-leaf arms of
`mentionsAnyGo`'s node step (both children always evaluated, no short circuit). -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:98-140 ConRon.Arena.mentionsAnyGo
@[l_impl ConRon.Arena.mentionsAnyGo]
def mentionsAnyNode : FunDecl := lfn (namesOff, namesLen, fuel1, g, x, y, z) locals (b1, b2, b3) {
  if g == 1 { b1 := call mentions_any_go(namesOff, namesLen, fuel1, y); return b1 };
  if g == 4 || g == 5 || g == 6 {
    b1 := call mentions_any_go(namesOff, namesLen, fuel1, x);
    b2 := call mentions_any_go(namesOff, namesLen, fuel1, y);
    if b1 != 0 || b2 != 0 { return 1 };
    return 0
  };
  if g == 7 {
    b1 := call mentions_any_go(namesOff, namesLen, fuel1, x);
    b2 := call mentions_any_go(namesOff, namesLen, fuel1, y);
    b3 := call mentions_any_go(namesOff, namesLen, fuel1, z);
    if b1 != 0 || b2 != 0 || b3 != 0 { return 1 };
    return 0
  };
  -- g == 9 (proj): the structure name is also a name-set test, both always evaluated.
  b1 := call mentions_any_go(namesOff, namesLen, fuel1, z);
  b2 := call sl_contains(namesOff, namesLen, x);
  if b1 != 0 || b2 != 0 { return 1 };
  return 0
}

/-- `mentions_any_go(namesOff, namesLen, fuel, h)`: `mentionsAnyGo`, memoised on `h` (`ma_*`). -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:98-140 ConRon.Arena.mentionsAnyGo
@[l_impl ConRon.Arena.mentionsAnyGo]
def mentionsAnyGo : FunDecl := lfn (namesOff, namesLen, fuel, h) locals (g, x, y, z, r, fd, j, d, u) {
  if fuel == 0 { abort };
  (g, x, y, z) := call e_view(h);
  if g == 0 { return 0 };
  if g == 2 { return 0 };
  if g == 8 { return 0 };
  if g == 3 { r := call sl_contains(namesOff, namesLen, x); return r };
  (fd, j, d) := call ma_find(h, 0);
  if fd != 0 { return MAM.u64[j * 4 + 3] };
  r := call mentions_any_node(namesOff, namesLen, fuel - 1, g, x, y, z);
  (fd, j, d) := call ma_find(h, 0);
  u := call ma_put(h, 0, r, fd, j);
  return r
}

/-- `mentions_any_const(namesOff, namesLen, e)`: `mentionsAnyConst`, one memoised DAG walk. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:142-146 ConRon.Arena.mentionsAnyConst
@[l_impl ConRon.Arena.mentionsAnyConst]
def mentionsAnyConst : FunDecl := lfn (namesOff, namesLen, e) locals (r, u) {
  u := call ma_clear();
  r := call mentions_any_go(namesOff, namesLen, ⟪CWF⟫, e);
  u := call ma_clear();
  return r
}

/-- `member_idx_at(namesOff, namesLen, lvls, e)`: `memberIdxAt?`. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:148-158 ConRon.Arena.memberIdxAt?
@[l_impl ConRon.Arena.memberIdxAt?]
def memberIdxAt : FunDecl := lfn (namesOff, namesLen, lvls, e) locals (g, n, us, z, ok, idx) {
  if e >> 28 != 3 { return (0, 0) };
  (g, n, us, z) := call e_view(e);
  if us != lvls { return (0, 0) };
  (ok, idx) := call sl_find(namesOff, namesLen, n);
  return (ok, idx)
}

/-! ## Closing a telescope -/

/-- `close_telescope(dsOff, dsLen, i, body)`: `closeTelescope`, the innermost binder (the LAST of
`ds`) abstracted and bound first (the twin recurses to the end of the list before building). -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:162-170 ConRon.Arena.closeTelescope
@[l_impl ConRon.Arena.closeTelescope]
def closeTelescope : FunDecl := lfn (dsOff, dsLen, i, body) locals (inner, closed, r) {
  if dsLen == 0 { return body };
  inner := call close_telescope(dsOff + 1, dsLen - 1, i + 1, body);
  closed := call abstract1_fast(⟪CWF⟫, inner, i, 0);
  r := call mk_forall(IW.u64[dsOff], closed);
  if 4294967296 <= r { abort };
  return r
}

/-! ## `nestOcc`: a member or a hole occurring in `h` -/

/-- `nest_occ_node(namesOff, namesLen, lo, hi, fuel1, g, x, y, z)`: the non-leaf arms, short
circuiting (the twin's `if b then true else …`). -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:174-210 ConRon.Arena.nestOccGo
@[l_impl ConRon.Arena.nestOccGo]
def nestOccNode : FunDecl := lfn (namesOff, namesLen, lo, hi, fuel1, g, x, y, z) locals (b1, b2, b3) {
  if g == 4 || g == 5 || g == 6 {
    b1 := call nest_occ_go(namesOff, namesLen, lo, hi, fuel1, x);
    if b1 != 0 { return 1 };
    b2 := call nest_occ_go(namesOff, namesLen, lo, hi, fuel1, y);
    return b2
  };
  if g == 7 {
    b1 := call nest_occ_go(namesOff, namesLen, lo, hi, fuel1, x);
    if b1 != 0 { return 1 };
    b2 := call nest_occ_go(namesOff, namesLen, lo, hi, fuel1, y);
    if b2 != 0 { return 1 };
    b3 := call nest_occ_go(namesOff, namesLen, lo, hi, fuel1, z);
    return b3
  };
  -- g == 9 (proj): a tail call into the structure, not an occurrence itself.
  b1 := call nest_occ_go(namesOff, namesLen, lo, hi, fuel1, z);
  return b1
}

/-- `nest_occ_go(namesOff, namesLen, lo, hi, fuel, h)`: `nestOccGo`, memoised on `h` (`no_*`). -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:174-210 ConRon.Arena.nestOccGo
@[l_impl ConRon.Arena.nestOccGo]
def nestOccGo : FunDecl := lfn (namesOff, namesLen, lo, hi, fuel, h) locals (g, x, y, z, r, fd, j, d, u) {
  if fuel == 0 { abort };
  (g, x, y, z) := call e_view(h);
  if g == 0 { return 0 };
  if g == 2 { return 0 };
  if g == 8 { return 0 };
  if g == 1 { if lo <= x && x < hi { return 1 }; return 0 };
  if g == 3 { r := call sl_contains(namesOff, namesLen, x); return r };
  (fd, j, d) := call no_find(h, 0);
  if fd != 0 { return NOM.u64[j * 4 + 3] };
  r := call nest_occ_node(namesOff, namesLen, lo, hi, fuel - 1, g, x, y, z);
  (fd, j, d) := call no_find(h, 0);
  u := call no_put(h, 0, r, fd, j);
  return r
}

/-- `nest_occ(namesOff, namesLen, lo, hi, e)`: `nestOcc`, one memoised DAG walk. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:212-216 ConRon.Arena.nestOcc
@[l_impl ConRon.Arena.nestOcc]
def nestOcc : FunDecl := lfn (namesOff, namesLen, lo, hi, e) locals (r, u) {
  u := call no_clear();
  r := call nest_occ_go(namesOff, namesLen, lo, hi, ⟪CWF⟫, e);
  u := call no_clear();
  return r
}

/-- `inst_pis_with(argsOff, argsLen, e)`: `instPisWith`. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:218-230 ConRon.Arena.instPisWith
@[l_impl ConRon.Arena.instPisWith]
def instPisWith : FunDecl := lfn (argsOff, argsLen, e) locals (g, x, y, z, b, ok, r) {
  if argsLen == 0 { return (1, e) };
  if e >> 28 != 6 { return (0, 0) };
  (g, x, y, z) := call e_view(e);
  b := call instantiate1_fast(⟪CWF⟫, y, IW.u64[argsOff], 0);
  (ok, r) := call inst_pis_with(argsOff + 1, argsLen - 1, b);
  return (ok, r)
}

/-! ## `Expr.depth` and the input-derived fuel -/

/-- `depth_node(fuel1, g, x, y, z)`: the non-leaf arms of `depthGo`'s node step (`max`, via the
`bb_node` idiom: `a + (b - a) * u64(a < b)`). -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:258-296 ConRon.Arena.depthGo
@[l_impl ConRon.Arena.depthGo]
def depthNode : FunDecl := lfn (fuel1, g, x, y, z) locals (d1, d2, d3, m) {
  if g == 4 || g == 5 || g == 6 {
    d1 := call depth_go(fuel1, x);
    d2 := call depth_go(fuel1, y);
    m := d1 + (d2 - d1) * u64(d1 < d2);
    if m >= 4294967295 { abort };
    return m + 1
  };
  if g == 7 {
    d1 := call depth_go(fuel1, x);
    d2 := call depth_go(fuel1, y);
    d3 := call depth_go(fuel1, z);
    m := d1 + (d2 - d1) * u64(d1 < d2);
    m := m + (d3 - m) * u64(m < d3);
    if m >= 4294967295 { abort };
    return m + 1
  };
  -- g == 9 (proj)
  d1 := call depth_go(fuel1, z);
  if d1 >= 4294967295 { abort };
  return d1 + 1
}

/-- `depth_go(fuel, h)`: `depthGo`, memoised on `h` (`dp_*`), value a number. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:258-296 ConRon.Arena.depthGo
@[l_impl ConRon.Arena.depthGo]
def depthGo : FunDecl := lfn (fuel, h) locals (g, x, y, z, fd, j, d, u, r) {
  if fuel == 0 { abort };
  (g, x, y, z) := call e_view(h);
  if g == 0 { return 1 };
  if g == 1 { return 1 };
  if g == 2 { return 1 };
  if g == 3 { return 1 };
  if g == 8 { return 1 };
  (fd, j, d) := call dp_find(h, 0);
  if fd != 0 { return DPM.u64[j * 4 + 3] };
  r := call depth_node(fuel - 1, g, x, y, z);
  (fd, j, d) := call dp_find(h, 0);
  u := call dp_put(h, 0, r, fd, j);
  return r
}

/-- `depth(e)`: `Expr.depth`, one memoised DAG walk. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:298-302 ConRon.Arena.depth
@[l_impl ConRon.Arena.depth]
def depth : FunDecl := lfn (e) locals (r, u) {
  u := call dp_clear();
  r := call depth_go(⟪CWF⟫, e);
  u := call dp_clear();
  return r
}

/-- `whnf_walk_fuel(e)`: `whnfWalkFuel`, the depth plus `fuelSlack` (`1024`). -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:304-308 ConRon.Arena.whnfWalkFuel
@[l_impl ConRon.Arena.whnfWalkFuel]
def whnfWalkFuel : FunDecl := lfn (e) locals (d) {
  d := call depth(e);
  if d >= 4294967296 { abort };
  return d + 1024
}

/-! ## `NestFieldKind` and the uniform-route test -/

/-- `nest_field_kind_flat(k)`: `NestFieldKind.flat` (IndIface's encoding: the low 3 bits are the
constructor tag, `0`/`1`/`2` flat). -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:320-324 ConRon.Arena.NestFieldKind.flat
@[l_impl ConRon.Arena.NestFieldKind.flat]
def nestFieldKindFlat : FunDecl := lfn (k) locals () {
  return u64((k & 7) <= 2)
}

/-- `nest_kinds_flat_inner(off, cnt)`: a field telescope's kinds, all flat. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:326-329 ConRon.Arena.nestKindsFlat
@[l_impl ConRon.Arena.nestKindsFlat]
def nestKindsFlatInner : FunDecl := lfn (off, cnt) locals (ok, r) {
  if cnt == 0 { return 1 };
  ok := call nest_field_kind_flat(IW.u64[off]);
  if ok == 0 { return 0 };
  r := call nest_kinds_flat_inner(off + 1, cnt - 1);
  return r
}

/-- `nest_kinds_flat_mid(off, cnt)`: a constructor's fields (pointers to field-kind headers), all
flat. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:326-329 ConRon.Arena.nestKindsFlat
@[l_impl ConRon.Arena.nestKindsFlat]
def nestKindsFlatMid : FunDecl := lfn (off, cnt) locals (ok, r) {
  if cnt == 0 { return 1 };
  ok := call nest_kinds_flat_inner(IW.u64[IW.u64[off]], IW.u64[IW.u64[off] + 1]);
  if ok == 0 { return 0 };
  r := call nest_kinds_flat_mid(off + 1, cnt - 1);
  return r
}

/-- `nest_kinds_flat(off, cnt)`: `nestKindsFlat`, every field of every constructor of every
member flat. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:326-329 ConRon.Arena.nestKindsFlat
@[l_impl ConRon.Arena.nestKindsFlat]
def nestKindsFlat : FunDecl := lfn (off, cnt) locals (ok, r) {
  if cnt == 0 { return 1 };
  ok := call nest_kinds_flat_mid(IW.u64[IW.u64[off]], IW.u64[IW.u64[off] + 1]);
  if ok == 0 { return 0 };
  r := call nest_kinds_flat(off + 1, cnt - 1);
  return r
}

/-! ## Containers -/

/-- `nest_ctor_entry_strip(ciq)`: the constructor's fields and its stripped body, `ok0 = 0` when
`ciq` is no constructor record or its type does not bind its parameters and fields. Aborts when
`nPc + nF` wraps (a capacity guard: the twin adds them as `Nat`s; docs/deviations.md). -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:368-384 ConRon.Arena.nestCtorEntry
@[l_impl ConRon.Arena.nestCtorEntry]
def nestCtorEntryStrip : FunDecl := lfn (ciq) locals (cv, nPc, nF, ok, bsOff, bsLen, body) {
  if EREC.u64[ciq] != 4 { return (0, 0, 0, 0, 0) };
  cv := ciq + 1;
  nPc := EREC.u64[ciq + 5];
  nF := EREC.u64[ciq + 6];
  if nPc + nF < nPc { abort };
  (ok, bsOff, bsLen, body) := call strip_pis(nPc + nF, EREC.u64[cv + 3]);
  if ok == 0 { return (0, 0, 0, 0, 0) };
  return (1, cv, nPc, nF, body)
}

/-- `nest_ctor_entry(C, ciq)`: `nestCtorEntry`, `ciq` the stored constant's `EREC` pointer. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:368-384 ConRon.Arena.nestCtorEntry
@[l_impl ConRon.Arena.nestCtorEntry]
def nestCtorEntry : FunDecl := lfn (C, ciq) locals (ok0, cv, nPc, nF, body, hd, g, n, us, z) {
  (ok0, cv, nPc, nF, body) := call nest_ctor_entry_strip(ciq);
  if ok0 == 0 { return (0, 0, 0, 0) };
  hd := call get_app_fn_f(⟪CWF⟫, body);
  if hd >> 28 != 3 { return (0, 0, 0, 0) };
  (g, n, us, z) := call e_view(hd);
  if n != C { return (0, 0, 0, 0) };
  return (1, cv, nPc, nF)
}

/-- `nest_container_ctors_go(vis, C, ctorsOff, ctorsLen, csOff, outLen, firstNPc)`: the rest of
`caps.ctors` (an `EREC` slice) looked up and filtered, each accepted `[cv, nF]` record written at
`csOff + outLen`; returns the final count and the first accepted entry's parameter count (the loop
of `nest_container_ctors`, as a recursion). -/
-- con-ron: none — the loop of nest_container_ctors as a self-recursive function (proof shape)
def nestContainerCtorsGo : FunDecl :=
    lfn (vis, C, ctorsOff, ctorsLen, csOff, outLen, firstNPc) locals (found, ciq, ok, cv, nPc, nF, r1, r2) {
  if ctorsLen == 0 { return (outLen, firstNPc) };
  (found, ciq) := call env_find(EREC.u64[ctorsOff], vis);
  if found != 0 {
    (ok, cv, nPc, nF) := call nest_ctor_entry(C, ciq);
    if ok != 0 {
      ciq := call rec2(cv, nF);
      IW.u64[csOff + outLen] := ciq;
      if outLen == 0 { firstNPc := nPc };
      outLen += 1
    }
  };
  (r1, r2) := call nest_container_ctors_go(vis, C, ctorsOff + 1, ctorsLen - 1, csOff, outLen, firstNPc);
  return (r1, r2)
}

/-- `nest_container_ctors(vis, C, ctorsOff, ctorsLen)`: `caps.ctors.filterMapM (nestCtorEntry C ∘
fe.find?)`, as the `[cv, nF]` records accepted and the first accepted entry's parameter count
(`0` if none are accepted). -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:386-402 ConRon.Arena.nestContainer
@[l_impl ConRon.Arena.nestContainer]
def nestContainerCtors : FunDecl :=
    lfn (vis, C, ctorsOff, ctorsLen) locals (csOff, outLen, firstNPc) {
  csOff := call iw_alloc(ctorsLen);
  (outLen, firstNPc) := call nest_container_ctors_go(vis, C, ctorsOff, ctorsLen, csOff, 0, 0);
  return (csOff, outLen, firstNPc)
}

/-- `nest_container(vis, C)`: `nestContainer`. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:386-402 ConRon.Arena.nestContainer
@[l_impl ConRon.Arena.nestContainer]
def nestContainer : FunDecl :=
    lfn (vis, C) locals (found, q, capsq, ctorsOff, ctorsLen, csOff, csLen, firstNPc) {
  (found, q) := call env_find(C, vis);
  if found == 0 { return (0, 0, 0, 0) };
  if EREC.u64[q] != 3 { return (0, 0, 0, 0) };
  capsq := q + 5;
  ctorsOff := EREC.u64[capsq + 13];
  ctorsLen := EREC.u64[capsq + 14];
  (csOff, csLen, firstNPc) := call nest_container_ctors(vis, C, ctorsOff, ctorsLen);
  if csLen == 0 { return (1, EREC.u64[capsq + 12], csOff, 0) };
  return (1, firstNPc, csOff, csLen)
}

/-! ## `NestCtx`'s small helpers -/

/-- `nest_ctx_hi_at(ctx, nf)`: `NestCtx.hiAt`. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:409-412 ConRon.Arena.NestCtx.hiAt
@[l_impl ConRon.Arena.NestCtx.hiAt]
def nestCtxHiAt : FunDecl := lfn (ctx, nf) locals () {
  return IW.u64[ctx + 4] + IW.u64[ctx + 1] + nf
}

/-- `nest_ctx_root_holes_go(namesOff, namesLen, lvls, paramsOff, paramsLen, nP, q, j)`: the holes
`j ..< namesLen`, written at `q + j` (the loop of `NestCtx.rootHoles`, as a recursion). -/
-- con-ron: none — the loop of nest_ctx_root_holes as a self-recursive function (proof shape)
def nestCtxRootHolesGo : FunDecl :=
    lfn (namesOff, namesLen, lvls, paramsOff, paramsLen, nP, q, j) locals (key, hole, u) {
  if j >= namesLen { return 0 };
  key := call rec4(IW.u64[namesOff + j], lvls, paramsOff, paramsLen);
  hole := call rec2(key, nP);
  IW.u64[q + j] := hole;
  u := call nest_ctx_root_holes_go(namesOff, namesLen, lvls, paramsOff, paramsLen, nP, q, j + 1);
  return 0
}

/-- `nest_ctx_root_holes(ctx)`: `NestCtx.rootHoles`, one `NestHole` per member, base `ctx.nP`. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:414-418 ConRon.Arena.NestCtx.rootHoles
@[l_impl ConRon.Arena.NestCtx.rootHoles]
def nestCtxRootHoles : FunDecl :=
    lfn (ctx) locals (namesOff, namesLen, lvls, paramsOff, paramsLen, nP, q, u) {
  namesOff := IW.u64[ctx];
  namesLen := IW.u64[ctx + 1];
  lvls := IW.u64[ctx + 10];
  paramsOff := IW.u64[ctx + 7];
  paramsLen := IW.u64[ctx + 8];
  nP := IW.u64[ctx + 4];
  q := call iw_alloc(namesLen);
  u := call nest_ctx_root_holes_go(namesOff, namesLen, lvls, paramsOff, paramsLen, nP, q, 0);
  return (q, namesLen)
}

/-- `nest_hole_at(ctx, progOff, progLen, i)`: `nestHoleAt`, the stack read root first. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:420-425 ConRon.Arena.nestHoleAt
@[l_impl ConRon.Arena.nestHoleAt]
def nestHoleAt : FunDecl := lfn (ctx, progOff, progLen, i) locals (nP, rhOff, rhLen, allOff, allLen, idx) {
  nP := IW.u64[ctx + 4];
  if i < nP { return (0, 0) };
  (rhOff, rhLen) := call nest_ctx_root_holes(ctx);
  (allOff, allLen) := call sl_append(rhOff, rhLen, progOff, progLen);
  idx := i - nP;
  if idx < allLen { return (1, IW.u64[allOff + idx]) };
  return (0, 0)
}

/-! ## `replaceFVars` and its four maps -/

/-- `nest_key_map(dsOff, dsLen, hoOff, hoLen, i)`: `nestKeyMap`. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:447-452 ConRon.Arena.nestKeyMap
@[l_impl ConRon.Arena.nestKeyMap]
def nestKeyMap : FunDecl := lfn (dsOff, dsLen, hoOff, hoLen, i) locals () {
  if i < dsLen { return (1, IW.u64[dsOff + i]) };
  if i - dsLen < hoLen { return (1, IW.u64[hoOff + (i - dsLen)]) };
  return (0, 0)
}

/-- `fv_map_at(f, i)`: `fvMapAt`, dispatching on `f`'s tag (IndIface's `FvMap` layout). -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:456-469 ConRon.Arena.fvMapAt
@[l_impl ConRon.Arena.fvMapAt]
def fvMapAt : FunDecl := lfn (f, i) locals (tag, ok, e, z, s, v) {
  tag := IW.u64[f];
  if tag == 0 {
    (ok, e) := call nest_hole_img(IW.u64[f + 1], IW.u64[f + 2], IW.u64[f + 3], IW.u64[f + 4], i);
    return (ok, e)
  };
  if tag == 1 {
    (ok, e) := call nest_key_map(IW.u64[f + 1], IW.u64[f + 2], IW.u64[f + 3], IW.u64[f + 4], i);
    return (ok, e)
  };
  if tag == 2 {
    z := call pin_word(53);
    s := call intern_sort(z);
    if 4294967296 <= s { abort };
    v := call intern_fvar(i, s);
    return (1, v)
  };
  -- tag == 3 (canon)
  if i < IW.u64[f + 2] { return (1, IW.u64[IW.u64[f + 1] + i]) };
  return (0, 0)
}

/-- `nest_hole_img_root(ctx, i)`: `nestHoleImg`'s `n = 0` arm, a member's hole. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:534-559 ConRon.Arena.nestHoleImg
@[l_impl ConRon.Arena.nestHoleImg]
def nestHoleImgRoot : FunDecl := lfn (ctx, i) locals (nP, hi, nm, hd, r) {
  nP := IW.u64[ctx + 4];
  hi := call nest_ctx_hi_at(ctx, 0);
  if nP <= i && i < hi {
    nm := call sl_getd(IW.u64[ctx], IW.u64[ctx + 1], i - nP, 0);
    hd := call intern_const(nm, IW.u64[ctx + 10]);
    if 4294967296 <= hd { abort };
    r := call mk_app_n_f(hd, IW.u64[ctx + 7], IW.u64[ctx + 8]);
    return (1, r)
  };
  return (0, 0)
}

/-- `nest_hole_img_ds_go(f, dsOff, dsLen, q, j)`: `replaceFVars f` of the rest of the slice, written
at `q + j`, … (the loop of `nest_hole_img_ds`, as a recursion). -/
-- con-ron: none — the loop of nest_hole_img_ds as a self-recursive function (proof shape)
def nestHoleImgDsGo : FunDecl := lfn (f, dsOff, dsLen, q, j) locals (r, u) {
  if j >= dsLen { return 0 };
  r := call replace_fvars(f, IW.u64[dsOff + j]);
  IW.u64[q + j] := r;
  u := call nest_hole_img_ds_go(f, dsOff, dsLen, q, j + 1);
  return 0
}

/-- `nest_hole_img_ds(f, dsOff, dsLen)`: `ds.mapM fun x => replaceFVars f x`, in list order. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:534-559 ConRon.Arena.nestHoleImg
@[l_impl ConRon.Arena.nestHoleImg]
def nestHoleImgDs : FunDecl := lfn (f, dsOff, dsLen) locals (q, u) {
  q := call iw_alloc(dsLen);
  u := call nest_hole_img_ds_go(f, dsOff, dsLen, q, 0);
  return (q, dsLen)
}

/-- `nest_hole_img_frame(ctx, progOff, progLen, n1, i)`: `nestHoleImg`'s hit arm (`n = n1 + 1`,
`i = ctx.hiAt n1`), the frame's hole read back. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:534-559 ConRon.Arena.nestHoleImg
@[l_impl ConRon.Arena.nestHoleImg]
def nestHoleImgFrame : FunDecl :=
    lfn (ctx, progOff, progLen, n1, i) locals (h, hDefKey, keyPtr, f, dsOff2, dsLen2, hd, r) {
  if n1 < progLen { h := IW.u64[progOff + n1] }
  else { hDefKey := call rec4(0, 0, 0, 0); h := call rec2(hDefKey, 0) };
  keyPtr := IW.u64[h];
  f := call rec5(0, ctx, progOff, progLen, n1);
  (dsOff2, dsLen2) := call nest_hole_img_ds(f, IW.u64[keyPtr + 2], IW.u64[keyPtr + 3]);
  hd := call intern_const(IW.u64[keyPtr], IW.u64[keyPtr + 1]);
  if 4294967296 <= hd { abort };
  r := call mk_app_n_f(hd, dsOff2, dsLen2);
  return (1, r)
}

/-- `nest_hole_img(ctx, progOff, progLen, n, i)`: `nestHoleImg`. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:534-559 ConRon.Arena.nestHoleImg
@[l_impl ConRon.Arena.nestHoleImg]
def nestHoleImg : FunDecl := lfn (ctx, progOff, progLen, n, i) locals (n1, hi, ok, r) {
  if n == 0 { (ok, r) := call nest_hole_img_root(ctx, i); return (ok, r) };
  n1 := n - 1;
  hi := call nest_ctx_hi_at(ctx, n1);
  if i == hi { (ok, r) := call nest_hole_img_frame(ctx, progOff, progLen, n1, i); return (ok, r) };
  (ok, r) := call nest_hole_img(ctx, progOff, progLen, n1, i);
  return (ok, r)
}

/-- `replace_fvars_node(f, fuel1, g, x, y, z)`: the non-leaf arms of `replaceFVarsGo`'s node
step. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:471-523 ConRon.Arena.replaceFVarsGo
@[l_impl ConRon.Arena.replaceFVarsGo]
def replaceFVarsNode : FunDecl := lfn (f, fuel1, g, x, y, z) locals (a2, b2, c2, u2, r) {
  if g == 4 {
    a2 := call replace_fvars_go(f, fuel1, x);
    b2 := call replace_fvars_go(f, fuel1, y);
    r := call mk_app(a2, b2);
    return r
  };
  if g == 5 {
    a2 := call replace_fvars_go(f, fuel1, x);
    b2 := call replace_fvars_go(f, fuel1, y);
    r := call mk_lam(a2, b2);
    return r
  };
  if g == 6 {
    a2 := call replace_fvars_go(f, fuel1, x);
    b2 := call replace_fvars_go(f, fuel1, y);
    r := call mk_forall(a2, b2);
    return r
  };
  if g == 7 {
    a2 := call replace_fvars_go(f, fuel1, x);
    b2 := call replace_fvars_go(f, fuel1, y);
    c2 := call replace_fvars_go(f, fuel1, z);
    r := call mk_let(a2, b2, c2);
    return r
  };
  -- g == 9 (proj)
  u2 := call replace_fvars_go(f, fuel1, z);
  r := call mk_proj(x, y, u2);
  return r
}

/-- `replace_fvars_go(f, fuel, h)`: `replaceFVarsGo`, memoised on `h` (`rf_*`, banked). -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:471-523 ConRon.Arena.replaceFVarsGo
@[l_impl ConRon.Arena.replaceFVarsGo]
def replaceFVarsGo : FunDecl := lfn (f, fuel, h) locals (g, x, y, z, ok, r, k2, fd, j, d, u) {
  if fuel == 0 { abort };
  (g, x, y, z) := call e_view(h);
  if g == 0 { return h };
  if g == 2 { return h };
  if g == 8 { return h };
  if g == 3 { return h };
  if g == 1 {
    (ok, r) := call fv_map_at(f, x);
    if ok != 0 { return r };
    return h
  };
  k2 := CTL.u64[219] << 32;
  (fd, j, d) := call rf_find(h, k2);
  if fd != 0 { return RFM.u64[j * 4 + 3] };
  r := call replace_fvars_node(f, fuel - 1, g, x, y, z);
  k2 := CTL.u64[219] << 32;
  (fd, j, d) := call rf_find(h, k2);
  u := call rf_put(h, k2, r, fd, j);
  return r
}

/-- `replace_fvars(f, e)`: `replaceFVars`, one memoised DAG walk in a fresh bank (nested calls,
via `nestHoleImg`, get their own). -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:525-532 ConRon.Arena.replaceFVars
@[l_impl ConRon.Arena.replaceFVars]
def replaceFVars : FunDecl := lfn (f, e) locals (s, r, u) {
  s := call rf_bank_enter();
  r := call replace_fvars_go(f, ⟪CWF⟫, e);
  u := call rf_bank_leave(s);
  if 4294967296 <= r { abort };
  return r
}

/-! ## The whole-application abstraction (`replaceApps` at `nestCanonSub`) -/

/-- `ph_app(b, e, n)`: `phApp?`. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:565-586 ConRon.Arena.phApp?
@[l_impl ConRon.Arena.phApp?]
def phApp : FunDecl := lfn (b, e, n) locals (g, x, y, z, g2, idx, y2, z2, ok, c, us) {
  if n == 0 {
    if e >> 28 != 3 { return (0, 0, 0) };
    (g, x, y, z) := call e_view(e);
    return (1, x, y)
  };
  if e >> 28 != 4 { return (0, 0, 0) };
  (g, x, y, z) := call e_view(e);
  if y >> 28 != 1 { return (0, 0, 0) };
  (g2, idx, y2, z2) := call e_view(y);
  if idx != b + (n - 1) { return (0, 0, 0) };
  (ok, c, us) := call ph_app(b, x, n - 1);
  return (ok, c, us)
}

/-- `nest_canon_sub(namesOff, namesLen, us, n, c, v)`: `nestCanonSub`. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:588-602 ConRon.Arena.nestCanonSub
@[l_impl ConRon.Arena.nestCanonSub]
def nestCanonSub : FunDecl := lfn (namesOff, namesLen, us, n, c, v) locals (ok, m, z, s, r) {
  if v != us { return (0, 0) };
  (ok, m) := call sl_find(namesOff, namesLen, c);
  if ok == 0 { return (0, 0) };
  z := call pin_word(53);
  if 4294967296 <= z { abort };
  s := call intern_sort(z);
  if 4294967296 <= s { abort };
  r := call intern_fvar(n + m, s);
  if 4294967296 <= r { abort };
  return (1, r)
}

/-- `app_hole(namesOff, namesLen, us, b, n, e)`: `appHole?`. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:604-611 ConRon.Arena.appHole?
@[l_impl ConRon.Arena.appHole?]
def appHole : FunDecl := lfn (namesOff, namesLen, us, b, n, e) locals (ok, c, v, ok2, r) {
  (ok, c, v) := call ph_app(b, e, n);
  if ok == 0 { return (0, 0) };
  (ok2, r) := call nest_canon_sub(namesOff, namesLen, us, n, c, v);
  return (ok2, r)
}

/-- `replace_apps_node(namesOff, namesLen, us, b, n, fuel1, h, g, x, y, z)`: the non-leaf arms of
`replaceAppsGo`'s node step (`app` tries `appHole?` first, as the twin does, inside the memo
miss). -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:613-665 ConRon.Arena.replaceAppsGo
@[l_impl ConRon.Arena.replaceAppsGo]
def replaceAppsNode : FunDecl :=
    lfn (namesOff, namesLen, us, b, n, fuel1, h, g, x, y, z) locals (ok, r, a2, x2, c2) {
  if g == 4 {
    (ok, r) := call app_hole(namesOff, namesLen, us, b, n, h);
    if ok != 0 { return r };
    a2 := call replace_apps_go(namesOff, namesLen, us, b, n, fuel1, x);
    x2 := call replace_apps_go(namesOff, namesLen, us, b, n, fuel1, y);
    r := call mk_app(a2, x2);
    return r
  };
  if g == 5 {
    a2 := call replace_apps_go(namesOff, namesLen, us, b, n, fuel1, x);
    x2 := call replace_apps_go(namesOff, namesLen, us, b, n, fuel1, y);
    r := call mk_lam(a2, x2);
    return r
  };
  if g == 6 {
    a2 := call replace_apps_go(namesOff, namesLen, us, b, n, fuel1, x);
    x2 := call replace_apps_go(namesOff, namesLen, us, b, n, fuel1, y);
    r := call mk_forall(a2, x2);
    return r
  };
  if g == 7 {
    a2 := call replace_apps_go(namesOff, namesLen, us, b, n, fuel1, x);
    x2 := call replace_apps_go(namesOff, namesLen, us, b, n, fuel1, y);
    c2 := call replace_apps_go(namesOff, namesLen, us, b, n, fuel1, z);
    r := call mk_let(a2, x2, c2);
    return r
  };
  -- g == 9 (proj)
  a2 := call replace_apps_go(namesOff, namesLen, us, b, n, fuel1, z);
  r := call mk_proj(x, y, a2);
  return r
}

/-- `replace_apps_go(namesOff, namesLen, us, b, n, fuel, h)`: `replaceAppsGo`, memoised on `h`
(`ra_*`; a whole application at a `const` is replaced before descending and is not memoised). -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:613-665 ConRon.Arena.replaceAppsGo
@[l_impl ConRon.Arena.replaceAppsGo]
def replaceAppsGo : FunDecl :=
    lfn (namesOff, namesLen, us, b, n, fuel, h) locals (g, x, y, z, ok, r, fd, j, d, u) {
  if fuel == 0 { abort };
  (g, x, y, z) := call e_view(h);
  if g == 0 { return h };
  if g == 2 { return h };
  if g == 8 { return h };
  if g == 1 { return h };
  if g == 3 {
    (ok, r) := call app_hole(namesOff, namesLen, us, b, n, h);
    if ok != 0 { return r };
    return h
  };
  (fd, j, d) := call ra_find(h, 0);
  if fd != 0 { return RAM.u64[j * 4 + 3] };
  r := call replace_apps_node(namesOff, namesLen, us, b, n, fuel - 1, h, g, x, y, z);
  (fd, j, d) := call ra_find(h, 0);
  u := call ra_put(h, 0, r, fd, j);
  return r
}

/-- `replace_apps(namesOff, namesLen, us, b, n, e)`: `replaceApps`, one memoised DAG walk. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:667-672 ConRon.Arena.replaceApps
@[l_impl ConRon.Arena.replaceApps]
def replaceApps : FunDecl := lfn (namesOff, namesLen, us, b, n, e) locals (r, u) {
  u := call ra_clear();
  r := call replace_apps_go(namesOff, namesLen, us, b, n, ⟪CWF⟫, e);
  u := call ra_clear();
  return r
}

/-- `nest_phs_go(q, n, i)`: the variables `fvar i, …, fvar (n - 1)` written at `q + i` (the loop of
`nestPhs`, as a recursion). -/
-- con-ron: none — the loop of nest_phs as a self-recursive function (proof shape)
def nestPhsGo : FunDecl := lfn (q, n, i) locals (z, s, v, u) {
  if i >= n { return 0 };
  z := call pin_word(53);
  if 4294967296 <= z { abort };
  s := call intern_sort(z);
  if 4294967296 <= s { abort };
  v := call intern_fvar(i, s);
  if 4294967296 <= v { abort };
  IW.u64[q + i] := v;
  u := call nest_phs_go(q, n, i + 1);
  return 0
}

/-- `nest_phs(n)`: `nestPhs`, the canonical parameter variables `fvar 0, …, fvar (n - 1)`. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:674-680 ConRon.Arena.nestPhs
@[l_impl ConRon.Arena.nestPhs]
def nestPhs : FunDecl := lfn (n) locals (q, u) {
  q := call iw_alloc(n);
  u := call nest_phs_go(q, n, 0);
  return (q, n)
}

/-- `nest_canon_crest(namesOff, namesLen, us, n, cty)`: `nestCanonCrest`. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:682-693 ConRon.Arena.nestCanonCrest
@[l_impl ConRon.Arena.nestCanonCrest]
def nestCanonCrest : FunDecl := lfn (namesOff, namesLen, us, n, cty) locals (phOff, phLen, ok, t, r) {
  (phOff, phLen) := call nest_phs(n);
  (ok, t) := call inst_pis_with(phOff, phLen, cty);
  if ok == 0 { return (0, 0) };
  r := call replace_apps(namesOff, namesLen, us, 0, n, t);
  if 4294967296 <= r { abort };
  return (1, r)
}

/-- `nest_crest(namesOff, namesLen, us, dsOff, dsLen, hoOff, hoLen, cty)`: `nestCrest`. -/
-- con-ron: ConRon/Arena/Inductives/Positivity.lean:695-704 ConRon.Arena.nestCrest
@[l_impl ConRon.Arena.nestCrest]
def nestCrest : FunDecl :=
    lfn (namesOff, namesLen, us, dsOff, dsLen, hoOff, hoLen, cty) locals (ok, c, f, r) {
  (ok, c) := call nest_canon_crest(namesOff, namesLen, us, dsLen, cty);
  if ok == 0 { return (0, 0) };
  f := call rec5(1, dsOff, dsLen, hoOff, hoLen);
  r := call replace_fvars(f, c);
  return (1, r)
}

/-! ## The program and its closure -/

/-- This module's functions. -/
def indPosFns : Prog :=
  [("mentions_any_node", mentionsAnyNode), ("mentions_any_go", mentionsAnyGo),
   ("mentions_any_const", mentionsAnyConst), ("member_idx_at", memberIdxAt),
   ("close_telescope", closeTelescope),
   ("nest_occ_node", nestOccNode), ("nest_occ_go", nestOccGo), ("nest_occ", nestOcc),
   ("inst_pis_with", instPisWith),
   ("depth_node", depthNode), ("depth_go", depthGo), ("depth", depth),
   ("whnf_walk_fuel", whnfWalkFuel),
   ("nest_field_kind_flat", nestFieldKindFlat), ("nest_kinds_flat_inner", nestKindsFlatInner),
   ("nest_kinds_flat_mid", nestKindsFlatMid), ("nest_kinds_flat", nestKindsFlat),
   ("nest_ctor_entry_strip", nestCtorEntryStrip), ("nest_ctor_entry", nestCtorEntry),
   ("nest_container_ctors_go", nestContainerCtorsGo), ("nest_container_ctors", nestContainerCtors), ("nest_container", nestContainer),
   ("nest_ctx_hi_at", nestCtxHiAt), ("nest_ctx_root_holes_go", nestCtxRootHolesGo),
   ("nest_ctx_root_holes", nestCtxRootHoles),
   ("nest_hole_at", nestHoleAt), ("nest_key_map", nestKeyMap), ("fv_map_at", fvMapAt),
   ("nest_hole_img_root", nestHoleImgRoot), ("nest_hole_img_ds_go", nestHoleImgDsGo), ("nest_hole_img_ds", nestHoleImgDs),
   ("nest_hole_img_frame", nestHoleImgFrame), ("nest_hole_img", nestHoleImg),
   ("replace_fvars_node", replaceFVarsNode), ("replace_fvars_go", replaceFVarsGo),
   ("replace_fvars", replaceFVars),
   ("ph_app", phApp), ("nest_canon_sub", nestCanonSub), ("app_hole", appHole),
   ("replace_apps_node", replaceAppsNode), ("replace_apps_go", replaceAppsGo),
   ("replace_apps", replaceApps),
   ("nest_phs_go", nestPhsGo), ("nest_phs", nestPhs), ("nest_canon_crest", nestCanonCrest), ("nest_crest", nestCrest)]

/-! ## A few `#guard`s: the pure-enough paths (no stub on them) -/

-- `nest_field_kind_flat`: `.ordinary` (0) is flat, `.inProgress` (3) is not.
#guard
  match run (indPosFns ++ libFns ++ stubFns ++ masterFns) 100 "nest_field_kind_flat" [0] testMem with
  | .ok ([1], _) =>
    (match run (indPosFns ++ libFns ++ stubFns ++ masterFns) 100 "nest_field_kind_flat" [3] testMem
     with
     | .ok ([0], _) => true | _ => false)
  | _ => false

-- `nest_key_map`: both `ds` and `holes` empty, every index misses.
#guard
  match run (indPosFns ++ libFns ++ stubFns ++ masterFns) 100 "nest_key_map" [0, 0, 0, 0, 0]
    testMem with
  | .ok ([0, 0], _) => true | _ => false

-- `member_idx_at`: a non-`const` handle (tag `0`, `bvar`) never names a member.
#guard
  match run (indPosFns ++ libFns ++ stubFns ++ masterFns) 100 "member_idx_at" [0, 0, 0, 0] testMem
  with
  | .ok ([0, 0], _) => true | _ => false

-- `nest_ctx_hi_at`: an all-zero `NestCtx` (`nP = 0`, no names) at frame `5` is hole `5`.
#guard
  match run (indPosFns ++ libFns ++ stubFns ++ masterFns) 100 "nest_ctx_hi_at" [0, 5] testMem with
  | .ok ([5], _) => true | _ => false

-- `close_telescope`: an empty telescope returns the body unchanged.
#guard
  match run (indPosFns ++ libFns ++ stubFns ++ masterFns) 100 "close_telescope" [0, 0, 3, 7] testMem
  with
  | .ok ([7], _) => true | _ => false

-- `inst_pis_with`: no arguments, the type unchanged.
#guard
  match run (indPosFns ++ libFns ++ stubFns ++ masterFns) 100 "inst_pis_with" [0, 0, 9] testMem with
  | .ok ([1, 9], _) => true | _ => false

-- `nest_kinds_flat`: vacuously true on the empty list.
#guard
  match run (indPosFns ++ libFns ++ stubFns ++ masterFns) 100 "nest_kinds_flat" [0, 0] testMem with
  | .ok ([1], _) => true | _ => false

end L.Ind
