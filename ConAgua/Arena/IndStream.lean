module

public import ConAgua.Arena.IndIface
meta import ConAgua.Arena.IndIface

@[expose] public section

/-!
# The stream's recursors, against the generated ones (lane `induct`, module `IndStream`)

The L translation of `vendor/con-ron/ConRon/Arena/Inductives/StreamRecs.lean`: the block's check
generates every recursor (`gen_rec_check`) and compares the stream's records with them up to
definitional equality (`stream_recs_check`), and checks the records' K flags against the block
(`stream_k_check`). What is installed is the record (`block_recs`, `IndDeclConsts.lean`).

Representation: a stream recursor is a `RecShape` record (`IndIface`: `[cvR, rP, mI, tgt,
rules.off, rules.len, isK]`, its rules the record's `EREC` run of 11-word rules); a generated one
is `gen_rec_check`'s triple `[cv, M, rhss.off, rhss.len]` (`M` a `TargetMajor`). A firing mode is
five words `(kind, lvls.off, lvls.len, pins.off, pins.len)` (`aux_rule_fire`'s, `IW` slices).

`open_pis_at_fvars(n, e, i)` (the twin's `openPisAtFvars`, which `recTyCheck` calls, not the `F`
variant) is written here over `opa_go` (`StubInd.lean`), in `open_pis_at_fvars_f`'s result
convention.

Foreign callees: `rec_k_expected`, `aux_rule_fire` (`RecCheck`); `unresolved_consts_error(vis, e,
w)` at `w = 5` ("the type of the recursor") and `w = 6` ("the recursor's rule"), arms its owner
adds (`ConstsResolveF.lean`); the core's entry points as in `IndIface`.
-/

namespace L.Ind

open L.Arena

/-- `open_pis_at_fvars(n, e, i)`: `openPisAtFvars n e i`, as `(1, fvs.off, n, body)` (the free
variables an `IW` slice, in binder order) or `(0, 0, 0, 0)` (`opa_go` pushes them on `SPN`, read
back and popped; a first index `i ≥ 2^63` a capacity abort, D33). -/
-- con-ron: ConRon/Arena/Core.lean:3042-3058 ConRon.Arena.openPisAtFvars
@[no_expose, l_impl ConRon.Arena.openPisAtFvars]
def openPisAtFvarsL : FunDecl := lfn (n, e, i) locals (co, ok, b, q, u) {
  if i >> 63 != 0 { abort };
  co := CTL.u64[136];
  if len(SPN.u64) < co { abort };
  (ok, b) := call opa_go(n, e, i);
  if ok == 0 { CTL.u64[136] := co; return (0, 0, 0, 0) };
  q := call iw_alloc(n);
  u := call spn_to_iw(q, co, n);
  CTL.u64[136] := co;
  return (1, q, n, b)
}

/-- `rec_doms_at(vis, sfvs.off, sfvs.len, gfvs.off, gfvs.len, j, k)`: a record's type's domains
against the generated one's, binder by binder from binder `j` on (`k` of them): each stored domain
`isDefEq` to the generated one at its depth. -/
-- con-ron: ConRon/Arena/Inductives/StreamRecs.lean:35-51 ConRon.Arena.recDomsAt
@[no_expose, l_impl ConRon.Arena.recDomsAt]
def recDomsAtL : FunDecl := lfn (vis, so, sl, go, gl, j, k) locals (a, b, eq, u) {
  if k == 0 { return 0 };
  if sl <= j { abort };
  if gl <= j { abort };
  a := call fvar_type_d(IW.u64[so + j]);
  b := call fvar_type_d(IW.u64[go + j]);
  eq := call is_def_eq_core(vis, j, a, b);
  if eq == 0 { fail R_THE_TYPE_OF_THE_RECURSOR_IS };
  u := call rec_doms_at(vis, so, sl, go, gl, j + 1, k - 1);
  return 0
}

/-- `rec_ty_opened(vis, n, sok, sfvs.off, sfvs.len, srest, gok, gfvs.off, gfvs.len, grest)`: the
record's and the generated type, opened `n` binders deep: the domains, then the residues. -/
-- con-ron: ConRon/Arena/Inductives/StreamRecs.lean:53-64 ConRon.Arena.recTyOpened
@[no_expose, l_impl ConRon.Arena.recTyOpened]
def recTyOpenedL : FunDecl := lfn (vis, n, sok, so, sl, sr, gok, go, gl, gr) locals (u, eq) {
  if sok == 0 { fail R_THE_TYPE_OF_THE };
  if gok == 0 { abort };
  u := call rec_doms_at(vis, so, sl, go, gl, 0, n);
  eq := call is_def_eq_core(vis, n, sr, gr);
  if eq == 0 { fail R_THE_TYPE_OF_THE_RECURSOR };
  return 0
}

/-- `stream_closed(s, g)`: `s.looseBVarsBounded 0 && !s.hasFvar && !g.hasFvar`. -/
-- con-ron: ConRon/Arena/Inductives/StreamRecs.lean:66-77 ConRon.Arena.streamClosed
@[no_expose, l_impl ConRon.Arena.streamClosed]
def streamClosedL : FunDecl := lfn (s, g) locals (b, h) {
  b := call loose_bvars_bounded_fast(⟪CWF⟫, 0, s);
  if b == 0 { return 0 };
  h := call has_fvar_fast(⟪CWF⟫, s);
  if h != 0 { return 0 };
  h := call has_fvar_fast(⟪CWF⟫, g);
  return u64(h == 0)
}

/-- `rec_ty_check(vis, lps.off, lps.len, n, s, g)`: a record's type's check — closed, at the
record's level parameters, resolving, a type, and the generated one binder by binder up to the
major (`n` binders). -/
-- con-ron: ConRon/Arena/Inductives/StreamRecs.lean:79-96 ConRon.Arena.recTyCheck
@[no_expose, l_impl ConRon.Arena.recTyCheck]
def recTyCheckL : FunDecl := lfn (vis, lo, ll, n, s, g)
    locals (c, u, st, sok, so, sl, sr, gok, go, gl, gr) {
  c := call stream_closed(s, g);
  if c == 0 { fail R_THE_TYPE_OF };
  c := call all_level_params_defined(lo, ll, s);
  if c == 0 { fail R_UNDECLARED_UNIVERSE_PARAMETER_IN_THE };
  c := call consts_resolve_ffast(vis, s);
  if c == 0 { u := call unresolved_consts_error(vis, s, 5); abort };
  st := call infer_type_core(vis, 0, s);
  u := call ensure_sort_core(vis, 0, st);
  (sok, so, sl, sr) := call open_pis_at_fvars(n, s, 0);
  (gok, go, gl, gr) := call open_pis_at_fvars(n, g, 0);
  u := call rec_ty_opened(vis, n, sok, so, sl, sr, gok, go, gl, gr);
  return 0
}

/-- `rule_agree(vis, lps.off, lps.len, s, g)`: one rule's check — the record's right-hand side `s`
closed, at the record's level parameters, resolving; it and the generated `g` inferred, their types
definitionally equal, and so are they. -/
-- con-ron: ConRon/Arena/Inductives/StreamRecs.lean:98-115 ConRon.Arena.ruleAgree
@[no_expose, l_impl ConRon.Arena.ruleAgree]
def ruleAgreeL : FunDecl := lfn (vis, lo, ll, s, g) locals (c, u, ts, tg, eq) {
  c := call stream_closed(s, g);
  if c == 0 { fail R_THE_RECURSOR_S };
  c := call all_level_params_defined(lo, ll, s);
  if c == 0 { fail R_THE_RECURSOR_S_RULE_FOR_HAS };
  c := call consts_resolve_ffast(vis, s);
  if c == 0 { u := call unresolved_consts_error(vis, s, 6); abort };
  ts := call infer_type_core(vis, 0, s);
  tg := call infer_type_core(vis, 0, g);
  eq := call is_def_eq_core(vis, 0, ts, tg);
  if eq == 0 { fail R_THE_RECURSOR_S_RULE_FOR };
  eq := call is_def_eq_core(vis, 0, s, g);
  if eq == 0 { fail R_THE_RECURSOR_S_RULE };
  return 0
}

/-- `stream_nested_pins(n, pins.off, pins.len)`: the pins lifted past the `n` index binders
(`pins.mapM (liftLooseBVarsFast coreWalkFuel n 0)`), a fresh `IW` slice. -/
-- con-ron: ConRon/Arena/Inductives/StreamRecs.lean:117-136 ConRon.Arena.streamNestedDom
@[no_expose, l_impl ConRon.Arena.streamNestedDom]
def streamNestedPins : FunDecl := lfn (n, po, pl) locals (x, ro, rl, o, l) {
  if pl == 0 { return (0, 0) };
  x := call lift_entry(IW.u64[po], n, 0, ⟪CWF⟫);
  if 4294967296 <= x { abort };
  (ro, rl) := call stream_nested_pins(n, po + 1, pl - 1);
  (o, l) := call sl_cons(x, ro, rl);
  return (o, l)
}

/-- `stream_nested_bvars(n, i)`: `bvar (n - 1 - i)` for `i, …, n - 1` (`(List.range n).mapM`, from
`i`), a fresh `IW` slice. -/
-- con-ron: ConRon/Arena/Inductives/StreamRecs.lean:117-136 ConRon.Arena.streamNestedDom
@[no_expose, l_impl ConRon.Arena.streamNestedDom]
def streamNestedBvars : FunDecl := lfn (n, i) locals (x, ro, rl, o, l) {
  if n <= i { return (0, 0) };
  x := call intern_bvar(n - 1 - i);
  if 4294967296 <= x { abort };
  (ro, rl) := call stream_nested_bvars(n, i + 1);
  (o, l) := call sl_cons(x, ro, rl);
  return (o, l)
}

/-- `stream_nested_dom(dom, n, lvls.off, lvls.len, pins.off, pins.len)`: the major's domain against
the firing data — its head a constant at the firing levels, its arguments the pins lifted past the
index binders and the index variables. -/
-- con-ron: ConRon/Arena/Inductives/StreamRecs.lean:117-136 ConRon.Arena.streamNestedDom
@[no_expose, l_impl ConRon.Arena.streamNestedDom]
def streamNestedDomL : FunDecl := lfn (dom, n, lo, ll, po, pl)
    locals (hd, g, x, us, z, uo, ul, eq, ao, al, so, sl, bo, bl, wo, wl) {
  hd := call get_app_fn_f(⟪CWF⟫, dom);
  if ⟦hd⟧.tag != 3 { return 0 };
  (g, x, us, z) := call e_view(hd);
  (uo, ul) := call view_ls(us);
  eq := call sl_eq(uo, ul, lo, ll);
  if eq == 0 { return 0 };
  (ao, al) := call get_app_args_f(⟪CWF⟫, dom);
  (so, sl) := call stream_nested_pins(n, po, pl);
  (bo, bl) := call stream_nested_bvars(n, 0);
  (wo, wl) := call sl_append(so, sl, bo, bl);
  eq := call sl_eq(ao, al, wo, wl);
  return eq
}

/-- `stream_nested_ok(ty, mI, rP, kind, lvls.off, lvls.len, pins.off, pins.len)`: an auxiliary
recursor's type fires where the generated one does — its major's domain (binder `mI`) is the
container at the firing data's levels, applied to the pins lifted past the index binders and the
index variables; `1` at `.plain` (kind `0`) and `.levels` (kind `2`). -/
-- con-ron: ConRon/Arena/Inductives/StreamRecs.lean:138-155 ConRon.Arena.streamNestedOk
@[no_expose, l_impl ConRon.Arena.streamNestedOk]
def streamNestedOkL : FunDecl := lfn (ty, mI, rP, kind, lo, ll, po, pl)
    locals (ok, bo, bl, rest, g, dom, b, z, d, r) {
  if kind != 1 { return 1 };
  (ok, bo, bl, rest) := call strip_pis(mI, ty);
  if ok == 0 { return 0 };
  if ⟦rest⟧.tag != 6 { return 0 };
  (g, dom, b, z) := call e_view(rest);
  d := mI - rP;
  if mI < rP { d := 0 };
  r := call stream_nested_dom(dom, d, lo, ll, po, pl);
  return r
}

/-- `generated_fire(M, rP)`: the firing mode the generated recursor's rules carry at its major —
`.nested` (`aux_rule_fire`) at an outside major, `.plain` at a member. -/
-- con-ron: ConRon/Arena/Inductives/StreamRecs.lean:157-164 ConRon.Arena.generatedFire
@[no_expose, l_impl ConRon.Arena.generatedFire]
def generatedFireL : FunDecl := lfn (M, rP) locals (k, lo, ll, po, pl) {
  if IW.u64[M + 8] != 0 { return (0, 0, 0, 0, 0) };
  (k, lo, ll, po, pl) := call aux_rule_fire(M, rP);
  return (k, lo, ll, po, pl)
}

/-- `stream_rules_shape(rules.off, rules.cnt, ctors.off, ctors.len)`: the record's rules (an `EREC`
run of 11-word rules) against the generated recursor's class (`[cv, nF]` pointers): one rule per
constructor, in order, each with its field count. -/
-- con-ron: ConRon/Arena/Inductives/StreamRecs.lean:166-176 ConRon.Arena.streamRulesShape
@[no_expose, l_impl ConRon.Arena.streamRulesShape]
def streamRulesShapeL : FunDecl := lfn (ro, rl, co, cl) locals (c, u) {
  if rl == 0 && cl == 0 { return 0 };
  if rl == 0 || cl == 0 { fail R_THE_RECURSOR_CARRIES };
  c := IW.u64[co];
  if EREC⦃ro⦄ != EREC⦃IW.u64[c]⦄ || EREC⦃ro + 1⦄ != IW.u64[c + 1] { fail R_THE_RECURSOR_S_RULE_FOR_IS };
  u := call stream_rules_shape(ro + 11, rl - 1, co + 1, cl - 1);
  return 0
}

/-- `stream_rules_check(vis, lps.off, lps.len, rules.off, rules.cnt, gs.off, gs.len)`: the record's
rules' checks, each against the generated right-hand side at its position (a rule equal to the
generated one needs none). -/
-- con-ron: ConRon/Arena/Inductives/StreamRecs.lean:178-189 ConRon.Arena.streamRulesCheck
@[no_expose, l_impl ConRon.Arena.streamRulesCheck]
def streamRulesCheckL : FunDecl := lfn (vis, lo, ll, ro, rl, go, gl) locals (s, u) {
  if rl == 0 && gl == 0 { return 0 };
  if rl == 0 || gl == 0 { abort };
  s := EREC⦃ro + 8⦄;
  if s != IW.u64[go] { u := call rule_agree(vis, lo, ll, s, IW.u64[go]) };
  u := call stream_rules_check(vis, lo, ll, ro + 11, rl - 1, go + 1, gl - 1);
  return 0
}

/-- `stream_rec_compare(vis, rc, g)`: the comparison of one recursor — its type unless it is the
generated one (`rec_ty_check` up to the major, `mI + 1` binders), and its rules. -/
-- con-ron: ConRon/Arena/Inductives/StreamRecs.lean:191-199 ConRon.Arena.streamRecCompare
@[no_expose, l_impl ConRon.Arena.streamRecCompare]
def streamRecCompareL : FunDecl := lfn (vis, rc, g) locals (cvR, cvG, lo, ll, n, u) {
  cvR := IW.u64[rc];
  cvG := IW.u64[g];
  (lo, ll) := call cv_lps(cvG);
  if EREC⦃cvR + ⟪CV.type⟫⦄ != EREC⦃cvG + ⟪CV.type⟫⦄ {
    n := IW.u64[rc + 2] + 1;
    if n == 0 { abort };
    u := call rec_ty_check(vis, lo, ll, n, EREC⦃cvR + ⟪CV.type⟫⦄, EREC⦃cvG + ⟪CV.type⟫⦄)
  };
  u := call stream_rules_check(vis, lo, ll, IW.u64[rc + 4], IW.u64[rc + 5], IW.u64[g + 2],
    IW.u64[g + 3]);
  return 0
}

/-- `stream_rec_check(vis, rc, g)`: one recursor, the stream's against the generated one — the
rules' shape and the record's major's container, then the comparison. -/
-- con-ron: ConRon/Arena/Inductives/StreamRecs.lean:201-211 ConRon.Arena.streamRecCheck
@[no_expose, l_impl ConRon.Arena.streamRecCheck]
def streamRecCheckL : FunDecl := lfn (vis, rc, g) locals (M, u, k, lo, ll, po, pl, ok) {
  M := IW.u64[g + 1];
  u := call stream_rules_shape(IW.u64[rc + 4], IW.u64[rc + 5], IW.u64[M + 6], IW.u64[M + 7]);
  (k, lo, ll, po, pl) := call generated_fire(M, IW.u64[rc + 1]);
  ok := call stream_nested_ok(EREC⦃IW.u64[rc] + ⟪CV.type⟫⦄, IW.u64[rc + 2], IW.u64[rc + 1], k, lo, ll, po,
    pl);
  if ok == 0 { fail R_THE_RECURSOR_S_STORED };
  u := call stream_rec_compare(vis, rc, g);
  return 0
}

/-- `stream_recs_check(vis, recs.off, recs.len, gs.off, gs.len)`: the block's recursors against
the generated ones, record by record (the generated family is in the records' order). -/
-- con-ron: ConRon/Arena/Inductives/StreamRecs.lean:213-223 ConRon.Arena.streamRecsCheck
@[no_expose, l_impl ConRon.Arena.streamRecsCheck]
def streamRecsCheckL : FunDecl := lfn (vis, ro, rl, go, gl) locals (u) {
  if rl == 0 && gl == 0 { return 0 };
  if rl == 0 || gl == 0 { abort };
  u := call stream_rec_check(vis, IW.u64[ro], IW.u64[go]);
  u := call stream_recs_check(vis, ro + 1, rl - 1, go + 1, gl - 1);
  return 0
}

/-- `stream_k_check(p, recs.off, recs.len, gs.off, gs.len)`: the records' K flags against the
block — each record's flag the one the generated recursor has (`rec_k_expected`). -/
-- con-ron: ConRon/Arena/Inductives/StreamRecs.lean:225-234 ConRon.Arena.streamKCheck
@[no_expose, l_impl ConRon.Arena.streamKCheck]
def streamKCheckL : FunDecl := lfn (p, ro, rl, go, gl) locals (rc, e, u) {
  if rl == 0 || gl == 0 { return 0 };
  rc := IW.u64[ro];
  e := call rec_k_expected(p, IW.u64[IW.u64[go] + 1]);
  if u64(IW.u64[rc + 6] != 0) != e { fail R_RECURSOR_DECLARES_K_THE };
  u := call stream_k_check(p, ro + 1, rl - 1, go + 1, gl - 1);
  return 0
}

/-- This module's functions. -/
def indStreamFns : Prog :=
  [("open_pis_at_fvars", openPisAtFvarsL), ("rec_doms_at", recDomsAtL),
   ("rec_ty_opened", recTyOpenedL), ("stream_closed", streamClosedL), ("rec_ty_check", recTyCheckL),
   ("rule_agree", ruleAgreeL), ("stream_nested_pins", streamNestedPins),
   ("stream_nested_bvars", streamNestedBvars), ("stream_nested_dom", streamNestedDomL),
   ("stream_nested_ok", streamNestedOkL), ("generated_fire", generatedFireL),
   ("stream_rules_shape", streamRulesShapeL), ("stream_rules_check", streamRulesCheckL),
   ("stream_rec_compare", streamRecCompareL), ("stream_rec_check", streamRecCheckL),
   ("stream_recs_check", streamRecsCheckL), ("stream_k_check", streamKCheckL)]

/-- Stubs for the functions of OTHER modules this module calls. -/
def indStreamForeign : Prog :=
  [("opa_go", stub 3), ("spn_to_iw", stub 3), ("unresolved_consts_error", stub 3),
   ("lift_entry", stub 4), ("rec_k_expected", stub 2), ("aux_rule_fire", stub 2)]

-- `stream_recs_check` and `stream_k_check` at empty lists: nothing read.
#guard
  match run (indStreamFns ++ libFns ++ stubFns ++ masterFns ++ indStreamForeign) 100
      "stream_recs_check" [0, 0, 0, 0, 0] testMem with
  | .ok ([0], _) => true
  | _ => false

end L.Ind
