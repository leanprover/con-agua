module

public import ConAgua.Arena.IotaFrame
meta import ConAgua.Arena.IndIface

@[expose] public section

/-!
# The ι reading rule in L, part 2: the comparisons and the driver (lane ronsync8)

The L translation of the last section of `vendor/con-ron/ConRon/Arena/Inductives/IotaRead.lean`
(con-leche #622, con-ron #164 lane I): terms equal up to equivalent levels (`expr_lvl_eq`, the
twin's `lvlEq`; `lvl_eq`/`lvls_eq` answer `2` for `some true`), up to consumed annotations
(`ann_eq`), the two readings of a rule related (`iota_parts_rel`), and the driver over a
block's recursors (`block_reads_at`, the `.indDecl` arm's `blockReadsAt`).

**Fuel.** `expr_lvl_eq` and `ann_eq` take the twin's fuel as their last argument (`CWF` at the
top) and abort at `0`, where the twin fails with `.internal`.

**Names.** The annotations' names `optParam`, `autoParam`, `outParam`, `semiOutParam` (the twin's
`topName s`: `.str .anonymous s`) and `n.missing` are interned from their bytes, as `name_rec`
does (one function per name).

**Lists.** `listRel` (`list_lvl_eq`, `list_ann_eq`) and the recursions over rules and recursors
(`rules_read`, `recs_read`) are loops. A rule list is the recursor record's `EREC` run of
`Rule.size`-word records; the recursors an `IW` slice of constant records.
-/

namespace L.Ind

open L.Arena

/-! ## Equal up to equivalent levels -/

/-- `expr_lvl_eq(a, b, fu)`: `a` and `b` the same handle, or the same node with each `Sort` and
constant at equivalent levels and its parts so related; `1`/`0`. -/
-- con-ron: ConRon/Arena/Inductives/IotaRead.lean:302-352 ConRon.Arena.lvlEq
@[no_expose, l_impl ConRon.Arena.lvlEq]
def exprLvlEqL : FunDecl := lfn (a, b, fu) locals
    (g, ga, a1, a2, a3, gb, b1, b2, b3, z) {
  if fu == 0 { abort };
  if a == b { return 1 };
  g := ⟦a⟧.tag;
  if g != ⟦b⟧.tag { return 0 };
  if g == 2 {
    (ga, a1, a2, a3) := call e_view(a);
    (gb, b1, b2, b3) := call e_view(b);
    z := call lvl_eq(a1, b1);
    return u64(z == 2)
  };
  if g == 3 {
    (ga, a1, a2, a3) := call e_view(a);
    (gb, b1, b2, b3) := call e_view(b);
    if a1 != b1 { return 0 };
    z := call lvls_eq(a2, b2);
    return u64(z == 2)
  };
  if g == 4 || g == 5 || g == 6 {
    (ga, a1, a2, a3) := call e_view(a);
    (gb, b1, b2, b3) := call e_view(b);
    z := call expr_lvl_eq(a1, b1, fu - 1);
    if z == 0 { return 0 };
    z := call expr_lvl_eq(a2, b2, fu - 1);
    return z
  };
  if g == 7 {
    (ga, a1, a2, a3) := call e_view(a);
    (gb, b1, b2, b3) := call e_view(b);
    z := call expr_lvl_eq(a1, b1, fu - 1);
    if z == 0 { return 0 };
    z := call expr_lvl_eq(a2, b2, fu - 1);
    if z == 0 { return 0 };
    z := call expr_lvl_eq(a3, b3, fu - 1);
    return z
  };
  if g == 9 {
    (ga, a1, a2, a3) := call e_view(a);
    (gb, b1, b2, b3) := call e_view(b);
    if a1 != b1 { return 0 };
    if a2 != b2 { return 0 };
    z := call expr_lvl_eq(a3, b3, fu - 1);
    return z
  };
  return 0
}

/-! ## The annotations' names -/

/-- `name_opt_param()`: `.str .anonymous "optParam"`, interned. -/
-- con-ron: ConRon/Arena/Inductives/IotaRead.lean:354-358 ConRon.Arena.topName
@[no_expose, l_impl ConRon.Arena.topName]
def nameOptParamL : FunDecl := lfn () locals (a, o, pt, pb, s) {
  a := call intern_nanon();
  if a >= 4294967296 { abort };
  o := call pool_room(8);
  pt := ⦃o⦄.tier;
  pb := ⦃o⦄.idx;
  POOL⟨pt⟩[pb] := 111; POOL⟨pt⟩[pb + 1] := 112; POOL⟨pt⟩[pb + 2] := 116; POOL⟨pt⟩[pb + 3] := 80;
  POOL⟨pt⟩[pb + 4] := 97; POOL⟨pt⟩[pb + 5] := 114; POOL⟨pt⟩[pb + 6] := 97; POOL⟨pt⟩[pb + 7] := 109;
  s := call intern_nstr(a, o, 8);
  if s >= 4294967296 { abort };
  return s
}

/-- `name_auto_param()`: `.str .anonymous "autoParam"`, interned. -/
-- con-ron: ConRon/Arena/Inductives/IotaRead.lean:354-358 ConRon.Arena.topName
@[no_expose, l_impl ConRon.Arena.topName]
def nameAutoParamL : FunDecl := lfn () locals (a, o, pt, pb, s) {
  a := call intern_nanon();
  if a >= 4294967296 { abort };
  o := call pool_room(9);
  pt := ⦃o⦄.tier;
  pb := ⦃o⦄.idx;
  POOL⟨pt⟩[pb] := 97; POOL⟨pt⟩[pb + 1] := 117; POOL⟨pt⟩[pb + 2] := 116; POOL⟨pt⟩[pb + 3] := 111;
  POOL⟨pt⟩[pb + 4] := 80; POOL⟨pt⟩[pb + 5] := 97; POOL⟨pt⟩[pb + 6] := 114; POOL⟨pt⟩[pb + 7] := 97;
  POOL⟨pt⟩[pb + 8] := 109;
  s := call intern_nstr(a, o, 9);
  if s >= 4294967296 { abort };
  return s
}

/-- `name_out_param()`: `.str .anonymous "outParam"`, interned. -/
-- con-ron: ConRon/Arena/Inductives/IotaRead.lean:354-358 ConRon.Arena.topName
@[no_expose, l_impl ConRon.Arena.topName]
def nameOutParamL : FunDecl := lfn () locals (a, o, pt, pb, s) {
  a := call intern_nanon();
  if a >= 4294967296 { abort };
  o := call pool_room(8);
  pt := ⦃o⦄.tier;
  pb := ⦃o⦄.idx;
  POOL⟨pt⟩[pb] := 111; POOL⟨pt⟩[pb + 1] := 117; POOL⟨pt⟩[pb + 2] := 116; POOL⟨pt⟩[pb + 3] := 80;
  POOL⟨pt⟩[pb + 4] := 97; POOL⟨pt⟩[pb + 5] := 114; POOL⟨pt⟩[pb + 6] := 97; POOL⟨pt⟩[pb + 7] := 109;
  s := call intern_nstr(a, o, 8);
  if s >= 4294967296 { abort };
  return s
}

/-- `name_semi_out_param()`: `.str .anonymous "semiOutParam"`, interned. -/
-- con-ron: ConRon/Arena/Inductives/IotaRead.lean:354-358 ConRon.Arena.topName
@[no_expose, l_impl ConRon.Arena.topName]
def nameSemiOutParamL : FunDecl := lfn () locals (a, o, pt, pb, s) {
  a := call intern_nanon();
  if a >= 4294967296 { abort };
  o := call pool_room(12);
  pt := ⦃o⦄.tier;
  pb := ⦃o⦄.idx;
  POOL⟨pt⟩[pb] := 115; POOL⟨pt⟩[pb + 1] := 101; POOL⟨pt⟩[pb + 2] := 109; POOL⟨pt⟩[pb + 3] := 105;
  POOL⟨pt⟩[pb + 4] := 79; POOL⟨pt⟩[pb + 5] := 117; POOL⟨pt⟩[pb + 6] := 116; POOL⟨pt⟩[pb + 7] := 80;
  POOL⟨pt⟩[pb + 8] := 97; POOL⟨pt⟩[pb + 9] := 114; POOL⟨pt⟩[pb + 10] := 97; POOL⟨pt⟩[pb + 11] := 109;
  s := call intern_nstr(a, o, 12);
  if s >= 4294967296 { abort };
  return s
}

/-- `name_missing(n)`: `.str n "missing"`, interned. -/
-- con-ron: ConRon/Arena/Inductives/IotaRead.lean:360-378 ConRon.Arena.annWitness
@[no_expose, l_impl ConRon.Arena.annWitness]
def nameMissingL : FunDecl := lfn (n) locals (o, pt, pb, s) {
  o := call pool_room(7);
  pt := ⦃o⦄.tier;
  pb := ⦃o⦄.idx;
  POOL⟨pt⟩[pb] := 109; POOL⟨pt⟩[pb + 1] := 105; POOL⟨pt⟩[pb + 2] := 115; POOL⟨pt⟩[pb + 3] := 115;
  POOL⟨pt⟩[pb + 4] := 105; POOL⟨pt⟩[pb + 5] := 110; POOL⟨pt⟩[pb + 6] := 103;
  s := call intern_nstr(n, o, 7);
  if s >= 4294967296 { abort };
  return s
}

/-! ## Consumed annotations -/

/-- `ann_witness(vis, D)`: `D` a constant type `n` at no levels, and `n.missing` stored at no
levels with type `D`. -/
-- con-ron: ConRon/Arena/Inductives/IotaRead.lean:360-378 ConRon.Arena.annWitness
@[no_expose, l_impl ConRon.Arena.annWitness]
def annWitnessL : FunDecl := lfn (vis, D) locals (g, n, us, z, ok, l, m, f, q) {
  if ⟦D⟧.tag != 3 { return 0 };
  (g, n, us, z) := call e_view(D);
  (ok, l) := call view_ls_len(us);
  if l != 0 { return 0 };
  m := call name_missing(n);
  (f, q) := call env_find(m, vis);
  if f == 0 { return 0 };
  if EREC⦃q + ⟪CI.cv + CV.type⟫⦄ != D { return 0 };
  return u64(EREC⦃q + ⟪CI.cv + CV.lpsLen⟫⦄ == 0)
}

/-- `ann_ident_body(vis, p, p2, arity, b)`: the value's body under `fun (α : Sort p2)`, at the
definition's level parameter `p`: `α` at arity 1, `fun (_ : D) => α` at arity 2 with `D` either
`α` or a type a stored constant inhabits. -/
-- con-ron: ConRon/Arena/Inductives/IotaRead.lean:380-408 ConRon.Arena.annIdentBody
@[no_expose, l_impl ConRon.Arena.annIdentBody]
def annIdentBodyL : FunDecl := lfn (vis, p, p2, arity, b) locals (g, j, y, z, D, c, zz, r) {
  if arity == 1 {
    if ⟦b⟧.tag != 0 { return 0 };
    (g, j, y, z) := call e_view(b);
    if j != 0 { return 0 };
    return u64(p == p2)
  };
  if arity == 2 {
    if ⟦b⟧.tag != 5 { return 0 };
    (g, D, c, z) := call e_view(b);
    if ⟦c⟧.tag != 0 { return 0 };
    (g, j, y, z) := call e_view(c);
    if j != 1 { return 0 };
    if p != p2 { return 0 };
    zz := call intern_bvar(0);
    if 4294967296 <= zz { abort };
    if D == zz { return 1 };
    r := call ann_witness(vis, D);
    return r
  };
  return 0
}

/-- `ann_ident_val(vis, lpsO, lpsL, arity, v)`: one level parameter (the `EREC` slice `(lpsO,
lpsL)`), the value `fun (α : Sort p2) => …` at a parameter level `p2`, `ann_ident_body` on its
body. -/
-- con-ron: ConRon/Arena/Inductives/IotaRead.lean:410-429 ConRon.Arena.annIdentVal
@[no_expose, l_impl ConRon.Arena.annIdentVal]
def annIdentValL : FunDecl := lfn (vis, lpsO, lpsL, arity, v) locals (g, ty, b, z, u, y, k, p2, x, r) {
  if lpsL != 1 { return 0 };
  if ⟦v⟧.tag != 5 { return 0 };
  (g, ty, b, z) := call e_view(v);
  if ⟦ty⟧.tag != 2 { return 0 };
  (g, u, y, z) := call e_view(ty);
  (k, p2, x) := call lv_node(u);
  if k != 4 { return 0 };
  r := call ann_ident_body(vis, EREC⦃lpsO⦄, p2, arity, b);
  return r
}

/-- `ann_ident(vis, n, arity)`: `n` a stored definition whose level parameters and value
`ann_ident_val` accepts. -/
-- con-ron: ConRon/Arena/Inductives/IotaRead.lean:431-437 ConRon.Arena.annIdent
@[no_expose, l_impl ConRon.Arena.annIdent]
def annIdentL : FunDecl := lfn (vis, n, arity) locals (f, q, r) {
  (f, q) := call env_find(n, vis);
  if f == 0 { return 0 };
  if EREC⦃q⦄ != 1 { return 0 };
  r := call ann_ident_val(vis, EREC⦃q + ⟪CI.cv + CV.lpsOff⟫⦄, EREC⦃q + ⟪CI.cv + CV.lpsLen⟫⦄, arity,
    EREC⦃q + ⟪CI.defnValue⟫⦄);
  return r
}

/-- `ann_eq(vis, s, c, fu)`: `s` is `c` with type annotations consumed at its head, up to
equivalent levels. -/
-- con-ron: ConRon/Arena/Inductives/IotaRead.lean:439-482 ConRon.Arena.annEq
@[no_expose, l_impl ConRon.Arena.annEq]
def annEqL : FunDecl := lfn (vis, s, c, fu) locals
    (z, g, f, x, y, gg, a, n, us, ok, l, o, t, w, r) {
  if fu == 0 { abort };
  z := call expr_lvl_eq(s, c, ⟪CWF⟫);
  if z != 0 { return 1 };
  if ⟦c⟧.tag != 4 { return 0 };
  (g, f, x, y) := call e_view(c);
  if ⟦f⟧.tag == 4 {
    (g, gg, a, y) := call e_view(f);
    if ⟦gg⟧.tag != 3 { return 0 };
    (g, n, us, y) := call e_view(gg);
    (ok, l) := call view_ls_len(us);
    if l != 1 { return 0 };
    o := call name_opt_param();
    t := call name_auto_param();
    if n != o && n != t { return 0 };
    w := call ann_ident(vis, n, 2);
    if w == 0 { return 0 };
    r := call ann_eq(vis, s, a, fu - 1);
    return r
  };
  if ⟦f⟧.tag == 3 {
    (g, n, us, y) := call e_view(f);
    (ok, l) := call view_ls_len(us);
    if l != 1 { return 0 };
    o := call name_out_param();
    t := call name_semi_out_param();
    if n != o && n != t { return 0 };
    w := call ann_ident(vis, n, 1);
    if w == 0 { return 0 };
    r := call ann_eq(vis, s, x, fu - 1);
    return r
  };
  return 0
}

/-! ## The lists -/

/-- `list_lvl_eq(ao, al, bo, bl)`: two `IW` slices, pairwise `expr_lvl_eq`. -/
-- con-ron: ConRon/Arena/Inductives/IotaRead.lean:484-490 ConRon.Arena.listLvlEq
@[no_expose, l_impl ConRon.Arena.listLvlEq]
def listLvlEqL : FunDecl := lfn (ao, al, bo, bl) locals (j, z) {
  j := 0;
  while j < al && j < bl {
    z := call expr_lvl_eq(IW.u64[ao + j], IW.u64[bo + j], ⟪CWF⟫);
    if z == 0 { return 0 };
    j := j + 1
  };
  return u64(al == bl)
}

/-- `list_ann_eq(vis, ao, al, bo, bl)`: two `IW` slices, pairwise `ann_eq`. -/
-- con-ron: ConRon/Arena/Inductives/IotaRead.lean:492-498 ConRon.Arena.listAnnEq
@[no_expose, l_impl ConRon.Arena.listAnnEq]
def listAnnEqL : FunDecl := lfn (vis, ao, al, bo, bl) locals (j, z) {
  j := 0;
  while j < al && j < bl {
    z := call ann_eq(vis, IW.u64[ao + j], IW.u64[bo + j], ⟪CWF⟫);
    if z == 0 { return 0 };
    j := j + 1
  };
  return u64(al == bl)
}

/-- `params_ann_eq(vis, cnP, q, pdO, pdL)`: the recursor's (constant value `q`) first `cnP`
binder domains are the constructor's parameter domains `(pdO, pdL)` up to consumed annotations. -/
-- con-ron: ConRon/Arena/Inductives/IotaRead.lean:500-509 ConRon.Arena.paramsAnnEq
@[no_expose, l_impl ConRon.Arena.paramsAnnEq]
def paramsAnnEqL : FunDecl := lfn (vis, cnP, q, pdO, pdL) locals (ok, ro, rl, rest, r) {
  (ok, ro, rl, rest) := call strip_pis(cnP, EREC⦃q + ⟪CV.type⟫⦄);
  if ok == 0 { return 0 };
  r := call list_ann_eq(vis, ro, rl, pdO, pdL);
  return r
}

/-! ## The rule -/

/-- `iota_parts_rel(vis, cnP, q, r, IIotaParts', IIotaParts, pdO, pdL)`: the two readings of a
rule's parts are one: the same indices, levels and parameters, the fields' domains up to
equivalent levels, or (a plain rule whose parameters fit) up to consumed annotations. -/
-- con-ron: ConRon/Arena/Inductives/IotaRead.lean:511-531 ConRon.Arena.iotaPartsRel
@[no_expose, l_impl ConRon.Arena.iotaPartsRel]
def iotaPartsRelL : FunDecl := lfn (vis, cnP, q, r, a1, a2, a3, a4, a5, a6, a7,
    b1, b2, b3, b4, b5, b6, b7, pdO, pdL) locals (z) {
  z := call sl_eq(a3, a4, b3, b4);
  if z == 0 { return 0 };
  if a5 != b5 { return 0 };
  z := call sl_eq(a6, a7, b6, b7);
  if z == 0 { return 0 };
  z := call list_lvl_eq(a1, a2, b1, b2);
  if z != 0 { return 1 };
  if EREC⦃r + ⟪Rule.fire⟫⦄ != 0 { return 0 };
  z := call params_ann_eq(vis, cnP, q, pdO, pdL);
  if z == 0 { return 0 };
  z := call list_ann_eq(vis, a1, a2, b1, b2);
  return z
}

/-- `rule_reads(vis, q, ok, IotaRec, mI, rP, i, r)`: rule `r` (the `i`-th) of the recursor with
constant value `q` and frame `(ok, IotaRec)` reads: its parts off the recursor's type are its
parts through its constructor, stored under the rule's name. -/
-- con-ron: ConRon/Arena/Inductives/IotaRead.lean:533-550 ConRon.Arena.ruleReads
@[no_expose, l_impl ConRon.Arena.ruleReads]
def ruleReadsL : FunDecl := lfn (vis, q, rok, r1, r2, r3, r4, r5, r6, r7, mI, rP, i, r) locals
    (nI, ok, a1, a2, a3, a4, a5, a6, a7, f, qj, cnP, b1, b2, b3, b4, b5, b6, b7, pdO, pdL, z) {
  if rok == 0 { return 0 };
  nI := mI - rP;
  if mI < rP { nI := 0 };
  (ok, a1, a2, a3, a4, a5, a6, a7) := call iota_parts_of_at(r1, r2, r3, r4, r5, r6, r7, rP, nI, i, r);
  if ok == 0 { return 0 };
  (f, qj) := call env_find(EREC⦃r⦄, vis);
  if f == 0 { return 0 };
  if EREC⦃qj⦄ != 4 { return 0 };
  cnP := EREC⦃qj + ⟪CI.ctorNparams⟫⦄;
  (ok, b1, b2, b3, b4, b5, b6, b7, pdO, pdL) := call iota_parts_at(qj + ⟪CI.cv⟫, cnP, mI, rP, r);
  if ok == 0 { return 0 };
  z := call iota_parts_rel(vis, cnP, q, r, a1, a2, a3, a4, a5, a6, a7, b1, b2, b3, b4, b5, b6, b7,
    pdO, pdL);
  return z
}

/-- `rules_read(vis, q, ok, IotaRec, mI, rP, ro, rl)`: each rule of the `EREC` run `(ro, rl)`
reads, by position. -/
-- con-ron: ConRon/Arena/Inductives/IotaRead.lean:552-560 ConRon.Arena.rulesRead
@[no_expose, l_impl ConRon.Arena.rulesRead]
def rulesReadL : FunDecl := lfn (vis, q, rok, r1, r2, r3, r4, r5, r6, r7, mI, rP, ro, rl) locals
    (i, z) {
  i := 0;
  while i < rl {
    z := call rule_reads(vis, q, rok, r1, r2, r3, r4, r5, r6, r7, mI, rP, i, ro + ⟪Rule.size⟫ * i);
    if z == 0 { return 0 };
    i := i + 1
  };
  return 1
}

/-- `rec_reads(vis, ci)`: at a recursor (constant record `ci`), each of its rules reads; any
other constant reads. -/
-- con-ron: ConRon/Arena/Inductives/IotaRead.lean:562-571 ConRon.Arena.recReads
@[no_expose, l_impl ConRon.Arena.recReads]
def recReadsL : FunDecl := lfn (vis, ci) locals
    (q, mI, rP, ok, r1, r2, r3, r4, r5, r6, r7, z) {
  if EREC⦃ci⦄ != 5 { return 1 };
  q := ci + ⟪CI.cv⟫;
  mI := EREC⦃ci + ⟪CI.recMajor⟫⦄;
  rP := EREC⦃ci + ⟪CI.recPrefix⟫⦄;
  (ok, r1, r2, r3, r4, r5, r6, r7) := call iota_rec_of(q, mI, rP);
  z := call rules_read(vis, q, ok, r1, r2, r3, r4, r5, r6, r7, mI, rP, EREC⦃ci + ⟪CI.recRulesOff⟫⦄,
    EREC⦃ci + ⟪CI.recRulesLen⟫⦄);
  return z
}

/-- `recs_read(vis, o, l)`: every constant of the `IW` slice reads. -/
-- con-ron: ConRon/Arena/Inductives/IotaRead.lean:573-579 ConRon.Arena.recsRead
@[no_expose, l_impl ConRon.Arena.recsRead]
def recsReadL : FunDecl := lfn (vis, o, l) locals (j, z) {
  j := 0;
  while j < l {
    z := call rec_reads(vis, IW.u64[o + j]);
    if z == 0 { return 0 };
    j := j + 1
  };
  return 1
}

/-- `block_reads_at(vis, p)`: every recursor the block `p` installs reads, against the input
view with the block's constants pushed in place (`cons_block_recs_temp`); `(b, vis')`, the view
with the pushes undone (`gen_rec_check_pop_all`) and the literal flags set back. -/
-- con-ron: ConRon/Arena/Inductives/IotaRead.lean:581-594 ConRon.Arena.blockReadsAt
@[no_expose, l_impl ConRon.Arena.blockReadsAt]
def blockReadsAtL : FunDecl := lfn (vis, p) locals
    (nl, sl, co, cl, ro, rl, feR, po, pl, ok, fe0, u) {
  nl := CTL.u64[160];
  sl := CTL.u64[161];
  (co, cl) := call block_constants(p);
  (ro, rl) := call block_recs(p, IW.u64[p + 2], IW.u64[p + 3]);
  (feR, po, pl) := call cons_block_recs_temp(co, cl, vis, 0, 0);
  ok := call recs_read(feR, ro, rl);
  fe0 := call gen_rec_check_pop_all(feR, po, pl);
  u := call env_set_flags(nl, sl);
  return (ok, fe0)
}

/-! ## The module's program -/

/-- This module's functions. -/
def iotaRelFns : Prog :=
  [("expr_lvl_eq", exprLvlEqL), ("name_opt_param", nameOptParamL),
   ("name_auto_param", nameAutoParamL), ("name_out_param", nameOutParamL),
   ("name_semi_out_param", nameSemiOutParamL), ("name_missing", nameMissingL),
   ("ann_witness", annWitnessL), ("ann_ident_body", annIdentBodyL),
   ("ann_ident_val", annIdentValL), ("ann_ident", annIdentL), ("ann_eq", annEqL),
   ("list_lvl_eq", listLvlEqL), ("list_ann_eq", listAnnEqL), ("params_ann_eq", paramsAnnEqL),
   ("iota_parts_rel", iotaPartsRelL), ("rule_reads", ruleReadsL), ("rules_read", rulesReadL),
   ("rec_reads", recReadsL), ("recs_read", recsReadL), ("block_reads_at", blockReadsAtL)]

end L.Ind
