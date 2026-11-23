module

public import ConAgua.Arena.IndIface
meta import ConAgua.Arena.IndIface

@[expose] public section

/-!
# The block reader in L (lane `induct`, module `IndParts`)

The L translation of `vendor/con-ron/ConRon/Arena/Inductives/FieldTele.lean`'s `piBinders`, all of
`vendor/con-ron/ConRon/Arena/Inductives/BlockShape.lean`, `BlockRec.lean`'s
`blockLargeElimAllowed`, and `CheckDecl.lean`'s `.indDecl` arm of `checkDeclKind` (as
`check_ind_decl`). No proofs this round (IndIface, "No proofs
this round"); the point is a faithful translation, one `FunDecl` per twin function, split into
helpers where a twin function has more than one loop or a long straight-line body.

## Representation, beyond IndIface's table

* **The block** (`List IConstantInfo`, the twin's `block` argument): an `EREC` slice of
  constant-record pointers (`ind_block_to_erec`'s `EREC` slice in `check_decl`; `pinsenv`'s `decCI` layout).
* **`blockSplitRecs`'s element** (`IConstantVal × Nat × Nat × Bool × List IRecRule`, a recursor
  before it is folded into a `RecShape`): a fresh `IW` record `[cvR, mI, rP, rules.off, rules.len,
  isK]` (`rules`
  an `EREC` slice of `decRule` records, unchanged — nothing to copy, it already lives in
  `EREC` and stays there).
* **`blockSplitCtors`'s element** (`IConstantVal × Nat × Nat`, a constructor before grouping):
  `[cv, nP, nF]`.
* **`blockSplit`'s result**: 7 words flattens past the 6-result cap, so (as IndIface's authors
  anticipated) it is `(ok, q)` with `q` a fresh 6-word record `[cvTs.off, cvTs.len, cs.off, cs.len,
  rs.off, rs.len]` (formers: plain `EREC` cv pointers; `cs`, `rs`: the element records above).

## Foreign callees (owned by other modules of this lane)

* `member_idx_at(names.off, names.len, lvls, e)` → `(ok, i)`: `ConRon.Arena.memberIdxAt?` (module
  `IndPos`).
* `param_levels(lps.off, lps.len)` → `us`: `ConRon.Arena.paramLevels` (module `IndSum`).
* `check_block(vis, boff, blen, p)` → `vis'`: `ConRon.Arena.checkBlock` (module `IndInstall`; the
  block as an `IW` slice of constant-record pointers, `p` the `BlockShape` pointer).

Everything else this file calls is in `libFns`, `stubFns` or `masterFns` (IndIface).
-/

namespace L.Ind

open L.Arena

/-! ## `FieldTele.piBinders` -/

/-- `pi_binders(fuel, h)`: `piBinders fuel h`. `h`'s tag is read off the raw handle (pure, no
`view`), as the twin's `h.tag` does; only once it is `forallE` do we call `e_view` (which can abort
on a dangling handle, as `viewBind` can). The result list is built by consing on the way out
(`sl_cons`), the same list the twin's recursion conses. -/
-- con-ron: ConRon/Arena/Inductives/FieldTele.lean:23-36 ConRon.Arena.piBinders
@[no_expose, l_impl ConRon.Arena.piBinders]
def piBinders : FunDecl := lfn (fuel, h) locals (g, ty, b, z, bo, bl, be, o, l) {
  if fuel == 0 { abort };
  if ⟦h⟧.tag != 6 { return (0, 0, h) };
  (g, ty, b, z) := call e_view(h);
  (bo, bl, be) := call pi_binders(fuel - 1, b);
  (o, l) := call sl_cons(ty, bo, bl);
  return (o, l, be)
}

/-! ## `BlockParts`: the record's pure projections -/

/-- `num_ctors_of(off, l)`: `numCtorsOf` of the `IW` slice of `MemberShape` pointers (sum of each
member's `ctors.len`, at offset `+3`), recursively on the slice (as the twin's recursion is). Aborts
when the sum wraps (a capacity: the twin's `Nat` does not). -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:124-128 ConRon.Arena.numCtorsOf
@[no_expose, l_impl ConRon.Arena.numCtorsOf]
def numCtorsOf : FunDecl := lfn (off, l) locals (r, m, s) {
  if l == 0 { return 0 };
  r := call num_ctors_of(off + 1, l - 1);
  m := IW.u64[off];
  s := IW.u64[m + 3] + r;
  if s < r { abort };
  return s
}

/-- `block_shape_k(p)`: `BlockShape.k`, the members' count (`members.len`, word `p + 1`). -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:130-132 ConRon.Arena.BlockShape.k
@[no_expose, l_impl ConRon.Arena.BlockShape.k]
def blockShapeK : FunDecl := lfn (p) locals () {
  return IW.u64[p + 1]
}

/-- `block_shape_num_ctors(p)`: `BlockShape.numCtors`. -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:134-136 ConRon.Arena.BlockShape.numCtors
@[no_expose, l_impl ConRon.Arena.BlockShape.numCtors]
def blockShapeNumCtors : FunDecl := lfn (p) locals (o, l, r) {
  o := IW.u64[p];
  l := IW.u64[p + 1];
  r := call num_ctors_of(o, l);
  return r
}

/-- `block_shape_member_names(p)`: `BlockShape.memberNames`, each member's `cvT.name` (`EREC` word
`0` of the member's `cvT` pointer). -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:138-140 ConRon.Arena.BlockShape.memberNames
@[no_expose, l_impl ConRon.Arena.BlockShape.memberNames]
def blockShapeMemberNames : FunDecl := lfn (p) locals (off, l, q, u) {
  off := IW.u64[p];
  l := IW.u64[p + 1];
  q := call iw_alloc(l);
  u := call member_names_copy(q, off, l);
  return (q, l)
}

/-- `member_names_copy(d, s, l)`: `IW[d+j] := EREC[IW[IW[s+j]]]` for `j < l` (each member's
`cvT.name`: the member record's word `0` is the `cvT` pointer), recursively. -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:138-140 ConRon.Arena.BlockShape.memberNames
@[no_expose, l_impl ConRon.Arena.BlockShape.memberNames]
def memberNamesCopy : FunDecl := lfn (d, s, l) locals (m, cv, u) {
  if l == 0 { return 0 };
  m := IW.u64[s];
  cv := IW.u64[m];
  IW.u64[d] := EREC⦃cv⦄;
  u := call member_names_copy(d + 1, s + 1, l - 1);
  return 0
}

/-- `block_shape_n_idxs(p)`: `BlockShape.nIdxs`, each member's `nIdx` (word `+1`). -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:142-144 ConRon.Arena.BlockShape.nIdxs
@[no_expose, l_impl ConRon.Arena.BlockShape.nIdxs]
def blockShapeNIdxs : FunDecl := lfn (p) locals (off, l, q, u) {
  off := IW.u64[p];
  l := IW.u64[p + 1];
  q := call iw_alloc(l);
  u := call n_idxs_copy(q, off, l);
  return (q, l)
}

/-- `n_idxs_copy(d, s, l)`: `IW[d+j] := IW[IW[s+j] + 1]` for `j < l` (each member pointer's
`nIdx`), recursively. -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:142-144 ConRon.Arena.BlockShape.nIdxs
@[no_expose, l_impl ConRon.Arena.BlockShape.nIdxs]
def nIdxsCopy : FunDecl := lfn (d, s, l) locals (m, u) {
  if l == 0 { return 0 };
  m := IW.u64[s];
  IW.u64[d] := IW.u64[m + 1];
  u := call n_idxs_copy(d + 1, s + 1, l - 1);
  return 0
}

/-- `block_shape_lps(p)`: `BlockShape.lps`, member `0`'s `cvT.levelParams` copied from `EREC` into
`IW` (`[]` at no member). -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:146-151 ConRon.Arena.BlockShape.lps
@[no_expose, l_impl ConRon.Arena.BlockShape.lps]
def blockShapeLps : FunDecl := lfn (p) locals (off, l, m, cv, o, pl) {
  off := IW.u64[p];
  l := IW.u64[p + 1];
  if l == 0 { return (0, 0) };
  m := IW.u64[off];
  cv := IW.u64[m];
  (o, pl) := call er_to_iw(EREC⦃cv + ⟪CV.lpsOff⟫⦄, EREC⦃cv + ⟪CV.lpsLen⟫⦄);
  return (o, pl)
}

/-- `block_shape_ctors_copy(off, q, k)`: copy the ctor slice of the member at `off` to `IW[q + k ..]`;
returns its length. -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:153-156 ConRon.Arena.BlockShape.allCtors
@[no_expose, l_impl ConRon.Arena.BlockShape.allCtors]
def blockShapeCtorsCopy : FunDecl := lfn (off, q, k) locals (m, co, cl, u) {
  m := IW.u64[off];
  co := IW.u64[m + 2];
  cl := IW.u64[m + 3];
  u := call iw_copy(q + k, co, cl);
  return cl
}

/-- `block_shape_all_ctors_go(off, l, q, k)`: copy the ctor slices of the `l` members at `off` to
`IW[q + k ..]`, one after the other (recursive on the members). -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:153-156 ConRon.Arena.BlockShape.allCtors
@[no_expose, l_impl ConRon.Arena.BlockShape.allCtors]
def blockShapeAllCtorsGo : FunDecl := lfn (off, l, q, k) locals (cl, r) {
  if l == 0 { return 0 };
  cl := call block_shape_ctors_copy(off, q, k);
  r := call block_shape_all_ctors_go(off + 1, l - 1, q, k + cl);
  return 0
}

/-- `block_shape_all_ctors(p)`: `BlockShape.allCtors`, every member's `ctors` list concatenated,
in block order. -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:153-156 ConRon.Arena.BlockShape.allCtors
@[no_expose, l_impl ConRon.Arena.BlockShape.allCtors]
def blockShapeAllCtors : FunDecl := lfn (p) locals (off, l, tot, q, u) {
  off := IW.u64[p];
  l := IW.u64[p + 1];
  tot := call num_ctors_of(off, l);
  q := call iw_alloc(tot);
  u := call block_shape_all_ctors_go(off, l, q, 0);
  return (q, tot)
}

/-- `block_shape_rule_prefix_at(p, r)`: `BlockShape.rulePrefixAt`, recursor `r`'s `rP` (word `+1`
of its record), `0` past the recursor list. -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:158-164 ConRon.Arena.BlockShape.rulePrefixAt
@[no_expose, l_impl ConRon.Arena.BlockShape.rulePrefixAt]
def blockShapeRulePrefixAt : FunDecl := lfn (p, r) locals (off, l, rc) {
  off := IW.u64[p + 2];
  l := IW.u64[p + 3];
  if l <= r { return 0 };
  rc := IW.u64[off + r];
  return IW.u64[rc + 1]
}

/-- `block_shape_major_idx_at(p, r)`: `BlockShape.majorIdxAt`, recursor `r`'s `mI` (word `+2`),
`0` past the recursor list. -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:166-171 ConRon.Arena.BlockShape.majorIdxAt
@[no_expose, l_impl ConRon.Arena.BlockShape.majorIdxAt]
def blockShapeMajorIdxAt : FunDecl := lfn (p, r) locals (off, l, rc) {
  off := IW.u64[p + 2];
  l := IW.u64[p + 3];
  if l <= r { return 0 };
  rc := IW.u64[off + r];
  return IW.u64[rc + 2]
}

/-- `block_shape_with_sort(p, s)`: `BlockShape.withSort`, a fresh record (values are immutable once
built) with `resSort := s` and `isProp` recomputed (`lvlEq? s zeroLevel`). -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:173-183 ConRon.Arena.BlockShape.withSort
@[no_expose, l_impl ConRon.Arena.BlockShape.withSort]
def blockShapeWithSort : FunDecl := lfn (p, s) locals (z, eq, isProp, q) {
  z := call pin_word(53);
  eq := call lvl_eq_c(s, z);
  isProp := u64(eq == 2);
  q := call iw_alloc(9);
  IW.u64[q] := IW.u64[p];
  IW.u64[q + 1] := IW.u64[p + 1];
  IW.u64[q + 2] := IW.u64[p + 2];
  IW.u64[q + 3] := IW.u64[p + 3];
  IW.u64[q + 4] := IW.u64[p + 4];
  IW.u64[q + 5] := IW.u64[p + 5];
  IW.u64[q + 6] := s;
  IW.u64[q + 7] := IW.u64[p + 7];
  IW.u64[q + 8] := isProp;
  return q
}

/-- `block_shape_with_members(p, ms.off, ms.len)`: `{ p with members := ms }`, a fresh 9-word
record (`checkBlock`'s record update after `reduceMembers`). -/
-- con-ron: ConRon/Arena/Inductives/BlockTail.lean:187-217 ConRon.Arena.checkBlock
@[no_expose, l_impl ConRon.Arena.checkBlock]
def blockShapeWithMembers : FunDecl := lfn (p, mo, ml) locals (q) {
  q := call iw_alloc(9);
  IW.u64[q] := mo;
  IW.u64[q + 1] := ml;
  IW.u64[q + 2] := IW.u64[p + 2];
  IW.u64[q + 3] := IW.u64[p + 3];
  IW.u64[q + 4] := IW.u64[p + 4];
  IW.u64[q + 5] := IW.u64[p + 5];
  IW.u64[q + 6] := IW.u64[p + 6];
  IW.u64[q + 7] := IW.u64[p + 7];
  IW.u64[q + 8] := IW.u64[p + 8];
  return q
}

/-- `block_shape_formers(p)`: `p.members.map (·.cvT)`, the members' formers at their telescopes,
a fresh `IW` slice of `EREC` pointers. -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:108-110 ConRon.Arena.BlockShape.formers
@[no_expose, l_impl ConRon.Arena.BlockShape.formers]
def blockShapeFormers : FunDecl := lfn (p) locals (q, u) {
  q := call iw_alloc(IW.u64[p + 1]);
  u := call member_field_copy(q, IW.u64[p], IW.u64[p + 1], 0);
  return (q, IW.u64[p + 1])
}

/-- `block_shape_declared(p)`: `p.members.map (·.declared)`, the members' formers as declared, a
fresh `IW` slice of `EREC` pointers. -/
-- con-ron: ConRon/Arena/Inductives/BlockInstall.lean:185-201 ConRon.Arena.checkBlockInds
@[no_expose, l_impl ConRon.Arena.checkBlockInds]
def blockShapeDeclared : FunDecl := lfn (p) locals (q, u) {
  q := call iw_alloc(IW.u64[p + 1]);
  u := call member_field_copy(q, IW.u64[p], IW.u64[p + 1], 4);
  return (q, IW.u64[p + 1])
}

/-- `member_field_copy(d, s, l, k)`: `IW[d + j] := IW[IW[s + j] + k]` for `j < l` (word `k` of
each member record), recursively. -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:108-110 ConRon.Arena.BlockShape.formers
@[no_expose, l_impl ConRon.Arena.BlockShape.formers]
def memberFieldCopy : FunDecl := lfn (d, s, l, k) locals (u) {
  if l == 0 { return 0 };
  IW.u64[d] := IW.u64[IW.u64[s] + k];
  u := call member_field_copy(d + 1, s + 1, l - 1, k);
  return 0
}

/-- `block_shape_member_ctors(p)`: `p.members.map (·.ctors)`, a fresh `IW` slice of pointers to
the members' `[ctors.off, ctors.len]` headers (word `2` of each member record: no copy of the
lists). -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:112-115 ConRon.Arena.BlockShape.memberCtors
@[no_expose, l_impl ConRon.Arena.BlockShape.memberCtors]
def blockShapeMemberCtors : FunDecl := lfn (p) locals (q, u) {
  q := call iw_alloc(IW.u64[p + 1]);
  u := call member_ctors_copy(q, IW.u64[p], IW.u64[p + 1]);
  return (q, IW.u64[p + 1])
}

/-- `member_ctors_copy(d, s, l)`: `IW[d + j] := IW[s + j] + 2` for `j < l`, recursively. -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:112-115 ConRon.Arena.BlockShape.memberCtors
@[no_expose, l_impl ConRon.Arena.BlockShape.memberCtors]
def memberCtorsCopy : FunDecl := lfn (d, s, l) locals (u) {
  if l == 0 { return 0 };
  IW.u64[d] := IW.u64[s] + 2;
  u := call member_ctors_copy(d + 1, s + 1, l - 1);
  return 0
}

/-- `block_shape_ctor_groups(p)`: `p.ctorGroups`, the constructors grouped by member, each under its
member's name. No copy: the groups are the member records themselves (the members' `IW` slice),
each read as its `cvT`'s name (the `EREC` word at member word `0`) and its `[ctors.off,
ctors.len]` (member words `2`, `3`), as `nest_out_kinds` reads its outputs. -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:117-122 ConRon.Arena.BlockShape.ctorGroups
@[no_expose, l_impl ConRon.Arena.BlockShape.ctorGroups]
def blockShapeCtorGroups : FunDecl := lfn (p) locals () {
  return (IW.u64[p], IW.u64[p + 1])
}

/-! ## Recognition -/

/-- `block_split_recs(off, l)`: `blockSplitRecs` of the `off, l` slice of `EREC` constant-record
pointers: `(1, q, l)` if every element is `recInfo` (kind `5`), each folded into a fresh
`[cvR, mI, rP, rules.off, rules.len, isK]` record; `(0, …)` at the first that is not. Recursive as the
twin (the rest first, then `sl_cons`; lane `indproofs2`: was a loop). -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:187-196 ConRon.Arena.blockSplitRecs
@[no_expose, l_impl ConRon.Arena.blockSplitRecs]
def blockSplitRecs : FunDecl := lfn (off, l) locals (ci, ok, ro, rl, rc, o2, l2) {
  if l == 0 { return (1, 0, 0) };
  ci := EREC⦃off⦄;
  if EREC⦃ci⦄ != 5 { return (0, 0, 0) };
  (ok, ro, rl) := call block_split_recs(off + 1, l - 1);
  if ok == 0 { return (0, 0, 0) };
  rc := call rec6(ci + ⟪CI.cv⟫, EREC⦃ci + ⟪CI.recMajor⟫⦄, EREC⦃ci + ⟪CI.recPrefix⟫⦄, EREC⦃ci + ⟪CI.recRulesOff⟫⦄,
    EREC⦃ci + ⟪CI.recRulesLen⟫⦄, EREC⦃ci + ⟪CI.recIsK⟫⦄);
  (o2, l2) := call sl_cons(rc, ro, rl);
  return (1, o2, l2)
}

/-- `block_split_ctors(off, l)`: `blockSplitCtors`: the leading `ctorInfo` (kind `4`) elements, each
folded into `[cv, nP, nF]`, then `block_split_recs` on the rest (recursive as the twin). -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:198-210 ConRon.Arena.blockSplitCtors
@[no_expose, l_impl ConRon.Arena.blockSplitCtors]
def blockSplitCtors : FunDecl := lfn (off, l) locals (ci, ok, co, cl, ro, rl, c, o2, l2) {
  if l == 0 { return (1, 0, 0, 0, 0) };
  ci := EREC⦃off⦄;
  if EREC⦃ci⦄ != 4 {
    (ok, ro, rl) := call block_split_recs(off, l);
    if ok == 0 { return (0, 0, 0, 0, 0) };
    return (1, 0, 0, ro, rl)
  };
  (ok, co, cl, ro, rl) := call block_split_ctors(off + 1, l - 1);
  if ok == 0 { return (0, 0, 0, 0, 0) };
  c := call rec3(ci + ⟪CI.cv⟫, EREC⦃ci + ⟪CI.ctorNparams⟫⦄, EREC⦃ci + ⟪CI.ctorNfields⟫⦄);
  (o2, l2) := call sl_cons(c, co, cl);
  return (1, o2, l2, ro, rl)
}

/-- `block_split(off, l)`: `blockSplit`: the leading `indInfo` (kind `3`) elements (their `cv`
pointers), then `block_split_ctors` on the rest (recursive as the twin). The twin's 3-list result
is 7 words, past the 6-result cap, so `(ok, q)` with `q` a fresh `[cvTs.off, cvTs.len, cs.off,
cs.len, rs.off, rs.len]` record. -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:212-224 ConRon.Arena.blockSplit
@[no_expose, l_impl ConRon.Arena.blockSplit]
def blockSplit : FunDecl := lfn (off, l) locals (ci, ok, q, co, cl, ro, rl, fo, fl, q2) {
  if l == 0 { q := call rec6(0, 0, 0, 0, 0, 0); return (1, q) };
  ci := EREC⦃off⦄;
  if EREC⦃ci⦄ != 3 {
    (ok, co, cl, ro, rl) := call block_split_ctors(off, l);
    if ok == 0 { return (0, 0) };
    q := call rec6(0, 0, co, cl, ro, rl);
    return (1, q)
  };
  (ok, q) := call block_split(off + 1, l - 1);
  if ok == 0 { return (0, 0) };
  (fo, fl) := call sl_cons(ci + ⟪CI.cv⟫, IW.u64[q], IW.u64[q + 1]);
  q2 := call rec6(fo, fl, IW.u64[q + 2], IW.u64[q + 3], IW.u64[q + 4], IW.u64[q + 5]);
  return (1, q2)
}

/-- `rec_target_of(no, nl, mI, ty)`: `recTargetOf`: strip `mI` leading `∀`s off `ty`; if the
remainder is itself a `∀` (pure tag test) whose domain's head is a `const` naming one of `no, nl`,
that member's index; else `no, nl`'s length (`names.length`, the twin's `none'`). -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:226-248 ConRon.Arena.recTargetOf
@[no_expose, l_impl ConRon.Arena.recTargetOf]
def recTargetOf : FunDecl := lfn (no, nl, mI, ty) locals (ok, bo, bl, body, g, x, y, z, hd, fnd, idx) {
  (ok, bo, bl, body) := call strip_pis(mI, ty);
  if ok == 0 { return nl };
  if ⟦body⟧.tag != 6 { return nl };
  (g, x, y, z) := call e_view(body);
  hd := call get_app_fn_f(⟪CWF⟫, x);
  if ⟦hd⟧.tag != 3 { return nl };
  (g, x, y, z) := call e_view(hd);
  (fnd, idx) := call sl_find(no, nl, x);
  if fnd == 0 { return nl };
  return idx
}

/-- `block_counts_pure(nPd, k, nC, nR, bl, g, rOk, rMI, rRP)`: the arithmetic tail of `blockCounts`
(from the binder count `bl` and the result's view tag `g`), as `(e, a, b)`: `e` the reason of the
cited `.error` (`0` at `.ok (a, b)`). -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:256-279 ConRon.Arena.blockCounts
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:250-254 ConRon.Arena.recCountsError
@[no_expose, l_impl ConRon.Arena.blockCounts ConRon.Arena.recCountsError]
def blockCountsPure : FunDecl := lfn (nPd, k, nC, nR, bl, g, rOk, rMI, rRP) locals () {
  if g == 2 {
    if bl < nPd { return (⟪R_INDUCTIVE_TYPE_DECLARES⟫, 0, 0) };
    return (0, nPd, bl - nPd)
  };
  if rOk == 0 { return (⟪R_NO_RECURSOR_OF⟫, 0, 0) };
  if rRP < nC + k || rMI < rRP { return (⟪R_THE_ARGUMENT_COUNTS⟫, 0, 0) };
  if rRP - (nC + k) == nPd { return (0, nPd, rMI - rRP) };
  if k < nR && nPd + nR + nC <= rRP { return (0, nPd, rMI - rRP) };
  return (⟪R_THE_ARGUMENT_COUNTS⟫, 0, 0)
}

/-- `block_counts_head(cvT)`: the binder count of the former's type and the tag of its result
(`piBinders`, then `view`). -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:256-279 ConRon.Arena.blockCounts
@[no_expose, l_impl ConRon.Arena.blockCounts]
def blockCountsHead : FunDecl := lfn (cvT) locals (ty, bo, bl, res, g, x, y, z) {
  ty := EREC⦃cvT + ⟪CV.type⟫⦄;
  (bo, bl, res) := call pi_binders(⟪CWF⟫, ty);
  (g, x, y, z) := call e_view(res);
  return (bl, g)
}

/-- `block_counts(nPd, k, nC, nR, cvT, rOk, rMI, rRP)`: `blockCounts`, as `(e, a, b)` (`e` the
error's reason, `0` at `.ok (a, b)`). `r : Option (Nat × Nat)` (`rOk, rMI, rRP`) is a bare argument,
not nested in a list or record, so it is flattened rather than boxed (by analogy with the result
convention). -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:256-279 ConRon.Arena.blockCounts
@[no_expose, l_impl ConRon.Arena.blockCounts]
def blockCounts : FunDecl := lfn (nPd, k, nC, nR, cvT, rOk, rMI, rRP) locals (bl, g, a, b, c) {
  (bl, g) := call block_counts_head(cvT);
  (a, b, c) := call block_counts_pure(nPd, k, nC, nR, bl, g, rOk, rMI, rRP);
  return (a, b, c)
}

/-- `ctor_member(no, nl, lvls, nP, c)`: `ctorMember?`, `c` a `[cv, nF]` pointer: strip `nP + nF`
leading `∀`s off `c.type`, then `member_idx_at` the head of what remains. -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:281-290 ConRon.Arena.ctorMember?
@[no_expose, l_impl ConRon.Arena.ctorMember?]
def ctorMember : FunDecl := lfn (no, nl, lvls, nP, c) locals (nF, ty, ok, bo, bl, body, hd, rok, ri) {
  nF := IW.u64[c + 1];
  if nP + nF < nP { abort };
  ty := EREC⦃IW.u64[c] + ⟪CV.type⟫⦄;
  (ok, bo, bl, body) := call strip_pis(nP + nF, ty);
  if ok == 0 { return (0, 0) };
  hd := call get_app_fn_f(⟪CWF⟫, body);
  (rok, ri) := call member_idx_at(no, nl, lvls, hd);
  return (rok, ri)
}

/-- `block_groups_one(no, nl, lvls, nP, co, cl, m)`: one group of `blockGroups`'s general case,
member `m`'s constructors: `cs.filterM` (`ctor_member` called once per candidate, in list order,
then the rest; recursive, lane `indproofs2`: was a loop). -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:292-306 ConRon.Arena.blockGroups
@[no_expose, l_impl ConRon.Arena.blockGroups]
def blockGroupsOne : FunDecl := lfn (no, nl, lvls, nP, co, cl, m) locals (c, ok, t, go, gl) {
  if cl == 0 { return (0, 0) };
  c := IW.u64[co];
  (ok, t) := call ctor_member(no, nl, lvls, nP, c);
  (go, gl) := call block_groups_one(no, nl, lvls, nP, co + 1, cl - 1, m);
  if ok != 0 && t == m { (go, gl) := call sl_cons(c, go, gl) };
  return (go, gl)
}

/-- `block_groups_go(no, nl, lvls, nP, co, cl, m, k)`: the groups of members `m, …, k - 1`
(`(List.range' m (k - m)).mapM`, in order: this member's group, then the rest). -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:292-306 ConRon.Arena.blockGroups
@[no_expose, l_impl ConRon.Arena.blockGroups]
def blockGroupsGo : FunDecl := lfn (no, nl, lvls, nP, co, cl, m, k) locals (go, gl, h0, ho, hl) {
  if k <= m { return (0, 0) };
  (go, gl) := call block_groups_one(no, nl, lvls, nP, co, cl, m);
  h0 := call rec2(go, gl);
  (ho, hl) := call block_groups_go(no, nl, lvls, nP, co, cl, m + 1, k);
  (ho, hl) := call sl_cons(h0, ho, hl);
  return (ho, hl)
}

/-- `block_groups(no, nl, lvls, nP, k, co, cl)`: `blockGroups`: at one member, `[cs]` with no
calls at all (the twin's short circuit); else one `block_groups_one` per member `0, …, k - 1`. -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:292-306 ConRon.Arena.blockGroups
@[no_expose, l_impl ConRon.Arena.blockGroups]
def blockGroups : FunDecl := lfn (no, nl, lvls, nP, k, co, cl) locals (h0, hdrs, hl) {
  if k == 1 {
    h0 := call rec2(co, cl);
    (hdrs, hl) := call sl_cons(h0, 0, 0);
    return (hdrs, hl)
  };
  (hdrs, hl) := call block_groups_go(no, nl, lvls, nP, co, cl, 0, k);
  return (hdrs, hl)
}

/-- `block_rec_lps_one(rc, wo, wl)`: whether recursor record `rc`'s `cvR.levelParams` equal the
wanted `(wo, wl)` (`1`/`0`). -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:308-316 ConRon.Arena.blockRecLpsOk
@[no_expose, l_impl ConRon.Arena.blockRecLpsOk]
def blockRecLpsOne : FunDecl := lfn (rc, wo, wl) locals (cv, rpo, rpl, eqv) {
  cv := IW.u64[rc];
  (rpo, rpl) := call er_to_iw(EREC⦃cv + ⟪CV.lpsOff⟫⦄, EREC⦃cv + ⟪CV.lpsLen⟫⦄);
  eqv := call sl_eq(rpo, rpl, wo, wl);
  return eqv
}

/-- `block_rec_lps_ok_go(ro, rl, wo, wl)`: every one of the `rl` recursor records at `ro` has the
wanted level parameters `(wo, wl)` (recursive on the slice, stopping at the first mismatch). -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:308-316 ConRon.Arena.blockRecLpsOk
@[no_expose, l_impl ConRon.Arena.blockRecLpsOk]
def blockRecLpsOkGo : FunDecl := lfn (ro, rl, wo, wl) locals (eqv, r) {
  if rl == 0 { return 1 };
  eqv := call block_rec_lps_one(IW.u64[ro], wo, wl);
  if eqv == 0 { return 0 };
  r := call block_rec_lps_ok_go(ro + 1, rl - 1, wo, wl);
  return r
}

/-- `block_rec_lps_ok(p)`: `blockRecLpsOk`: every recursor's `cvR.levelParams` equals `elim :: lps`
(`large`) or `lps` (pure, so an early `return 0` is fine). -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:308-316 ConRon.Arena.blockRecLpsOk
@[no_expose, l_impl ConRon.Arena.blockRecLpsOk]
def blockRecLpsOk : FunDecl := lfn (p) locals (lo, ll, wo, wl, large, elim, ro, rl, r) {
  (lo, ll) := call block_shape_lps(p);
  large := IW.u64[p + 7];
  elim := IW.u64[p + 5];
  if large != 0 { (wo, wl) := call sl_cons(elim, lo, ll) } else { wo := lo; wl := ll };
  ro := IW.u64[p + 2];
  rl := IW.u64[p + 3];
  r := call block_rec_lps_ok_go(ro, rl, wo, wl);
  return r
}

/-- `block_rec_want(mo, ml)`: `T_m.rec` at every member (`name_rec`, interned in block order: this
member's, then the rest's; consed on with `sl_cons`). -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:318-326 ConRon.Arena.blockRecNameSetOk
@[no_expose, l_impl ConRon.Arena.blockRecNameSetOk]
def blockRecWant : FunDecl := lfn (mo, ml) locals (m, cv, w, o, l) {
  if ml == 0 { return (0, 0) };
  m := IW.u64[mo];
  cv := IW.u64[m];
  w := call name_rec(EREC⦃cv⦄);
  (o, l) := call block_rec_want(mo + 1, ml - 1);
  (o, l) := call sl_cons(w, o, l);
  return (o, l)
}

/-- `block_rec_got(ro, rl)`: the recursors' names (`recs.map (·.cvR.name)`), recursively. -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:318-326 ConRon.Arena.blockRecNameSetOk
@[no_expose, l_impl ConRon.Arena.blockRecNameSetOk]
def blockRecGot : FunDecl := lfn (ro, rl) locals (rc, o, l) {
  if rl == 0 { return (0, 0) };
  rc := IW.u64[ro];
  (o, l) := call block_rec_got(ro + 1, rl - 1);
  (o, l) := call sl_cons(EREC⦃IW.u64[rc]⦄, o, l);
  return (o, l)
}

/-- `block_rec_name_set_ok(mo, ml, ro, rl)`: `blockRecNameSetOk`: the recursor names, as a set,
are exactly `T_m.rec` at every member (`sl_set_eq`; lane `indproofs2`: the loops became
`block_rec_want`/`block_rec_got`). -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:318-326 ConRon.Arena.blockRecNameSetOk
@[no_expose, l_impl ConRon.Arena.blockRecNameSetOk]
def blockRecNameSetOk : FunDecl := lfn (mo, ml, ro, rl) locals (wo, wl, go, gl, b) {
  (wo, wl) := call block_rec_want(mo, ml);
  (go, gl) := call block_rec_got(ro, rl);
  b := call sl_set_eq(go, gl, wo, wl);
  return b
}

/-- `block_rec_names_unreserved(ro, rl)`: `blockRecNamesUnreserved`, stopping at the first
recursor whose name is reserved (`reserved_rec_name`), as the twin's recursion does (recursive on
the slice: `ro + 1`, `rl - 1`). -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:328-336 ConRon.Arena.blockRecNamesUnreserved
@[no_expose, l_impl ConRon.Arena.blockRecNamesUnreserved]
def blockRecNamesUnreserved : FunDecl := lfn (ro, rl) locals (rc, cv, nm, b, r) {
  if rl == 0 { return 1 };
  rc := IW.u64[ro];
  cv := IW.u64[rc];
  nm := EREC⦃cv⦄;
  b := call reserved_rec_name(nm);
  if b != 0 { return 0 };
  r := call block_rec_names_unreserved(ro + 1, rl - 1);
  return r
}

/-- `block_member_counts_find(no, nl, ro, rl, m)`: the `rs.findM?` inside `blockMemberCounts`,
one `rec_target_of` call per candidate, stopping at the first whose target is `m` (recursive,
lane `indproofs2`: was a loop). -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:338-357 ConRon.Arena.blockMemberCounts
@[no_expose, l_impl ConRon.Arena.blockMemberCounts]
def blockMemberCountsFind : FunDecl := lfn (no, nl, ro, rl, m) locals (e, mI, t, a, b, c) {
  if rl == 0 { return (0, 0, 0) };
  e := IW.u64[ro];
  mI := IW.u64[e + 1];
  t := call rec_target_of(no, nl, mI, EREC⦃IW.u64[e] + ⟪CV.type⟫⦄);
  if t == m { return (1, mI, IW.u64[e + 2]) };
  (a, b, c) := call block_member_counts_find(no, nl, ro + 1, rl - 1, m);
  return (a, b, c)
}

/-- `block_member_counts_go(nPd, k, nC, no, nl, ro, rl, cto, ctl, idx)`: `blockMemberCounts` from
member `idx` on, as `(e, o, l)` (`e` the first failing member's reason, `0` at `.ok`): one
`block_member_counts_find` and one `block_counts` for this former, then the rest; an error stops
the walk there (no further calls). The record words past `2^32` are a capacity abort
(`block_counts`' arithmetic). -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:338-357 ConRon.Arena.blockMemberCounts
@[no_expose, l_impl ConRon.Arena.blockMemberCounts]
def blockMemberCountsGo : FunDecl := lfn (nPd, k, nC, no, nl, ro, rl, cto, ctl, idx)
    locals (cv, rok, rmi, rrp, ce, ca, cb, e, o, l) {
  if ctl == 0 { return (0, 0, 0) };
  cv := IW.u64[cto];
  (rok, rmi, rrp) := call block_member_counts_find(no, nl, ro, rl, idx);
  if 4294967296 <= rmi || 4294967296 <= rrp { abort };
  (ce, ca, cb) := call block_counts(nPd, k, nC, rl, cv, rok, rmi, rrp);
  if ce != 0 { return (ce, 0, 0) };
  (e, o, l) := call block_member_counts_go(nPd, k, nC, no, nl, ro, rl, cto + 1, ctl - 1, idx + 1);
  if e != 0 { return (e, 0, 0) };
  (o, l) := call sl_cons(cb, o, l);
  return (0, o, l)
}

/-- `block_member_counts(nPd, k, nC, no, nl, ro, rl, cto, ctl)`: `blockMemberCounts` from member
`0` (the counts past `2^32` a capacity abort). -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:338-357 ConRon.Arena.blockMemberCounts
@[no_expose, l_impl ConRon.Arena.blockMemberCounts]
def blockMemberCounts : FunDecl := lfn (nPd, k, nC, no, nl, ro, rl, cto, ctl) locals (e, o, l) {
  if 4294967296 <= nPd || 4294967296 <= k || 4294967296 <= nC || 4294967296 <= rl { abort };
  (e, o, l) := call block_member_counts_go(nPd, k, nC, no, nl, ro, rl, cto, ctl, 0);
  return (e, o, l)
}

/-! ### `readBlock`: one helper per stretch -/

/-- `block_shape_names_of(cto, ctl)`: the former `cv` pointers' names (`cvTs.map (·.name)`). -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:359-429 ConRon.Arena.readBlock
@[no_expose, l_impl ConRon.Arena.readBlock]
def blockShapeNamesOf : FunDecl := lfn (cto, ctl) locals (o, l) {
  if ctl == 0 { return (0, 0) };
  (o, l) := call block_shape_names_of(cto + 1, ctl - 1);
  (o, l) := call sl_cons(EREC⦃IW.u64[cto]⦄, o, l);
  return (o, l)
}

/-- `formers_lps_ok(cto, ctl, lo, ll)`: `cvTs.all fun c => c.levelParams == lps`. -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:359-429 ConRon.Arena.readBlock
@[no_expose, l_impl ConRon.Arena.readBlock]
def formersLpsOk : FunDecl := lfn (cto, ctl, lo, ll) locals (cv, plo, pll, eqv, r) {
  if ctl == 0 { return 1 };
  cv := IW.u64[cto];
  (plo, pll) := call er_to_iw(EREC⦃cv + ⟪CV.lpsOff⟫⦄, EREC⦃cv + ⟪CV.lpsLen⟫⦄);
  eqv := call sl_eq(plo, pll, lo, ll);
  if eqv == 0 { return 0 };
  r := call formers_lps_ok(cto + 1, ctl - 1, lo, ll);
  return r
}

/-- `ctors_params_ok(nP, cso, csl)`: `cs.all fun c => c.2.1 == nP`. -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:359-429 ConRon.Arena.readBlock
@[no_expose, l_impl ConRon.Arena.readBlock]
def ctorsParamsOk : FunDecl := lfn (nP, cso, csl) locals (r) {
  if csl == 0 { return 1 };
  if IW.u64[IW.u64[cso] + 1] != nP { return 0 };
  r := call ctors_params_ok(nP, cso + 1, csl - 1);
  return r
}

/-- `ctors_lps_ok(cso, csl, lo, ll)`: `cs.all fun c => c.1.levelParams == lps`. -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:359-429 ConRon.Arena.readBlock
@[no_expose, l_impl ConRon.Arena.readBlock]
def ctorsLpsOk : FunDecl := lfn (cso, csl, lo, ll) locals (cv, plo, pll, eqv, r) {
  if csl == 0 { return 1 };
  cv := IW.u64[IW.u64[cso]];
  (plo, pll) := call er_to_iw(EREC⦃cv + ⟪CV.lpsOff⟫⦄, EREC⦃cv + ⟪CV.lpsLen⟫⦄);
  eqv := call sl_eq(plo, pll, lo, ll);
  if eqv == 0 { return 0 };
  r := call ctors_lps_ok(cso + 1, csl - 1, lo, ll);
  return r
}

/-- The result sort: the sort at the end of `nP + nIdxs[0]` leading `∀`s off `cvT0.type`, else
`zeroLevel` (the install's whnf loop replaces the placeholder). -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:359-429 ConRon.Arena.readBlock
@[no_expose, l_impl ConRon.Arena.readBlock]
def blockShapeResultSort : FunDecl := lfn (nP, io, il, ty) locals (h0, ok, bo, bl, body, g, x, y, z, s) {
  h0 := call sl_getd(io, il, 0, 0);
  if nP + h0 < nP { abort };
  (ok, bo, bl, body) := call strip_pis(nP + h0, ty);
  if ok == 0 { s := call pin_word(53); return s };
  (g, x, y, z) := call e_view(body);
  if g == 2 { return x };
  s := call pin_word(53);
  return s
}

/-- `cs.map fun c => (c.1, c.2.2)`: the constructors, as `[cv, nF]` (dropping each's own `nP`). -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:359-429 ConRon.Arena.readBlock
@[no_expose, l_impl ConRon.Arena.readBlock]
def blockShapeCtorsOf : FunDecl := lfn (cso, csl) locals (c, o, l, e) {
  if csl == 0 { return (0, 0) };
  c := IW.u64[cso];
  (o, l) := call block_shape_ctors_of(cso + 1, csl - 1);
  e := call rec2(IW.u64[c], IW.u64[c + 2]);
  (o, l) := call sl_cons(e, o, l);
  return (o, l)
}

/-- The members: `((cvTs.zip nIdxs).zip groups).map`, each a fresh `[cvT, nIdx, ctors.off,
ctors.len, declared]` with `declared := cvT` (a group is a pointer to a `[off, len]` header; its
fields are inlined here). -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:359-429 ConRon.Arena.readBlock
@[no_expose, l_impl ConRon.Arena.readBlock]
def blockShapeMembersOf : FunDecl := lfn (cto, ctl, io, go) locals (o, l, hdr, ms) {
  if ctl == 0 { return (0, 0) };
  (o, l) := call block_shape_members_of(cto + 1, ctl - 1, io + 1, go + 1);
  hdr := IW.u64[go];
  ms := call rec5(IW.u64[cto], IW.u64[io], IW.u64[hdr], IW.u64[hdr + 1], IW.u64[cto]);
  (o, l) := call sl_cons(ms, o, l);
  return (o, l)
}

/-- The recursors: `rs.mapM` building a fresh `RecShape` (`[cvR, rP, mI, tgt, rules.off,
rules.len, isK]`, `decRS`'s order; the rules the record's `EREC` slice, not copied) per element,
`tgt` by `rec_target_of`. -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:359-429 ConRon.Arena.readBlock
@[no_expose, l_impl ConRon.Arena.readBlock]
def blockShapeRecsOf : FunDecl := lfn (no, nl, ro, rl) locals (e, tgt, rc, o, l) {
  if rl == 0 { return (0, 0) };
  e := IW.u64[ro];
  tgt := call rec_target_of(no, nl, IW.u64[e + 1], EREC⦃IW.u64[e] + ⟪CV.type⟫⦄);
  rc := call rec7(IW.u64[e], IW.u64[e + 2], IW.u64[e + 1], tgt, IW.u64[e + 3], IW.u64[e + 4],
    IW.u64[e + 5]);
  (o, l) := call block_shape_recs_of(no, nl, ro + 1, rl - 1);
  (o, l) := call sl_cons(rc, o, l);
  return (o, l)
}

/-- `cvR0.levelParams` as `elim :: relps` with `relps == lps` and `elim ∉ lps`: `(1, elim)`;
anything else (including no level parameters at all): `(0, 0)`. -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:359-429 ConRon.Arena.readBlock
@[no_expose, l_impl ConRon.Arena.readBlock]
def blockShapeLarge : FunDecl := lfn (cvR0, lo, ll) locals (off, cnt, elim, rlo, rll, eqv, has) {
  off := EREC⦃cvR0 + ⟪CV.lpsOff⟫⦄;
  cnt := EREC⦃cvR0 + ⟪CV.lpsLen⟫⦄;
  if cnt == 0 { return (0, 0) };
  elim := EREC⦃off⦄;
  (rlo, rll) := call er_to_iw(off + 1, cnt - 1);
  eqv := call sl_eq(rlo, rll, lo, ll);
  if eqv == 0 { return (0, 0) };
  has := call sl_contains(lo, ll, elim);
  if has != 0 { return (0, 0) };
  return (1, elim)
}

/-- The final 9-word `BlockShape` record. -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:359-429 ConRon.Arena.readBlock
@[no_expose, l_impl ConRon.Arena.readBlock]
def blockShapePack : FunDecl := lfn (mo, ml, ro, rl, nP, elim, s, large, isProp) locals (q) {
  q := call iw_alloc(9);
  IW.u64[q] := mo;
  IW.u64[q + 1] := ml;
  IW.u64[q + 2] := ro;
  IW.u64[q + 3] := rl;
  IW.u64[q + 4] := nP;
  IW.u64[q + 5] := elim;
  IW.u64[q + 6] := s;
  IW.u64[q + 7] := large;
  IW.u64[q + 8] := isProp;
  return q
}

/-- `block_shape_seal`: which eliminator, then the record (split off `read_block_at`). -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:359-429 ConRon.Arena.readBlock
@[no_expose, l_impl ConRon.Arena.readBlock]
def blockShapeSeal : FunDecl := lfn (mo, ml, ro2, rl2, nPd, s, isProp, largeOk, elim) locals (e, q) {
  if largeOk != 0 {
    q := call block_shape_pack(mo, ml, ro2, rl2, nPd, elim, s, 1, isProp);
    return (1, q)
  };
  e := call intern_nanon();
  q := call block_shape_pack(mo, ml, ro2, rl2, nPd, e, s, 0, isProp);
  return (1, q)
}

/-- `block_shape_fin`: `readBlock`'s last stretch — the constructors, the levels, the groups,
the members and recursors, which eliminator, the record (lane `indproofs2`: split off
`read_block_at`). -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:359-429 ConRon.Arena.readBlock
@[no_expose, l_impl ConRon.Arena.readBlock]
def blockShapeFin : FunDecl := lfn (nPd, cto, ctl, cso, csl, rso, rsl, no, nl, io, lo, ll, s, isProp)
    locals (cvR0, cof, cl2, lvls, go, gl, mo, ml, ro2, rl2, largeOk, elim, ok, q) {
  cvR0 := IW.u64[IW.u64[rso]];
  (cof, cl2) := call block_shape_ctors_of(cso, csl);
  lvls := call param_levels(lo, ll);
  (go, gl) := call block_groups(no, nl, lvls, nPd, ctl, cof, cl2);
  (mo, ml) := call block_shape_members_of(cto, ctl, io, go);
  (ro2, rl2) := call block_shape_recs_of(no, nl, rso, rsl);
  (largeOk, elim) := call block_shape_large(cvR0, lo, ll);
  (ok, q) := call block_shape_seal(mo, ml, ro2, rl2, nPd, s, isProp, largeOk, elim);
  return (ok, q)
}

/-- `block_shape_tail`: the result sort and `isProp`, then `block_shape_fin` (split off
`read_block_at`). -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:359-429 ConRon.Arena.readBlock
@[no_expose, l_impl ConRon.Arena.readBlock]
def blockShapeTail : FunDecl := lfn (nPd, cto, ctl, cso, csl, rso, rsl, no, nl, io, il, lo, ll)
    locals (s, z, eq, isProp, ok, q) {
  s := call block_shape_result_sort(nPd, io, il, EREC⦃IW.u64[cto] + ⟪CV.type⟫⦄);
  z := call pin_word(53);
  eq := call lvl_eq_c(s, z);
  isProp := u64(eq == 2);
  (ok, q) := call block_shape_fin(nPd, cto, ctl, cso, csl, rso, rsl, no, nl, io, lo, ll, s, isProp);
  return (ok, q)
}

/-- `read_block_at(nPd, cto, ctl, cso, csl, rso, rsl)`: `readBlock` from its split, non-empty
components, as `(e, q)` (`e` the reason of the cited `.error`, `0` at `.ok q`): the names, the
counts, the universe and parameter declarations (the formers' level parameters, the constructors'
parameter counts, the constructors' level parameters; each cited `all`, its failure's reason),
then `block_shape_tail` (the Rust's `read_block_at`, from the counts on). -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:359-429 ConRon.Arena.readBlock
@[no_expose, l_impl ConRon.Arena.readBlock]
def readBlockAt : FunDecl := lfn (nPd, cto, ctl, cso, csl, rso, rsl)
    locals (cvT0, no, nl, e, io, il, lo, ll, b, ok, q) {
  cvT0 := IW.u64[cto];
  (no, nl) := call block_shape_names_of(cto, ctl);
  (e, io, il) := call block_member_counts(nPd, ctl, csl, no, nl, rso, rsl, cto, ctl);
  if e != 0 { return (e, 0) };
  (lo, ll) := call er_to_iw(EREC⦃cvT0 + ⟪CV.lpsOff⟫⦄, EREC⦃cvT0 + ⟪CV.lpsLen⟫⦄);
  b := call formers_lps_ok(cto, ctl, lo, ll);
  if b == 0 { return (⟪R_INDUCTIVE_TYPE_DECLARES_OTHER⟫, 0) };
  b := call ctors_params_ok(nPd, cso, csl);
  if b == 0 { return (⟪R_CONSTRUCTOR_DECLARES_ANOTHER⟫, 0) };
  b := call ctors_lps_ok(cso, csl, lo, ll);
  if b == 0 {
    if ctl == 1 { return (⟪R_CONSTRUCTOR_DECLARES_OTHER⟫, 0) };
    return (⟪R_CONSTRUCTOR_DECLARES_OTHER_UNIVERSE⟫, 0)
  };
  (ok, q) := call block_shape_tail(nPd, cto, ctl, cso, csl, rso, rsl, no, nl, io, il, lo, ll);
  return (0, q)
}

/-- `read_block(nPd, off, l)`: `readBlock`, as `(e, q)` (`e` the reason of the cited `.error`, `0`
at `.ok q`): split the block; its records out of order, no formers, or no recursors (the twin's
`cvT0 :: _, (cvR0, _, _, _) :: _` match) are the three structural reasons; else `read_block_at`. -/
-- con-ron: ConRon/Arena/Inductives/BlockShape.lean:359-429 ConRon.Arena.readBlock
@[no_expose, l_impl ConRon.Arena.readBlock]
def readBlock : FunDecl := lfn (nPd, off, l) locals (ok, q, cto, ctl, cso, csl, rso, rsl, e, r) {
  (ok, q) := call block_split(off, l);
  if ok == 0 { return (⟪R_INDUCTIVE_BLOCK_ITS⟫, 0) };
  cto := IW.u64[q];
  ctl := IW.u64[q + 1];
  cso := IW.u64[q + 2];
  csl := IW.u64[q + 3];
  rso := IW.u64[q + 4];
  rsl := IW.u64[q + 5];
  if ctl == 0 { return (⟪R_INDUCTIVE_BLOCK_DECLARES⟫, 0) };
  if rsl == 0 { return (⟪R_INDUCTIVE_BLOCK_CARRIES⟫, 0) };
  (e, r) := call read_block_at(nPd, cto, ctl, cso, csl, rso, rsl);
  return (e, r)
}

/-! ## `BlockRec.blockLargeElimAllowed` -/

/-- `block_large_elim_allowed(p, nested)`: always at a never-zero result sort
(`Level.isNeverZero`, `lv_nz`); never when nested; else one member, at most one constructor, and
the large shape. -/
-- con-ron: ConRon/Arena/Inductives/BlockRec.lean:25-35 ConRon.Arena.blockLargeElimAllowed
@[no_expose, l_impl ConRon.Arena.blockLargeElimAllowed]
def blockLargeElimAllowed : FunDecl := lfn (p, nested) locals (nz, n, large, k) {
  nz := call lv_nz(IW.u64[p + 6]);
  if nz != 0 { return 1 };
  if nested != 0 { return 0 };
  n := call block_shape_num_ctors(p);
  large := IW.u64[p + 7];
  k := IW.u64[p + 1];
  if large == 0 { return 0 };
  if k != 1 { return 0 };
  if n == 0 { return 1 };
  if n == 1 { return 1 };
  return 0
}

/-! ## `CheckDecl`: the `.indDecl` arm -/

/-- `check_ind_decl(vis, boff, blen, nP)`: the `.indDecl block nP` arm of `checkDeclKind`
(`@[l_impl ConRon.Arena.checkDeclKind]`, one arm of it): the declared parameter count
(`ind_params_ok`), then the one route (`read_block`, `check_block`), or the reader's reason. -/
-- con-ron: ConRon/Arena/CheckDecl.lean:74-158 ConRon.Arena.checkDeclKind
-- con-ron: CHANGED since de06320f — below `ConRon.Arena.checkDeclKind`, `ConRon.Arena.blockReadsAt` changed; re-check the L code and its proofs, then delete this line
-- con-ron: CHANGED since de06320f — `ConRon.Arena.checkDeclKind` changed; re-check the L code and its proofs, then delete this line
@[no_expose, l_impl ConRon.Arena.checkDeclKind]
def checkIndDecl : FunDecl := lfn (vis, boff, blen, nP) locals (pOk, e, pNew, reads, vis0, vis2) {
  pOk := call ind_params_ok(nP, boff, blen);
  if pOk == 0 { fail R_NUMBER_OF_PARAMETERS };
  (e, pNew) := call read_block(nP, boff, blen);
  -- the twin's `fail e`: the reject at the reader's reason `e`
  if e != 0 {
    if e == ⟪R_INDUCTIVE_TYPE_DECLARES⟫ { fail R_INDUCTIVE_TYPE_DECLARES };
    if e == ⟪R_NO_RECURSOR_OF⟫ { fail R_NO_RECURSOR_OF };
    if e == ⟪R_THE_ARGUMENT_COUNTS⟫ { fail R_THE_ARGUMENT_COUNTS };
    if e == ⟪R_INDUCTIVE_TYPE_DECLARES_OTHER⟫ { fail R_INDUCTIVE_TYPE_DECLARES_OTHER };
    if e == ⟪R_CONSTRUCTOR_DECLARES_ANOTHER⟫ { fail R_CONSTRUCTOR_DECLARES_ANOTHER };
    if e == ⟪R_CONSTRUCTOR_DECLARES_OTHER⟫ { fail R_CONSTRUCTOR_DECLARES_OTHER };
    if e == ⟪R_CONSTRUCTOR_DECLARES_OTHER_UNIVERSE⟫ { fail R_CONSTRUCTOR_DECLARES_OTHER_UNIVERSE };
    if e == ⟪R_INDUCTIVE_BLOCK_ITS⟫ { fail R_INDUCTIVE_BLOCK_ITS };
    if e == ⟪R_INDUCTIVE_BLOCK_DECLARES⟫ { fail R_INDUCTIVE_BLOCK_DECLARES };
    if e == ⟪R_INDUCTIVE_BLOCK_CARRIES⟫ { fail R_INDUCTIVE_BLOCK_CARRIES };
    abort
  };
  -- the ι reading rule before the block's check, its verdict after it
  (reads, vis0) := call block_reads_at(vis, pNew);
  vis2 := call check_block(vis0, boff, blen, pNew);
  if reads == 0 { fail R_THE_RECURSOR_S_MINOR };
  return vis2
}

/-! ## The module's program -/

/-- This module's functions. -/
def indPartsFns : Prog :=
  [("pi_binders", piBinders), ("num_ctors_of", numCtorsOf), ("block_shape_k", blockShapeK),
   ("block_shape_num_ctors", blockShapeNumCtors), ("block_shape_member_names", blockShapeMemberNames),
   ("member_names_copy", memberNamesCopy),
   ("block_shape_n_idxs", blockShapeNIdxs), ("n_idxs_copy", nIdxsCopy), ("block_shape_lps", blockShapeLps),
   ("block_shape_ctors_copy", blockShapeCtorsCopy), ("block_shape_all_ctors_go", blockShapeAllCtorsGo), ("block_shape_all_ctors", blockShapeAllCtors), ("block_shape_rule_prefix_at", blockShapeRulePrefixAt),
   ("block_shape_major_idx_at", blockShapeMajorIdxAt), ("block_shape_with_sort", blockShapeWithSort),
   ("block_shape_with_members", blockShapeWithMembers), ("block_shape_formers", blockShapeFormers),
   ("block_shape_declared", blockShapeDeclared), ("member_field_copy", memberFieldCopy),
   ("block_shape_member_ctors", blockShapeMemberCtors), ("member_ctors_copy", memberCtorsCopy),
   ("block_shape_ctor_groups", blockShapeCtorGroups),
   ("block_split_recs", blockSplitRecs),
   ("block_split_ctors", blockSplitCtors), ("block_split", blockSplit), ("rec_target_of", recTargetOf),
   ("block_counts_head", blockCountsHead), ("block_counts_pure", blockCountsPure), ("block_counts", blockCounts), ("ctor_member", ctorMember), ("block_groups_one", blockGroupsOne), ("block_groups_go", blockGroupsGo),
   ("block_groups", blockGroups), ("block_rec_lps_one", blockRecLpsOne), ("block_rec_lps_ok_go", blockRecLpsOkGo), ("block_rec_lps_ok", blockRecLpsOk),
   ("block_rec_want", blockRecWant), ("block_rec_got", blockRecGot), ("block_rec_name_set_ok", blockRecNameSetOk), ("block_rec_names_unreserved", blockRecNamesUnreserved),
   ("block_member_counts_find", blockMemberCountsFind), ("block_member_counts_go", blockMemberCountsGo), ("block_member_counts", blockMemberCounts),
   ("block_shape_names_of", blockShapeNamesOf), ("formers_lps_ok", formersLpsOk),
   ("ctors_params_ok", ctorsParamsOk), ("ctors_lps_ok", ctorsLpsOk),
   ("block_shape_result_sort", blockShapeResultSort),
   ("block_shape_ctors_of", blockShapeCtorsOf), ("block_shape_members_of", blockShapeMembersOf),
   ("block_shape_recs_of", blockShapeRecsOf),
   ("block_shape_large", blockShapeLarge), ("block_shape_pack", blockShapePack),
   ("block_shape_seal", blockShapeSeal), ("block_shape_fin", blockShapeFin), ("block_shape_tail", blockShapeTail), ("read_block_at", readBlockAt), ("read_block", readBlock),
   ("block_large_elim_allowed", blockLargeElimAllowed),
   ("check_ind_decl", checkIndDecl)]

/-- Stubs for the functions of OTHER modules this module calls. -/
def indPartsForeign : Prog :=
  [("member_idx_at", stub 4), ("param_levels", stub 2), ("check_block", stub 4),
   ("block_reads_at", stub 2)]

/-! ## A few runnable tests (no stub on their path) -/

-- `pi_binders` off a non-`forallE` handle (tag `0`, `bvar`): `([], h)`, no calls into the arena.
#guard
  match run (indPartsFns ++ libFns ++ stubFns ++ masterFns ++ indPartsForeign) 100
    "pi_binders" [1, 0] testMem with
  | .ok ([_, 0, 0], _) => true
  | _ => false

-- `num_ctors_of` of two members with `2` and `0` constructors: `2`.
#guard
  let m1 := (testMem.set64 IW 0 7).set64 IW 1 2 |>.set64 IW 2 70 |>.set64 IW 3 0
  let m2 : L.Mem := (m1.set64 IW 10 0) |>.set64 IW 11 0 |>.set64 IW 12 80 |>.set64 IW 13 2
  let m3 : L.Mem := (m2.set64 IW 20 0) |>.set64 IW 21 10
  match run (indPartsFns ++ libFns ++ stubFns ++ masterFns ++ indPartsForeign) 100
    "num_ctors_of" [20, 2] m3 with
  | .ok ([2], _) => true
  | _ => false

-- `block_shape_k`/`block_shape_num_ctors` off a record whose `members` slice is the one above.
#guard
  let m1 := (testMem.set64 IW 0 7).set64 IW 1 2 |>.set64 IW 2 70 |>.set64 IW 3 0
  let m2 : L.Mem := (m1.set64 IW 10 0) |>.set64 IW 11 0 |>.set64 IW 12 80 |>.set64 IW 13 2
  let m3 : L.Mem := (m2.set64 IW 20 0) |>.set64 IW 21 10
  let m4 : L.Mem := m3.set64 IW 22 20 |>.set64 IW 23 2 |>.set64 IW 24 0 |>.set64 IW 25 0
    |>.set64 IW 26 0 |>.set64 IW 27 0 |>.set64 IW 28 0 |>.set64 IW 29 0 |>.set64 IW 30 0
  match run (indPartsFns ++ libFns ++ stubFns ++ masterFns ++ indPartsForeign) 100
    "block_shape_k" [22] m4 with
  | .ok ([2], _) =>
    (match run (indPartsFns ++ libFns ++ stubFns ++ masterFns ++ indPartsForeign) 100
      "block_shape_num_ctors" [22] m4 with
     | .ok ([2], _) => true
     | _ => false)
  | _ => false

-- `block_shape_rule_prefix_at`/`block_shape_major_idx_at` past the recursor list: `0`.
#guard
  let m1 := (testMem.set64 IW 0 7).set64 IW 1 2 |>.set64 IW 2 70 |>.set64 IW 3 0
  let m2 : L.Mem := (m1.set64 IW 10 0) |>.set64 IW 11 0 |>.set64 IW 12 80 |>.set64 IW 13 2
  let m3 : L.Mem := (m2.set64 IW 20 0) |>.set64 IW 21 10
  let m4 : L.Mem := m3.set64 IW 22 0 |>.set64 IW 23 0 |>.set64 IW 24 0 |>.set64 IW 25 0
    |>.set64 IW 26 0 |>.set64 IW 27 0 |>.set64 IW 28 0
  match run (indPartsFns ++ libFns ++ stubFns ++ masterFns ++ indPartsForeign) 10
    "block_shape_rule_prefix_at" [22, 0] m4 with
  | .ok ([0], _) =>
    (match run (indPartsFns ++ libFns ++ stubFns ++ masterFns ++ indPartsForeign) 10
      "block_shape_major_idx_at" [22, 0] m4 with
     | .ok ([0], _) => true
     | _ => false)
  | _ => false

end L.Ind
