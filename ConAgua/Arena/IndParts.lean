import ConAgua.Arena.IndIface
import ConAgua.Census.Attr

/-!
# The block recogniser in L (lane `induct`, module `IndParts`)

The L translation of `vendor/con-ron/ConRon/Arena/Inductives/FieldTele.lean`'s `piBinders`, all of
`vendor/con-ron/ConRon/Arena/Inductives/BlockParts.lean`, `BlockRec.lean`'s
`blockLargeElimAllowed`, and `CheckDecl.lean`'s `checkShapelessFormers`, `checkShapeless` and the
`.indDecl` arm of `checkDecl` (as `check_ind_decl`). No proofs this round (IndIface, "No proofs
this round"); the point is a faithful translation, one `FunDecl` per twin function, split into
helpers where a twin function has more than one loop or a long straight-line body.

## Representation, beyond IndIface's table

* **The block** (`List IConstantInfo`, the twin's `block` argument): an `IW` slice of `EREC`
  constant-record pointers (`er_to_iw`'s result in `check_ind_decl`; `pinsenv`'s `decCI` layout).
* **`blockSplitRecs`'s element** (`IConstantVal × Nat × Nat × List IRecRule`, a recursor before it
  is folded into a `RecShape`): a fresh `IW` record `[cvR, mI, rP, rules.off, rules.len]` (`rules`
  an `EREC` slice of 11-word `decRule` records, unchanged — nothing to copy, it already lives in
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
  block as an `IW` slice of constant-record pointers, `p` the `BlockParts` pointer).

Everything else this file calls is in `libFns`, `stubFns` or `masterFns` (IndIface).
-/

namespace L.Ind

open L.Arena

/-! ## `FieldTele.piBinders` -/

/-- `pi_binders(fuel, h)`: `piBinders fuel h`. `h`'s tag is read off the raw handle (pure, no
`view`), as the twin's `h.tag` does; only once it is `forallE` do we call `e_view` (which can abort
on a dangling handle, as `viewBind` can). The result list is built by consing on the way out
(`sl_cons`), the same list the twin's recursion conses. -/
-- con-ron: ConRon/Arena/Inductives/FieldTele.lean:19-32 ConRon.Arena.piBinders
@[l_impl ConRon.Arena.piBinders]
def piBinders : FunDecl := lfn (fuel, h) locals (g, ty, b, z, bo, bl, be, o, l) {
  if fuel == 0 { abort };
  if h >> 28 != 6 { return (0, 0, h) };
  (g, ty, b, z) := call e_view(h);
  (bo, bl, be) := call pi_binders(fuel - 1, b);
  (o, l) := call sl_cons(ty, bo, bl);
  return (o, l, be)
}

/-! ## `BlockParts`: the record's pure projections -/

/-- `num_ctors_of(off, l)`: `numCtorsOf` of the `IW` slice of `MemberShape` pointers (sum of each
member's `ctors.len`, at offset `+3`), recursively on the slice (as the twin's recursion is). Aborts
when the sum wraps (a capacity: the twin's `Nat` does not). -/
-- con-ron: ConRon/Arena/Inductives/BlockParts.lean:90-94 ConRon.Arena.numCtorsOf
@[l_impl ConRon.Arena.numCtorsOf]
def numCtorsOf : FunDecl := lfn (off, l) locals (r, m, s) {
  if l == 0 { return 0 };
  r := call num_ctors_of(off + 1, l - 1);
  m := IW.u64[off];
  s := IW.u64[m + 3] + r;
  if s < r { abort };
  return s
}

/-- `block_shape_k(p)`: `BlockShape.k`, the members' count (`members.len`, word `p + 1`). -/
-- con-ron: ConRon/Arena/Inductives/BlockParts.lean:96-98 ConRon.Arena.BlockShape.k
@[l_impl ConRon.Arena.BlockShape.k]
def blockShapeK : FunDecl := lfn (p) locals () {
  return IW.u64[p + 1]
}

/-- `block_shape_num_ctors(p)`: `BlockShape.numCtors`. -/
-- con-ron: ConRon/Arena/Inductives/BlockParts.lean:100-102 ConRon.Arena.BlockShape.numCtors
@[l_impl ConRon.Arena.BlockShape.numCtors]
def blockShapeNumCtors : FunDecl := lfn (p) locals (o, l, r) {
  o := IW.u64[p];
  l := IW.u64[p + 1];
  r := call num_ctors_of(o, l);
  return r
}

/-- `block_shape_member_names(p)`: `BlockShape.memberNames`, each member's `cvT.name` (`EREC` word
`0` of the member's `cvT` pointer). -/
-- con-ron: ConRon/Arena/Inductives/BlockParts.lean:104-106 ConRon.Arena.BlockShape.memberNames
@[l_impl ConRon.Arena.BlockShape.memberNames]
def blockShapeMemberNames : FunDecl := lfn (p) locals (off, l, q, u) {
  off := IW.u64[p];
  l := IW.u64[p + 1];
  q := call iw_alloc(l);
  u := call member_names_copy(q, off, l);
  return (q, l)
}

/-- `member_names_copy(d, s, l)`: `IW[d+j] := EREC[IW[IW[s+j]]]` for `j < l` (each member's
`cvT.name`: the member record's word `0` is the `cvT` pointer), recursively. -/
-- con-ron: ConRon/Arena/Inductives/BlockParts.lean:104-106 ConRon.Arena.BlockShape.memberNames
@[l_impl ConRon.Arena.BlockShape.memberNames]
def memberNamesCopy : FunDecl := lfn (d, s, l) locals (m, cv, u) {
  if l == 0 { return 0 };
  m := IW.u64[s];
  cv := IW.u64[m];
  IW.u64[d] := EREC.u64[cv];
  u := call member_names_copy(d + 1, s + 1, l - 1);
  return 0
}

/-- `block_shape_n_idxs(p)`: `BlockShape.nIdxs`, each member's `nIdx` (word `+1`). -/
-- con-ron: ConRon/Arena/Inductives/BlockParts.lean:108-110 ConRon.Arena.BlockShape.nIdxs
@[l_impl ConRon.Arena.BlockShape.nIdxs]
def blockShapeNIdxs : FunDecl := lfn (p) locals (off, l, q, u) {
  off := IW.u64[p];
  l := IW.u64[p + 1];
  q := call iw_alloc(l);
  u := call n_idxs_copy(q, off, l);
  return (q, l)
}

/-- `n_idxs_copy(d, s, l)`: `IW[d+j] := IW[IW[s+j] + 1]` for `j < l` (each member pointer's
`nIdx`), recursively. -/
-- con-ron: ConRon/Arena/Inductives/BlockParts.lean:108-110 ConRon.Arena.BlockShape.nIdxs
@[l_impl ConRon.Arena.BlockShape.nIdxs]
def nIdxsCopy : FunDecl := lfn (d, s, l) locals (m, u) {
  if l == 0 { return 0 };
  m := IW.u64[s];
  IW.u64[d] := IW.u64[m + 1];
  u := call n_idxs_copy(d + 1, s + 1, l - 1);
  return 0
}

/-- `block_shape_lps(p)`: `BlockShape.lps`, member `0`'s `cvT.levelParams` copied from `EREC` into
`IW` (`[]` at no member). -/
-- con-ron: ConRon/Arena/Inductives/BlockParts.lean:112-117 ConRon.Arena.BlockShape.lps
@[l_impl ConRon.Arena.BlockShape.lps]
def blockShapeLps : FunDecl := lfn (p) locals (off, l, m, cv, o, pl) {
  off := IW.u64[p];
  l := IW.u64[p + 1];
  if l == 0 { return (0, 0) };
  m := IW.u64[off];
  cv := IW.u64[m];
  (o, pl) := call er_to_iw(EREC.u64[cv + 1], EREC.u64[cv + 2]);
  return (o, pl)
}

/-- `block_shape_ctors_copy(off, q, k)`: copy the ctor slice of the member at `off` to `IW[q + k ..]`;
returns its length. -/
-- con-ron: ConRon/Arena/Inductives/BlockParts.lean:119-122 ConRon.Arena.BlockShape.allCtors
@[l_impl ConRon.Arena.BlockShape.allCtors]
def blockShapeCtorsCopy : FunDecl := lfn (off, q, k) locals (m, co, cl, u) {
  m := IW.u64[off];
  co := IW.u64[m + 2];
  cl := IW.u64[m + 3];
  u := call iw_copy(q + k, co, cl);
  return cl
}

/-- `block_shape_all_ctors_go(off, l, q, k)`: copy the ctor slices of the `l` members at `off` to
`IW[q + k ..]`, one after the other (recursive on the members). -/
-- con-ron: ConRon/Arena/Inductives/BlockParts.lean:119-122 ConRon.Arena.BlockShape.allCtors
@[l_impl ConRon.Arena.BlockShape.allCtors]
def blockShapeAllCtorsGo : FunDecl := lfn (off, l, q, k) locals (cl, r) {
  if l == 0 { return 0 };
  cl := call block_shape_ctors_copy(off, q, k);
  r := call block_shape_all_ctors_go(off + 1, l - 1, q, k + cl);
  return 0
}

/-- `block_shape_all_ctors(p)`: `BlockShape.allCtors`, every member's `ctors` list concatenated,
in block order. -/
-- con-ron: ConRon/Arena/Inductives/BlockParts.lean:119-122 ConRon.Arena.BlockShape.allCtors
@[l_impl ConRon.Arena.BlockShape.allCtors]
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
-- con-ron: ConRon/Arena/Inductives/BlockParts.lean:124-130 ConRon.Arena.BlockShape.rulePrefixAt
@[l_impl ConRon.Arena.BlockShape.rulePrefixAt]
def blockShapeRulePrefixAt : FunDecl := lfn (p, r) locals (off, l, rc) {
  off := IW.u64[p + 2];
  l := IW.u64[p + 3];
  if l <= r { return 0 };
  rc := IW.u64[off + r];
  return IW.u64[rc + 1]
}

/-- `block_shape_major_idx_at(p, r)`: `BlockShape.majorIdxAt`, recursor `r`'s `mI` (word `+2`),
`0` past the recursor list. -/
-- con-ron: ConRon/Arena/Inductives/BlockParts.lean:132-137 ConRon.Arena.BlockShape.majorIdxAt
@[l_impl ConRon.Arena.BlockShape.majorIdxAt]
def blockShapeMajorIdxAt : FunDecl := lfn (p, r) locals (off, l, rc) {
  off := IW.u64[p + 2];
  l := IW.u64[p + 3];
  if l <= r { return 0 };
  rc := IW.u64[off + r];
  return IW.u64[rc + 2]
}

/-- `block_shape_with_sort(p, s)`: `BlockShape.withSort`, a fresh record (values are immutable once
built) with `resSort := s` and `isProp` recomputed (`lvlEq? s zeroLevel`). -/
-- con-ron: ConRon/Arena/Inductives/BlockParts.lean:139-149 ConRon.Arena.BlockShape.withSort
@[l_impl ConRon.Arena.BlockShape.withSort]
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

/-- `block_parts_complete(p0, p1)`: `BlockParts.complete`, identity on the pointer (`BlockParts` and
its `BlockShape` share one pointer, `decBP`). -/
-- con-ron: ConRon/Arena/Inductives/BlockParts.lean:158-162 ConRon.Arena.BlockParts.complete
@[l_impl ConRon.Arena.BlockParts.complete]
def blockPartsComplete : FunDecl := lfn (p0, p1) locals () {
  return p1
}

/-! ## Recognition -/

/-- `block_split_recs(off, l)`: `blockSplitRecs` of the `off, l` slice of `EREC` constant-record
pointers: `(1, q, l)` if every element is `recInfo` (kind `5`), each folded into a fresh
`[cvR, mI, rP, rules.off, rules.len]` record; `(0, …)` at the first that is not. Recursive as the
twin (the rest first, then `sl_cons`; lane `indproofs2`: was a loop). -/
-- con-ron: ConRon/Arena/Inductives/BlockParts.lean:166-175 ConRon.Arena.blockSplitRecs
@[l_impl ConRon.Arena.blockSplitRecs]
def blockSplitRecs : FunDecl := lfn (off, l) locals (ci, ok, ro, rl, rc, o2, l2) {
  if l == 0 { return (1, 0, 0) };
  ci := EREC.u64[off];
  if EREC.u64[ci] != 5 { return (0, 0, 0) };
  (ok, ro, rl) := call block_split_recs(off + 1, l - 1);
  if ok == 0 { return (0, 0, 0) };
  rc := call rec5(ci + 1, EREC.u64[ci + 5], EREC.u64[ci + 6], EREC.u64[ci + 7], EREC.u64[ci + 8]);
  (o2, l2) := call sl_cons(rc, ro, rl);
  return (1, o2, l2)
}

/-- `block_split_ctors(off, l)`: `blockSplitCtors`: the leading `ctorInfo` (kind `4`) elements, each
folded into `[cv, nP, nF]`, then `block_split_recs` on the rest (recursive as the twin). -/
-- con-ron: ConRon/Arena/Inductives/BlockParts.lean:177-189 ConRon.Arena.blockSplitCtors
@[l_impl ConRon.Arena.blockSplitCtors]
def blockSplitCtors : FunDecl := lfn (off, l) locals (ci, ok, co, cl, ro, rl, c, o2, l2) {
  if l == 0 { return (1, 0, 0, 0, 0) };
  ci := EREC.u64[off];
  if EREC.u64[ci] != 4 {
    (ok, ro, rl) := call block_split_recs(off, l);
    if ok == 0 { return (0, 0, 0, 0, 0) };
    return (1, 0, 0, ro, rl)
  };
  (ok, co, cl, ro, rl) := call block_split_ctors(off + 1, l - 1);
  if ok == 0 { return (0, 0, 0, 0, 0) };
  c := call rec3(ci + 1, EREC.u64[ci + 5], EREC.u64[ci + 6]);
  (o2, l2) := call sl_cons(c, co, cl);
  return (1, o2, l2, ro, rl)
}

/-- `block_split(off, l)`: `blockSplit`: the leading `indInfo` (kind `3`) elements (their `cv`
pointers), then `block_split_ctors` on the rest (recursive as the twin). The twin's 3-list result
is 7 words, past the 6-result cap, so `(ok, q)` with `q` a fresh `[cvTs.off, cvTs.len, cs.off,
cs.len, rs.off, rs.len]` record. -/
-- con-ron: ConRon/Arena/Inductives/BlockParts.lean:191-203 ConRon.Arena.blockSplit
@[l_impl ConRon.Arena.blockSplit]
def blockSplit : FunDecl := lfn (off, l) locals (ci, ok, q, co, cl, ro, rl, fo, fl, q2) {
  if l == 0 { q := call rec6(0, 0, 0, 0, 0, 0); return (1, q) };
  ci := EREC.u64[off];
  if EREC.u64[ci] != 3 {
    (ok, co, cl, ro, rl) := call block_split_ctors(off, l);
    if ok == 0 { return (0, 0) };
    q := call rec6(0, 0, co, cl, ro, rl);
    return (1, q)
  };
  (ok, q) := call block_split(off + 1, l - 1);
  if ok == 0 { return (0, 0) };
  (fo, fl) := call sl_cons(ci + 1, IW.u64[q], IW.u64[q + 1]);
  q2 := call rec6(fo, fl, IW.u64[q + 2], IW.u64[q + 3], IW.u64[q + 4], IW.u64[q + 5]);
  return (1, q2)
}

/-- `rec_target_of(no, nl, mI, ty)`: `recTargetOf`: strip `mI` leading `∀`s off `ty`; if the
remainder is itself a `∀` (pure tag test) whose domain's head is a `const` naming one of `no, nl`,
that member's index; else `no, nl`'s length (`names.length`, the twin's `none'`). -/
-- con-ron: ConRon/Arena/Inductives/BlockParts.lean:205-227 ConRon.Arena.recTargetOf
@[l_impl ConRon.Arena.recTargetOf]
def recTargetOf : FunDecl := lfn (no, nl, mI, ty) locals (ok, bo, bl, body, g, x, y, z, hd, fnd, idx) {
  (ok, bo, bl, body) := call strip_pis(mI, ty);
  if ok == 0 { return nl };
  if body >> 28 != 6 { return nl };
  (g, x, y, z) := call e_view(body);
  hd := call get_app_fn_f(⟪CWF⟫, x);
  if hd >> 28 != 3 { return nl };
  (g, x, y, z) := call e_view(hd);
  (fnd, idx) := call sl_find(no, nl, x);
  if fnd == 0 { return nl };
  return idx
}

/-- `block_counts_pure(nPd, k, nC, nR, bl, g, rOk, rMI, rRP)`: the arithmetic tail of `blockCounts?`
(from the binder count `bl` and the result's view tag `g`), as `(ok, a, b)`. -/
-- con-ron: ConRon/Arena/Inductives/BlockParts.lean:229-248 ConRon.Arena.blockCounts?
@[l_impl ConRon.Arena.blockCounts?]
def blockCountsPure : FunDecl := lfn (nPd, k, nC, nR, bl, g, rOk, rMI, rRP) locals () {
  if g == 2 {
    if bl < nPd { return (0, 0, 0) };
    return (1, nPd, bl - nPd)
  };
  if rOk == 0 { return (0, 0, 0) };
  if rRP < nC + k || rMI < rRP { return (0, 0, 0) };
  if rRP - (nC + k) == nPd { return (1, nPd, rMI - rRP) };
  if k < nR && nPd + nR + nC <= rRP { return (1, nPd, rMI - rRP) };
  return (0, 0, 0)
}

/-- `block_counts_head(cvT)`: the binder count of the former's type and the tag of its result
(`piBinders`, then `view`). -/
-- con-ron: ConRon/Arena/Inductives/BlockParts.lean:229-248 ConRon.Arena.blockCounts?
@[l_impl ConRon.Arena.blockCounts?]
def blockCountsHead : FunDecl := lfn (cvT) locals (ty, bo, bl, res, g, x, y, z) {
  ty := EREC.u64[cvT + 3];
  (bo, bl, res) := call pi_binders(⟪CWF⟫, ty);
  (g, x, y, z) := call e_view(res);
  return (bl, g)
}

/-- `block_counts(nPd, k, nC, nR, cvT, rOk, rMI, rRP)`: `blockCounts?`. `r : Option (Nat × Nat)`
(`rOk, rMI, rRP`) is a bare argument, not nested in a list or record, so it is flattened rather
than boxed (by analogy with the result convention). -/
-- con-ron: ConRon/Arena/Inductives/BlockParts.lean:229-248 ConRon.Arena.blockCounts?
@[l_impl ConRon.Arena.blockCounts?]
def blockCounts : FunDecl := lfn (nPd, k, nC, nR, cvT, rOk, rMI, rRP) locals (bl, g, a, b, c) {
  (bl, g) := call block_counts_head(cvT);
  (a, b, c) := call block_counts_pure(nPd, k, nC, nR, bl, g, rOk, rMI, rRP);
  return (a, b, c)
}

/-- `ctor_member(no, nl, lvls, nP, c)`: `ctorMember?`, `c` a `[cv, nF]` pointer: strip `nP + nF`
leading `∀`s off `c.type`, then `member_idx_at` the head of what remains. -/
-- con-ron: ConRon/Arena/Inductives/BlockParts.lean:250-259 ConRon.Arena.ctorMember?
@[l_impl ConRon.Arena.ctorMember?]
def ctorMember : FunDecl := lfn (no, nl, lvls, nP, c) locals (nF, ty, ok, bo, bl, body, hd, rok, ri) {
  nF := IW.u64[c + 1];
  if nP + nF < nP { abort };
  ty := EREC.u64[IW.u64[c] + 3];
  (ok, bo, bl, body) := call strip_pis(nP + nF, ty);
  if ok == 0 { return (0, 0) };
  hd := call get_app_fn_f(⟪CWF⟫, body);
  (rok, ri) := call member_idx_at(no, nl, lvls, hd);
  return (rok, ri)
}

/-- `block_groups_one(no, nl, lvls, nP, co, cl, m)`: one group of `blockGroups`'s general case,
member `m`'s constructors: `cs.filterM` (`ctor_member` called once per candidate, in list order,
then the rest; recursive, lane `indproofs2`: was a loop). -/
-- con-ron: ConRon/Arena/Inductives/BlockParts.lean:261-275 ConRon.Arena.blockGroups
@[l_impl ConRon.Arena.blockGroups]
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
-- con-ron: ConRon/Arena/Inductives/BlockParts.lean:261-275 ConRon.Arena.blockGroups
@[l_impl ConRon.Arena.blockGroups]
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
-- con-ron: ConRon/Arena/Inductives/BlockParts.lean:261-275 ConRon.Arena.blockGroups
@[l_impl ConRon.Arena.blockGroups]
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
-- con-ron: ConRon/Arena/Inductives/BlockParts.lean:277-285 ConRon.Arena.blockRecLpsOk
@[l_impl ConRon.Arena.blockRecLpsOk]
def blockRecLpsOne : FunDecl := lfn (rc, wo, wl) locals (cv, rpo, rpl, eqv) {
  cv := IW.u64[rc];
  (rpo, rpl) := call er_to_iw(EREC.u64[cv + 1], EREC.u64[cv + 2]);
  eqv := call sl_eq(rpo, rpl, wo, wl);
  return eqv
}

/-- `block_rec_lps_ok_go(ro, rl, wo, wl)`: every one of the `rl` recursor records at `ro` has the
wanted level parameters `(wo, wl)` (recursive on the slice, stopping at the first mismatch). -/
-- con-ron: ConRon/Arena/Inductives/BlockParts.lean:277-285 ConRon.Arena.blockRecLpsOk
@[l_impl ConRon.Arena.blockRecLpsOk]
def blockRecLpsOkGo : FunDecl := lfn (ro, rl, wo, wl) locals (eqv, r) {
  if rl == 0 { return 1 };
  eqv := call block_rec_lps_one(IW.u64[ro], wo, wl);
  if eqv == 0 { return 0 };
  r := call block_rec_lps_ok_go(ro + 1, rl - 1, wo, wl);
  return r
}

/-- `block_rec_lps_ok(p)`: `blockRecLpsOk`: every recursor's `cvR.levelParams` equals `elim :: lps`
(`large`) or `lps` (pure, so an early `return 0` is fine). -/
-- con-ron: ConRon/Arena/Inductives/BlockParts.lean:277-285 ConRon.Arena.blockRecLpsOk
@[l_impl ConRon.Arena.blockRecLpsOk]
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
-- con-ron: ConRon/Arena/Inductives/BlockParts.lean:287-295 ConRon.Arena.blockRecNameSetOk
@[l_impl ConRon.Arena.blockRecNameSetOk]
def blockRecWant : FunDecl := lfn (mo, ml) locals (m, cv, w, o, l) {
  if ml == 0 { return (0, 0) };
  m := IW.u64[mo];
  cv := IW.u64[m];
  w := call name_rec(EREC.u64[cv]);
  (o, l) := call block_rec_want(mo + 1, ml - 1);
  (o, l) := call sl_cons(w, o, l);
  return (o, l)
}

/-- `block_rec_got(ro, rl)`: the recursors' names (`recs.map (·.cvR.name)`), recursively. -/
-- con-ron: ConRon/Arena/Inductives/BlockParts.lean:287-295 ConRon.Arena.blockRecNameSetOk
@[l_impl ConRon.Arena.blockRecNameSetOk]
def blockRecGot : FunDecl := lfn (ro, rl) locals (rc, o, l) {
  if rl == 0 { return (0, 0) };
  rc := IW.u64[ro];
  (o, l) := call block_rec_got(ro + 1, rl - 1);
  (o, l) := call sl_cons(EREC.u64[IW.u64[rc]], o, l);
  return (o, l)
}

/-- `block_rec_name_set_ok(mo, ml, ro, rl)`: `blockRecNameSetOk`: the recursor names, as a set,
are exactly `T_m.rec` at every member (`sl_set_eq`; lane `indproofs2`: the loops became
`block_rec_want`/`block_rec_got`). -/
-- con-ron: ConRon/Arena/Inductives/BlockParts.lean:287-295 ConRon.Arena.blockRecNameSetOk
@[l_impl ConRon.Arena.blockRecNameSetOk]
def blockRecNameSetOk : FunDecl := lfn (mo, ml, ro, rl) locals (wo, wl, go, gl, b) {
  (wo, wl) := call block_rec_want(mo, ml);
  (go, gl) := call block_rec_got(ro, rl);
  b := call sl_set_eq(go, gl, wo, wl);
  return b
}

/-- `block_rec_names_unreserved(ro, rl)`: `blockRecNamesUnreserved`, stopping at the first
recursor whose name is reserved (`reserved_rec_name`), as the twin's recursion does (recursive on
the slice: `ro + 1`, `rl - 1`). -/
-- con-ron: ConRon/Arena/Inductives/BlockParts.lean:297-305 ConRon.Arena.blockRecNamesUnreserved
@[l_impl ConRon.Arena.blockRecNamesUnreserved]
def blockRecNamesUnreserved : FunDecl := lfn (ro, rl) locals (rc, cv, nm, b, r) {
  if rl == 0 { return 1 };
  rc := IW.u64[ro];
  cv := IW.u64[rc];
  nm := EREC.u64[cv];
  b := call reserved_rec_name(nm);
  if b != 0 { return 0 };
  r := call block_rec_names_unreserved(ro + 1, rl - 1);
  return r
}

/-- `block_member_counts_find(no, nl, ro, rl, m)`: the `rs.findM?` inside `blockMemberCounts?`,
one `rec_target_of` call per candidate, stopping at the first whose target is `m` (recursive,
lane `indproofs2`: was a loop). -/
-- con-ron: ConRon/Arena/Inductives/BlockParts.lean:307-325 ConRon.Arena.blockMemberCounts?
@[l_impl ConRon.Arena.blockMemberCounts?]
def blockMemberCountsFind : FunDecl := lfn (no, nl, ro, rl, m) locals (e, mI, t, a, b, c) {
  if rl == 0 { return (0, 0, 0) };
  e := IW.u64[ro];
  mI := IW.u64[e + 1];
  t := call rec_target_of(no, nl, mI, EREC.u64[IW.u64[e] + 3]);
  if t == m { return (1, mI, IW.u64[e + 2]) };
  (a, b, c) := call block_member_counts_find(no, nl, ro + 1, rl - 1, m);
  return (a, b, c)
}

/-- `block_member_counts_go(nPd, k, nC, no, nl, ro, rl, cto, ctl, idx)`: `blockMemberCounts?` from
member `idx` on: one `block_member_counts_find` and one `block_counts` for this former, then the
rest; a failure stops the walk there (no further calls). The record words past `2^32` are a
capacity abort (`block_counts`' arithmetic). -/
-- con-ron: ConRon/Arena/Inductives/BlockParts.lean:307-325 ConRon.Arena.blockMemberCounts?
@[l_impl ConRon.Arena.blockMemberCounts?]
def blockMemberCountsGo : FunDecl := lfn (nPd, k, nC, no, nl, ro, rl, cto, ctl, idx)
    locals (cv, rok, rmi, rrp, cok, ca, cb, ok, o, l) {
  if ctl == 0 { return (1, 0, 0) };
  cv := IW.u64[cto];
  (rok, rmi, rrp) := call block_member_counts_find(no, nl, ro, rl, idx);
  if 4294967296 <= rmi || 4294967296 <= rrp { abort };
  (cok, ca, cb) := call block_counts(nPd, k, nC, rl, cv, rok, rmi, rrp);
  if cok == 0 { return (0, 0, 0) };
  (ok, o, l) := call block_member_counts_go(nPd, k, nC, no, nl, ro, rl, cto + 1, ctl - 1, idx + 1);
  if ok == 0 { return (0, 0, 0) };
  (o, l) := call sl_cons(cb, o, l);
  return (1, o, l)
}

/-- `block_member_counts(nPd, k, nC, no, nl, ro, rl, cto, ctl)`: `blockMemberCounts?` from member
`0` (the counts past `2^32` a capacity abort). -/
-- con-ron: ConRon/Arena/Inductives/BlockParts.lean:307-325 ConRon.Arena.blockMemberCounts?
@[l_impl ConRon.Arena.blockMemberCounts?]
def blockMemberCounts : FunDecl := lfn (nPd, k, nC, no, nl, ro, rl, cto, ctl) locals (ok, o, l) {
  if 4294967296 <= nPd || 4294967296 <= k || 4294967296 <= nC || 4294967296 <= rl { abort };
  (ok, o, l) := call block_member_counts_go(nPd, k, nC, no, nl, ro, rl, cto, ctl, 0);
  return (ok, o, l)
}

/-! ### `blockShape?`: one helper per phase -/

/-- `block_shape_names_of(cto, ctl)`: the former `cv` pointers' names (`cvTs.map (·.name)`). -/
-- con-ron: ConRon/Arena/Inductives/BlockParts.lean:327-384 ConRon.Arena.blockShape?
@[l_impl ConRon.Arena.blockShape?]
def blockShapeNamesOf : FunDecl := lfn (cto, ctl) locals (o, l) {
  if ctl == 0 { return (0, 0) };
  (o, l) := call block_shape_names_of(cto + 1, ctl - 1);
  (o, l) := call sl_cons(EREC.u64[IW.u64[cto]], o, l);
  return (o, l)
}

/-- The formers' pins: unreserved and sharing `lps`. -/
-- con-ron: ConRon/Arena/Inductives/BlockParts.lean:327-384 ConRon.Arena.blockShape?
@[l_impl ConRon.Arena.blockShape?]
def blockShapePinsFormers : FunDecl := lfn (cto, ctl, lo, ll) locals (cv, b, plo, pll, eqv, r) {
  if ctl == 0 { return 1 };
  cv := IW.u64[cto];
  b := call reserved_contains(EREC.u64[cv]);
  if b != 0 { return 0 };
  (plo, pll) := call er_to_iw(EREC.u64[cv + 1], EREC.u64[cv + 2]);
  eqv := call sl_eq(plo, pll, lo, ll);
  if eqv == 0 { return 0 };
  r := call block_shape_pins_formers(cto + 1, ctl - 1, lo, ll);
  return r
}

/-- The recursors' pins: unreserved. -/
-- con-ron: ConRon/Arena/Inductives/BlockParts.lean:327-384 ConRon.Arena.blockShape?
@[l_impl ConRon.Arena.blockShape?]
def blockShapePinsRecs : FunDecl := lfn (ro, rl) locals (b, r) {
  if rl == 0 { return 1 };
  b := call reserved_contains(EREC.u64[IW.u64[IW.u64[ro]]]);
  if b != 0 { return 0 };
  r := call block_shape_pins_recs(ro + 1, rl - 1);
  return r
}

/-- The constructors' pins: `nP` matches, unreserved, sharing `lps`. -/
-- con-ron: ConRon/Arena/Inductives/BlockParts.lean:327-384 ConRon.Arena.blockShape?
@[l_impl ConRon.Arena.blockShape?]
def blockShapePinsCtors : FunDecl := lfn (nP, cso, csl, lo, ll) locals (c, cv, b, plo, pll, eqv, r) {
  if csl == 0 { return 1 };
  c := IW.u64[cso];
  cv := IW.u64[c];
  if IW.u64[c + 1] != nP { return 0 };
  b := call reserved_contains(EREC.u64[cv]);
  if b != 0 { return 0 };
  (plo, pll) := call er_to_iw(EREC.u64[cv + 1], EREC.u64[cv + 2]);
  eqv := call sl_eq(plo, pll, lo, ll);
  if eqv == 0 { return 0 };
  r := call block_shape_pins_ctors(nP, cso + 1, csl - 1, lo, ll);
  return r
}

/-- The three pin passes, in the twin's own order (formers, then recursors, then constructors;
module note: "all four are pure", so this order is a choice, not a requirement). -/
-- con-ron: ConRon/Arena/Inductives/BlockParts.lean:327-384 ConRon.Arena.blockShape?
@[l_impl ConRon.Arena.blockShape?]
def blockShapePinsOk : FunDecl := lfn (nP, cto, ctl, lo, ll, ro, rl, cso, csl) locals (a, b, c) {
  a := call block_shape_pins_formers(cto, ctl, lo, ll);
  if a == 0 { return 0 };
  b := call block_shape_pins_recs(ro, rl);
  if b == 0 { return 0 };
  c := call block_shape_pins_ctors(nP, cso, csl, lo, ll);
  return c
}

/-- The result sort: the sort at the end of `nP + nIdxs[0]` leading `∀`s off `cvT0.type`, else
`zeroLevel` (the install's whnf loop replaces the placeholder). -/
-- con-ron: ConRon/Arena/Inductives/BlockParts.lean:327-384 ConRon.Arena.blockShape?
@[l_impl ConRon.Arena.blockShape?]
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
-- con-ron: ConRon/Arena/Inductives/BlockParts.lean:327-384 ConRon.Arena.blockShape?
@[l_impl ConRon.Arena.blockShape?]
def blockShapeCtorsOf : FunDecl := lfn (cso, csl) locals (c, o, l, e) {
  if csl == 0 { return (0, 0) };
  c := IW.u64[cso];
  (o, l) := call block_shape_ctors_of(cso + 1, csl - 1);
  e := call rec2(IW.u64[c], IW.u64[c + 2]);
  (o, l) := call sl_cons(e, o, l);
  return (o, l)
}

/-- The members: `((cvTs.zip nIdxs).zip groups).map`, each a fresh `[cvT, nIdx, ctors.off,
ctors.len]` (a group is a pointer to a `[off, len]` header; its fields are inlined here). -/
-- con-ron: ConRon/Arena/Inductives/BlockParts.lean:327-384 ConRon.Arena.blockShape?
@[l_impl ConRon.Arena.blockShape?]
def blockShapeMembersOf : FunDecl := lfn (cto, ctl, io, go) locals (o, l, hdr, ms) {
  if ctl == 0 { return (0, 0) };
  (o, l) := call block_shape_members_of(cto + 1, ctl - 1, io + 1, go + 1);
  hdr := IW.u64[go];
  ms := call rec4(IW.u64[cto], IW.u64[io], IW.u64[hdr], IW.u64[hdr + 1]);
  (o, l) := call sl_cons(ms, o, l);
  return (o, l)
}

/-- A recursor rule slice's `rhs` fields (word `+8` of each 11-word `decRule` record), copied from
`EREC` into `IW`. -/
-- con-ron: ConRon/Arena/Inductives/BlockParts.lean:327-384 ConRon.Arena.blockShape?
@[l_impl ConRon.Arena.blockShape?]
def blockShapeRhssOf : FunDecl := lfn (ro, rl) locals (o, l) {
  if rl == 0 { return (0, 0) };
  (o, l) := call block_shape_rhss_of(ro + 11, rl - 1);
  (o, l) := call sl_cons(EREC.u64[ro + 8], o, l);
  return (o, l)
}

/-- The recursors: `rs.mapM` building a fresh `RecShape` (`[cvR, rP, mI, tgt, rhss.off, rhss.len]`,
`decRS`'s order) per element, `tgt` by `rec_target_of`. -/
-- con-ron: ConRon/Arena/Inductives/BlockParts.lean:327-384 ConRon.Arena.blockShape?
@[l_impl ConRon.Arena.blockShape?]
def blockShapeRecsOf : FunDecl := lfn (no, nl, ro, rl) locals (e, tgt, rhso, rhsl, rc, o, l) {
  if rl == 0 { return (0, 0) };
  e := IW.u64[ro];
  tgt := call rec_target_of(no, nl, IW.u64[e + 1], EREC.u64[IW.u64[e] + 3]);
  (rhso, rhsl) := call block_shape_rhss_of(IW.u64[e + 3], IW.u64[e + 4]);
  rc := call rec6(IW.u64[e], IW.u64[e + 2], IW.u64[e + 1], tgt, rhso, rhsl);
  (o, l) := call block_shape_recs_of(no, nl, ro + 1, rl - 1);
  (o, l) := call sl_cons(rc, o, l);
  return (o, l)
}

/-- `cvR0.levelParams` as `elim :: relps` with `relps == lps` and `elim ∉ lps`: `(1, elim)`;
anything else (including no level parameters at all): `(0, 0)`. -/
-- con-ron: ConRon/Arena/Inductives/BlockParts.lean:327-384 ConRon.Arena.blockShape?
@[l_impl ConRon.Arena.blockShape?]
def blockShapeLarge : FunDecl := lfn (cvR0, lo, ll) locals (off, cnt, elim, rlo, rll, eqv, has) {
  off := EREC.u64[cvR0 + 1];
  cnt := EREC.u64[cvR0 + 2];
  if cnt == 0 { return (0, 0) };
  elim := EREC.u64[off];
  (rlo, rll) := call er_to_iw(off + 1, cnt - 1);
  eqv := call sl_eq(rlo, rll, lo, ll);
  if eqv == 0 { return (0, 0) };
  has := call sl_contains(lo, ll, elim);
  if has != 0 { return (0, 0) };
  return (1, elim)
}

/-- The final 9-word `BlockShape` record. -/
-- con-ron: ConRon/Arena/Inductives/BlockParts.lean:327-384 ConRon.Arena.blockShape?
@[l_impl ConRon.Arena.blockShape?]
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

/-- `block_shape_seal`: which eliminator, then the record (split off `block_shape_build`). -/
-- con-ron: ConRon/Arena/Inductives/BlockParts.lean:327-384 ConRon.Arena.blockShape?
@[l_impl ConRon.Arena.blockShape?]
def blockShapeSeal : FunDecl := lfn (mo, ml, ro2, rl2, nPd, s, isProp, largeOk, elim) locals (e, q) {
  if largeOk != 0 {
    q := call block_shape_pack(mo, ml, ro2, rl2, nPd, elim, s, 1, isProp);
    return (1, q)
  };
  e := call intern_nanon();
  q := call block_shape_pack(mo, ml, ro2, rl2, nPd, e, s, 0, isProp);
  return (1, q)
}

/-- `block_shape_fin`: `blockShape?`'s last stretch — the constructors, the levels, the groups,
the members and recursors, which eliminator, the record (lane `indproofs2`: split off
`block_shape_build`). -/
-- con-ron: ConRon/Arena/Inductives/BlockParts.lean:327-384 ConRon.Arena.blockShape?
@[l_impl ConRon.Arena.blockShape?]
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
`block_shape_build`). -/
-- con-ron: ConRon/Arena/Inductives/BlockParts.lean:327-384 ConRon.Arena.blockShape?
@[l_impl ConRon.Arena.blockShape?]
def blockShapeTail : FunDecl := lfn (nPd, cto, ctl, cso, csl, rso, rsl, no, nl, io, il, lo, ll)
    locals (s, z, eq, isProp, ok, q) {
  s := call block_shape_result_sort(nPd, io, il, EREC.u64[IW.u64[cto] + 3]);
  z := call pin_word(53);
  eq := call lvl_eq_c(s, z);
  isProp := u64(eq == 2);
  (ok, q) := call block_shape_fin(nPd, cto, ctl, cso, csl, rso, rsl, no, nl, io, lo, ll, s, isProp);
  return (ok, q)
}

/-- `block_shape_build`: `blockShape?` from its split, non-empty components — the names, the
counts, the level parameters and the pins; then `block_shape_tail`. -/
-- con-ron: ConRon/Arena/Inductives/BlockParts.lean:327-384 ConRon.Arena.blockShape?
@[l_impl ConRon.Arena.blockShape?]
def blockShapeBuild : FunDecl := lfn (nPd, cto, ctl, cso, csl, rso, rsl)
    locals (cvT0, no, nl, mcOk, io, il, lo, ll, pinsOk, ok, q) {
  cvT0 := IW.u64[cto];
  (no, nl) := call block_shape_names_of(cto, ctl);
  (mcOk, io, il) := call block_member_counts(nPd, ctl, csl, no, nl, rso, rsl, cto, ctl);
  if mcOk == 0 { return (0, 0) };
  (lo, ll) := call er_to_iw(EREC.u64[cvT0 + 1], EREC.u64[cvT0 + 2]);
  pinsOk := call block_shape_pins_ok(nPd, cto, ctl, lo, ll, rso, rsl, cso, csl);
  if pinsOk == 0 { return (0, 0) };
  (ok, q) := call block_shape_tail(nPd, cto, ctl, cso, csl, rso, rsl, no, nl, io, il, lo, ll);
  return (ok, q)
}

/-- `block_shape(nPd, off, l)`: `blockShape?`: split the block; decline with no formers or no
recursors (the twin's `cvT0 :: _, (cvR0, _, _, _) :: _` match); else `block_shape_build`. -/
-- con-ron: ConRon/Arena/Inductives/BlockParts.lean:327-384 ConRon.Arena.blockShape?
@[l_impl ConRon.Arena.blockShape?]
def blockShape : FunDecl := lfn (nPd, off, l) locals (ok, q, cto, ctl, cso, csl, rso, rsl, r) {
  (ok, q) := call block_split(off, l);
  if ok == 0 { return (0, 0) };
  cto := IW.u64[q];
  ctl := IW.u64[q + 1];
  cso := IW.u64[q + 2];
  csl := IW.u64[q + 3];
  rso := IW.u64[q + 4];
  rsl := IW.u64[q + 5];
  if ctl == 0 || rsl == 0 { return (0, 0) };
  (ok, r) := call block_shape_build(nPd, cto, ctl, cso, csl, rso, rsl);
  return (ok, r)
}

/-- `block_parts(nPd, off, l)`: `blockParts?`, `block_shape`'s result (`BlockParts` and
`BlockShape` share a pointer). -/
-- con-ron: ConRon/Arena/Inductives/BlockParts.lean:386-392 ConRon.Arena.blockParts?
@[l_impl ConRon.Arena.blockParts?]
def blockParts : FunDecl := lfn (nPd, off, l) locals (ok, p) {
  (ok, p) := call block_shape(nPd, off, l);
  return (ok, p)
}

/-! ## `BlockRec.blockLargeElimAllowed` -/

/-- `block_large_elim_allowed(p, nested)`: always at a never-zero result sort
(`Level.isNeverZero`, `lv_nz`); never when nested; else one member, at most one constructor, and
the large shape. -/
-- con-ron: ConRon/Arena/Inductives/BlockRec.lean:21-31 ConRon.Arena.blockLargeElimAllowed
@[l_impl ConRon.Arena.blockLargeElimAllowed]
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

/-! ## `CheckDecl`: the shapeless decline, and the `.indDecl` arm -/

/-- `check_shapeless_formers(vis, off, cnt)`: `checkShapelessFormers`, every type former
(`indInfo`, kind `3`) checked as a constant (its `cv`, inline at `+1`), discarded; every other
member skipped. -/
-- con-ron: ConRon/Arena/CheckDecl.lean:52-65 ConRon.Arena.checkShapelessFormers
@[l_impl ConRon.Arena.checkShapelessFormers]
def checkShapelessFormers : FunDecl := lfn (vis, off, cnt) locals (ci, z, r) {
  if cnt == 0 { return 0 };
  ci := EREC.u64[off];
  if EREC.u64[ci] == 3 { z := call check_constant_val(vis, ci + 1) };
  r := call check_shapeless_formers(vis, off + 1, cnt - 1);
  return 0
}

/-- `check_shapeless(vis, off, cnt)`: `checkShapeless`: check the formers, then always decline
(`fail (.notImplemented …)`). -/
-- con-ron: ConRon/Arena/CheckDecl.lean:67-78 ConRon.Arena.checkShapeless
@[l_impl ConRon.Arena.checkShapeless]
def checkShapeless : FunDecl := lfn (vis, off, cnt) locals (z) {
  z := call check_shapeless_formers(vis, off, cnt);
  fail R_INDUCTIVE_BLOCK_SHAPE
}

/-- `check_ind_decl(vis, boff, blen, nP)`: the `.indDecl block nP` arm of `checkDecl`
(`@[l_impl ConRon.Arena.checkDecl]`, one arm of it). The pinned basis blocks first
(`basis_pin_hit`); then the declared parameter count (`ind_params_ok`); then the one route
(`block_parts`, `check_block`), or the shapeless decline. -/
-- con-ron: ConRon/Arena/CheckDecl.lean:82-214 ConRon.Arena.checkDecl
-- con-ron: ConRon/Arena/CheckDecl.lean:82-214 ConRon.Arena.checkDecl
@[l_impl ConRon.Arena.checkDecl]
def checkIndDecl : FunDecl := lfn (vis, boff, blen, nP) locals (hitOk, kind, vis2, pOk, pok2, pNew, z) {
  (hitOk, kind) := call basis_pin_hit(boff, blen);
  if hitOk != 0 {
    vis2 := call check_basis_decl(vis, kind);
    return vis2
  };
  pOk := call ind_params_ok(nP, boff, blen);
  if pOk == 0 { fail R_NUMBER_OF_PARAMETERS };
  (pok2, pNew) := call block_parts(nP, boff, blen);
  if pok2 != 0 {
    vis2 := call check_block(vis, boff, blen, pNew);
    return vis2
  };
  z := call check_shapeless(vis, boff, blen)
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
   ("block_parts_complete", blockPartsComplete), ("block_split_recs", blockSplitRecs),
   ("block_split_ctors", blockSplitCtors), ("block_split", blockSplit), ("rec_target_of", recTargetOf),
   ("block_counts_head", blockCountsHead), ("block_counts_pure", blockCountsPure), ("block_counts", blockCounts), ("ctor_member", ctorMember), ("block_groups_one", blockGroupsOne), ("block_groups_go", blockGroupsGo),
   ("block_groups", blockGroups), ("block_rec_lps_one", blockRecLpsOne), ("block_rec_lps_ok_go", blockRecLpsOkGo), ("block_rec_lps_ok", blockRecLpsOk),
   ("block_rec_want", blockRecWant), ("block_rec_got", blockRecGot), ("block_rec_name_set_ok", blockRecNameSetOk), ("block_rec_names_unreserved", blockRecNamesUnreserved),
   ("block_member_counts_find", blockMemberCountsFind), ("block_member_counts_go", blockMemberCountsGo), ("block_member_counts", blockMemberCounts),
   ("block_shape_names_of", blockShapeNamesOf), ("block_shape_pins_formers", blockShapePinsFormers),
   ("block_shape_pins_recs", blockShapePinsRecs), ("block_shape_pins_ctors", blockShapePinsCtors),
   ("block_shape_pins_ok", blockShapePinsOk), ("block_shape_result_sort", blockShapeResultSort),
   ("block_shape_ctors_of", blockShapeCtorsOf), ("block_shape_members_of", blockShapeMembersOf),
   ("block_shape_rhss_of", blockShapeRhssOf), ("block_shape_recs_of", blockShapeRecsOf),
   ("block_shape_large", blockShapeLarge), ("block_shape_pack", blockShapePack),
   ("block_shape_seal", blockShapeSeal), ("block_shape_fin", blockShapeFin), ("block_shape_tail", blockShapeTail), ("block_shape_build", blockShapeBuild), ("block_shape", blockShape), ("block_parts", blockParts),
   ("block_large_elim_allowed", blockLargeElimAllowed),
   ("check_shapeless_formers", checkShapelessFormers), ("check_shapeless", checkShapeless),
   ("check_ind_decl", checkIndDecl)]

/-- Stubs for the functions of OTHER modules this module calls. -/
def indPartsForeign : Prog :=
  [("member_idx_at", stub 4), ("param_levels", stub 2), ("check_block", stub 4)]

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

-- `block_parts_complete` is the identity on its second argument.
#guard
  match run (indPartsFns ++ libFns ++ stubFns ++ masterFns ++ indPartsForeign) 10
    "block_parts_complete" [5, 9] testMem with
  | .ok ([9], _) => true
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
