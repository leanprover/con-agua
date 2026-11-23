module

public import ConAgua.Arena.DeclArms
public import ConAgua.Front.IndApply

@[expose] public section

/-!
# A record's check in L: `check_decl`, the front's records as constant records

The twin's `checkDecl` dispatch (`vendor/con-ron/ConRon/Arena/CheckDecl.lean`), on lane `induct`'s
conventions (`IndIface.lean`: the work pool `IW`, constants as `EREC` records, the view word for
the environment).

* `check_decl(i, vis)` → `vis'`: record `i` of `DECL`. An inductive block (kind `6`, the front's
  records in `DIND`) is copied into `EREC` (`ind_block_to_erec`: every record, its universe
  parameters and its recursor rules relocated). `check_decl_kind(i, vis, bo, bl)` is the twin's
  dispatch: the block goes to lane `induct`'s `check_ind_decl(vis, boff, blen, nP)` (the declared
  parameter count, then the one route), every one-constant record to its arm (`DeclArms.lean`:
  `check_decl_axiom`, `check_decl_defn`, `check_decl_thm`, `check_decl_opaque`, `check_decl_quot`,
  each `(i, vis)`). Then the caches are flushed and the reserved names checked (`basis_names_ok`,
  `BasisL.lean`, at the record's kind and name and the block).
* `erec_ci(i, kind)`: the record's constant as an `EREC` record of the kind the arm's value check
  returns.
-/

open ConRon.Arena

namespace L.Arena

open L.Front (DECL DLP)
open L.Front.Ind (DIND)
open L.Ind (IW)

/-! ## Constant records from the front's records -/

/-- `dlp_copy(d, s, l)`: `EREC[d + j] := DLP[s + j]` cut to 32 bits, for `j < l`. -/
-- con-ron: none — copies the front's records into `EREC` (the twin's `checkDecl` takes the front's values as they are)
@[no_expose] def dlpCopy : FunDecl := lfn (d, s, l) locals (u, ez) {
  if l == 0 { return 0 };
  ez := call erec_put(d, DLP.u64[s] & 4294967295);
  u := call dlp_copy(d + 1, s + 1, l - 1);
  return 0
}

/-- `erec_ci(i, kind)`: the constant record of `DECL` record `i` with kind word `kind`
(`decCI`'s layout of a definition, `CI.defnSize` words: kind, the constant value, the value, the
hint (`0` opaque, `1` abbrev, `2` regular), the height); its universe parameters a fresh `EREC`
slice. -/
-- con-ron: none — builds the front's record as a constant record (the twin's `checkDecl` takes the declaration's values as they are)
@[no_expose] def erecCi : FunDecl := lfn (i, kind) locals (lo, ll, s, z, p, hq, ez) {
  lo := DECL.u64[3 + 8 * i];
  ll := DECL.u64[4 + 8 * i];
  s := call erec_alloc(ll);
  z := call dlp_copy(s, 1 + lo, ll);
  p := call erec_alloc(⟪CI.defnSize⟫);
  ez := call erec_put(p, kind);
  ez := call erec_put(p + ⟪CI.cv + CV.name⟫, DECL.u64[2 + 8 * i] & 4294967295);
  ez := call erec_put(p + ⟪CI.cv + CV.lpsOff⟫, s);
  ez := call erec_put(p + ⟪CI.cv + CV.lpsLen⟫, ll);
  ez := call erec_put(p + ⟪CI.cv + CV.type⟫, DECL.u64[5 + 8 * i] & 4294967295);
  ez := call erec_put(p + ⟪CI.defnValue⟫, DECL.u64[6 + 8 * i] & 4294967295);
  hq := DECL.u64[7 + 8 * i];
  if hq == 1 { ez := call erec_put(p + ⟪CI.defnHint⟫, 1)} else if hq == 2 {
    ez := call erec_put(p + ⟪CI.defnHint⟫, 0)} else { ez := call erec_put(p + ⟪CI.defnHint⟫, 2)};
  ez := call erec_put(p + ⟪CI.defnHint + Hint.height⟫, DECL.u64[8 + 8 * i]);
  return p
}

/-! ## An inductive block from the front's `DIND` into `EREC` -/

/-- `dind_copy(d, s, l)`: `EREC[d + j] := DIND[s + j]` for `j < l`. A non-empty source at word `0`
(the pool's top, never a record's or a slice's place: the front writes them at `1 + top`) aborts,
so that the copy reads only what `IndDeclAt`'s cut pool (`trunc`, word `0` cleared) decodes. -/
-- con-ron: none — copies the front's records into `EREC` (the twin's `checkDecl` takes the front's values as they are)
@[no_expose] def dindCopy : FunDecl := lfn (d, s, l) locals (u, ez) {
  if l == 0 { return 0 };
  if s == 0 { abort };
  ez := call erec_put(d, DIND.u64[s]);
  u := call dind_copy(d + 1, s + 1, l - 1);
  return 0
}

/-- `ind_rec_copy(s)`: the constant record at `DIND[s]` (kind `3` inductive, `CI.indSize` words;
`4` constructor, `CI.ctorSize`; `5` recursor, `CI.recSize` and its `Rule.size`-word rules; the layout of
`EREC`'s records) copied into `EREC`, its slices too. -/
-- con-ron: none — copies the front's records into `EREC` (the twin's `checkDecl` takes the front's values as they are)
@[no_expose] def indRecCopy : FunDecl := lfn (s) locals (k, q, z, r, n, p, ez) {
  k := DIND.u64[s];
  q := call erec_alloc(DIND.u64[s + ⟪CI.cv + CV.lpsLen⟫]);
  z := call dind_copy(q, DIND.u64[s + ⟪CI.cv + CV.lpsOff⟫], DIND.u64[s + ⟪CI.cv + CV.lpsLen⟫]);
  r := 0;
  if k == 3 { n := ⟪CI.indSize⟫ } else if k == 4 { n := ⟪CI.ctorSize⟫ } else if k == 5 {
    n := ⟪CI.recSize⟫;
    if DIND.u64[s + ⟪CI.recRulesLen⟫] >= 144115188075855872 { abort };
    r := call erec_alloc(⟪Rule.size⟫ * DIND.u64[s + ⟪CI.recRulesLen⟫]);
    z := call dind_copy(r, DIND.u64[s + ⟪CI.recRulesOff⟫], ⟪Rule.size⟫ * DIND.u64[s + ⟪CI.recRulesLen⟫])
  } else { abort };
  p := call erec_alloc(n);
  z := call dind_copy(p, s, n);
  ez := call erec_put(p + ⟪CI.cv + CV.lpsOff⟫, q);
  if k == 5 { ez := call erec_put(p + ⟪CI.recRulesOff⟫, r)};
  return p
}

/-- `ind_copy_go(o, bo, bl)`: the records the pointers `DIND[bo‥bo + bl)` name, copied, their
`EREC` pointers to `EREC[o‥]`. -/
-- con-ron: none — copies the front's records into `EREC` (the twin's `checkDecl` takes the front's values as they are)
@[no_expose] def indCopyGo : FunDecl := lfn (o, bo, bl) locals (p, u, ez) {
  if bl == 0 { return 0 };
  p := call ind_rec_copy(DIND.u64[bo]);
  ez := call erec_put(o, p);
  u := call ind_copy_go(o + 1, bo + 1, bl - 1);
  return 0
}

/-- `ind_block_to_erec(i)`: the block of `DECL` record `i` (kind `6`) as an `EREC` slice. -/
-- con-ron: none — copies the front's records into `EREC` (the twin's `checkDecl` takes the front's values as they are)
@[no_expose] def indBlockToErec : FunDecl := lfn (i) locals (bo, bl, o, u) {
  bo := DECL.u64[3 + 8 * i];
  bl := DECL.u64[4 + 8 * i];
  o := call erec_alloc(bl);
  u := call ind_copy_go(o, bo, bl);
  return (o, bl)
}

/-! ## `check_decl_kind`, `check_decl` -/

/-- `check_decl_kind(i, vis, bo, bl)`: `checkDeclKind` on record `i` (an inductive block's records
already copied into `EREC`: the slice `(bo, bl)`, `check_decl`'s). -/
-- con-ron: ConRon/Arena/CheckDecl.lean:74-158 ConRon.Arena.checkDeclKind
@[no_expose, l_impl ConRon.Arena.checkDeclKind]
def checkDeclKindL : FunDecl := lfn (i, vis, bo, bl) locals (k, np, v) {
  k := DECL.u64[1 + 8 * i];
  if k == 6 {
    np := DECL.u64[5 + 8 * i];
    v := call check_ind_decl(vis, bo, bl, np);
    return v
  };
  if k == 1 { v := call check_decl_axiom(i, vis); return v };
  if k == 2 { v := call check_decl_defn(i, vis); return v };
  if k == 3 { v := call check_decl_thm(i, vis); return v };
  if k == 4 { v := call check_decl_opaque(i, vis); return v };
  if k == 5 { v := call check_decl_quot(i, vis); return v };
  abort
}

/-- `check_decl(i, vis)`: `checkDecl` on record `i`: an inductive block's records copied into
`EREC` (`ind_block_to_erec`), the declaration's own checks (`check_decl_kind`), the caches flushed,
then the reserved names' check (`basis_names_ok`; its failure `basis_names_error`'s reason). -/
-- con-ron: ConRon/Arena/CheckDecl.lean:160-173 ConRon.Arena.checkDecl
@[no_expose, l_impl ConRon.Arena.checkDecl]
def checkDeclL : FunDecl := lfn (i, vis) locals (k, bo, bl, v, z, ok, e) {
  k := DECL.u64[1 + 8 * i];
  bo := 0;
  bl := 0;
  if k == 6 { (bo, bl) := call ind_block_to_erec(i) };
  v := call check_decl_kind(i, vis, bo, bl);
  z := call flush_caches();
  ok := call basis_names_ok(k, DECL.u64[2 + 8 * i] & 4294967295, bo, bl);
  if ok == 0 {
    e := call basis_names_error(k, bo, bl);
    -- the twin's `fail e`: the reject at the reason `e` (one of `basis_names_error`'s)
    if e == ⟪R_RESERVED_BASIS_NAME_THE⟫ { fail R_RESERVED_BASIS_NAME_THE };
    if e == ⟪R_RESERVED_BASIS_NAME_IN⟫ { fail R_RESERVED_BASIS_NAME_IN };
    fail R_RESERVED_BASIS_NAME
  };
  return v
}

/-! ## The program -/

/-- This module's functions. -/
def declStepFns : Prog :=
  [("dlp_copy", dlpCopy), ("erec_ci", erecCi),
   ("dind_copy", dindCopy), ("ind_rec_copy", indRecCopy), ("ind_copy_go", indCopyGo),
   ("ind_block_to_erec", indBlockToErec), ("check_decl_kind", checkDeclKindL),
   ("check_decl", checkDeclL)]

/-- The step's program: this module, the arms (`DeclArms*.lean`, with their ROM stubs and the
master functions lane `induct`'s program lacks), lane `induct`'s stage (with its stubs, but for
the two the arms provide: `L.Ind.armsReplaced`). -/
def declStepProg : Prog := declStepFns ++ L.Ind.declArmsAll ++ L.Ind.indProgArms

end L.Arena
