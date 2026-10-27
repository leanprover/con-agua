import ConAgua.Census.Attr
import ConAgua.Layout

/-!
# The fields of an `inductive` line (lane `induct`, worker I)

A declaration line `{"inductive":{…}}` is recognised and validated by Stage B (`scan_ind_decl`,
`pl = 25` in `rec_decl_line`); this second pass reads its contents, as `FieldsDecl.lean` does for
the other declaration kinds, into **records in two front-owned scratch arrays** (both reset per
line by `if_reset()`, word `0` of each is its top: the next record goes at `1 + top`, every
pointer below is an absolute index):

* `IFR` (70): the fixed-size records of the block's three lists. A list is a run of consecutive
  records `(off, cnt)` (record `j` at `off + size · j`): nothing is allocated in `IFR` while a
  list is read, the nested lists go to `IFL`.
* `IFL` (71): word lists (a type's constructor name ids) and the 3-word rule records; later the
  apply step's own lists (`IndApply.lean`).

| record (con-leche) | array | words |
|---|---|---|
| the block (`DeclRec.ind`), kind 4 | `IFR`, 6 | `types.off, types.cnt, ctors.off, ctors.cnt, recs.off, recs.cnt` |
| `IndTypeRec`, kind 0 | `IFR`, 11 | `name, lps, type, ctors.off, ctors.len, isRec, isReflexive, isUnsafe, numIndices, numNested, numParams` |
| `IndCtorRec`, kind 1 | `IFR`, 10 | `name, lps, type, isUnsafe, numFields, numParams, hasCidx, cidx, hasInduct, induct` |
| `IndRecRec`, kind 2 | `IFR`, 11 | `name, lps, type, isUnsafe, k, numIndices, numMinors, numMotives, numParams, rules.off, rules.cnt` |
| `RuleRec`, kind 3 | `IFL`, 3 | `ctor, nfields, rhs` |

Numbers are export ids or counts as `read_nat` reads them; `lps` is the input position of the
`levelParams` list's `[` (read again by the apply step, as `lp_put` does); a type's `ctors` is an
`IFL` slice of name ids; Booleans are `0`/`1`; `cidx`/`induct` are `Option Nat` as a flag and a
value. The block-level `all` and `isUnsafe` are read past and dropped, as con-leche does.

The pass trusts the validator (no `seen` masks, no key-set check) and **aborts** wherever the line
is not what the validator accepted, and on a number of more than 18 digits (`NONE`: a capacity
abort; con-leche reads any length).

The functions: `if_reset()`, `ifr_alloc(n)`, `ifl_alloc(n)`, `ifl_push(x)`, `fld_alloc(kind, n)`,
`fld_put(kind, p, s, x)`, `ind_size(kind)`, `ind_slot(kind, k)`, `ifl_ids(v)`, `ind_num`,
`ind_bool`, `ind_nlist`, `ind_member(kind, p, ks, k, v)`, `ind_obj(i, kind, p)`, `ind_list(v, sub)`, `ind_fields(v)`.
-/

open L.Arena

namespace L.Front.Ind

open L.Front

/-! ## The scratch arrays -/

/-- `if_reset()`: both scratch arrays empty. -/
-- con-ron: none — L scratch-array plumbing (the twin builds `List`s/`Array`s)
def ifReset : FunDecl := lfn () {
  if len(IFR.u64) == 0 || len(IFL.u64) == 0 { abort };
  IFR.u64[0] := 0;
  IFL.u64[0] := 0;
  return 0
}

/-- `ifr_alloc(n)`: `n` words of `IFR` (not cleared); their absolute index. -/
-- con-ron: none — L scratch-array plumbing (the twin builds `List`s/`Array`s)
def ifrAlloc : FunDecl := lfn (n) locals (o) {
  if len(IFR.u64) == 0 { abort };
  o := IFR.u64[0] + 1;
  if len(IFR.u64) < o { abort R_CAP_TABLE };
  if len(IFR.u64) - o < n { abort R_CAP_TABLE };
  IFR.u64[0] := o - 1 + n;
  return o
}

/-- `ifl_alloc(n)`: `n` words of `IFL` (not cleared); their absolute index. -/
-- con-ron: none — L scratch-array plumbing (the twin builds `List`s/`Array`s)
def iflAlloc : FunDecl := lfn (n) locals (o) {
  if len(IFL.u64) == 0 { abort };
  o := IFL.u64[0] + 1;
  if len(IFL.u64) < o { abort R_CAP_TABLE };
  if len(IFL.u64) - o < n { abort R_CAP_TABLE };
  IFL.u64[0] := o - 1 + n;
  return o
}

/-- `ifl_push(x)`: `x` appended to `IFL`; its index. -/
-- con-ron: none — L scratch-array plumbing (the twin builds `List`s/`Array`s)
def iflPush : FunDecl := lfn (x) locals (o) {
  o := call ifl_alloc(1);
  IFL.u64[o] := x;
  return o
}

/-- `fld_alloc(kind, n)`: a record of kind `kind` (`3`, a rule, in `IFL`; else in `IFR`). -/
-- con-ron: none — L scratch-array plumbing (the twin builds `List`s/`Array`s)
def fldAlloc : FunDecl := lfn (kind, n) locals (o) {
  if kind == 3 { o := call ifl_alloc(n); return o };
  o := call ifr_alloc(n);
  return o
}

/-- `fld_put(kind, p, s, x)`: word `s` of the record of kind `kind` at `p` is `x`. -/
-- con-ron: none — L scratch-array plumbing (the twin builds `List`s/`Array`s)
def fldPut : FunDecl := lfn (kind, p, s, x) {
  if kind == 3 { IFL.u64[p + s] := x; return 0 };
  IFR.u64[p + s] := x;
  return 0
}

/-- `ind_size(kind)`: the record size of each kind. -/
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:2397-2401 ConLeche.Frontend.scanIndDecl
def indSize : FunDecl := lfn (kind) {
  if kind == 0 || kind == 2 { return 11 };
  if kind == 1 { return 10 };
  if kind == 3 { return 3 };
  return 6
}

/-! ## The keys

`ind_slot(kind, k)` → `(how, slot, sub)`: how the value of key `k` (Stage B's key codes) in a
record of kind `kind` is read, and where it goes. `how`: `1` a number, `2` a Boolean, `3` a
`levelParams` list (its position), `4` a number list read past (`all`), `5` a list of name ids
(into `IFL`, slots `slot`, `slot + 1`), `6` an optional number (flag at `slot`, value at
`slot + 1`), `7` a list of records of kind `sub` (slots `slot`, `slot + 1`), `8` a Boolean read
past; `0` a key the record cannot have (aborts). -/
/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:2397-2401 ConLeche.Frontend.scanIndDecl -/
def indSlot : FunDecl := lfn (kind, k) {
  if k == 34 { if kind <= 2 { return (1, 0, 0) } };  -- `name`
  if k == 61 { if kind <= 2 { return (1, 2, 0) } };  -- `type`
  if k == 31 { if kind <= 2 { return (3, 1, 0) } };  -- `levelParams`
  if kind == 0 {
    if k == 1 { return (4, 0, 0) };    -- `all`
    if k == 11 { return (5, 3, 0) };   -- `ctors`
    if k == 24 { return (2, 5, 0) };   -- `isRec`
    if k == 25 { return (2, 6, 0) };   -- `isReflexive`
    if k == 26 { return (2, 7, 0) };   -- `isUnsafe`
    if k == 40 { return (1, 8, 0) };   -- `numIndices`
    if k == 43 { return (1, 9, 0) };   -- `numNested`
    if k == 44 { return (1, 10, 0) };  -- `numParams`
    return (0, 0, 0)
  };
  if kind == 1 {
    if k == 8 { return (6, 6, 0) };    -- `cidx`
    if k == 22 { return (6, 8, 0) };   -- `induct`
    if k == 26 { return (2, 3, 0) };   -- `isUnsafe`
    if k == 39 { return (1, 4, 0) };   -- `numFields`
    if k == 44 { return (1, 5, 0) };   -- `numParams`
    return (0, 0, 0)
  };
  if kind == 2 {
    if k == 1 { return (4, 0, 0) };    -- `all`
    if k == 26 { return (2, 3, 0) };   -- `isUnsafe`
    if k == 27 { return (2, 4, 0) };   -- `k`
    if k == 40 { return (1, 5, 0) };   -- `numIndices`
    if k == 41 { return (1, 6, 0) };   -- `numMinors`
    if k == 42 { return (1, 7, 0) };   -- `numMotives`
    if k == 44 { return (1, 8, 0) };   -- `numParams`
    if k == 53 { return (7, 9, 3) };   -- `rules`
    return (0, 0, 0)
  };
  if kind == 3 {
    if k == 10 { return (1, 0, 0) };   -- `ctor`
    if k == 36 { return (1, 1, 0) };   -- `nfields`
    if k == 52 { return (1, 2, 0) };   -- `rhs`
    return (0, 0, 0)
  };
  if k == 1 { return (4, 0, 0) };      -- the block's `all`
  if k == 26 { return (8, 0, 0) };     -- the block's `isUnsafe`
  if k == 63 { return (7, 0, 0) };     -- `types`
  if k == 11 { return (7, 2, 1) };     -- `ctors`
  if k == 50 { return (7, 4, 2) };     -- `recs`
  return (0, 0, 0)
}

/-! ## Values -/

def iflIdsLoop : Stmt := lblk (v, i, o, cnt, c, e, x) {
  while 0 == 0 {
    if len(IN.u8) <= i { return (o, cnt) };
    c := IN.u8[i];
    if c == 93 { return (o, cnt) };
    if 48 <= c && c <= 57 {
      e := call num_end(i);
      if e <= i { abort };
      x := call read_nat(i, e);
      if x == 18446744073709551615 { abort R_LONG_NUMBER };
      x := call ifl_push(x);
      cnt += 1;
      i := e
    } else {
      i += 1
    }
  }
}

/-- `ifl_ids(v)`: the number list whose `[` is at `v`, its items appended to `IFL`;
`(off, cnt)`. -/
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:2397-2401 ConLeche.Frontend.scanIndDecl
def iflIds : FunDecl := lfn (v) locals (i, o, cnt, c, e, x) {
  o := call ifl_alloc(0);
  i := v + 1;
  ⟪iflIdsLoop⟫;
  return (0, 0)
}

/-- `ind_num(kind, p, ks, v, h, s)`: a number value at `v` (key quote at `ks`) into slot `s` of the
record (`h = 6`: an optional number, its flag at `s`, the number at `s + 1`); the end. -/
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:2397-2401 ConLeche.Frontend.scanIndDecl
def indNum : FunDecl := lfn (kind, p, ks, v, h, s) locals (e, x, o) {
  e := call slot_nat(ks, v);
  x := call read_nat(v, e);
  if x == 18446744073709551615 { abort R_LONG_NUMBER };
  if h == 6 { o := call fld_put(kind, p, s, 1); s += 1 };
  o := call fld_put(kind, p, s, x);
  return e
}

/-- `ind_bool(kind, p, v, h, s)`: a Boolean value at `v` into slot `s` (`h = 8`: read past);
the end. -/
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:2397-2401 ConLeche.Frontend.scanIndDecl
def indBool : FunDecl := lfn (kind, p, v, h, s) locals (o, x, e) {
  (o, x, e) := call scan_bool(v);
  if o == 0 { abort };
  if h == 2 { o := call fld_put(kind, p, s, x) };
  return e
}

/-- `ind_nlist(kind, p, v, h, s)`: a number list at `v`: its position into slot `s` (`h = 3`),
read past (`h = 4`), or its items appended to `IFL` and the slice into slots `s`, `s + 1`
(`h = 5`); the end. -/
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:2397-2401 ConLeche.Frontend.scanIndDecl
def indNList : FunDecl := lfn (kind, p, v, h, s) locals (e, x, o, c) {
  (e, x) := call scan_nat_list(v);
  if h == 3 { o := call fld_put(kind, p, s, v) };
  if h == 5 {
    (o, c) := call ifl_ids(v);
    x := call fld_put(kind, p, s, o);
    x := call fld_put(kind, p, s + 1, c)
  };
  return e
}

/-- `ind_member(kind, p, ks, k, v)`: the member with key `k` (key quote at `ks`, value at `v`) of
the record of kind `kind` at `p`, read into it; the end of the value. -/
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:2397-2401 ConLeche.Frontend.scanIndDecl
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:1698-1702 ConLeche.Frontend.scanIndType
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:1845-1851 ConLeche.Frontend.scanIndCtor
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:1523-1527 ConLeche.Frontend.scanIndRec
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:1349-1353 ConLeche.Frontend.scanRule
@[l_impl ConLeche.Frontend.scanIndDecl ConLeche.Frontend.scanIndType ConLeche.Frontend.scanIndCtor
  ConLeche.Frontend.scanIndRec ConLeche.Frontend.scanRule]
def indMember : FunDecl := lfn (kind, p, ks, k, v) locals (h, s, sub, e, x, o, c) {
  (h, s, sub) := call ind_slot(kind, k);
  if h == 1 || h == 6 { e := call ind_num(kind, p, ks, v, h, s); return e };
  if h == 2 || h == 8 { e := call ind_bool(kind, p, v, h, s); return e };
  if h == 3 || h == 4 || h == 5 { e := call ind_nlist(kind, p, v, h, s); return e };
  if h == 7 {
    if v <= ks { abort };
    (o, c, e) := call ind_list(v, sub);
    x := call fld_put(kind, p, s, o);
    x := call fld_put(kind, p, s + 1, c);
    return e
  };
  abort
}

def indObjLoop : Stmt := lblk (i, kind, p, w, tag, ks, k, v, e) {
  while 0 == 0 {
    (tag, ks, w, k, v) := call next_member(i, w);
    if tag == 0 { abort };
    if tag == 1 { return ks + 1 };
    e := call ind_member(kind, p, ks, k, v);
    if e <= ks { abort };
    i := e;
    w := 0
  }
}

/-- `ind_obj(i, kind, p)`: the object whose `{` is at `i`, read into the record of kind `kind`
at `p`; the position after its `}`. -/
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:2397-2401 ConLeche.Frontend.scanIndDecl
def indObj : FunDecl := lfn (i, kind, p) locals (w, tag, ks, k, v, e) {
  i += 1;
  w := 1;
  ⟪indObjLoop⟫;
  return 0
}

def indListLoop : Stmt := lblk (v, sub, i, o, cnt, c, e, q, sz) {
  while 0 == 0 {
    if len(IN.u8) <= i { abort };
    c := IN.u8[i];
    if c == 93 { return (o, cnt, i + 1) };
    if c == 123 {
      q := call fld_alloc(sub, sz);
      if sub == 1 { IFR.u64[q + 6] := 0; IFR.u64[q + 8] := 0 };
      e := call ind_obj(i, sub, q);
      if e <= i { abort };
      cnt += 1;
      i := e
    } else {
      i += 1
    }
  }
}

/-- `ind_list(v, sub)`: the list of objects whose `[` is at `v`, each read into a fresh record of
kind `sub` (consecutive records; a constructor record's two optional fields start absent, their
flags `0`); `(off, cnt, end)`. -/
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:1732-1736 ConLeche.Frontend.scanIndTypes
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:1881-1885 ConLeche.Frontend.scanIndCtors
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:1557-1561 ConLeche.Frontend.scanIndRecs
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:1383-1387 ConLeche.Frontend.scanRules
@[l_impl ConLeche.Frontend.scanIndTypes ConLeche.Frontend.scanIndCtors
  ConLeche.Frontend.scanIndRecs ConLeche.Frontend.scanRules]
def indList : FunDecl := lfn (v, sub) locals (i, o, cnt, c, e, q, sz) {
  if len(IN.u8) <= v { abort };
  if IN.u8[v] != 91 { abort };
  sz := call ind_size(sub);
  o := call fld_alloc(sub, 0);
  i := v + 1;
  ⟪indListLoop⟫;
  return (0, 0, 0)
}

/-- `ind_fields(v)`: the `inductive` object whose `{` is at `v`, read (the scratch arrays reset
first); its three lists `(types.off, types.cnt, ctors.off, ctors.cnt, recs.off, recs.cnt)`. -/
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:2397-2401 ConLeche.Frontend.scanIndDecl
@[l_impl ConLeche.Frontend.scanIndDecl]
def indFields : FunDecl := lfn (v) locals (p, e) {
  e := call if_reset();
  p := call ifr_alloc(6);
  e := call ind_obj(v, 4, p);
  return (IFR.u64[p], IFR.u64[p + 1], IFR.u64[p + 2], IFR.u64[p + 3], IFR.u64[p + 4],
    IFR.u64[p + 5])
}

/-- The fields pass. -/
def indFieldsFns : Prog :=
  [("if_reset", ifReset), ("ifr_alloc", ifrAlloc), ("ifl_alloc", iflAlloc), ("ifl_push", iflPush),
   ("fld_alloc", fldAlloc), ("fld_put", fldPut), ("ind_size", indSize), ("ind_slot", indSlot),
   ("ifl_ids", iflIds), ("ind_num", indNum), ("ind_bool", indBool), ("ind_nlist", indNList),
   ("ind_member", indMember), ("ind_obj", indObj), ("ind_list", indList),
   ("ind_fields", indFields)]

/-- A stub with `k` parameters (the closure check's stand-in for a callee of another file). -/
-- con-ron: none — a closure-check stub for a callee in another file
def stub (k : Nat) : FunDecl := ⟨k, k, .abort (.const 0)⟩

end L.Front.Ind
