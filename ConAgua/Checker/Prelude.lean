import ConAgua.Checker.Hoist
import ConRon.Arena.Frontend.PreludeText
import ConAgua.Compiler.Compile
import ConAgua.Arena.GrindAttr
import ConAgua.Census.Attr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen

/-!
# The prelude stages: `builtin_prelude()`, `prepare_prelude()` (lane `integrate`)

**`builtin_prelude()`** is the twin's `builtinPreludeE`: `parseBytes preludeText` with a fresh
parse state, into the same stores. In L it runs **the frontend itself on the prelude bytes**: the
functions reachable from `front_run` that read the input (byte array `0`), or call one that does,
are copied with `preFn` (`pre_<name>`; `scripts/checker_prog.py` lists them in
`ConAgua/Checker/Prog.lean`), reading the program's constant `preludeBytes` instead of the input
(`ld8 0 i` becomes `ldc preludeBytes i`, `len8 0` the constant `preludeLenW`). Everything else is
shared, the parse state included: `builtin_prelude` runs `pre_front_run` on the stream's own id
tables and declaration arrays (empty at that point), aborts if a line did not apply (the twin's
`.error`), records the number of prelude records in `CTL[240]`, and resets the id tables
(`front_reset`: the three dense sizes to `0`, the sparse maps cleared). The prelude's records stay
in `DECL[0‥P)`: `front_run` then runs from the parse state with empty id tables and the prelude's
records, and appends the stream's after them (the twin's second `parseBytes` starts from an empty
`decls` and only ever pushes to it, `Front/DeclsPre.lean`, so its records are `DECL[P‥)`). Proofs: the input renaming is a simulation (a copied
function on memory `m` runs as the original on `m` with the input replaced by `preludeBytes`);
the frontend's refinement then gives `parseBytes preludeText`.

**`prepare_prelude()`** is `preparePrelude pre r.decls` on `DECL` = the prelude's `P = CTL[240]`
records, then the stream's: `frontOf` (each prelude record, in order, replaced by the first stream record that declares its
key, which leaves the stream), then the ground hoist `hoistNatOpGround` (`hoist_nat_op_ground`,
`ConAgua/Checker/Hoist.lean`), which reorders the stream when a pinned `Nat` operation precedes
its ground. Then `DECL` is rewritten in the prepared order.

`preludeBytes` is the twin's `preludeText` (`preludeBytes_eq`, by the kernel).
-/

namespace L.Checker

open L L.Arena L.Ind L.Compiler L.Front L.Front.Ind

/-! ## The prelude bytes -/

/-- The prelude's bytes, as the program's constant data (the twin's 62 chunks, concatenated). -/
def preludeBytes : List UInt8 := List.flatten
  [ConRon.Arena.Frontend.P00.data.toList, ConRon.Arena.Frontend.P01.data.toList,
   ConRon.Arena.Frontend.P02.data.toList, ConRon.Arena.Frontend.P03.data.toList,
   ConRon.Arena.Frontend.P04.data.toList, ConRon.Arena.Frontend.P05.data.toList,
   ConRon.Arena.Frontend.P06.data.toList, ConRon.Arena.Frontend.P07.data.toList,
   ConRon.Arena.Frontend.P08.data.toList, ConRon.Arena.Frontend.P09.data.toList,
   ConRon.Arena.Frontend.P10.data.toList, ConRon.Arena.Frontend.P11.data.toList,
   ConRon.Arena.Frontend.P12.data.toList, ConRon.Arena.Frontend.P13.data.toList,
   ConRon.Arena.Frontend.P14.data.toList, ConRon.Arena.Frontend.P15.data.toList,
   ConRon.Arena.Frontend.P16.data.toList, ConRon.Arena.Frontend.P17.data.toList,
   ConRon.Arena.Frontend.P18.data.toList, ConRon.Arena.Frontend.P19.data.toList,
   ConRon.Arena.Frontend.P20.data.toList, ConRon.Arena.Frontend.P21.data.toList,
   ConRon.Arena.Frontend.P22.data.toList, ConRon.Arena.Frontend.P23.data.toList,
   ConRon.Arena.Frontend.P24.data.toList, ConRon.Arena.Frontend.P25.data.toList,
   ConRon.Arena.Frontend.P26.data.toList, ConRon.Arena.Frontend.P27.data.toList,
   ConRon.Arena.Frontend.P28.data.toList, ConRon.Arena.Frontend.P29.data.toList,
   ConRon.Arena.Frontend.P30.data.toList, ConRon.Arena.Frontend.P31.data.toList,
   ConRon.Arena.Frontend.P32.data.toList, ConRon.Arena.Frontend.P33.data.toList,
   ConRon.Arena.Frontend.P34.data.toList, ConRon.Arena.Frontend.P35.data.toList,
   ConRon.Arena.Frontend.P36.data.toList, ConRon.Arena.Frontend.P37.data.toList,
   ConRon.Arena.Frontend.P38.data.toList, ConRon.Arena.Frontend.P39.data.toList,
   ConRon.Arena.Frontend.P40.data.toList, ConRon.Arena.Frontend.P41.data.toList,
   ConRon.Arena.Frontend.P42.data.toList, ConRon.Arena.Frontend.P43.data.toList,
   ConRon.Arena.Frontend.P44.data.toList, ConRon.Arena.Frontend.P45.data.toList,
   ConRon.Arena.Frontend.P46.data.toList, ConRon.Arena.Frontend.P47.data.toList,
   ConRon.Arena.Frontend.P48.data.toList, ConRon.Arena.Frontend.P49.data.toList,
   ConRon.Arena.Frontend.P50.data.toList, ConRon.Arena.Frontend.P51.data.toList,
   ConRon.Arena.Frontend.P52.data.toList, ConRon.Arena.Frontend.P53.data.toList,
   ConRon.Arena.Frontend.P54.data.toList, ConRon.Arena.Frontend.P55.data.toList,
   ConRon.Arena.Frontend.P56.data.toList, ConRon.Arena.Frontend.P57.data.toList,
   ConRon.Arena.Frontend.P58.data.toList, ConRon.Arena.Frontend.P59.data.toList,
   ConRon.Arena.Frontend.P60.data.toList, ConRon.Arena.Frontend.P61.data.toList]

set_option maxRecDepth 100000 in
/-- **L's prelude is the twin's** (`builtinPreludeE` parses `preludeText`; DESIGN.md lane
`romload`, "the prelude is not free in `TwinAccepts`"). About 15 s in the kernel. -/
theorem preludeBytes_eq : preludeBytes = ConRon.Arena.Frontend.preludeText.data.toList := by
  decide +kernel

/-! ## The frontend, reading the prelude's bytes -/

/-- The prelude's length, as a word. -/
def preludeLenW : Word := UInt64.ofNat preludeBytes.length

/-- A block's byte source, renamed: the input's bytes are the prelude's. -/
def preB : BSrc → BSrc
  | .arr a => if a = 0 then .rom preludeBytes else .arr a
  | .rom d => .rom d

/-- An expression of the frontend, renamed: the input's bytes are the prelude's. -/
def preE : Expr → Expr
  | .ld8 a i => if a = 0 then .ldc preludeBytes (preE i) else .ld8 a (preE i)
  | .len8 a => if a = 0 then .const preludeLenW else .len8 a
  | .ld64 a i => .ld64 a (preE i)
  | .bin op a b => .bin op (preE a) (preE b)
  | .cmpw c a b => .cmpw c (preE a) (preE b)
  | .ldc d i => .ldc d (preE i)
  | .ld64t a t i => .ld64t a (preE t) (preE i)
  | .len64t a t => .len64t a (preE t)
  | .ld8x8 b i => .ld8x8 (preB b) (preE i)
  | e => e

def preW : WArr → WArr
  | .plain a => .plain a
  | .tier a t => .tier a (preE t)

def preC : Cond → Cond
  | .cmp c a b => .cmp c (preE a) (preE b)
  | .and p q => .and (preC p) (preC q)
  | .or p q => .or (preC p) (preC q)
  | .not p => .not (preC p)

/-- A callee of the frontend, renamed if it is copied (its name code is in `t`). -/
def preName (t : NTree) (f : String) : String :=
  match t.find (nameCode f) with
  | some _ => "pre_" ++ f
  | none => f

def preS (t : NTree) : Stmt → Stmt
  | .set x e => .set x (preE e)
  | .st8 a i e => .st8 a (preE i) (preE e)
  | .st64 a i e => .st64 a (preE i) (preE e)
  | .seq s u => .seq (preS t s) (preS t u)
  | .ite c s u => .ite (preC c) (preS t s) (preS t u)
  | .while c s => .while (preC c) (preS t s)
  | .ret es => .ret (es.map preE)
  | .call xs f args => .call xs (preName t f) (args.map preE)
  | .gset g e => .gset g (preE e)
  | .st64t a t i e => .st64t a (preE t) (preE i) (preE e)
  | .copy64 d di s si n => .copy64 (preW d) (preE di) (preW s) (preE si) (preE n)
  | .copy8w d di s si n => .copy8w (preW d) (preE di) (preB s) (preE si) (preE n)
  | .scan8 x s i e c => .scan8 x (preB s) (preE i) (preE e) c
  | s => s

/-- **A frontend function, reading the prelude's bytes** (`t`: the copied functions). -/
-- con-ron: none — a renaming of the frontend's L code (the twin's `parseBytes` runs on any bytes)
def preFn (t : NTree) (d : FunDecl) : FunDecl := { d with body := preS t d.body }

/-- The tree of a list of names (`preName`'s argument). -/
def nameTree (fs : List String) : NTree :=
  fs.foldl (fun t f => (t.insert (nameCode f) 0).getD t) .leaf

/-! ## `builtin_prelude()` -/

/-- `nid_sp_clear()` etc.: the id tables' sparse maps cleared. -/
-- con-ron: none — the memo library (open addressing over fixed arrays; the twin's `Std.HashMap` caches)
def nidSpClear : FunDecl := memoClearG (L.Front.spS L.Front.NID)
-- con-ron: none — the memo library (open addressing over fixed arrays; the twin's `Std.HashMap` caches)
def lidSpClear : FunDecl := memoClearG (L.Front.spS L.Front.LID)
-- con-ron: none — the memo library (open addressing over fixed arrays; the twin's `Std.HashMap` caches)
def eidSpClear : FunDecl := memoClearG (L.Front.spS L.Front.EID)

/-- `front_reset()`: the id tables emptied (their dense sizes `0`, their sparse maps cleared);
the declaration records stay. -/
-- con-ron: ConRon/Arena/Frontend/ExportC.lean:490-499 ConRon.Arena.Frontend.StateD.init
def frontResetL : FunDecl := lfn () locals (z) {
  CTL.u64[70] := 0;
  CTL.u64[71] := 0;
  CTL.u64[72] := 0;
  z := call nid_sp_clear();
  z := call lid_sp_clear();
  z := call eid_sp_clear();
  return 0
}

/-- `builtin_prelude()`: `builtinPreludeE` — the frontend on the prelude's bytes; the number of
prelude records into `CTL[240]`; the id tables emptied. -/
-- con-ron: ConRon/Arena/Frontend/Prelude.lean:39-52 ConRon.Arena.Frontend.builtinPreludeE
@[l_impl ConRon.Arena.Frontend.builtinPreludeE]
def builtinPreludeL : FunDecl := lfn () locals (r, z) {
  r := call pre_front_run();
  if r != 0 { abort };
  CTL.u64[240] := DECL.u64[0];
  z := call front_reset();
  return 0
}

/-! ## `prepare_prelude()` -/

/-- `decl_declares_go(o, c, n, j)`: a block member `DIND[o + j ‥ o + c)` (a `DIND` record
pointer) is named `n`. -/
-- con-ron: ConRon/Arena/Frontend/Prepare.lean:73-75 ConRon.Arena.Frontend.declares
def declDeclaresGoL : FunDecl := lfn (o, c, n, j) locals (r) {
  if c <= j { return 0 };
  if DIND.u64[DIND.u64[o + j] + 1] == n { return 1 };
  r := call decl_declares_go(o, c, n, j + 1);
  return r
}

/-- `decl_declares(i, n)`: `declares n ds[i]` — record `i`'s names contain `n` (an inductive
block's: its members', `DIND` records' names). -/
-- con-ron: ConRon/Arena/Frontend/Prepare.lean:73-75 ConRon.Arena.Frontend.declares
@[l_impl ConRon.Arena.Frontend.declares]
def declDeclaresL : FunDecl := lfn (i, n) locals (x, r) {
  x := 1 + 8 * i;
  if DECL.u64[x] != 6 {
    if DECL.u64[x + 1] == n { return 1 };
    return 0
  };
  r := call decl_declares_go(DECL.u64[x + 2], DECL.u64[x + 3], n, 0);
  return r
}

/-- `decl_key(i)`: `preludeKey ds[i]` — the first name, or the anonymous name. -/
-- con-ron: ConRon/Arena/Frontend/Prepare.lean:52-59 ConRon.Arena.Frontend.preludeKey
@[l_impl ConRon.Arena.Frontend.preludeKey]
def declKeyL : FunDecl := lfn (i) locals (x, r) {
  x := 1 + 8 * i;
  if DECL.u64[x] != 6 { return DECL.u64[x + 1] };
  if DECL.u64[x + 3] != 0 {
    return DIND.u64[DIND.u64[DECL.u64[x + 2]] + 1]
  };
  r := call intern_nanon();
  return r
}

/-- `prep_find(mk, n, key, j)`: the first record `j' ∈ [j, n)` not marked in `mk` that declares
`key`, plus one; `0` if there is none (`pick`'s `findIdx` on the stream not yet picked). -/
-- con-ron: ConRon/Arena/Frontend/Prepare.lean:77-90 ConRon.Arena.Frontend.pick
@[l_impl ConRon.Arena.Frontend.pick]
def prepFindL : FunDecl := lfn (mk, n, key, j) locals (d, r) {
  if n <= j { return 0 };
  if IW.u64[mk + j] == 0 {
    d := call decl_declares(j, key);
    if d != 0 { return j + 1 }
  };
  r := call prep_find(mk, n, key, j + 1);
  return r
}

/-- `prep_front(np, n, ord, mk, a)`: the prelude records `a ‥ np`: each replaced by the first
unmarked stream record declaring its key (which gets marked: it leaves the stream), or kept
(`frontOf`). -/
-- con-ron: ConRon/Arena/Frontend/Prepare.lean:92-101 ConRon.Arena.Frontend.frontOf
@[l_impl ConRon.Arena.Frontend.frontOf]
def prepFrontL : FunDecl := lfn (np, n, ord, mk, a) locals (key, f, r) {
  if np <= a { return 0 };
  key := call decl_key(a);
  f := call prep_find(mk, n, key, np);
  if f != 0 {
    IW.u64[mk + f - 1] := 1;
    IW.u64[ord + a] := f - 1
  } else {
    IW.u64[ord + a] := a
  };
  r := call prep_front(np, n, ord, mk, a + 1);
  return r
}

/-- `prep_rest(n, ord, mk, c, j)`: the unmarked stream records `j ‥ n`, in order, to
`ord[c ..]`; the new `c` (`frontOf`'s rest of the stream, `front ++ rest`). -/
-- con-ron: ConRon/Arena/Frontend/Prepare.lean:126-131 ConRon.Arena.Frontend.prepareD
def prepRestL : FunDecl := lfn (n, ord, mk, c, j) locals (r) {
  if n <= j { return c };
  if IW.u64[mk + j] == 0 { IW.u64[ord + c] := j; c += 1 };
  r := call prep_rest(n, ord, mk, c, j + 1);
  return r
}

/-- `prep_copy_rec(t, q, i, k)`: words `k ‥ 8` of the record at `DECL[q ..]` to `IW[t + 8 i ..]`. -/
-- con-ron: none — L plumbing (the twin's arrays are values: the reordered records are a new array)
def prepCopyRecL : FunDecl := lfn (t, q, i, k) locals (r) {
  if 8 <= k { return 0 };
  IW.u64[t + 8 * i + k] := DECL.u64[q + k];
  r := call prep_copy_rec(t, q, i, k + 1);
  return r
}

/-- `prep_copy(ord, c, t, i)`: the records `ord[i ‥ c)` to `IW[t + 8 i ..]`. -/
-- con-ron: none — L plumbing (the twin's arrays are values: the reordered records are a new array)
def prepCopyL : FunDecl := lfn (ord, c, t, i) locals (z, r) {
  if c <= i { return 0 };
  z := call prep_copy_rec(t, 1 + 8 * IW.u64[ord + i], i, 0);
  r := call prep_copy(ord, c, t, i + 1);
  return r
}

/-- `prep_back_rec(t, i, k)`: words `k ‥ 8` of record `i` from `IW[t + 8 i ..]` back to `DECL`. -/
-- con-ron: none — L plumbing (the twin's arrays are values: the reordered records are a new array)
def prepBackRecL : FunDecl := lfn (t, i, k) locals (r) {
  if 8 <= k { return 0 };
  DECL.u64[1 + 8 * i + k] := IW.u64[t + 8 * i + k];
  r := call prep_back_rec(t, i, k + 1);
  return r
}

/-- `prep_back(t, c, i)`: the records `i ‥ c` from `IW[t ..]` back to `DECL`. -/
-- con-ron: none — L plumbing (the twin's arrays are values: the reordered records are a new array)
def prepBackL : FunDecl := lfn (t, c, i) locals (z, r) {
  if c <= i { return 0 };
  z := call prep_back_rec(t, i, 0);
  r := call prep_back(t, c, i + 1);
  return r
}

/-- `prepare_prelude()`: `preparePrelude pre ds` on `DECL` = the prelude's `P = CTL[240]`
records, then the stream's: the front (`prep_front`), the rest
(`prep_rest`), the ground hoist, then `DECL` rewritten in the prepared order. -/
-- con-ron: ConRon/Arena/Frontend/Prepare.lean:133-140 ConRon.Arena.Frontend.preparePrelude
-- con-ron: ConRon/Arena/Frontend/Prepare.lean:126-131 ConRon.Arena.Frontend.prepareD
@[l_impl ConRon.Arena.Frontend.preparePrelude ConRon.Arena.Frontend.prepareD]
def preparePreludeL : FunDecl := lfn () locals (np, n, ord, mk, z, c, t) {
  np := CTL.u64[240];
  n := DECL.u64[0];
  if n < np { abort };
  if 576460752303423488 <= n { abort };
  ord := call iw_alloc(n);
  mk := call iw_alloc(n);
  z := call hoist_zero(mk, n, 0);
  z := call prep_front(np, n, ord, mk, 0);
  c := call prep_rest(n, ord, mk, np, np);
  ord := call hoist_nat_op_ground(ord, c);
  t := call iw_alloc(8 * c);
  z := call prep_copy(ord, c, t, 0);
  z := call prep_back(t, c, 0);
  DECL.u64[0] := c;
  return 0
}

/-- The prelude stages' functions (`checkerProg` takes them from here). -/
def preludeProg : Prog :=
  [("builtin_prelude", builtinPreludeL), ("front_reset", frontResetL),
   ("nid_sp_clear", nidSpClear), ("lid_sp_clear", lidSpClear), ("eid_sp_clear", eidSpClear),
   ("prepare_prelude", preparePreludeL),
   ("decl_declares", declDeclaresL), ("decl_declares_go", declDeclaresGoL), ("decl_key", declKeyL),
   ("prep_find", prepFindL), ("prep_front", prepFrontL), ("prep_rest", prepRestL),
   ("prep_copy_rec", prepCopyRecL), ("prep_copy", prepCopyL), ("prep_back_rec", prepBackRecL),
   ("prep_back", prepBackL)] ++ hoistProg

/-- The prelude stages' functions in a program. -/
abbrev PrepProg (p : Prog) : Prop := ProgHas p preludeProg

/-- The functions outside the prelude stages that `prepare_prelude` calls (the anonymous name). -/
def prepExtProg : Prog :=
  [("nanon_find", nanonFind), ("nanon_push", nanonPush), ("intern_nanon", internNAnon)]

/-- Those in a program. -/
abbrev PrepExt (p : Prog) : Prop := ProgHas p prepExtProg

/-! ## The models of `prepare_prelude` (generated) -/

set_option experimental.vcgen true
open Std.WP
open scoped Lean.Order

/-- **`decl_declares_go` is its model `pDeclGoW`** (generated; reads only). -/
l_model declDeclaresGo_spec (p : Prog) (hp : PrepProg p)
  fns [hp.get "decl_declares_go" ↦ pDeclGoW ro]
  specs []
  grind [arena_grind]

/-- **`decl_declares` is its model `pDeclW`** (generated; reads only). -/
l_model declDeclares_spec (p : Prog) (hp : PrepProg p)
  fns [hp.get "decl_declares" ↦ pDeclW ro]
  specs [declDeclaresGo_spec p hp n]
  grind [arena_grind]

/-- **`decl_key` is its model `pKeyW`** (generated). -/
l_model declKey_spec (p : Prog) (hp : PrepProg p) (hn : PrepExt p)
  fns [hp.get "decl_key" ↦ pKeyW]
  specs [internNAnon_spec p (hn.get "nanon_find") (hn.get "nanon_push") (hn.get "intern_nanon") n]
  grind [arena_grind]

/-- **`prep_find` is its model `pFindW`** (generated; reads only). -/
l_model prepFind_spec (p : Prog) (hp : PrepProg p)
  fns [hp.get "prep_find" ↦ pFindW ro]
  specs [declDeclares_spec p hp n]
  grind [arena_grind]

/-- **`prep_front` is its model `pFrontW`** (generated). -/
l_model prepFront_spec (p : Prog) (hp : PrepProg p) (hn : PrepExt p)
  fns [hp.get "prep_front" ↦ pFrontW]
  specs [declKey_spec p hp hn n, prepFind_spec p hp n]
  grind [arena_grind] extra [L.st64]

/-- **`prep_rest` is its model `pRestW`** (generated). -/
l_model prepRest_spec (p : Prog) (hp : PrepProg p)
  fns [hp.get "prep_rest" ↦ pRestW]
  specs []
  grind [arena_grind] extra [L.st64]

/-- **`prep_copy_rec` is its model `pCopyRecW`** (generated). -/
l_model prepCopyRec_spec (p : Prog) (hp : PrepProg p)
  fns [hp.get "prep_copy_rec" ↦ pCopyRecW]
  specs []
  grind [arena_grind] extra [L.st64]

/-- **`prep_copy` is its model `pCopyW`** (generated). -/
l_model prepCopy_spec (p : Prog) (hp : PrepProg p)
  fns [hp.get "prep_copy" ↦ pCopyW]
  specs [prepCopyRec_spec p hp n]
  grind [arena_grind]

/-- **`prep_back_rec` is its model `pBackRecW`** (generated). -/
l_model prepBackRec_spec (p : Prog) (hp : PrepProg p)
  fns [hp.get "prep_back_rec" ↦ pBackRecW]
  specs []
  grind [arena_grind] extra [L.st64]

/-- **`prep_back` is its model `pBackW`** (generated). -/
l_model prepBack_spec (p : Prog) (hp : PrepProg p)
  fns [hp.get "prep_back" ↦ pBackW]
  specs [prepBackRec_spec p hp n]
  grind [arena_grind]

/-- **`prepare_prelude` is its model `pPrepW`** (generated). -/
l_model preparePrelude_spec (p : Prog) (hp : PrepProg p) (hn : PrepExt p) (hh : HoistProg p)
    (hx : HoistExt p)
  fns [hp.get "prepare_prelude" ↦ pPrepW]
  specs [iwAlloc_specW p (hx.get "iw_alloc") n, hoistZero_spec p hh n,
    prepFront_spec p hp hn n,
    prepRest_spec p hp n, hoistNatOpGround_spec p hh hx n, prepCopy_spec p hp n, prepBack_spec p hp n]
  grind [arena_grind] extra [L.st64] gen 20

end L.Checker
