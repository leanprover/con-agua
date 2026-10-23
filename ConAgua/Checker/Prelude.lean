import ConAgua.Checker.Entry
import ConAgua.Compiler.WFFast
import ConAgua.Front.IndApply
import ConAgua.Arena.DeclArmsNat
import ConAgua.Checker.Hoist
import ConRon.Arena.Frontend.PreludeText

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
`decls` and only ever pushes to it, so its records are `DECL[P‥)`). Proofs: the input renaming is a simulation (a copied
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

/-- An expression of the frontend, renamed: the input's bytes are the prelude's. -/
def preE : Expr → Expr
  | .ld8 a i => if a = 0 then .ldc preludeBytes (preE i) else .ld8 a (preE i)
  | .len8 a => if a = 0 then .const preludeLenW else .len8 a
  | .ld64 a i => .ld64 a (preE i)
  | .bin op a b => .bin op (preE a) (preE b)
  | .cmpw c a b => .cmpw c (preE a) (preE b)
  | .ldc d i => .ldc d (preE i)
  | e => e

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

/-- `decl_declares(i, n)`: `declares n ds[i]` — record `i`'s names contain `n` (an inductive
block's: its members', `DIND` records' names). -/
-- con-ron: ConRon/Arena/Frontend/Prepare.lean:73-75 ConRon.Arena.Frontend.declares
@[l_impl ConRon.Arena.Frontend.declares]
def declDeclaresL : FunDecl := lfn (i, n) locals (x, o, c, j) {
  x := 1 + 8 * i;
  if DECL.u64[x] != 6 {
    if DECL.u64[x + 1] == n { return 1 };
    return 0
  };
  o := DECL.u64[x + 2];
  c := DECL.u64[x + 3];
  j := 0;
  while j < c {
    if DIND.u64[DIND.u64[o + j] + 1] == n { return 1 };
    j += 1
  };
  return 0
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

/-- `prepare_prelude()`: `preparePrelude pre ds` on `DECL` = the prelude's `P = CTL[240]`
records, then the stream's. -/
-- con-ron: ConRon/Arena/Frontend/Prepare.lean:77-90 ConRon.Arena.Frontend.pick
-- con-ron: ConRon/Arena/Frontend/Prepare.lean:133-140 ConRon.Arena.Frontend.preparePrelude
-- con-ron: ConRon/Arena/Frontend/Prepare.lean:126-131 ConRon.Arena.Frontend.prepareD
-- con-ron: ConRon/Arena/Frontend/Prepare.lean:92-101 ConRon.Arena.Frontend.frontOf
@[l_impl ConRon.Arena.Frontend.preparePrelude ConRon.Arena.Frontend.prepareD
  ConRon.Arena.Frontend.frontOf ConRon.Arena.Frontend.pick]
def preparePreludeL : FunDecl :=
    lfn () locals (np, n, ord, mk, a, key, j, f, d, c, t, i, q, k) {
  np := CTL.u64[240];
  n := DECL.u64[0];
  if n < np { abort };
  if 1152921504606846976 <= n { abort };
  ord := call iw_alloc(n);
  mk := call iw_alloc(n);
  j := 0;
  while j < n { IW.u64[mk + j] := 0; j += 1 };
  a := 0;
  while a < np {
    key := call decl_key(a);
    j := np;
    f := 0;
    while j < n {
      if IW.u64[mk + j] == 0 {
        d := call decl_declares(j, key);
        if d != 0 { f := 1; break }
      };
      j += 1
    };
    if f != 0 {
      IW.u64[mk + j] := 1;
      IW.u64[ord + a] := j
    } else {
      IW.u64[ord + a] := a
    };
    a += 1
  };
  c := np;
  j := np;
  while j < n {
    if IW.u64[mk + j] == 0 { IW.u64[ord + c] := j; c += 1 };
    j += 1
  };
  ord := call hoist_nat_op_ground(ord, c);
  t := call iw_alloc(8 * c);
  i := 0;
  while i < c {
    q := 1 + 8 * IW.u64[ord + i];
    k := 0;
    while k < 8 { IW.u64[t + 8 * i + k] := DECL.u64[q + k]; k += 1 };
    i += 1
  };
  i := 0;
  while i < 8 * c { DECL.u64[1 + i] := IW.u64[t + i]; i += 1 };
  DECL.u64[0] := c;
  return 0
}

/-- The prelude stages' functions (`checkerProg` takes them from here). -/
def preludeProg : Prog :=
  [("builtin_prelude", builtinPreludeL), ("front_reset", frontResetL),
   ("nid_sp_clear", nidSpClear), ("lid_sp_clear", lidSpClear), ("eid_sp_clear", eidSpClear),
   ("prepare_prelude", preparePreludeL),
   ("decl_declares", declDeclaresL), ("decl_key", declKeyL)] ++ hoistProg

end L.Checker
