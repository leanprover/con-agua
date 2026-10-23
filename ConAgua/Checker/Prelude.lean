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
functions reachable from `front_run` that read the input (byte array `0`) or the parse state's id
tables (`NID`, `LID`, `EID`) are copied with `preFn` (`pre_<name>`; `scripts/checker_prog.py` lists
them in `ConAgua/Checker/Prog.lean`), reading the byte array `PRE` (`2`) instead of the input, the
constant `preludeLen` instead of its length, and the id tables `PNID`, `PLID`, `PEID` (dense),
`PNSP`, `PLSP`, `PESP` (sparse) and `CTL[241‥249]` (`preCtl`) instead of the stream's (so the
stream's parse starts with empty id tables, as the twin's second
`parseBytes` does). `builtin_prelude` copies the prelude bytes (`preludeBytes`, a constant of the
program) into `PRE`, runs `pre_front_run`, aborts if a line did not apply (the twin's
`.error`), and records the number of prelude records in `CTL[240]`. The declaration arrays
(`DECL`, `DLP`, `DIND`) are shared: the prelude's records are `DECL[0‥P)`, the stream's follow.

**`prepare_prelude()`** is `preparePrelude pre r.decls`: `frontOf` (each prelude record, in order,
replaced by the first stream record that declares its key, which leaves the stream), then the
ground hoist `hoistNatOpGround` (`hoist_nat_op_ground`, `ConAgua/Checker/Hoist.lean`), which
reorders the stream when a pinned `Nat` operation precedes its ground. Then `DECL` is
rewritten in the prepared order.

`preludeBytes` is the twin's `preludeText` (`preludeBytes_eq`, by the kernel). Proof obligations
(DESIGN.md, lane `integrate`, `sorry`s): `preFn` preserves the frontend's refinement with the arrays
renamed; `front_run`'s refinement from a `DECL` that already holds the prelude's records.
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

/-! ## The frontend, renamed onto the prelude's arrays -/

/-- The prelude's bytes (a byte array). -/
abbrev PRE : ArrId := 2
/-- The prelude parse's id tables (the stream's are `NID`, `LID`, `EID`, `64`‥`66`). -/
abbrev PNID : ArrId := 208
abbrev PLID : ArrId := 209
abbrev PEID : ArrId := 210
/-- The prelude parse's sparse id tables (the stream's are `72`‥`74`, `Front/IdTable.lean`). -/
abbrev PNSP : ArrId := 211
abbrev PLSP : ArrId := 212
abbrev PESP : ArrId := 213

/-- The prelude parse's id-table `CTL` words: the stream's `64`‥`72` moved to `241`‥`249`. -/
def preCtl (k : Word) : Word := if 64 ≤ k ∧ k ≤ 72 then k + 177 else k

/-- The prelude's length, as a word. -/
def preludeLenW : Word := UInt64.ofNat preludeBytes.length

/-- A word array of the frontend's parse state, renamed. -/
def preA64 (a : ArrId) : ArrId :=
  if a = L.Front.NID then PNID else if a = L.Front.LID then PLID else if a = L.Front.EID then PEID
  else if a = 72 then PNSP else if a = 73 then PLSP else if a = 74 then PESP
  else a

/-- An index into array `a`, renamed: `CTL`'s id-table words (`preCtl`). -/
def preIx (a : ArrId) : Expr → Expr
  | .const k => if a = CTL then .const (preCtl k) else .const k
  | e => e

/-- An expression of the frontend, renamed. -/
def preE : Expr → Expr
  | .ld8 a i => .ld8 (if a = 0 then PRE else a) (preE i)
  | .len8 a => if a = 0 then .const preludeLenW else .len8 a
  | .ld64 a i => .ld64 (preA64 a) (preIx a (preE i))
  | .len64 a => .len64 (preA64 a)
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
  | .st8 a i e => .st8 (if a = 0 then PRE else a) (preE i) (preE e)
  | .st64 a i e => .st64 (preA64 a) (preIx a (preE i)) (preE e)
  | .seq s u => .seq (preS t s) (preS t u)
  | .ite c s u => .ite (preC c) (preS t s) (preS t u)
  | .while c s => .while (preC c) (preS t s)
  | .ret es => .ret (es.map preE)
  | .call xs f args => .call xs (preName t f) (args.map preE)
  | .gset g e => .gset g (preE e)
  | s => s

/-- **A frontend function, renamed onto the prelude's arrays** (`t`: the copied functions). -/
-- con-ron: none — a renaming of the frontend's L code (the twin's `parseBytes` runs on any bytes)
def preFn (t : NTree) (d : FunDecl) : FunDecl := { d with body := preS t d.body }

/-- The tree of a list of names (`preName`'s argument). -/
def nameTree (fs : List String) : NTree :=
  fs.foldl (fun t f => (t.insert (nameCode f) 0).getD t) .leaf

/-! ## `builtin_prelude()` -/

/-- `builtin_prelude()`: `builtinPreludeE` — the prelude's bytes into `PRE`, the frontend on them;
the number of prelude records into `CTL[240]`. -/
-- con-ron: ConRon/Arena/Frontend/Prelude.lean:39-52 ConRon.Arena.Frontend.builtinPreludeE
@[l_impl ConRon.Arena.Frontend.builtinPreludeE]
def builtinPreludeL : FunDecl := lfn () locals (i, r) {
  if len(PRE.u8) < len(preludeBytes.c8) { abort };
  i := 0;
  while i < len(preludeBytes.c8) {
    PRE.u8[i] := preludeBytes.c8[i];
    i += 1
  };
  r := call pre_front_run();
  if r != 0 { abort };
  CTL.u64[240] := DECL.u64[0];
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
  [("builtin_prelude", builtinPreludeL), ("prepare_prelude", preparePreludeL),
   ("decl_declares", declDeclaresL), ("decl_key", declKeyL)] ++ hoistProg

end L.Checker
