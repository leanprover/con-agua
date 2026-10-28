module

meta import ConAgua.L.Semantics
public import ConAgua.Front.FieldsExpr
public import ConAgua.Scan.Line
import ConAgua.Census.Attr
import ConAgua.Front.Preserve
import ConAgua.L.GrindAttr
import ConAgua.Scan.Common
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# One pass over a line: the sub-objects

con-ron's `scan_line_fwd` reads a line once and builds its record. Here, in the same shape,
`sub_rec(o, kd, mk)` reads one object of a line's payload at `o`: an expression's sub-object
(`app`, `lam`/`forallE`, `letE`, `const`, `proj`, by the payload key `kd`) or a name
(`str`, `num`). It checks what Stage B's record loop for that object checks (the key set by its
bits `subBit kd`, each key once, the required keys `mk`, the comma alternation), and fills the
slots the record pass reads (`objRecN`, `strRecN`, `numRecN`): `(end, x0, x1, x2, x3)`, `end = 0`
when the object does not scan. Each value is read once (`sub_val`), each number's value once
(`read_nat`).

The model `subN` mirrors the code; `ConAgua.Front.LineRecLink` relates it to Stage B's `objN` and
to the record passes.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Front.LineRec

open L.Scan.Utf8 (byteW)
open L.Scan.Member
open L.Scan.Values
open L.Scan.Records
open L.Front.Fields
open L.Scan.Line (idxCode lineVal)

/-! ## The code -/

/-- The key bit of key `k` in the object of payload key `kd`, `0` if the object has no key `k`. -/
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:2427-2574 ConLeche.Frontend.scanLineLoop
def subBitF : FunDecl := lfn (kd, k) {
  if kd == 2 {  -- `app`: `arg`, `fn`
    if k == 3 { return 1 };
    if k == 13 { return 2 };
    return 0
  };
  if kd == 29 || kd == 14 {  -- `lam`, `forallE`: `binderInfo`, `body`, `name`, `type`
    if k == 5 { return 1 };
    if k == 6 { return 2 };
    if k == 34 { return 4 };
    if k == 61 { return 8 };
    return 0
  };
  if kd == 30 {  -- `letE`: `body`, `name`, `nondep`, `type`, `value`
    if k == 6 { return 1 };
    if k == 34 { return 2 };
    if k == 37 { return 4 };
    if k == 61 { return 8 };
    if k == 65 { return 16 };
    return 0
  };
  if kd == 9 {  -- `const`: `name`, `us`
    if k == 34 { return 1 };
    if k == 64 { return 2 };
    return 0
  };
  if kd == 48 {  -- `proj`: `idx`, `struct`, `typeName`
    if k == 17 { return 1 };
    if k == 58 { return 2 };
    if k == 62 { return 4 };
    return 0
  };
  if kd == 56 {  -- a `str` name: `pre`, `str`
    if k == 47 { return 1 };
    if k == 56 { return 2 };
    return 0
  };
  if kd == 38 {  -- a `num` name: `i`, `pre`
    if k == 16 { return 1 };
    if k == 47 { return 2 };
    return 0
  };
  return 0
}

/-- The end of key `k`'s value at `v` (its quote at `ks`), `0` if it does not scan. -/
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:2427-2574 ConLeche.Frontend.scanLineLoop
def subValF : FunDecl := lfn (ks, k, v) locals (e, ok, x) {
  if k == 5 {  -- `binderInfo`
    e := call scan_binder_info(v);
    return e
  };
  if k == 37 {  -- `nondep`
    (ok, x, e) := call scan_bool(v);
    if ok == 0 { return 0 };
    return e
  };
  if k == 64 {  -- `us`
    (e, x) := call scan_nat_list(v);
    return e
  };
  if k == 56 {  -- a name's `str`
    e := call scan_string(v);
    return e
  };
  e := call slot_nat(ks, v);  -- every other key has a number
  return e
}

def subLoop : Stmt := lblk (o, kd, mk, i, w, seen, x0, x1, x2, x3, tag, ks, k, v, e, x, bt) {
  while 0 == 0 {
    (tag, ks, w, k, v) := call next_member(i, w);
    if tag == 0 { return (0, 0, 0, 0, 0) };
    if tag == 1 {
      if w != 0 && seen != 0 { return (0, 0, 0, 0, 0) };
      if (seen & mk) != mk { return (0, 0, 0, 0, 0) };
      return (ks + 1, x0, x1, x2, x3)
    };
    bt := call sub_bit(kd, k);
    if bt == 0 { return (0, 0, 0, 0, 0) };
    if (seen & bt) != 0 { return (0, 0, 0, 0, 0) };
    e := call sub_val(ks, k, v);
    if e <= ks { return (0, 0, 0, 0, 0) };
    if k == 13 || k == 61 || k == 62 || k == 47 {
      x0 := call read_nat(v, e)
    } else if k == 3 || k == 6 || k == 58 || k == 16 {
      x1 := call read_nat(v, e)
    } else if k == 64 {
      x1 := v
    } else if k == 65 || k == 17 {
      x2 := call read_nat(v, e)
    } else if k == 34 {
      x3 := call read_nat(v, e)
    } else if k == 56 {
      x1 := v + 1;
      x2 := e - 1
    };
    seen := seen | bt;
    i := e;
    w := 0
  }
}

/-- The object of payload key `kd` at `o`, its required keys `mk`: `(end, x0, x1, x2, x3)`. -/
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:2427-2574 ConLeche.Frontend.scanLineLoop
def subRec : FunDecl := lfn (o, kd, mk) locals (i, w, seen, x0, x1, x2, x3, tag, ks, k, v, e, x, bt) {
  if !(o < len(IN.u8) && IN.u8[o] == 123) { return (0, 0, 0, 0, 0) };
  i := o + 1;
  w := 1;
  ⟪subLoop⟫;
  return (0, 0, 0, 0, 0)
}

/-! ### The line -/

/-- An index key `in`/`il`/`ie`: `idx` and the index kind. -/
def lrArmIdx : Stmt := lblk (i, w, ik, pk, pl, idx, a, c, d, tag, ks, k, v, e, x, t0, t1, t2, t3, y) {
  if ik != 0 { return (0, 0, 0, 0, 0, 0) };
  e := call slot_nat(ks, v);
  if e == 0 { return (0, 0, 0, 0, 0, 0) };
  idx := call read_nat(v, e);
  if k == 21 { ik := 1 } else if k == 19 { ik := 2 } else { ik := 3 }
}

/-- `bvar`, `sort` (expressions), `succ`, `param` (levels): one number. -/
def lrArmNat : Stmt := lblk (i, w, ik, pk, pl, idx, a, c, d, tag, ks, k, v, e, x, t0, t1, t2, t3, y) {
  if pk != 0 { return (0, 0, 0, 0, 0, 0) };
  e := call slot_nat(ks, v);
  if e == 0 { return (0, 0, 0, 0, 0, 0) };
  x := call read_nat(v, e);
  if k == 7 { pl := 8; a := x; c := 0; d := 0; pk := 3 }
  else if k == 55 { pl := 9; a := x; c := 0; d := 0; pk := 3 }
  else if k == 59 { pl := 3; a := x; pk := 2 }
  else { pl := 6; a := x; pk := 2 }
}

/-- `max`, `imax`: a list of two numbers. -/
def lrArmList : Stmt := lblk (i, w, ik, pk, pl, idx, a, c, d, tag, ks, k, v, e, x, t0, t1, t2, t3, y) {
  if pk != 0 { return (0, 0, 0, 0, 0, 0) };
  (e, x) := call scan_nat_list(v);
  if e == 0 { return (0, 0, 0, 0, 0, 0) };
  if x != 2 { return (0, 0, 0, 0, 0, 0) };
  if e <= ks { return (0, 0, 0, 0, 0, 0) };
  (y, a, c) := call rec_nat_list(v);
  if k == 32 { pl := 4 } else { pl := 5 };
  pk := 2
}

/-- `str`, `num`: a name. -/
def lrArmName : Stmt := lblk (i, w, ik, pk, pl, idx, a, c, d, tag, ks, k, v, e, x, t0, t1, t2, t3, y) {
  if pk != 0 { return (0, 0, 0, 0, 0, 0) };
  (e, t0, t1, t2, t3) := call sub_rec(v, k, 3);
  if e == 0 { return (0, 0, 0, 0, 0, 0) };
  if e <= ks { return (0, 0, 0, 0, 0, 0) };
  if k == 56 { pl := 1; a := t0; c := t1; d := t2 } else { pl := 2; a := t0; c := t1 };
  pk := 1
}

/-- `app`, `lam`, `forallE`, `letE`, `const`, `proj`: an expression's sub-object. -/
def lrArmExpr : Stmt := lblk (i, w, ik, pk, pl, idx, a, c, d, tag, ks, k, v, e, x, t0, t1, t2, t3, y) {
  if pk != 0 { return (0, 0, 0, 0, 0, 0) };
  if k == 2 || k == 9 { y := 3 } else if k == 30 { y := 27 } else if k == 48 { y := 7 }
  else { y := 15 };
  (e, t0, t1, t2, t3) := call sub_rec(v, k, y);
  if e == 0 { return (0, 0, 0, 0, 0, 0) };
  if e <= ks { return (0, 0, 0, 0, 0, 0) };
  if k == 2 { pl := 10; a := t0; c := t1; d := t1 }
  else if k == 29 { pl := 11; a := t0; c := t1; d := t1 }
  else if k == 14 { pl := 12; a := t0; c := t1; d := t1 }
  else if k == 30 { pl := 13; a := t0; c := t2; d := t1 }
  else if k == 48 { pl := 14; a := t0; c := t2; d := t1 }
  else { pl := 15; a := t3; c := t1; d := t1 };
  pk := 3
}

/-- `natVal`, `strVal`: a literal. -/
def lrArmLit : Stmt := lblk (i, w, ik, pk, pl, idx, a, c, d, tag, ks, k, v, e, x, t0, t1, t2, t3, y) {
  if pk != 0 { return (0, 0, 0, 0, 0, 0) };
  if k == 35 { e := call scan_quoted_nat(v) } else { e := call scan_string(v) };
  if e == 0 { return (0, 0, 0, 0, 0, 0) };
  if e <= ks { return (0, 0, 0, 0, 0, 0) };
  if k == 35 { pl := 16; a := call read_nat(v + 1, e - 1) } else { pl := 17; a := 0 };
  c := v + 1;
  d := e - 1;
  pk := 3
}

/-- A declaration: validated here, read by `apply_dline`. -/
def lrArmDecl : Stmt := lblk (i, w, ik, pk, pl, idx, a, c, d, tag, ks, k, v, e, x, t0, t1, t2, t3, y) {
  if pk != 0 { return (0, 0, 0, 0, 0, 0) };
  if k == 4 { e := call scan_axiom(v) }
  else if k == 12 { e := call scan_def(v) }
  else if k == 60 { e := call scan_thm(v) }
  else if k == 45 { e := call scan_opaque(v) }
  else if k == 49 { e := call scan_quot(v) }
  else { e := call scan_ind_decl(v) };
  if e == 0 { return (0, 0, 0, 0, 0, 0) };
  if e <= ks { return (0, 0, 0, 0, 0, 0) };
  pk := 4
}

/-- `meta`: the header. -/
def lrArmMeta : Stmt := lblk (i, w, ik, pk, pl, idx, a, c, d, tag, ks, k, v, e, x, t0, t1, t2, t3, y) {
  if pk != 0 { return (0, 0, 0, 0, 0, 0) };
  if !(v < len(IN.u8) && IN.u8[v] == 123) { return (0, 0, 0, 0, 0, 0) };
  e := call skip_braced(v + 1, 0);
  if e == 0 { return (0, 0, 0, 0, 0, 0) };
  if e <= ks { return (0, 0, 0, 0, 0, 0) };
  pl := 7;
  pk := 5
}

/-- One member of the line: its value's end `e`, the kinds, the fields; else `return` zeros. -/
def lrDisp : Stmt := lblk (i, w, ik, pk, pl, idx, a, c, d, tag, ks, k, v, e, x, t0, t1, t2, t3, y) {
  if k == 21 || k == 19 || k == 18 { ⟪lrArmIdx⟫ }
  else if k == 7 || k == 55 || k == 59 || k == 46 { ⟪lrArmNat⟫ }
  else if k == 32 || k == 20 { ⟪lrArmList⟫ }
  else if k == 56 || k == 38 { ⟪lrArmName⟫ }
  else if k == 2 || k == 29 || k == 14 || k == 30 || k == 9 || k == 48 { ⟪lrArmExpr⟫ }
  else if k == 35 || k == 57 { ⟪lrArmLit⟫ }
  else if k == 4 || k == 12 || k == 60 || k == 45 || k == 49 || k == 23 { ⟪lrArmDecl⟫ }
  else if k == 33 { ⟪lrArmMeta⟫ }
  else { return (0, 0, 0, 0, 0, 0) }
}

def lrLoop : Stmt := lblk (i, w, ik, pk, pl, idx, a, c, d, tag, ks, k, v, e, x, t0, t1, t2, t3, y) {
  while 0 == 0 {
    (tag, ks, w, k, v) := call next_member(i, w);
    if tag == 0 { return (0, 0, 0, 0, 0, 0) };
    if tag == 1 {
      if w != 0 && (ik != 0 || pk != 0) { return (0, 0, 0, 0, 0, 0) };
      if pk == 1 && ik == 1 { return (ks + 1, pl, idx, a, c, d) };
      if pk == 2 && ik == 2 { return (ks + 1, pl, idx, a, c, d) };
      if pk == 3 && ik == 3 { return (ks + 1, pl, idx, a, c, d) };
      if pk == 4 && ik == 0 { return (ks + 1, pl, idx, a, c, d) };
      if pk == 5 && ik == 0 { return (ks + 1, pl, idx, a, c, d) };
      return (0, 0, 0, 0, 0, 0)
    };
    ⟪lrDisp⟫;
    i := e;
    w := 0
  }
}

/-- The members of the line after its `{` at `i - 1`: `(end, pl, idx, a, c, d)`, `end` after its
closing brace (`0` if the line does not scan), the fields as the record passes read them (`pl`
`1`–`7` a name, a level or the header, `8`–`17` an expression, `0` a declaration). -/
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:2427-2574 ConLeche.Frontend.scanLineLoop
def lineRec : FunDecl := lfn (i) locals (w, ik, pk, pl, idx, a, c, d, tag, ks, k, v, e, x, t0, t1, t2, t3, y) {
  w := 1;
  ⟪lrLoop⟫;
  return (0, 0, 0, 0, 0, 0)
}

/-! ## The models -/

/-- The key bits (`sub_bit`). -/
def subBit (kd k : Word) : Word :=
  if kd = 2 then appBit k
  else if kd = 29 ∨ kd = 14 then binderBit k
  else if kd = 30 then letEBit k
  else if kd = 9 then constEBit k
  else if kd = 48 then projBit k
  else if kd = 56 then strNameBit k
  else if kd = 38 then numNameBit k
  else 0

/-- A key with a number value. -/
def NumVal (k : Word) : Prop := k ≠ 5 ∧ k ≠ 37 ∧ k ≠ 64 ∧ k ≠ 56

/-- The value ends (`sub_val`). -/
def subVal (b : Array UInt8) (k ks v : Word) : Word :=
  if k = 5 then binderInfoN b v
  else if k = 37 then boolEndN b v
  else if k = 64 then (natListEntryN b v).1
  else if k = 56 then L.Scan.Str.scanStringN b v
  else slotNatN b ks v

/-- The slots after key `k` with its value `[v, e)`. -/
def subPut (b : Array UInt8) (k v e : Word) (o : Obj) : Obj :=
  if k = 13 ∨ k = 61 ∨ k = 62 ∨ k = 47 then ⟨o.e, rdNatN b v e, o.x1, o.x2, o.x3⟩
  else if k = 3 ∨ k = 6 ∨ k = 58 ∨ k = 16 then ⟨o.e, o.x0, rdNatN b v e, o.x2, o.x3⟩
  else if k = 64 then ⟨o.e, o.x0, v, o.x2, o.x3⟩
  else if k = 65 ∨ k = 17 then ⟨o.e, o.x0, o.x1, rdNatN b v e, o.x3⟩
  else if k = 34 then ⟨o.e, o.x0, o.x1, o.x2, rdNatN b v e⟩
  else if k = 56 then ⟨o.e, o.x0, v + 1, e - 1, o.x3⟩
  else o

/-- The object loop (`subLoop`): the end and the slots, `Obj.none` when it does not scan. -/
def subN (b : Array UInt8) (kd mk i w seen : Word) (o : Obj) : Obj :=
  if (nextMemberN b i w).tag = 0 then .none
  else if (nextMemberN b i w).tag = 1 then
    if (nextMemberN b i w).w ≠ 0 ∧ seen ≠ 0 then .none
    else if seen &&& mk ≠ mk then .none
    else ⟨(nextMemberN b i w).pos + 1, o.x0, o.x1, o.x2, o.x3⟩
  else if subBit kd (nextMemberN b i w).key = 0 then .none
  else if seen &&& subBit kd (nextMemberN b i w).key ≠ 0 then .none
  else if _h : (nextMemberN b i w).pos <
      subVal b (nextMemberN b i w).key (nextMemberN b i w).pos (nextMemberN b i w).val then
    subN b kd mk (subVal b (nextMemberN b i w).key (nextMemberN b i w).pos (nextMemberN b i w).val)
      0 (seen ||| subBit kd (nextMemberN b i w).key)
      (subPut b (nextMemberN b i w).key (nextMemberN b i w).val
        (subVal b (nextMemberN b i w).key (nextMemberN b i w).pos (nextMemberN b i w).val) o)
  else .none
termination_by b.size - i.toNat
decreasing_by
  have hk := nextMemberN_key b i w (nextMemberN_tag b i w (by assumption) (by assumption))
  have := L.Scan.lt_of_lt_ofNat hk.2
  rw [UInt64.le_iff_toNat_le] at hk
  rw [UInt64.lt_iff_toNat_lt] at _h
  omega

/-- `sub_rec(o, kd, mk)`. -/
def subRecN (b : Array UInt8) (o kd mk : Word) : Obj :=
  if o < UInt64.ofNat b.size ∧ byteW b o = 123 then subN b kd mk (o + 1) 1 0 ⟨0, 0, 0, 0, 0⟩
  else .none

section
variable (b : Array UInt8) (kd mk i w seen : Word) (o : Obj)
theorem subN_err (h : (nextMemberN b i w).tag = 0) : subN b kd mk i w seen o = .none := by
  rw [subN, ite_eq_left h]
theorem subN_close (h : (nextMemberN b i w).tag = 1) :
    subN b kd mk i w seen o =
      if (nextMemberN b i w).w ≠ 0 ∧ seen ≠ 0 then .none
      else if seen &&& mk ≠ mk then .none
      else ⟨(nextMemberN b i w).pos + 1, o.x0, o.x1, o.x2, o.x3⟩ := by
  rw [subN, ite_eq_right (by simp [h]), ite_eq_left h]
theorem subN_key (h0 : (nextMemberN b i w).tag ≠ 0) (h1 : (nextMemberN b i w).tag ≠ 1) :
    subN b kd mk i w seen o =
      if subBit kd (nextMemberN b i w).key = 0 then .none
      else if seen &&& subBit kd (nextMemberN b i w).key ≠ 0 then .none
      else if (nextMemberN b i w).pos <
          subVal b (nextMemberN b i w).key (nextMemberN b i w).pos (nextMemberN b i w).val then
        subN b kd mk
          (subVal b (nextMemberN b i w).key (nextMemberN b i w).pos (nextMemberN b i w).val)
          0 (seen ||| subBit kd (nextMemberN b i w).key)
          (subPut b (nextMemberN b i w).key (nextMemberN b i w).val
            (subVal b (nextMemberN b i w).key (nextMemberN b i w).pos (nextMemberN b i w).val) o)
      else .none := by
  rw [subN, ite_eq_right h0, ite_eq_right h1]
  simp only [dite_eq_ite]
end
grind_pattern [lang_grind] subN_err => subN b kd mk i w seen o, nextMemberN b i w
grind_pattern [lang_grind] subN_close => subN b kd mk i w seen o, nextMemberN b i w
grind_pattern [lang_grind] subN_key => subN b kd mk i w seen o, nextMemberN b i w

/-! ### The line's model -/

/-- The line loop's state after a member: the value's end `e` (`0`: the line does not scan), the
index and payload kinds, the fields. -/
structure LRS where
  e : Word
  ik : Word
  pk : Word
  f : Fld

/-- The line does not scan. -/
def LRS.fail : LRS := ⟨0, 0, 0, .none⟩

/-- An index key. -/
def lrIdx (b : Array UInt8) (k ks v ik pk : Word) (f : Fld) : LRS :=
  if ik = 0 ∧ slotNatN b ks v ≠ 0 then
    ⟨slotNatN b ks v, idxCode k, pk, ⟨f.pl, rdNatN b v (slotNatN b ks v), f.a, f.c, f.d⟩⟩
  else .fail

/-- The fields of `bvar`, `sort`, `succ`, `param` with the number `x`. -/
def natF (k : Word) (f : Fld) (x : Word) : Fld :=
  if k = 7 then ⟨8, f.idx, x, 0, 0⟩
  else if k = 55 then ⟨9, f.idx, x, 0, 0⟩
  else if k = 59 then ⟨3, f.idx, x, f.c, f.d⟩
  else ⟨6, f.idx, x, f.c, f.d⟩

/-- `bvar`, `sort`, `succ`, `param`. -/
def lrNat (b : Array UInt8) (k ks v ik pk : Word) (f : Fld) : LRS :=
  if pk = 0 ∧ slotNatN b ks v ≠ 0 then
    ⟨slotNatN b ks v, ik, if k = 7 ∨ k = 55 then 3 else 2,
      natF k f (rdNatN b v (slotNatN b ks v))⟩
  else .fail

/-- `max`, `imax`. -/
def lrList (b : Array UInt8) (k ks v ik pk : Word) (f : Fld) : LRS :=
  if pk = 0 ∧ (natListEntryN b v).1 ≠ 0 ∧ (natListEntryN b v).2 = 2 ∧ ks < (natListEntryN b v).1
  then
    ⟨(natListEntryN b v).1, ik, 2,
      ⟨if k = 32 then 4 else 5, f.idx, (pairEntryN b v).2.1, (pairEntryN b v).2.2, f.d⟩⟩
  else .fail

/-- The fields of a name with the slots `o`. -/
def nameF (k : Word) (f : Fld) (o : Obj) : Fld :=
  if k = 56 then ⟨1, f.idx, o.x0, o.x1, o.x2⟩ else ⟨2, f.idx, o.x0, o.x1, f.d⟩

/-- `str`, `num`. -/
def lrName (b : Array UInt8) (k ks v ik pk : Word) (f : Fld) : LRS :=
  if pk = 0 ∧ (subRecN b v k 3).e ≠ 0 ∧ ks < (subRecN b v k 3).e then
    ⟨(subRecN b v k 3).e, ik, 1, nameF k f (subRecN b v k 3)⟩
  else .fail

/-- The required keys of an expression's sub-object. -/
def exprMask (k : Word) : Word :=
  if k = 2 ∨ k = 9 then 3 else if k = 30 then 27 else if k = 48 then 7 else 15

/-- The fields of an expression with the sub-object's slots `o` (`objFld`'s, without the end). -/
def exprF (k : Word) (f : Fld) (o : Obj) : Fld :=
  ⟨(objFld k o).x0, f.idx, (objFld k o).x1, (objFld k o).x2, (objFld k o).x3⟩

/-- `app`, `lam`, `forallE`, `letE`, `const`, `proj`. -/
def lrExpr (b : Array UInt8) (k ks v ik pk : Word) (f : Fld) : LRS :=
  if pk = 0 ∧ (subRecN b v k (exprMask k)).e ≠ 0 ∧ ks < (subRecN b v k (exprMask k)).e then
    ⟨(subRecN b v k (exprMask k)).e, ik, 3, exprF k f (subRecN b v k (exprMask k))⟩
  else .fail

/-- The end of a literal. -/
def litEnd (b : Array UInt8) (k v : Word) : Word :=
  if k = 35 then quotedNatN b v else L.Scan.Str.scanStringN b v

/-- `natVal`, `strVal`. -/
def lrLit (b : Array UInt8) (k ks v ik pk : Word) (f : Fld) : LRS :=
  if pk = 0 ∧ litEnd b k v ≠ 0 ∧ ks < litEnd b k v then
    ⟨litEnd b k v, ik, 3,
      if k = 35 then ⟨16, f.idx, rdNatN b (v + 1) (litEnd b k v - 1), v + 1, litEnd b k v - 1⟩
      else ⟨17, f.idx, 0, v + 1, litEnd b k v - 1⟩⟩
  else .fail

/-- A declaration (Stage B's value scanner, `lineVal`). -/
def lrDecl (b : Array UInt8) (k ks v ik pk : Word) (f : Fld) : LRS :=
  if pk = 0 ∧ lineVal b k ks v ≠ 0 ∧ ks < lineVal b k ks v then ⟨lineVal b k ks v, ik, 4, f⟩
  else .fail

/-- The header. -/
def lrMeta (b : Array UInt8) (k ks v ik pk : Word) (f : Fld) : LRS :=
  if pk = 0 ∧ metaN b v ≠ 0 ∧ ks < metaN b v then ⟨metaN b v, ik, 5, ⟨7, f.idx, f.a, f.c, f.d⟩⟩
  else .fail

/-- One member `k` with its quote at `ks` and its value at `v` (`lrDisp`). -/
def lrStepN (b : Array UInt8) (k ks v ik pk : Word) (f : Fld) : LRS :=
  if k = 21 ∨ k = 19 ∨ k = 18 then lrIdx b k ks v ik pk f
  else if k = 7 ∨ k = 55 ∨ k = 59 ∨ k = 46 then lrNat b k ks v ik pk f
  else if k = 32 ∨ k = 20 then lrList b k ks v ik pk f
  else if k = 56 ∨ k = 38 then lrName b k ks v ik pk f
  else if k = 2 ∨ k = 29 ∨ k = 14 ∨ k = 30 ∨ k = 9 ∨ k = 48 then lrExpr b k ks v ik pk f
  else if k = 35 ∨ k = 57 then lrLit b k ks v ik pk f
  else if k = 4 ∨ k = 12 ∨ k = 60 ∨ k = 45 ∨ k = 49 ∨ k = 23 then lrDecl b k ks v ik pk f
  else if k = 33 then lrMeta b k ks v ik pk f
  else .fail

/-- The line loop (`lrLoop`): its end and fields, `LRS.fail` when the line does not scan. -/
def lineRecN (b : Array UInt8) (i w ik pk : Word) (f : Fld) : LRS :=
  if (nextMemberN b i w).tag = 0 then .fail
  else if (nextMemberN b i w).tag = 1 then
    if (nextMemberN b i w).w ≠ 0 ∧ (ik ≠ 0 ∨ pk ≠ 0) then .fail
    else if (pk = 1 ∧ ik = 1) ∨ (pk = 2 ∧ ik = 2) ∨ (pk = 3 ∧ ik = 3) ∨ (pk = 4 ∧ ik = 0) ∨
        (pk = 5 ∧ ik = 0) then ⟨(nextMemberN b i w).pos + 1, ik, pk, f⟩
    else .fail
  else if _h : (nextMemberN b i w).pos <
      (lrStepN b (nextMemberN b i w).key (nextMemberN b i w).pos (nextMemberN b i w).val ik pk f).e
  then
    lineRecN b
      (lrStepN b (nextMemberN b i w).key (nextMemberN b i w).pos (nextMemberN b i w).val ik pk f).e
      0 (lrStepN b (nextMemberN b i w).key (nextMemberN b i w).pos (nextMemberN b i w).val ik pk f).ik
      (lrStepN b (nextMemberN b i w).key (nextMemberN b i w).pos (nextMemberN b i w).val ik pk f).pk
      (lrStepN b (nextMemberN b i w).key (nextMemberN b i w).pos (nextMemberN b i w).val ik pk f).f
  else .fail
termination_by b.size - i.toNat
decreasing_by
  have hk := nextMemberN_key b i w (nextMemberN_tag b i w (by assumption) (by assumption))
  have := L.Scan.lt_of_lt_ofNat hk.2
  rw [UInt64.le_iff_toNat_le] at hk
  rw [UInt64.lt_iff_toNat_lt] at _h
  omega

/-- `line_rec(i)`'s six words. -/
def LRS.enc (r : LRS) : List Word := [r.e, r.f.pl, r.f.idx, r.f.a, r.f.c, r.f.d]

/-- `line_rec(i)`, `i` after the line's `{`. -/
def lineRecEntryN (b : Array UInt8) (i : Word) : LRS := lineRecN b i 1 0 0 .none

/-! ## Specs -/

section specs
variable (p : Prog) (b : Array UInt8) (hb : b.size < 2 ^ 63)
    (hpw : p.lookup "skip_ws" = some L.Scan.Leaves.skipWs)
    (hpd : p.lookup "skip_digits" = some L.Scan.Leaves.skipDigits)
    (hpk : p.lookup "key_end" = some L.Scan.Leaves.keyEnd)
    (hpn : p.lookup "num_end" = some L.Scan.Leaves.numEnd)
    (hpa1 : p.lookup "key_at_g1" = some L.Scan.Key.keyAtG1)
    (hpa2 : p.lookup "key_at_g2" = some L.Scan.Key.keyAtG2)
    (hpa3 : p.lookup "key_at_g3" = some L.Scan.Key.keyAtG3)
    (hpa4 : p.lookup "key_at_g4" = some L.Scan.Key.keyAtG4)
    (hpa5 : p.lookup "key_at_g5" = some L.Scan.Key.keyAtG5)
    (hpa6 : p.lookup "key_at_g6" = some L.Scan.Key.keyAtG6)
    (hpa : p.lookup "key_at" = some L.Scan.Key.keyAt)
    (hpv : p.lookup "value_at" = some L.Scan.Key.valueAt)
    (hpm : p.lookup "next_member" = some nextMember)
    (hps : p.lookup "slot_nat" = some slotNat)
    (hpmw : p.lookup "match_word" = some matchWord)
    (hpi : p.lookup "scan_binder_info" = some scanBinderInfo)
    (hpl : p.lookup "scan_nat_list" = some scanNatList)
    (hpml : p.lookup "match_lit" = some L.Scan.Lit.matchLit)
    (hpbo : p.lookup "scan_bool" = some L.Scan.Lit.scanBool)
    (hpc : p.lookup "utf8_char" = some L.Scan.Utf8.utf8Char)
    (hpu8 : p.lookup "utf8_valid" = some L.Scan.Str.utf8Valid)
    (hpbi : p.lookup "byte_in" = some L.Scan.Str.byteIn)
    (hphv : p.lookup "hex_val" = some L.Scan.Str.hexVal)
    (hp4 : p.lookup "hex4" = some L.Scan.Str.hex4)
    (hp3 : p.lookup "hex3" = some L.Scan.Str.hex3)
    (hpux : p.lookup "u_next" = some L.Scan.Str.uNext)
    (hpue : p.lookup "unescape" = some L.Scan.Str.unescape)
    (hpsc : p.lookup "str_close" = some L.Examples.strClose)
    (hpe : p.lookup "has_escape" = some L.Scan.Leaves.hasEscape)
    (hpt : p.lookup "scan_string" = some L.Scan.Str.scanString)
    (hprn : p.lookup "read_nat" = some readNat)
    (hpsb : p.lookup "sub_bit" = some subBitF)
    (hpsv : p.lookup "sub_val" = some subValF)
    (hpsr : p.lookup "sub_rec" = some subRec)
    (hprp : p.lookup "rec_nat_list" = some recNatList)
    (hpq : p.lookup "scan_quoted_nat" = some scanQuotedNat)
    (hpbr : p.lookup "skip_braced" = some L.Examples.skipBraced)
    (hphn : p.lookup "hints_num" = some hintsNum)
    (hpho : p.lookup "hints_obj" = some hintsObj)
    (hph : p.lookup "scan_hints" = some scanHints)
    (hp_rule : p.lookup "scan_rule" = some scanRule)
    (hp_rules : p.lookup "scan_rules" = some scanRules)
    (hp_indRec : p.lookup "scan_ind_rec" = some scanIndRec)
    (hp_indRecs : p.lookup "scan_ind_recs" = some scanIndRecs)
    (hp_indType : p.lookup "scan_ind_type" = some scanIndType)
    (hp_indTypes : p.lookup "scan_ind_types" = some scanIndTypes)
    (hp_indCtor : p.lookup "scan_ind_ctor" = some scanIndCtor)
    (hp_indCtors : p.lookup "scan_ind_ctors" = some scanIndCtors)
    (hp_axiomD : p.lookup "scan_axiom" = some scanAxiomD)
    (hp_defD : p.lookup "scan_def" = some scanDefD)
    (hp_thmD : p.lookup "scan_thm" = some scanThmD)
    (hp_opaqueD : p.lookup "scan_opaque" = some scanOpaqueD)
    (hp_quotD : p.lookup "scan_quot" = some scanQuotD)
    (hp_indD : p.lookup "scan_ind_decl" = some scanIndD)
    (hplr : p.lookup "line_rec" = some lineRec)
include hb

omit hb in
include hpsb in
attribute [local lang_grind] subBit appBit binderBit letEBit constEBit projBit strNameBit
  numNameBit in
theorem subBit_spec (n : Nat) (s₀ : St) (kd k : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "sub_bit" [kd, k]
    ⦃fun r s' => s' = s₀ ∧ r = [subBit kd k]; ⊤⦄ := by
  rw [invoke_eq _ hpsb]
  simp only [callFn, subBitF]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, L.evalC_spec, L.evalE_spec, evalArgs, setLoc]
    all_goals simp only [Cond.pval, Expr.pval, Locals.init, List.getD_cons_zero,
      List.getD_cons_succ, Cmp.eval, BinOp.eval, Bool.and_eq_true, Bool.or_eq_true,
      beq_iff_eq, decide_eq_true_eq] at *
    all_goals subst_vars
    all_goals grind [subBit, appBit, binderBit, letEBit, constEBit, projBit, strNameBit,
      numNameBit, Sig.retVal, Sig.retOr]

include hpd hpn hps hpmw hpi hpl hpml hpbo hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hpsv in
attribute [local lang_grind] subVal boolEndN in
theorem subVal_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (ks k v : Word)
    (hv : v.toNat ≤ b.size) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "sub_val" [ks, k, v]
    ⦃fun r s' => s' = s₀ ∧ r = [subVal b k ks v]; ⊤⦄ := by
  rw [invoke_eq _ hpsv]
  simp only [callFn, subValF]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hb64 : b.size < 2 ^ 64 := by omega
    sym only [lang_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        scanBinderInfo_spec p b hb hpmw hpi n, L.Scan.Lit.scanBool_spec p hpml hpbo b hb64 n,
        scanNatList_spec p b hb hpd hpn hpl n, slotNat_spec p b hb hpd hpn hps n,
        L.Scan.Str.scanString_spec p b hb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt n] <;>
        finish

include hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hpl hpml hpbo hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hprn hpsb hpsv in
attribute [local lang_grind] subPut Obj.enc Obj.none in
set_option maxHeartbeats 2000000 in
theorem subLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n subLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr Obj.none.enc = (subN b (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 4) (s₀.loc 5)
        ⟨0, s₀.loc 6, s₀.loc 7, s₀.loc 8, s₀.loc 9⟩).enc; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := subLoop) rfl]
    sym (gen := 16) only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih,
        nextMember_spec p b hb hpw hpk hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm n,
        subBit_spec p hpsb n,
        subVal_spec p b hb hpd hpn hps hpmw hpi hpl hpml hpbo hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hpsv n,
        readNat_spec p b hprn n] <;> finish

include hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hpl hpml hpbo hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hprn hpsb hpsv hpsr in
attribute [local lang_grind] subRecN Obj.enc Obj.none in
theorem subRec_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (o kd mk : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "sub_rec" [o, kd, mk]
    ⦃fun r s' => s' = s₀ ∧ r = (subRecN b o kd mk).enc; ⊤⦄ := by
  rw [invoke_eq _ hpsr]
  simp only [callFn, subRec]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld8,
        fun s₀ => Triple.step_exec (subLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hpl hpml hpbo hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hprn hpsb hpsv (n + 1) s₀)] <;>
        finish

/-! ### The line's arms -/

/-- The member the dispatch reads, in the state `s` (`k` at local 11, its quote at 10, its value
at 12, the kinds at 2 and 3, the fields at 4–8). -/
def lrStepS (b : Array UInt8) (s : St) : LRS :=
  lrStepN b (s.loc 11) (s.loc 10) (s.loc 12) (s.loc 2) (s.loc 3)
    ⟨s.loc 4, s.loc 5, s.loc 6, s.loc 7, s.loc 8⟩

/-- What an arm (and the dispatch) does from `s₁`: the memory stays, and it sets `e`, the kinds
and the fields as `lrStepN` says, or returns zeros, as `lrStepN`'s `e = 0` says. -/
def LRArmPost (b : Array UInt8) (s₁ : St) (r : Sig) (s' : St) : Prop :=
  s'.mem = s₁.mem ∧ r ≠ .brk ∧
  (r = .normal →
    s'.loc 13 = (lrStepS b s₁).e ∧ s'.loc 2 = (lrStepS b s₁).ik ∧ s'.loc 3 = (lrStepS b s₁).pk ∧
    s'.loc 4 = (lrStepS b s₁).f.pl ∧ s'.loc 5 = (lrStepS b s₁).f.idx ∧
    s'.loc 6 = (lrStepS b s₁).f.a ∧ s'.loc 7 = (lrStepS b s₁).f.c ∧
    s'.loc 8 = (lrStepS b s₁).f.d ∧ (lrStepS b s₁).e ≠ 0) ∧
  (r ≠ .normal → r.retOr [] = [0, 0, 0, 0, 0, 0] ∧ (lrStepS b s₁).e = 0)

attribute [local lang_grind] LRS.fail Fld.none in
include hpd hpn hps hprn in
theorem lrArmIdx_spec (n : Nat) (s₁ : St) :
    ⦃fun s => s = s₁ ∧ s.mem.arr8 IN = b ∧ (s.loc 12).toNat ≤ b.size ∧
      (s.loc 11 = 21 ∨ s.loc 11 = 19 ∨ s.loc 11 = 18)⦄
    step p (exec p n) lrArmIdx
    ⦃fun r s' => LRArmPost b s₁ r s'; ⊤⦄ := by
  dsimp only [lrArmIdx]
  vcgen [step, L.evalE_spec, L.evalC_spec, evalArgs, setLoc, setLocs,
      slotNat_spec p b hb hpd hpn hps n, readNat_spec p b hprn n]
  all_goals subst_vars
  all_goals try rfl
  all_goals simp only [Cond.pval, Expr.pval, St.setLoc_loc, St.setLocs_nil, St.setLocs_cons,
      List.headD_cons, List.tail_cons, Cmp.eval, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
      Nat.reduceEqDiff, reduceIte] at *
  all_goals grind (splits := 40) [lang_grind, LRArmPost, lrStepS, lrStepN, lrIdx, idxCode,
    Sig.retOr]

attribute [local lang_grind] LRS.fail Fld.none natF in
include hpd hpn hps hprn in
theorem lrArmNat_spec (n : Nat) (s₁ : St) :
    ⦃fun s => s = s₁ ∧ s.mem.arr8 IN = b ∧ (s.loc 12).toNat ≤ b.size ∧
      (s.loc 11 = 7 ∨ s.loc 11 = 55 ∨ s.loc 11 = 59 ∨ s.loc 11 = 46)⦄
    step p (exec p n) lrArmNat
    ⦃fun r s' => LRArmPost b s₁ r s'; ⊤⦄ := by
  dsimp only [lrArmNat]
  vcgen [step, L.evalE_spec, L.evalC_spec, evalArgs, setLoc, setLocs,
      slotNat_spec p b hb hpd hpn hps n, readNat_spec p b hprn n]
  all_goals subst_vars
  all_goals try rfl
  all_goals simp only [Cond.pval, Expr.pval, L.rd8, St.setLoc_loc, St.setLocs_nil, St.setLocs_cons,
      List.headD_cons, List.tail_cons, Cmp.eval, BinOp.eval, Bool.or_eq_true, Bool.not_eq_true',
      beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq, Nat.reduceEqDiff, reduceIte] at *
  all_goals grind (splits := 40) [lang_grind, LRArmPost, lrStepS, lrStepN, lrNat, natF,
    Sig.retOr]

attribute [local lang_grind] LRS.fail Fld.none in
include hpd hpn hpl hprn hprp in
theorem lrArmList_spec (n : Nat) (s₁ : St) :
    ⦃fun s => s = s₁ ∧ s.mem.arr8 IN = b ∧ (s.loc 12).toNat ≤ b.size ∧
      (s.loc 11 = 32 ∨ s.loc 11 = 20)⦄
    step p (exec p n) lrArmList
    ⦃fun r s' => LRArmPost b s₁ r s'; ⊤⦄ := by
  dsimp only [lrArmList]
  vcgen [step, L.evalE_spec, L.evalC_spec, evalArgs, setLoc, setLocs,
      scanNatList_spec p b hb hpd hpn hpl n, recNatList_spec p b hb hpd hpn hprn hprp n]
  all_goals subst_vars
  all_goals try rfl
  all_goals simp only [Cond.pval, Expr.pval, L.rd8, St.setLoc_loc, St.setLocs_nil, St.setLocs_cons,
      List.headD_cons, List.tail_cons, Cmp.eval, BinOp.eval, Bool.or_eq_true, Bool.not_eq_true',
      beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq, Nat.reduceEqDiff, reduceIte] at *
  all_goals grind (splits := 40) [lang_grind, LRArmPost, lrStepS, lrStepN, lrList, Sig.retOr]

attribute [local lang_grind] LRS.fail Fld.none nameF in
include hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hpl hpml hpbo hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hprn hpsb hpsv hpsr in
theorem lrArmName_spec (n : Nat) (s₁ : St) :
    ⦃fun s => s = s₁ ∧ s.mem.arr8 IN = b ∧ (s.loc 12).toNat ≤ b.size ∧
      (s.loc 11 = 56 ∨ s.loc 11 = 38)⦄
    step p (exec p n) lrArmName
    ⦃fun r s' => LRArmPost b s₁ r s'; ⊤⦄ := by
  dsimp only [lrArmName]
  vcgen [step, L.evalE_spec, L.evalC_spec, evalArgs, setLoc, setLocs,
      subRec_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hpl hpml hpbo hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hprn hpsb hpsv hpsr n]
  all_goals subst_vars
  all_goals try rfl
  all_goals simp only [Cond.pval, Expr.pval, L.rd8, St.setLoc_loc, St.setLocs_nil, St.setLocs_cons,
      List.headD_cons, List.tail_cons, Cmp.eval, BinOp.eval, Bool.or_eq_true, Bool.not_eq_true',
      beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq, Nat.reduceEqDiff, reduceIte] at *
  all_goals grind (splits := 40) [lang_grind, LRArmPost, lrStepS, lrStepN, lrName, nameF,
    Obj.enc, Sig.retOr]

attribute [local lang_grind] LRS.fail Fld.none in
include hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hpl hpml hpbo hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hprn hpsb hpsv hpsr in
theorem lrArmExpr_spec (n : Nat) (s₁ : St) :
    ⦃fun s => s = s₁ ∧ s.mem.arr8 IN = b ∧ (s.loc 12).toNat ≤ b.size ∧
      (s.loc 11 = 2 ∨ s.loc 11 = 29 ∨ s.loc 11 = 14 ∨ s.loc 11 = 30 ∨ s.loc 11 = 9 ∨
        s.loc 11 = 48)⦄
    step p (exec p n) lrArmExpr
    ⦃fun r s' => LRArmPost b s₁ r s'; ⊤⦄ := by
  dsimp only [lrArmExpr]
  vcgen [step, L.evalE_spec, L.evalC_spec, evalArgs, setLoc, setLocs,
      subRec_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpi hpl hpml hpbo hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hprn hpsb hpsv hpsr n]
  all_goals subst_vars
  all_goals try rfl
  all_goals simp only [Cond.pval, Expr.pval, L.rd8, St.setLoc_loc, St.setLocs_nil, St.setLocs_cons,
      List.headD_cons, List.tail_cons, Cmp.eval, BinOp.eval, Bool.or_eq_true, Bool.not_eq_true',
      beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq, Nat.reduceEqDiff, reduceIte] at *
  all_goals grind (splits := 40) [lang_grind, LRArmPost, lrStepS, lrStepN, lrExpr, exprF,
    exprMask, objFld, Obj.enc, Sig.retOr]

attribute [local lang_grind] LRS.fail Fld.none in
include hpd hpq hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hprn in
theorem lrArmLit_spec (n : Nat) (s₁ : St) :
    ⦃fun s => s = s₁ ∧ s.mem.arr8 IN = b ∧ (s.loc 12).toNat ≤ b.size ∧
      (s.loc 11 = 35 ∨ s.loc 11 = 57)⦄
    step p (exec p n) lrArmLit
    ⦃fun r s' => LRArmPost b s₁ r s'; ⊤⦄ := by
  dsimp only [lrArmLit]
  vcgen [step, L.evalE_spec, L.evalC_spec, evalArgs, setLoc, setLocs,
      scanQuotedNat_spec p b hb hpd hpq n,
      L.Scan.Str.scanString_spec p b hb hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt n,
      readNat_spec p b hprn n]
  all_goals subst_vars
  all_goals try rfl
  all_goals simp only [Cond.pval, Expr.pval, L.rd8, St.setLoc_loc, St.setLocs_nil, St.setLocs_cons,
      List.headD_cons, List.tail_cons, Cmp.eval, BinOp.eval, Bool.or_eq_true, Bool.not_eq_true',
      beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq, Nat.reduceEqDiff, reduceIte] at *
  all_goals grind (splits := 40) [lang_grind, LRArmPost, lrStepS, lrStepN, lrLit, litEnd,
    Sig.retOr]

attribute [local lang_grind] LRS.fail Fld.none in
include hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hpl hpml hpbo hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hphn hpho hph hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_axiomD hp_defD hp_thmD hp_opaqueD hp_quotD hp_indD in
theorem lrArmDecl_spec (n : Nat) (s₁ : St) :
    ⦃fun s => s = s₁ ∧ s.mem.arr8 IN = b ∧ (s.loc 12).toNat ≤ b.size ∧
      (s.loc 11 = 4 ∨ s.loc 11 = 12 ∨ s.loc 11 = 60 ∨ s.loc 11 = 45 ∨ s.loc 11 = 49 ∨
        s.loc 11 = 23)⦄
    step p (exec p n) lrArmDecl
    ⦃fun r s' => LRArmPost b s₁ r s'; ⊤⦄ := by
  dsimp only [lrArmDecl]
  vcgen [step, L.evalE_spec, L.evalC_spec, evalArgs, setLoc, setLocs,
      L.Scan.Records.scanAxiomD_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpl hpml hpbo hp_axiomD n,
      L.Scan.Records.scanDefD_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpmw hphn hpho hph hpl hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_defD n,
      L.Scan.Records.scanThmD_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpl hp_thmD n,
      L.Scan.Records.scanOpaqueD_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpl hpml hpbo hp_opaqueD n,
      L.Scan.Records.scanQuotD_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpl hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hp_quotD n,
      L.Scan.Records.scanIndD_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpl hpml hpbo hp_rule hp_rules hp_indRec hp_indRecs hp_indType hp_indTypes hp_indCtor hp_indCtors hp_indD n]
  all_goals subst_vars
  all_goals try rfl
  all_goals simp only [Cond.pval, Expr.pval, L.rd8, St.setLoc_loc, St.setLocs_nil, St.setLocs_cons,
      List.headD_cons, List.tail_cons, Cmp.eval, BinOp.eval, Bool.or_eq_true, Bool.not_eq_true',
      beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq, Nat.reduceEqDiff, reduceIte] at *
  all_goals grind (splits := 40) [lang_grind, LRArmPost, lrStepS, lrStepN, lrDecl, lineVal,
    Sig.retOr]

attribute [local lang_grind] LRS.fail Fld.none in
include hpsc hpbr in
theorem lrArmMeta_spec (n : Nat) (s₁ : St) :
    ⦃fun s => s = s₁ ∧ s.mem.arr8 IN = b ∧ (s.loc 12).toNat ≤ b.size ∧ s.loc 11 = 33⦄
    step p (exec p n) lrArmMeta
    ⦃fun r s' => LRArmPost b s₁ r s'; ⊤⦄ := by
  have hb64 : b.size < 2 ^ 64 := by omega
  dsimp only [lrArmMeta]
  vcgen [step, L.evalE_spec, L.evalC_spec, evalArgs, setLoc, setLocs,
      L.Examples.skipBraced_spec p hpsc hpbr b hb64 n]
  all_goals subst_vars
  all_goals try rfl
  all_goals simp only [Cond.pval, Expr.pval, L.rd8, St.setLoc_loc, St.setLocs_nil, St.setLocs_cons,
      List.headD_cons, List.tail_cons, Cmp.eval, BinOp.eval, Bool.or_eq_true, Bool.not_eq_true',
      beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq, Nat.reduceEqDiff, reduceIte] at *
  all_goals grind (splits := 40) [lang_grind, LRArmPost, lrStepS, lrStepN, lrMeta, metaN, byteW,
    Sig.retOr]

end specs

end L.Front.LineRec
