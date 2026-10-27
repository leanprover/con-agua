module

meta import ConAgua.L.Semantics
import ConAgua.Census.Attr
public import ConAgua.Scan.Member
public import ConAgua.Scan.Str
public import ConAgua.Scan.Values
import ConAgua.Front.Preserve
import ConAgua.L.GrindAttr
import ConAgua.Scan.Common
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# The fields of name and level lines (`scan_fast.rs`'s record values)

Stage B's scanner validates a line and stores nothing (`ConAgua.Scan.Line`). This file adds the
values of the records the frontend applies first, names and levels, as a second pass over a line
the validator accepted: `rec_line_loop(i)` walks the line's members again (`next_member`) and
returns five words `(pl, idx, a, c, d)`:

| `pl` | record | `a` | `c` | `d` |
|---|---|---|---|---|
| 1 | name `{"pre":p,"str":s}` | `p` | start of `s`'s body | its end (the closing quote) |
| 2 | name `{"i":n,"pre":p}` | `p` | `n` | |
| 3 | level `succ` | the operand | | |
| 4, 5 | level `max`, `imax` | first operand | second | |
| 6 | level `param` | the name | | |
| 7 | the `meta` header | | | |
| 0 | anything else (expressions, declarations), or a failure | | | |

`idx` is the value of the line's index key (`in`/`il`/`ie`). A number is read by `read_nat`,
con-leche's `readNat64` (`readNatAt` for at most 18 digits); a longer one reads as `NONE`
(`2^64 - 1`), which the caller refuses: no export index or name component has 19 digits, and
refusing is a defined failure.

The pass trusts the validator: it checks no `seen` mask, no comma alternation, no key set (a
member that is not a name/level key ends it with `pl = 0`), and it reads a string's body as the
byte range between its quotes; `ConAgua.Front.FieldsLink` shows that on a line con-leche's
`scanLineFwd` accepts, the words are the record's fields. Each loop keeps con-leche's progress
guard (`e ≤ ks` stops it), which is also what makes its model terminate.
-/

set_option experimental.vcgen true
set_option linter.unusedSectionVars false

open Std.WP
open scoped Lean.Order

namespace L.Front.Fields

open L.Scan.Utf8 (byteW)
open L.Scan.Member
open L.Scan.Values
open L.Scan.Leaves (numEndN)

/-- The input buffer. -/
abbrev IN : ArrId := 0

/-- A number too long to be read (19 digits or more). -/
def NONE : Word := 0xFFFFFFFFFFFFFFFF

/-! ## `read_nat` -/

def readNatLoop : Stmt := lblk (v, e, x) {
  while 0 == 0 {
    if e <= v { return x };
    x := x * 10 + ((IN.u8[v] - 48) & 255);
    v += 1
  }
}

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:493-497 ConLeche.Frontend.readNatAt -/
@[l_impl ConLeche.Frontend.readNatAt]
def readNat : FunDecl := lfn (v, e) locals (x) {
  if v + 18 < e { return 0xFFFFFFFFFFFFFFFF };
  ⟪readNatLoop⟫;
  return 0
}

/-- con-leche's `readNat64` on words: the digits `[v, e)` into `x`, modulo `2^64`. -/
def rdLoopN (b : Array UInt8) (v e x : Word) : Word :=
  if h : v < e then rdLoopN b (v + 1) e (x * 10 + ((byteW b v - 48) &&& 255)) else x
termination_by e.toNat - v.toNat
decreasing_by
  have := UInt64.lt_iff_toNat_lt.mp h
  have : (v + 1).toNat = v.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; have := e.toNat_lt; omega
  omega

/-- `read_nat(v, e)`. -/
def rdNatN (b : Array UInt8) (v e : Word) : Word := if v + 18 < e then NONE else rdLoopN b v e 0

section
variable (b : Array UInt8) (v e x : Word)
theorem rdLoopN_stop (h : ¬ v < e) : rdLoopN b v e x = x := by rw [rdLoopN, dite_eq_right h]
theorem rdLoopN_step (h : v < e) :
    rdLoopN b v e x = rdLoopN b (v + 1) e (x * 10 + ((byteW b v - 48) &&& 255)) := by
  rw [rdLoopN, dite_eq_left h]
end
grind_pattern [lang_grind] rdLoopN_stop => rdLoopN b v e x
grind_pattern [lang_grind] rdLoopN_step => rdLoopN b v e x, b[v.toNat]

/-! ## `rec_nat_list`: the first two items of a `[…]` -/

def pairLoop : Stmt := lblk (i, cnt, x0, x1, c, e, x) {
  while 0 == 0 {
    if len(IN.u8) <= i { return (0, 0, 0) };
    c := IN.u8[i];
    if c == 93 { return (i + 1, x0, x1) };
    if 48 <= c && c <= 57 {
      e := call num_end(i);
      if e <= i { return (0, 0, 0) };
      x := call read_nat(i, e);
      if cnt == 0 { x0 := x };
      if cnt == 1 { x1 := x };
      cnt += 1;
      i := e
    } else {
      i += 1
    }
  }
}

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:697-699 ConLeche.Frontend.scanNatList -/
@[l_impl ConLeche.Frontend.scanNatList]
def recNatList : FunDecl := lfn (i) locals (cnt, x0, x1, c, e, x) {
  i += 1;
  ⟪pairLoop⟫;
  return (0, 0, 0)
}

/-- The pair loop: `(end, first item, second item)`. -/
def pairN (b : Array UInt8) (i cnt x0 x1 : Word) : Word × Word × Word :=
  if h : i < UInt64.ofNat b.size then
    if byteW b i = 93 then (i + 1, x0, x1)
    else if 48 ≤ byteW b i ∧ byteW b i ≤ 57 then
      if hj : i < UInt64.ofNat (numEndN b i.toNat) then
        pairN b (UInt64.ofNat (numEndN b i.toNat)) (cnt + 1)
          (if cnt = 0 then rdNatN b i (UInt64.ofNat (numEndN b i.toNat)) else x0)
          (if cnt = 1 then rdNatN b i (UInt64.ofNat (numEndN b i.toNat)) else x1)
      else (0, 0, 0)
    else pairN b (i + 1) cnt x0 x1
  else (0, 0, 0)
termination_by b.size - i.toNat
decreasing_by
  all_goals
    have := L.Scan.lt_of_lt_ofNat h
    first
      | (rw [UInt64.lt_iff_toNat_lt] at hj; omega)
      | (have := L.Scan.toNat_add_one_of_lt_ofNat h; omega)

/-- `rec_nat_list(i)`, `i` at the `[`. -/
def pairEntryN (b : Array UInt8) (i : Word) : Word × Word × Word := pairN b (i + 1) 0 0 0

section
variable (b : Array UInt8) (i cnt x0 x1 : Word)
theorem pairN_end (h : ¬ i < UInt64.ofNat b.size) : pairN b i cnt x0 x1 = (0, 0, 0) := by
  rw [pairN, dite_eq_right h]
theorem pairN_close (h : i < UInt64.ofNat b.size) (hc : byteW b i = 93) :
    pairN b i cnt x0 x1 = (i + 1, x0, x1) := by
  rw [pairN, dite_eq_left h, ite_eq_left hc]
theorem pairN_digit (h : i < UInt64.ofNat b.size) (hc : byteW b i ≠ 93)
    (hd : 48 ≤ byteW b i ∧ byteW b i ≤ 57) (he : i < UInt64.ofNat (numEndN b i.toNat)) :
    pairN b i cnt x0 x1 = pairN b (UInt64.ofNat (numEndN b i.toNat)) (cnt + 1)
      (if cnt = 0 then rdNatN b i (UInt64.ofNat (numEndN b i.toNat)) else x0)
      (if cnt = 1 then rdNatN b i (UInt64.ofNat (numEndN b i.toNat)) else x1) := by
  rw [pairN, dite_eq_left h, ite_eq_right hc, ite_eq_left hd, dite_eq_left he]
theorem pairN_noprog (h : i < UInt64.ofNat b.size) (hc : byteW b i ≠ 93)
    (hd : 48 ≤ byteW b i ∧ byteW b i ≤ 57) (he : ¬ i < UInt64.ofNat (numEndN b i.toNat)) :
    pairN b i cnt x0 x1 = (0, 0, 0) := by
  rw [pairN, dite_eq_left h, ite_eq_right hc, ite_eq_left hd, dite_eq_right he]
theorem pairN_other (h : i < UInt64.ofNat b.size) (hc : byteW b i ≠ 93)
    (hd : ¬ (48 ≤ byteW b i ∧ byteW b i ≤ 57)) :
    pairN b i cnt x0 x1 = pairN b (i + 1) cnt x0 x1 := by
  rw [pairN, dite_eq_left h, ite_eq_right hc, ite_eq_right hd]
end
grind_pattern [lang_grind] pairN_end => pairN b i cnt x0 x1
grind_pattern [lang_grind] pairN_close => pairN b i cnt x0 x1, b[i.toNat]
grind_pattern [lang_grind] pairN_digit => pairN b i cnt x0 x1, b[i.toNat], numEndN b i.toNat
grind_pattern [lang_grind] pairN_noprog => pairN b i cnt x0 x1, b[i.toNat], numEndN b i.toNat
grind_pattern [lang_grind] pairN_other => pairN b i cnt x0 x1, b[i.toNat]

/-! ## `rec_str_name`, `rec_num_name` -/

def strRecLoop : Stmt := lblk (i, w, pre, vs, ve, tag, ks, k, v, e) {
  while 0 == 0 {
    (tag, ks, w, k, v) := call next_member(i, w);
    if tag == 0 { return (0, pre, vs, ve) };
    if tag == 1 { return (ks + 1, pre, vs, ve) };
    if k == 47 {  -- `pre`
      e := call slot_nat(ks, v);
      if e <= ks { return (0, pre, vs, ve) };
      pre := call read_nat(v, e)
    } else {  -- `str`
      e := call scan_string(v);
      if e <= ks { return (0, pre, vs, ve) };
      vs := v + 1;
      ve := e - 1
    };
    i := e;
    w := 0
  }
}

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:831-835 ConLeche.Frontend.scanStrName -/
@[l_impl ConLeche.Frontend.scanStrName]
def recStrName : FunDecl := lfn (i) locals (w, pre, vs, ve, tag, ks, k, v, e) {
  i += 1;
  w := 1;
  ⟪strRecLoop⟫;
  return (0, 0, 0, 0)
}

def numRecLoop : Stmt := lblk (i, w, pre, n, tag, ks, k, v, e) {
  while 0 == 0 {
    (tag, ks, w, k, v) := call next_member(i, w);
    if tag == 0 { return (0, pre, n) };
    if tag == 1 { return (ks + 1, pre, n) };
    e := call slot_nat(ks, v);
    if e <= ks { return (0, pre, n) };
    if k == 47 {  -- `pre`
      pre := call read_nat(v, e)
    } else {  -- `i`
      n := call read_nat(v, e)
    };
    i := e;
    w := 0
  }
}

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:886-890 ConLeche.Frontend.scanNumName -/
@[l_impl ConLeche.Frontend.scanNumName]
def recNumName : FunDecl := lfn (i) locals (w, pre, n, tag, ks, k, v, e) {
  i += 1;
  w := 1;
  ⟪numRecLoop⟫;
  return (0, 0, 0)
}

/-- The `str` name loop: `(end, pre, body start, body end)`. -/
def strRecN (b : Array UInt8) (i w pre vs ve : Word) : Word × Word × Word × Word :=
  if (nextMemberN b i w).tag = 0 then (0, pre, vs, ve)
  else if (nextMemberN b i w).tag = 1 then ((nextMemberN b i w).pos + 1, pre, vs, ve)
  else if (nextMemberN b i w).key = 47 then
    if _h : (nextMemberN b i w).pos < slotNatN b (nextMemberN b i w).pos (nextMemberN b i w).val then
      strRecN b (slotNatN b (nextMemberN b i w).pos (nextMemberN b i w).val) 0
        (rdNatN b (nextMemberN b i w).val
          (slotNatN b (nextMemberN b i w).pos (nextMemberN b i w).val)) vs ve
    else (0, pre, vs, ve)
  else
    if _h : (nextMemberN b i w).pos < L.Scan.Str.scanStringN b (nextMemberN b i w).val then
      strRecN b (L.Scan.Str.scanStringN b (nextMemberN b i w).val) 0 pre
        ((nextMemberN b i w).val + 1) (L.Scan.Str.scanStringN b (nextMemberN b i w).val - 1)
    else (0, pre, vs, ve)
termination_by b.size - i.toNat
decreasing_by
  all_goals
    have hk := nextMemberN_key b i w (nextMemberN_tag b i w (by assumption) (by assumption))
    have := L.Scan.lt_of_lt_ofNat hk.2
    rw [UInt64.le_iff_toNat_le] at hk
    rw [UInt64.lt_iff_toNat_lt] at _h
    omega

/-- The `num` name loop: `(end, pre, i)`. -/
def numRecN (b : Array UInt8) (i w pre n : Word) : Word × Word × Word :=
  if (nextMemberN b i w).tag = 0 then (0, pre, n)
  else if (nextMemberN b i w).tag = 1 then ((nextMemberN b i w).pos + 1, pre, n)
  else if _h : (nextMemberN b i w).pos < slotNatN b (nextMemberN b i w).pos (nextMemberN b i w).val then
    if (nextMemberN b i w).key = 47 then
      numRecN b (slotNatN b (nextMemberN b i w).pos (nextMemberN b i w).val) 0
        (rdNatN b (nextMemberN b i w).val
          (slotNatN b (nextMemberN b i w).pos (nextMemberN b i w).val)) n
    else
      numRecN b (slotNatN b (nextMemberN b i w).pos (nextMemberN b i w).val) 0 pre
        (rdNatN b (nextMemberN b i w).val
          (slotNatN b (nextMemberN b i w).pos (nextMemberN b i w).val))
  else (0, pre, n)
termination_by b.size - i.toNat
decreasing_by
  all_goals
    have hk := nextMemberN_key b i w (nextMemberN_tag b i w (by assumption) (by assumption))
    have := L.Scan.lt_of_lt_ofNat hk.2
    rw [UInt64.le_iff_toNat_le] at hk
    rw [UInt64.lt_iff_toNat_lt] at _h
    omega

/-- `rec_str_name(i)`, `i` at the `{`. -/
def strRecEntryN (b : Array UInt8) (i : Word) : Word × Word × Word × Word := strRecN b (i + 1) 1 0 0 0
/-- `rec_num_name(i)`, `i` at the `{`. -/
def numRecEntryN (b : Array UInt8) (i : Word) : Word × Word × Word := numRecN b (i + 1) 1 0 0

section
variable (b : Array UInt8) (i w pre vs ve n : Word)
theorem strRecN_err (h : (nextMemberN b i w).tag = 0) : strRecN b i w pre vs ve = (0, pre, vs, ve) := by
  rw [strRecN, ite_eq_left h]
theorem strRecN_close (h : (nextMemberN b i w).tag = 1) :
    strRecN b i w pre vs ve = ((nextMemberN b i w).pos + 1, pre, vs, ve) := by
  rw [strRecN, ite_eq_right (by simp [h]), ite_eq_left h]
theorem strRecN_key (h0 : (nextMemberN b i w).tag ≠ 0) (h1 : (nextMemberN b i w).tag ≠ 1) :
    strRecN b i w pre vs ve =
      if (nextMemberN b i w).key = 47 then
        if (nextMemberN b i w).pos < slotNatN b (nextMemberN b i w).pos (nextMemberN b i w).val then
          strRecN b (slotNatN b (nextMemberN b i w).pos (nextMemberN b i w).val) 0
            (rdNatN b (nextMemberN b i w).val
              (slotNatN b (nextMemberN b i w).pos (nextMemberN b i w).val)) vs ve
        else (0, pre, vs, ve)
      else
        if (nextMemberN b i w).pos < L.Scan.Str.scanStringN b (nextMemberN b i w).val then
          strRecN b (L.Scan.Str.scanStringN b (nextMemberN b i w).val) 0 pre
            ((nextMemberN b i w).val + 1) (L.Scan.Str.scanStringN b (nextMemberN b i w).val - 1)
        else (0, pre, vs, ve) := by
  rw [strRecN, ite_eq_right h0, ite_eq_right h1]
  simp only [dite_eq_ite]
theorem numRecN_err (h : (nextMemberN b i w).tag = 0) : numRecN b i w pre n = (0, pre, n) := by
  rw [numRecN, ite_eq_left h]
theorem numRecN_close (h : (nextMemberN b i w).tag = 1) :
    numRecN b i w pre n = ((nextMemberN b i w).pos + 1, pre, n) := by
  rw [numRecN, ite_eq_right (by simp [h]), ite_eq_left h]
theorem numRecN_key (h0 : (nextMemberN b i w).tag ≠ 0) (h1 : (nextMemberN b i w).tag ≠ 1) :
    numRecN b i w pre n =
      if (nextMemberN b i w).pos < slotNatN b (nextMemberN b i w).pos (nextMemberN b i w).val then
        if (nextMemberN b i w).key = 47 then
          numRecN b (slotNatN b (nextMemberN b i w).pos (nextMemberN b i w).val) 0
            (rdNatN b (nextMemberN b i w).val
              (slotNatN b (nextMemberN b i w).pos (nextMemberN b i w).val)) n
        else
          numRecN b (slotNatN b (nextMemberN b i w).pos (nextMemberN b i w).val) 0 pre
            (rdNatN b (nextMemberN b i w).val
              (slotNatN b (nextMemberN b i w).pos (nextMemberN b i w).val))
      else (0, pre, n) := by
  rw [numRecN, ite_eq_right h0, ite_eq_right h1]
  simp only [dite_eq_ite]
end
grind_pattern [lang_grind] strRecN_err => strRecN b i w pre vs ve, nextMemberN b i w
grind_pattern [lang_grind] strRecN_close => strRecN b i w pre vs ve, nextMemberN b i w
grind_pattern [lang_grind] strRecN_key => strRecN b i w pre vs ve, nextMemberN b i w
grind_pattern [lang_grind] numRecN_err => numRecN b i w pre n, nextMemberN b i w
grind_pattern [lang_grind] numRecN_close => numRecN b i w pre n, nextMemberN b i w
grind_pattern [lang_grind] numRecN_key => numRecN b i w pre n, nextMemberN b i w

/-! ## `rec_line_loop` -/

def recLoop : Stmt := lblk (i, w, pl, idx, a, c, d, tag, ks, k, v, e, x) {
  while 0 == 0 {
    (tag, ks, w, k, v) := call next_member(i, w);
    if tag == 0 { return (0, 0, 0, 0, 0) };
    if tag == 1 { return (pl, idx, a, c, d) };
    if k == 21 || k == 19 || k == 18 {  -- `in`, `il`, `ie`
      e := call slot_nat(ks, v);
      if e <= ks { return (0, 0, 0, 0, 0) };
      idx := call read_nat(v, e)
    } else if k == 59 || k == 46 {  -- `succ`, `param`
      e := call slot_nat(ks, v);
      if e <= ks { return (0, 0, 0, 0, 0) };
      a := call read_nat(v, e);
      if k == 59 { pl := 3 } else { pl := 6 }
    } else if k == 32 || k == 20 {  -- `max`, `imax`
      (e, a, c) := call rec_nat_list(v);
      if e <= ks { return (0, 0, 0, 0, 0) };
      if k == 32 { pl := 4 } else { pl := 5 }
    } else if k == 56 {  -- `str`
      (e, a, c, d) := call rec_str_name(v);
      if e <= ks { return (0, 0, 0, 0, 0) };
      pl := 1
    } else if k == 38 {  -- `num`
      (e, a, c) := call rec_num_name(v);
      if e <= ks { return (0, 0, 0, 0, 0) };
      pl := 2
    } else if k == 33 {  -- `meta`
      if !(v < len(IN.u8) && IN.u8[v] == 123) { return (0, 0, 0, 0, 0) };
      e := call skip_braced(v + 1, 0);
      if e <= ks { return (0, 0, 0, 0, 0) };
      pl := 7
    } else {
      return (0, 0, 0, 0, 0)
    };
    i := e;
    w := 0
  }
}

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:2427-2574 ConLeche.Frontend.scanLineLoop -/
@[l_impl ConLeche.Frontend.scanLineLoop]
def recLineLoop : FunDecl := lfn (i) locals (w, pl, idx, a, c, d, tag, ks, k, v, e, x) {
  w := 1;
  ⟪recLoop⟫;
  return (0, 0, 0, 0, 0)
}

/-- What `rec_line_loop` returns. -/
structure Fld where
  pl : Word
  idx : Word
  a : Word
  c : Word
  d : Word

/-- The five words. -/
def Fld.enc (f : Fld) : List Word := [f.pl, f.idx, f.a, f.c, f.d]

/-- Not a name or level line, or a failure. -/
def Fld.none : Fld := ⟨0, 0, 0, 0, 0⟩

/-- The end of the `meta` header's object at `v`, or `0`. -/
def metaN (b : Array UInt8) (v : Word) : Word :=
  if v < UInt64.ofNat b.size ∧ byteW b v = 123 then
    UInt64.ofNat (L.Examples.skipBracedN b (v + 1).toNat 0) else 0

/-- The line loop. -/
def recN (b : Array UInt8) (i w : Word) (f : Fld) : Fld :=
  if (nextMemberN b i w).tag = 0 then .none
  else if (nextMemberN b i w).tag = 1 then f
  else if (nextMemberN b i w).key = 21 ∨ (nextMemberN b i w).key = 19 ∨
      (nextMemberN b i w).key = 18 then
    if _h : (nextMemberN b i w).pos < slotNatN b (nextMemberN b i w).pos (nextMemberN b i w).val then
      recN b (slotNatN b (nextMemberN b i w).pos (nextMemberN b i w).val) 0
        ⟨f.pl, rdNatN b (nextMemberN b i w).val
          (slotNatN b (nextMemberN b i w).pos (nextMemberN b i w).val), f.a, f.c, f.d⟩
    else .none
  else if (nextMemberN b i w).key = 59 ∨ (nextMemberN b i w).key = 46 then
    if _h : (nextMemberN b i w).pos < slotNatN b (nextMemberN b i w).pos (nextMemberN b i w).val then
      recN b (slotNatN b (nextMemberN b i w).pos (nextMemberN b i w).val) 0
        ⟨if (nextMemberN b i w).key = 59 then 3 else 6, f.idx,
          rdNatN b (nextMemberN b i w).val
            (slotNatN b (nextMemberN b i w).pos (nextMemberN b i w).val), f.c, f.d⟩
    else .none
  else if (nextMemberN b i w).key = 32 ∨ (nextMemberN b i w).key = 20 then
    if _h : (nextMemberN b i w).pos < (pairEntryN b (nextMemberN b i w).val).1 then
      recN b (pairEntryN b (nextMemberN b i w).val).1 0
        ⟨if (nextMemberN b i w).key = 32 then 4 else 5, f.idx,
          (pairEntryN b (nextMemberN b i w).val).2.1,
          (pairEntryN b (nextMemberN b i w).val).2.2, f.d⟩
    else .none
  else if (nextMemberN b i w).key = 56 then
    if _h : (nextMemberN b i w).pos < (strRecEntryN b (nextMemberN b i w).val).1 then
      recN b (strRecEntryN b (nextMemberN b i w).val).1 0
        ⟨1, f.idx, (strRecEntryN b (nextMemberN b i w).val).2.1,
          (strRecEntryN b (nextMemberN b i w).val).2.2.1,
          (strRecEntryN b (nextMemberN b i w).val).2.2.2⟩
    else .none
  else if (nextMemberN b i w).key = 38 then
    if _h : (nextMemberN b i w).pos < (numRecEntryN b (nextMemberN b i w).val).1 then
      recN b (numRecEntryN b (nextMemberN b i w).val).1 0
        ⟨2, f.idx, (numRecEntryN b (nextMemberN b i w).val).2.1,
          (numRecEntryN b (nextMemberN b i w).val).2.2, f.d⟩
    else .none
  else if (nextMemberN b i w).key = 33 then
    if _h : (nextMemberN b i w).pos < metaN b (nextMemberN b i w).val then
      recN b (metaN b (nextMemberN b i w).val) 0 ⟨7, f.idx, f.a, f.c, f.d⟩
    else .none
  else .none
termination_by b.size - i.toNat
decreasing_by
  all_goals
    have hk := nextMemberN_key b i w (nextMemberN_tag b i w (by assumption) (by assumption))
    have := L.Scan.lt_of_lt_ofNat hk.2
    rw [UInt64.le_iff_toNat_le] at hk
    rw [UInt64.lt_iff_toNat_lt] at _h
    omega

/-- `rec_line_loop(i)`, `i` after the line's `{`. -/
def recLineN (b : Array UInt8) (i : Word) : Fld := recN b i 1 .none

section
variable (b : Array UInt8) (i w : Word) (f : Fld)
theorem recN_err (h : (nextMemberN b i w).tag = 0) : recN b i w f = .none := by
  rw [recN, ite_eq_left h]
theorem recN_close (h : (nextMemberN b i w).tag = 1) : recN b i w f = f := by
  rw [recN, ite_eq_right (by simp [h]), ite_eq_left h]
theorem recN_key (h0 : (nextMemberN b i w).tag ≠ 0) (h1 : (nextMemberN b i w).tag ≠ 1) :
    recN b i w f =
  if (nextMemberN b i w).key = 21 ∨ (nextMemberN b i w).key = 19 ∨
      (nextMemberN b i w).key = 18 then
    if (nextMemberN b i w).pos < slotNatN b (nextMemberN b i w).pos (nextMemberN b i w).val then
      recN b (slotNatN b (nextMemberN b i w).pos (nextMemberN b i w).val) 0
        ⟨f.pl, rdNatN b (nextMemberN b i w).val
          (slotNatN b (nextMemberN b i w).pos (nextMemberN b i w).val), f.a, f.c, f.d⟩
    else .none
  else if (nextMemberN b i w).key = 59 ∨ (nextMemberN b i w).key = 46 then
    if (nextMemberN b i w).pos < slotNatN b (nextMemberN b i w).pos (nextMemberN b i w).val then
      recN b (slotNatN b (nextMemberN b i w).pos (nextMemberN b i w).val) 0
        ⟨if (nextMemberN b i w).key = 59 then 3 else 6, f.idx,
          rdNatN b (nextMemberN b i w).val
            (slotNatN b (nextMemberN b i w).pos (nextMemberN b i w).val), f.c, f.d⟩
    else .none
  else if (nextMemberN b i w).key = 32 ∨ (nextMemberN b i w).key = 20 then
    if (nextMemberN b i w).pos < (pairEntryN b (nextMemberN b i w).val).1 then
      recN b (pairEntryN b (nextMemberN b i w).val).1 0
        ⟨if (nextMemberN b i w).key = 32 then 4 else 5, f.idx,
          (pairEntryN b (nextMemberN b i w).val).2.1,
          (pairEntryN b (nextMemberN b i w).val).2.2, f.d⟩
    else .none
  else if (nextMemberN b i w).key = 56 then
    if (nextMemberN b i w).pos < (strRecEntryN b (nextMemberN b i w).val).1 then
      recN b (strRecEntryN b (nextMemberN b i w).val).1 0
        ⟨1, f.idx, (strRecEntryN b (nextMemberN b i w).val).2.1,
          (strRecEntryN b (nextMemberN b i w).val).2.2.1,
          (strRecEntryN b (nextMemberN b i w).val).2.2.2⟩
    else .none
  else if (nextMemberN b i w).key = 38 then
    if (nextMemberN b i w).pos < (numRecEntryN b (nextMemberN b i w).val).1 then
      recN b (numRecEntryN b (nextMemberN b i w).val).1 0
        ⟨2, f.idx, (numRecEntryN b (nextMemberN b i w).val).2.1,
          (numRecEntryN b (nextMemberN b i w).val).2.2, f.d⟩
    else .none
  else if (nextMemberN b i w).key = 33 then
    if (nextMemberN b i w).pos < metaN b (nextMemberN b i w).val then
      recN b (metaN b (nextMemberN b i w).val) 0 ⟨7, f.idx, f.a, f.c, f.d⟩
    else .none
  else .none := by
  rw [recN, ite_eq_right h0, ite_eq_right h1]
  simp only [dite_eq_ite]
end
grind_pattern [lang_grind] recN_err => recN b i w f, nextMemberN b i w
grind_pattern [lang_grind] recN_close => recN b i w f, nextMemberN b i w
grind_pattern [lang_grind] recN_key => recN b i w f, nextMemberN b i w

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
    (hpbr : p.lookup "skip_braced" = some L.Examples.skipBraced)
    (hprn : p.lookup "read_nat" = some readNat)
    (hprp : p.lookup "rec_nat_list" = some recNatList)
    (hprs : p.lookup "rec_str_name" = some recStrName)
    (hprm : p.lookup "rec_num_name" = some recNumName)
    (hprl : p.lookup "rec_line_loop" = some recLineLoop)
include hb

theorem readNatLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n readNatLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [rdLoopN b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := readNatLoop) rfl]
    sym only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld8, ih] <;> finish

theorem readNatLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    step p (exec p n) readNatLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [rdLoopN b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ :=
  Triple.step_exec (readNatLoop_spec p b hb (n + 1) s₀)

include hprn in
attribute [local lang_grind] rdNatN NONE in
theorem readNat_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (v e : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "read_nat" [v, e]
    ⦃fun r s' => s' = s₀ ∧ r = [rdNatN b v e]; ⊤⦄ := by
  rw [invoke_eq _ hprn]
  simp only [callFn, readNat]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, readNatLoop_step_spec p b hb n] <;> finish

include hpd hpn hprn in
theorem pairLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n pairLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0, 0, 0] = [(pairN b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3)).1,
        (pairN b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3)).2.1,
        (pairN b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3)).2.2]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := pairLoop) rfl]
    have hb64 : b.size < 2 ^ 64 := by omega
    sym only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld8, ih,
        L.Scan.Leaves.numEnd_spec p hpd hpn b hb64 n, readNat_spec p b hb hprn n] <;> finish

include hpd hpn hprn in
theorem pairLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    step p (exec p n) pairLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0, 0, 0] = [(pairN b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3)).1,
        (pairN b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3)).2.1,
        (pairN b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3)).2.2]; ⊤⦄ :=
  Triple.step_exec (pairLoop_spec p b hb hpd hpn hprn (n + 1) s₀)

include hpd hpn hprn hprp in
attribute [local lang_grind] pairEntryN in
theorem recNatList_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "rec_nat_list" [i]
    ⦃fun r s' => s' = s₀ ∧
      r = [(pairEntryN b i).1, (pairEntryN b i).2.1, (pairEntryN b i).2.2]; ⊤⦄ := by
  rw [invoke_eq _ hprp]
  simp only [callFn, recNatList]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, pairLoop_step_spec p b hb hpd hpn hprn n] <;>
        finish

include hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hprn in
theorem strRecLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n strRecLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0, 0, 0, 0] =
        [(strRecN b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 4)).1,
         (strRecN b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 4)).2.1,
         (strRecN b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 4)).2.2.1,
         (strRecN b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 4)).2.2.2]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := strRecLoop) rfl]
    sym (gen := 16) only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih,
        nextMember_spec p b hb hpw hpk hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm n,
        L.Scan.Str.scanString_spec p b hb ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› n,
        slotNat_spec p b hb ‹_› ‹_› ‹_› n, readNat_spec p b hb hprn n] <;> finish

include hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hprn in
theorem strRecLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    step p (exec p n) strRecLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0, 0, 0, 0] =
        [(strRecN b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 4)).1,
         (strRecN b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 4)).2.1,
         (strRecN b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 4)).2.2.1,
         (strRecN b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 4)).2.2.2]; ⊤⦄ :=
  Triple.step_exec (strRecLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hprn (n + 1) s₀)

include hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hprn hprs in
attribute [local lang_grind] strRecEntryN in
theorem recStrName_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "rec_str_name" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [(strRecEntryN b i).1, (strRecEntryN b i).2.1,
      (strRecEntryN b i).2.2.1, (strRecEntryN b i).2.2.2]; ⊤⦄ := by
  rw [invoke_eq _ hprs]
  simp only [callFn, recStrName]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc,
        strRecLoop_step_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hprn n] <;>
        finish

include hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hprn in
theorem numRecLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n numRecLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0, 0, 0] =
        [(numRecN b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3)).1,
         (numRecN b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3)).2.1,
         (numRecN b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3)).2.2]; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := numRecLoop) rfl]
    sym (gen := 16) only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih,
        nextMember_spec p b hb hpw hpk hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm n,
        slotNat_spec p b hb ‹_› ‹_› ‹_› n, readNat_spec p b hb hprn n] <;> finish

include hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hprn in
theorem numRecLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    step p (exec p n) numRecLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0, 0, 0] =
        [(numRecN b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3)).1,
         (numRecN b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3)).2.1,
         (numRecN b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3)).2.2]; ⊤⦄ :=
  Triple.step_exec (numRecLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hprn (n + 1) s₀)

include hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hprn hprm in
attribute [local lang_grind] numRecEntryN in
theorem recNumName_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "rec_num_name" [i]
    ⦃fun r s' => s' = s₀ ∧ r = [(numRecEntryN b i).1, (numRecEntryN b i).2.1,
      (numRecEntryN b i).2.2]; ⊤⦄ := by
  rw [invoke_eq _ hprm]
  simp only [callFn, recNumName]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc,
        numRecLoop_step_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hprn n] <;>
        finish

attribute [local lang_grind] Mbr.err Fld.enc Fld.none metaN

include hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hpbr hprn hprp hprs hprm in
set_option maxHeartbeats 4000000 in
theorem recLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n recLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr Fld.none.enc = (recN b (s₀.loc 0) (s₀.loc 1)
        ⟨s₀.loc 2, s₀.loc 3, s₀.loc 4, s₀.loc 5, s₀.loc 6⟩).enc; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := recLoop) rfl]
    have hb64 : b.size < 2 ^ 64 := by omega
    sym (gen := 16) only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld8, ih,
        nextMember_spec p b hb hpw hpk hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm n,
        slotNat_spec p b hb ‹_› ‹_› ‹_› n, readNat_spec p b hb hprn n,
        recNatList_spec p b hb hpd hpn hprn hprp n,
        recStrName_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hprn hprs n,
        recNumName_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hprn hprm n,
        L.Examples.skipBraced_spec p ‹_› ‹_› b hb64 n] <;> finish

include hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hpbr hprn hprp hprs hprm in
theorem recLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    step p (exec p n) recLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr Fld.none.enc = (recN b (s₀.loc 0) (s₀.loc 1)
        ⟨s₀.loc 2, s₀.loc 3, s₀.loc 4, s₀.loc 5, s₀.loc 6⟩).enc; ⊤⦄ :=
  Triple.step_exec (recLoop_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hpbr hprn hprp hprs hprm (n + 1) s₀)

include hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hpbr hprn hprp hprs hprm hprl in
attribute [local lang_grind] recLineN in
theorem recLineLoop_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "rec_line_loop" [i]
    ⦃fun r s' => s' = s₀ ∧ r = (recLineN b i).enc; ⊤⦄ := by
  rw [invoke_eq _ hprl]
  simp only [callFn, recLineLoop]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, recLoop_step_spec p b hb hpw hpd hpk hpn hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv hpm hps hpc hpu8 hpbi hphv hp4 hp3 hpux hpue hpsc hpe hpt hpbr hprn hprp hprs hprm n] <;>
        finish

end specs

end L.Front.Fields
