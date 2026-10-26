module

public import ConAgua.Front.DeclIface
public import ConAgua.Scan.Records
public import ConAgua.Census.Attr
meta import ConAgua.L.Semantics

@[expose] public section

/-!
# The fields of declaration lines

A second pass over a declaration line the validator accepted (as `ConAgua.Front.Fields` does
for names and levels), returning the eight words of `DFld` (`ConAgua.Front.DeclIface`):

* `rec_decl_obj(i)` (`i` at the record's `{`): one member loop for the five non-inductive
  records (`axiom`, `def`, `thm`, `opaque`, `quot`). By key: `name`/`type`/`value` numbers
  (`slot_nat`, `read_nat`); `levelParams` its position (the list skipped by `scan_nat_list`);
  `all` skipped the same way; `isUnsafe` by `scan_bool`; `hints` ended by `scan_hints`, its kind
  and height read by `hints_val`; `safety`/`kind` ended by `scan_string`, its body classified by
  `str_code` (raw bytes against the literals `DLITS`, `has_escape` for a backslash). Any other key
  fails. Each member is one call `d_member` (with the fields so far, returning them after: a
  branch-free loop body keeps the verification conditions small). It returns the end (or `0`)
  and the seven fields; `hints` starts as `regular 0` (`hk = 3`), con-leche's default.
* `rec_decl_line(i)` (`i` after the line's `{`): the line's members; a declaration key reads the
  record (`pl` `20`‥`24`), `inductive` is only validated (Stage B's `scan_ind_decl`, `pl = 25`),
  any other key fails (`DFld.none`). Each member is one call `decl_val`, as above.

The specs are in `FieldsDeclSpec.lean`.

As in `Fields.lean`, the pass checks no `seen` mask and no key set: `FieldsDeclLink` relates it
to con-leche's loops on their `ok` path only.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Front.Fields

open L.Scan.Utf8 (byteW)
open L.Scan.Member
open L.Scan.Values
open L.Scan.Lit (matchLitN encBool scanBoolN)
open L.Scan.Leaves (numEndN skipWsN keyEndN hasEscapeN)
open L.Scan.Key (valueAtN)
open L.Scan.Records (boolEndN)

/-! ## `match_dlit`, `str_code` -/

/-- The literals of `str_code`: `safe` at `0`, `type` at `4`, `ctor` at `8`, `lift` at `12`,
`ind` at `16`. -/
def DLITS : List UInt8 := [115, 97, 102, 101, 116, 121, 112, 101, 99, 116, 111, 114, 108, 105, 102,
  116, 105, 110, 100]

theorem DLITS_length : DLITS.length = 19 := rfl

def matchDlitLoop : Stmt := lblk (i, o, n, k, c) {
  while k < n {
    if i + k < len(IN.u8) { c := IN.u8[i + k] } else { c := 0 };
    if c != DLITS.c8[o + k] { return 0 };
    k += 1
  }
}

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:2427-2574 ConLeche.Frontend.scanLineLoop -/
def matchDlit : FunDecl := lfn (i, o, n) locals (k, c) { ⟪matchDlitLoop⟫; return 1 }

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:2427-2574 ConLeche.Frontend.scanLineLoop -/
def strCode : FunDecl := lfn (c, d, k) locals (z, m) {
  if len(IN.u8) < c { return 0 };
  z := call has_escape(c, d);
  if z != 0 { if k == 54 { return 2 }; return 5 };
  if k == 54 {
    if d - c == 4 {
      m := call match_dlit(c, 0, 4);
      if m != 0 { return 1 }
    };
    return 0
  };
  if d - c == 4 {
    m := call match_dlit(c, 4, 4);
    if m != 0 { return 1 };
    m := call match_dlit(c, 8, 4);
    if m != 0 { return 2 };
    m := call match_dlit(c, 12, 4);
    if m != 0 { return 3 }
  };
  if d - c == 3 {
    m := call match_dlit(c, 16, 3);
    if m != 0 { return 4 }
  };
  return 0
}

/-- `str_code(c, d, k)`: the string body `[c, d)` of the key `k` (`54` safety, `28` kind)
classified (`DeclIface`'s table). -/
def strCodeN (b : Array UInt8) (c d k : Word) : Word :=
  if UInt64.ofNat b.size < c then 0
  else if UInt64.ofNat (hasEscapeN b c.toNat d.toNat) ≠ 0 then (if k = 54 then 2 else 5)
  else if k = 54 then (if d - c = 4 ∧ matchLitN b c.toNat DLITS 0 4 0 = true then 1 else 0)
  else if d - c = 4 ∧ matchLitN b c.toNat DLITS 4 4 0 = true then 1
  else if d - c = 4 ∧ matchLitN b c.toNat DLITS 8 4 0 = true then 2
  else if d - c = 4 ∧ matchLitN b c.toNat DLITS 12 4 0 = true then 3
  else if d - c = 3 ∧ matchLitN b c.toNat DLITS 16 3 0 = true then 4
  else 0

/-! ## `hints_val` -/

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:2427-2574 ConLeche.Frontend.scanLineLoop -/
def hintsVal : FunDecl := lfn (v) locals (p, ke, x, e) {
  if len(IN.u8) <= v { return (0, 0) };
  if IN.u8[v] == 34 {
    if v + 1 < len(IN.u8) && IN.u8[v + 1] == 97 { return (1, 0) };
    return (2, 0)
  };
  p := call skip_ws(v + 1);
  if len(IN.u8) <= p + 1 { return (0, 0) };
  ke := call key_end(p + 1);
  if len(IN.u8) <= ke { return (0, 0) };
  x := call value_at(p, ke);
  e := call num_end(x);
  e := call read_nat(x, e);
  return (3, e)
}

/-- `hints_val(v)`: the kind of the `hints` value at `v` (`1` abbrev, `2` opaque, `3` regular)
and the height of a `regular`. Only meaningful where `scan_hints` accepted the value. -/
def hkvN (b : Array UInt8) (v : Word) : Word × Word :=
  if UInt64.ofNat b.size ≤ v then (0, 0)
  else if byteW b v = 34 then
    (if v + 1 < UInt64.ofNat b.size ∧ byteW b (v + 1) = 97 then (1, 0) else (2, 0))
  else if UInt64.ofNat b.size ≤ UInt64.ofNat (skipWsN b (v + 1).toNat) + 1 then (0, 0)
  else if UInt64.ofNat b.size ≤
      UInt64.ofNat (keyEndN b (UInt64.ofNat (skipWsN b (v + 1).toNat) + 1).toNat) then (0, 0)
  else (3, rdNatN b (valueAtN b (UInt64.ofNat (skipWsN b (v + 1).toNat))
      (UInt64.ofNat (keyEndN b (UInt64.ofNat (skipWsN b (v + 1).toNat) + 1).toNat)))
    (UInt64.ofNat (numEndN b (valueAtN b (UInt64.ofNat (skipWsN b (v + 1).toNat))
      (UInt64.ofNat (keyEndN b (UInt64.ofNat (skipWsN b (v + 1).toNat) + 1).toNat))).toNat)))

/-! ## `rec_decl_obj` -/

/-- One member, by key `k` (value at `v`, key quote at `ks`), with the fields so far: the end
of the value (`0`: failure) and the fields after. -/
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:2427-2574 ConLeche.Frontend.scanLineLoop
def dMember : FunDecl := lfn (ks, k, v, nm, lp, ty, vl, hk, hn, fl) locals (e, x, ok, y) {
  if k == 34 || k == 61 || k == 65 {  -- `name`, `type`, `value`
    e := call slot_nat(ks, v);
    x := call read_nat(v, e);
    if k == 34 { return (e, x, lp, ty, vl, hk, hn, fl) };
    if k == 61 { return (e, nm, lp, x, vl, hk, hn, fl) };
    return (e, nm, lp, ty, x, hk, hn, fl)
  };
  if k == 31 || k == 1 {  -- `levelParams`, `all`
    (e, x) := call scan_nat_list(v);
    if k == 31 { return (e, nm, v, ty, vl, hk, hn, fl) };
    return (e, nm, lp, ty, vl, hk, hn, fl)
  };
  if k == 26 {  -- `isUnsafe`
    (ok, x, e) := call scan_bool(v);
    if ok == 0 { e := 0 };
    return (e, nm, lp, ty, vl, hk, hn, x)
  };
  if k == 15 {  -- `hints`
    e := call scan_hints(v);
    (x, y) := call hints_val(v);
    return (e, nm, lp, ty, vl, x, y, fl)
  };
  if k == 54 || k == 28 {  -- `safety`, `kind`
    e := call scan_string(v);
    x := call str_code(v + 1, e - 1, k);
    return (e, nm, lp, ty, vl, hk, hn, x)
  };
  return (0, nm, lp, ty, vl, hk, hn, fl)
}

def dobjLoop : Stmt := lblk (i, w, nm, lp, ty, vl, hk, hn, fl, tag, ks, k, v, e) {
  while 0 == 0 {
    (tag, ks, w, k, v) := call next_member(i, w);
    if tag == 0 { return (0, 0, 0, 0, 0, 0, 0, 0) };
    if tag == 1 { return (ks + 1, nm, lp, ty, vl, hk, hn, fl) };
    (e, nm, lp, ty, vl, hk, hn, fl) := call d_member(ks, k, v, nm, lp, ty, vl, hk, hn, fl);
    if e <= ks { return (0, 0, 0, 0, 0, 0, 0, 0) };
    i := e;
    w := 0
  }
}

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:2427-2574 ConLeche.Frontend.scanLineLoop -/
def recDeclObj : FunDecl :=
    lfn (i) locals (w, nm, lp, ty, vl, hk, hn, fl, tag, ks, k, v, e) {
  i += 1;
  w := 1;
  hk := 3;
  ⟪dobjLoop⟫;
  return (0, 0, 0, 0, 0, 0, 0, 0)
}

/-- The flag `scan_bool` reads. -/
def boolValN (b : Array UInt8) (v : Word) : Word := ((encBool (scanBoolN b v.toNat) v).tail).headD 0

/-- The end of a member's value (`0`: failure). -/
def dendN (b : Array UInt8) (ks k v : Word) : Word :=
  if k = 34 ∨ k = 61 ∨ k = 65 then slotNatN b ks v
  else if k = 31 ∨ k = 1 then (natListEntryN b v).1
  else if k = 26 then
    (if (encBool (scanBoolN b v.toNat) v).headD 0 = 0 then 0
     else (encBool (scanBoolN b v.toNat) v).tail.tail.headD 0)
  else if k = 15 then hintsN b v
  else if k = 54 ∨ k = 28 then L.Scan.Str.scanStringN b v
  else 0

/-- A number field after the member: key `kf` stores the number at `v`. -/
def dnumN (b : Array UInt8) (kf ks k v old : Word) : Word :=
  if k = kf then rdNatN b v (slotNatN b ks v) else old

/-- `levelParams` after the member. -/
def dlpsN (k v old : Word) : Word := if k = 31 then v else old

/-- `hints` after the member. -/
def dhkN (b : Array UInt8) (k v old : Word) : Word := if k = 15 then (hkvN b v).1 else old
def dhnN (b : Array UInt8) (k v old : Word) : Word := if k = 15 then (hkvN b v).2 else old

/-- The flag after the member. -/
def dflagN (b : Array UInt8) (k v old : Word) : Word :=
  if k = 26 then boolValN b v
  else if k = 54 ∨ k = 28 then strCodeN b (v + 1) (L.Scan.Str.scanStringN b v - 1) k
  else old

/-- One member of a declaration record with key `k` and value at `v` (`ks` the key's quote):
the end of the value (`0`: failure, or no progress if `≤ ks`) and the fields after. -/
def dstepN (b : Array UInt8) (ks k v : Word) (f : DFld) : Word × DFld :=
  (dendN b ks k v, ⟨0, dnumN b 34 ks k v f.name, dlpsN k v f.lps, dnumN b 61 ks k v f.type,
    dnumN b 65 ks k v f.value, dhkN b k v f.hk, dhnN b k v f.hn, dflagN b k v f.flag⟩)

/-- The member loop: the fields, with `pl` the end (`0`: failure). -/
def dobjN (b : Array UInt8) (i w : Word) (f : DFld) : DFld :=
  if (nextMemberN b i w).tag = 0 then .none
  else if (nextMemberN b i w).tag = 1 then { f with pl := (nextMemberN b i w).pos + 1 }
  else if _h : (nextMemberN b i w).pos <
      (dstepN b (nextMemberN b i w).pos (nextMemberN b i w).key (nextMemberN b i w).val f).1 then
    dobjN b (dstepN b (nextMemberN b i w).pos (nextMemberN b i w).key (nextMemberN b i w).val f).1 0
      (dstepN b (nextMemberN b i w).pos (nextMemberN b i w).key (nextMemberN b i w).val f).2
  else .none
termination_by b.size - i.toNat
decreasing_by
  have hk := nextMemberN_key b i w (nextMemberN_tag b i w (by assumption) (by assumption))
  have := L.Scan.lt_of_lt_ofNat hk.2
  rw [UInt64.le_iff_toNat_le] at hk
  rw [UInt64.lt_iff_toNat_lt] at _h
  omega

/-- The fields a declaration record starts with: `hints` is `regular 0`. -/
def DFld.init : DFld := ⟨0, 0, 0, 0, 0, 3, 0, 0⟩

/-- `rec_decl_obj(i)`, `i` at the `{`. -/
def dobjEntryN (b : Array UInt8) (i : Word) : DFld := dobjN b (i + 1) 1 .init

section
variable (b : Array UInt8) (i w : Word) (f : DFld)
theorem dobjN_err (h : (nextMemberN b i w).tag = 0) : dobjN b i w f = .none := by
  rw [dobjN, if_pos h]
theorem dobjN_close (h : (nextMemberN b i w).tag = 1) :
    dobjN b i w f = { f with pl := (nextMemberN b i w).pos + 1 } := by
  rw [dobjN, if_neg (by simp [h]), if_pos h]
theorem dobjN_key (h0 : (nextMemberN b i w).tag ≠ 0) (h1 : (nextMemberN b i w).tag ≠ 1) :
    dobjN b i w f =
      if (nextMemberN b i w).pos <
          (dstepN b (nextMemberN b i w).pos (nextMemberN b i w).key (nextMemberN b i w).val f).1 then
        dobjN b (dstepN b (nextMemberN b i w).pos (nextMemberN b i w).key (nextMemberN b i w).val f).1 0
          (dstepN b (nextMemberN b i w).pos (nextMemberN b i w).key (nextMemberN b i w).val f).2
      else .none := by
  rw [dobjN, if_neg h0, if_neg h1]
  simp only [dite_eq_ite]
end
grind_pattern [lang_grind] dobjN_err => dobjN b i w f, nextMemberN b i w
grind_pattern [lang_grind] dobjN_close => dobjN b i w f, nextMemberN b i w
grind_pattern [lang_grind] dobjN_key => dobjN b i w f, nextMemberN b i w

/-! ## `rec_decl_line` -/

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:2427-2574 ConLeche.Frontend.scanLineLoop -/
def declCodeF : FunDecl := lfn (k) {
  if k == 4 { return 20 };
  if k == 12 { return 21 };
  if k == 60 { return 22 };
  if k == 45 { return 23 };
  return 24
}

/-- One member of a declaration line, by key `k` (value at `v`, key quote at `ks`), with the
fields so far: the end of the value (`0`: failure) and the fields after. -/
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:2427-2574 ConLeche.Frontend.scanLineLoop
def declVal : FunDecl :=
    lfn (ks, k, v, pl, nm, lp, ty, vl, hk, hn, fl) locals (e) {
  if k == 4 || k == 12 || k == 60 || k == 45 || k == 49 {
    (e, nm, lp, ty, vl, hk, hn, fl) := call rec_decl_obj(v);
    pl := call decl_code(k);
    return (e, pl, nm, lp, ty, vl, hk, hn, fl)
  };
  if k == 23 {  -- `inductive`: validated by Stage B's `scan_ind_decl`; its value's position in `nm`
    e := call scan_ind_decl(v);
    return (e, 25, v, lp, ty, vl, hk, hn, fl)
  };
  return (0, pl, nm, lp, ty, vl, hk, hn, fl)
}

def dlineLoop : Stmt := lblk (i, w, pl, nm, lp, ty, vl, hk, hn, fl, tag, ks, k, v, e) {
  while 0 == 0 {
    (tag, ks, w, k, v) := call next_member(i, w);
    if tag == 0 { return (0, 0, 0, 0, 0, 0, 0, 0) };
    if tag == 1 { return (pl, nm, lp, ty, vl, hk, hn, fl) };
    (e, pl, nm, lp, ty, vl, hk, hn, fl) := call decl_val(ks, k, v, pl, nm, lp, ty, vl, hk, hn, fl);
    if e <= ks { return (0, 0, 0, 0, 0, 0, 0, 0) };
    i := e;
    w := 0
  }
}

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:2427-2574 ConLeche.Frontend.scanLineLoop -/
@[l_impl ConLeche.Frontend.scanLineLoop]
def recDeclLine : FunDecl := lfn (i) locals (w, pl, nm, lp, ty, vl, hk, hn, fl, tag, ks, k, v, e) {
  w := 1;
  ⟪dlineLoop⟫;
  return (0, 0, 0, 0, 0, 0, 0, 0)
}

/-- The `pl` of a declaration key. -/
def declCode (k : Word) : Word :=
  if k = 4 then 20 else if k = 12 then 21 else if k = 60 then 22 else if k = 45 then 23 else 24

/-- The end of a declaration line's member (`0`: failure). -/
def dendDN (b : Array UInt8) (k v : Word) : Word :=
  if k = 4 ∨ k = 12 ∨ k = 60 ∨ k = 45 ∨ k = 49 then (dobjEntryN b v).pl else if k = 23 then L.Scan.Records.indDN b v else 0

/-- The `pl` after the member. -/
def dplN (k old : Word) : Word := if k = 4 ∨ k = 12 ∨ k = 60 ∨ k = 45 ∨ k = 49 then declCode k else if k = 23 then 25 else old

/-- A field after the member: `x`, the record's, at a declaration key. -/
def dpickN (k x old : Word) : Word := if k = 4 ∨ k = 12 ∨ k = 60 ∨ k = 45 ∨ k = 49 then x else old

/-- The name field after the member: the record's at a declaration key, the value's position `v`
at `inductive` (`apply_ind` reads the block there). -/
def dnameN (k x v old : Word) : Word :=
  if k = 4 ∨ k = 12 ∨ k = 60 ∨ k = 45 ∨ k = 49 then x else if k = 23 then v else old

/-- `decl_val(ks, k, v, …)`: the end and the fields after the member. -/
def dlvN (b : Array UInt8) (k v : Word) (f : DFld) : Word × DFld :=
  (dendDN b k v, ⟨dplN k f.pl, dnameN k (dobjEntryN b v).name v f.name,
    dpickN k (dobjEntryN b v).lps f.lps, dpickN k (dobjEntryN b v).type f.type,
    dpickN k (dobjEntryN b v).value f.value, dpickN k (dobjEntryN b v).hk f.hk,
    dpickN k (dobjEntryN b v).hn f.hn, dpickN k (dobjEntryN b v).flag f.flag⟩)

/-- The line loop. -/
def declN (b : Array UInt8) (i w : Word) (f : DFld) : DFld :=
  if (nextMemberN b i w).tag = 0 then .none
  else if (nextMemberN b i w).tag = 1 then f
  else if _h : (nextMemberN b i w).pos < (dlvN b (nextMemberN b i w).key (nextMemberN b i w).val f).1 then
    declN b (dlvN b (nextMemberN b i w).key (nextMemberN b i w).val f).1 0
      (dlvN b (nextMemberN b i w).key (nextMemberN b i w).val f).2
  else .none
termination_by b.size - i.toNat
decreasing_by
  have hk := nextMemberN_key b i w (nextMemberN_tag b i w (by assumption) (by assumption))
  have := L.Scan.lt_of_lt_ofNat hk.2
  rw [UInt64.le_iff_toNat_le] at hk
  rw [UInt64.lt_iff_toNat_lt] at _h
  omega

/-- `rec_decl_line(i)`, `i` after the line's `{`. -/
def declLineN (b : Array UInt8) (i : Word) : DFld := declN b i 1 .none

section
variable (b : Array UInt8) (i w : Word) (f : DFld)
theorem declN_err (h : (nextMemberN b i w).tag = 0) : declN b i w f = .none := by
  rw [declN, if_pos h]
theorem declN_close (h : (nextMemberN b i w).tag = 1) : declN b i w f = f := by
  rw [declN, if_neg (by simp [h]), if_pos h]
theorem declN_key (h0 : (nextMemberN b i w).tag ≠ 0) (h1 : (nextMemberN b i w).tag ≠ 1) :
    declN b i w f =
      if (nextMemberN b i w).pos < (dlvN b (nextMemberN b i w).key (nextMemberN b i w).val f).1 then
        declN b (dlvN b (nextMemberN b i w).key (nextMemberN b i w).val f).1 0
          (dlvN b (nextMemberN b i w).key (nextMemberN b i w).val f).2
      else .none := by
  rw [declN, if_neg h0, if_neg h1]
  simp only [dite_eq_ite]
end
grind_pattern [lang_grind] declN_err => declN b i w f, nextMemberN b i w
grind_pattern [lang_grind] declN_close => declN b i w f, nextMemberN b i w
grind_pattern [lang_grind] declN_key => declN b i w f, nextMemberN b i w


end L.Front.Fields
