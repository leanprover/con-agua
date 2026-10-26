module

public import ConAgua.Front.FieldsLink

@[expose] public section


/-!
# Expression lines: what the fields pass hands the apply step

The fields of an expression line are five words `(pl, idx, a, c, d)` (`Fld`), as for name and
level lines (`ConAgua.Front.Fields`), with the kinds `8`‥`17`:

| `pl` | con-leche's `ExprRec` | `a` | `c` | `d` |
|---|---|---|---|---|
| 8 | `bvar k` | `k` | | |
| 9 | `sort u` | `u` | | |
| 10 | `app fn arg` | `fn` | `arg` | |
| 11 | `lam ty bd` | `ty` | `bd` | |
| 12 | `forallE ty bd` | `ty` | `bd` | |
| 13 | `letE ty vl bd` | `ty` | `vl` | `bd` |
| 14 | `proj tn ix st` | `tn` | `ix` | `st` |
| 15 | `const nm us` | `nm` | the position of `us`'s `[` | |
| 16 | `natVal n` | `n` (`NONE` past 18 digits) | first digit | after the last digit |
| 17 | `strVal s` | | start of the body | its end (the closing quote) |

`ExprR b r f` says what the words of `f` mean for con-leche's record `r` on the buffer `b`; the
fields pass proves it on con-leche's `ok` path (`ERecR`), the apply step consumes it. A `const`'s
universe list is read again by the apply step at `c` (`listN`, the items as `read_nat` reads
them); a literal's digits and a string's body are described by con-leche's own scanner results
(`NatValR`, `StrR`), so that the decimal parse and the unescaping can be related to them.
-/

namespace L.Front.Fields

open L.Scan.Utf8 (byteW)
open L.Scan.Leaves (numEndN)

/-- The items of a number list from `i` (after its `[`): each number as `read_nat` reads it,
up to the `]`. Whitespace and commas are skipped (the validator has checked the list). -/
def itemsN (b : Array UInt8) (i : Word) : List Word :=
  if h : i < UInt64.ofNat b.size then
    if byteW b i = 93 then []
    else if 48 ≤ byteW b i ∧ byteW b i ≤ 57 then
      if _hj : i < UInt64.ofNat (numEndN b i.toNat) then
        rdNatN b i (UInt64.ofNat (numEndN b i.toNat)) :: itemsN b (UInt64.ofNat (numEndN b i.toNat))
      else []
    else itemsN b (i + 1)
  else []
termination_by b.size - i.toNat
decreasing_by
  all_goals
    have := L.Scan.lt_of_lt_ofNat h
    first
      | (rw [UInt64.lt_iff_toNat_lt] at hj; omega)
      | (have := L.Scan.toNat_add_one_of_lt_ofNat h; omega)

/-- The items of the number list whose `[` is at `v`. -/
def listN (b : Array UInt8) (v : Word) : List Word := itemsN b (v + 1)

section
variable (b : Array UInt8) (i : Word)
theorem itemsN_end (h : ¬ i < UInt64.ofNat b.size) : itemsN b i = [] := by
  rw [itemsN, dite_eq_right h]
theorem itemsN_close (h : i < UInt64.ofNat b.size) (hc : byteW b i = 93) : itemsN b i = [] := by
  rw [itemsN, dite_eq_left h, ite_eq_left hc]
theorem itemsN_digit (h : i < UInt64.ofNat b.size) (hc : byteW b i ≠ 93)
    (hd : 48 ≤ byteW b i ∧ byteW b i ≤ 57) (he : i < UInt64.ofNat (numEndN b i.toNat)) :
    itemsN b i = rdNatN b i (UInt64.ofNat (numEndN b i.toNat)) ::
      itemsN b (UInt64.ofNat (numEndN b i.toNat)) := by
  rw [itemsN, dite_eq_left h, ite_eq_right hc, ite_eq_left hd, dite_eq_left he]
theorem itemsN_noprog (h : i < UInt64.ofNat b.size) (hc : byteW b i ≠ 93)
    (hd : 48 ≤ byteW b i ∧ byteW b i ≤ 57) (he : ¬ i < UInt64.ofNat (numEndN b i.toNat)) :
    itemsN b i = [] := by
  rw [itemsN, dite_eq_left h, ite_eq_right hc, ite_eq_left hd, dite_eq_right he]
theorem itemsN_other (h : i < UInt64.ofNat b.size) (hc : byteW b i ≠ 93)
    (hd : ¬ (48 ≤ byteW b i ∧ byteW b i ≤ 57)) : itemsN b i = itemsN b (i + 1) := by
  rw [itemsN, dite_eq_left h, ite_eq_right hc, ite_eq_right hd]
end

end L.Front.Fields

namespace ConAgua.Front.FieldsLink
open ConLeche.Frontend ConAgua.Scan
open L (Word)
open L.Front.Fields

/-- A list of words read for a list of numbers, item by item (`ItemR`). -/
def ItemsR : List Word → List Nat → Prop
  | [], [] => True
  | x :: xs, n :: ns => ItemR x n ∧ ItemsR xs ns
  | _, _ => False

/-- A `natVal`'s digits `[c, d)`: con-leche reads the number `n` there (`readNatAt`, at the
digit run `skipDigits` ends). -/
def NatValR (b : ByteArray) (c d : Word) (n : Nat) : Prop :=
  ∃ v e : USize, v.toUInt64 = c ∧ e.toUInt64 = d ∧ v < e ∧ skipDigits b v = e ∧
    readNatAt b v e = n

/-- What an expression line's words say about con-leche's expression record. -/
def ExprR (b : ByteArray) : ExprRec → Fld → Prop
  | .bvar k, f => f.pl = 8 ∧ ItemR f.a k
  | .sort u, f => f.pl = 9 ∧ ItemR f.a u
  | .app fn x, f => f.pl = 10 ∧ ItemR f.a fn ∧ ItemR f.c x
  | .lam ty bd, f => f.pl = 11 ∧ ItemR f.a ty ∧ ItemR f.c bd
  | .forallE ty bd, f => f.pl = 12 ∧ ItemR f.a ty ∧ ItemR f.c bd
  | .letE ty vl bd, f => f.pl = 13 ∧ ItemR f.a ty ∧ ItemR f.c vl ∧ ItemR f.d bd
  | .proj tn ix st, f => f.pl = 14 ∧ ItemR f.a tn ∧ ItemR f.c ix ∧ ItemR f.d st
  | .const nm us, f => f.pl = 15 ∧ ItemR f.a nm ∧ ItemsR (listN b.data f.c) us
  | .natVal n, f => f.pl = 16 ∧ ItemR f.a n ∧ NatValR b f.c f.d n
  | .strVal s, f => f.pl = 17 ∧ StrR b f.c f.d s

/-- What an expression line's words say about con-leche's line record. -/
def ERecR (b : ByteArray) : LineRec → Fld → Prop
  | .expr i r, f => ItemR f.idx i ∧ ExprR b r f
  | _, _ => False

end ConAgua.Front.FieldsLink
