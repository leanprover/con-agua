module

meta import ConAgua.L.Semantics
public import ConAgua.Front.Fields
import ConAgua.Census.Attr
public import ConAgua.Scan.Records
import ConAgua.Front.Preserve
import ConAgua.L.GrindAttr
import ConAgua.Scan.Common
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# The fields of expression lines

The expression analogue of `recN` (`ConAgua.Front.Fields`): `exprN` walks an accepted line's
members again and gives the five words `(pl, idx, a, c, d)` of `ConAgua.Front.ExprIface`'s table
(`pl` `8`‥`17`, `0` for any other line or a failure). It is a model of `front_line`'s spec; the
code reads the line once (`ConAgua.Front.LineRec`).

* `recObjN`: one member loop for the six expression sub-objects (`app`, `lam`, `forallE`,
  `letE`, `const`, `proj`): `(end, x0, x1, x2, x3)`, the slots by key: `fn`/`type`/`typeName` →
  `x0`; `arg`/`body`/`struct` → `x1`, `us` → `x1` the position of its `[`; `value`/`idx` → `x2`;
  `name` → `x3`; `binderInfo` and `nondep` are skipped. The value's end is `exValN`: Stage B's
  scanner for the key's kind, `0` for a key no sub-object has.
* `exVN`: one member of the line, `(end, pl, a, c, d)`; `pl = 0` with `a` the index for
  `in`/`il`/`ie`.
* `exprN`: the members.

As for name and level lines, the model trusts the validator (no `seen` masks, no alternation),
keeps con-leche's progress guard, and reads every number as `read_nat` does (`NONE` past 18
digits).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Front.Fields

open L.Scan.Utf8 (byteW)
open L.Scan.Member
open L.Scan.Values
open L.Scan.Records (boolEndN)

/-! ## The end of a sub-object member's value -/

/-- A numeric key of a sub-object: `fn`, `type`, `typeName`, `arg`, `body`, `struct`, `value`,
`idx`, `name`. -/
def numKey (k : Word) : Prop :=
  k = 13 ∨ k = 61 ∨ k = 62 ∨ k = 3 ∨ k = 6 ∨ k = 58 ∨ k = 65 ∨ k = 17 ∨ k = 34

instance (k : Word) : Decidable (numKey k) := by unfold numKey; infer_instance

/-- The model of `obj_val(ks, k, v)`. -/
def exValN (b : Array UInt8) (k ks v : Word) : Word :=
  if k = 5 then binderInfoN b v
  else if k = 37 then boolEndN b v
  else if k = 64 then (natListEntryN b v).1
  else if numKey k then slotNatN b ks v
  else 0

/-! ## The sub-object -/

/-- Five words: an end and four slots (`rec_obj`), or an end and four fields (`expr_val`). -/
structure Obj where
  e : Word
  x0 : Word
  x1 : Word
  x2 : Word
  x3 : Word

/-- The five words. -/
def Obj.enc (o : Obj) : List Word := [o.e, o.x0, o.x1, o.x2, o.x3]

/-- A failure. -/
def Obj.none : Obj := ⟨0, 0, 0, 0, 0⟩

/-- The slots after the member `k` with value at `v`, read as `x`. -/
def objPut (k v x : Word) (o : Obj) : Obj :=
  if k = 13 ∨ k = 61 ∨ k = 62 then ⟨o.e, x, o.x1, o.x2, o.x3⟩
  else if k = 3 ∨ k = 6 ∨ k = 58 then ⟨o.e, o.x0, x, o.x2, o.x3⟩
  else if k = 64 then ⟨o.e, o.x0, v, o.x2, o.x3⟩
  else if k = 65 ∨ k = 17 then ⟨o.e, o.x0, o.x1, x, o.x3⟩
  else if k = 34 then ⟨o.e, o.x0, o.x1, o.x2, x⟩
  else o

/-- The sub-object loop. -/
def objRecN (b : Array UInt8) (i w : Word) (o : Obj) : Obj :=
  if (nextMemberN b i w).tag = 0 then .none
  else if (nextMemberN b i w).tag = 1 then
    ⟨(nextMemberN b i w).pos + 1, o.x0, o.x1, o.x2, o.x3⟩
  else if _h : (nextMemberN b i w).pos <
      exValN b (nextMemberN b i w).key (nextMemberN b i w).pos (nextMemberN b i w).val then
    objRecN b (exValN b (nextMemberN b i w).key (nextMemberN b i w).pos (nextMemberN b i w).val) 0
      (objPut (nextMemberN b i w).key (nextMemberN b i w).val
        (rdNatN b (nextMemberN b i w).val
          (exValN b (nextMemberN b i w).key (nextMemberN b i w).pos (nextMemberN b i w).val)) o)
  else .none
termination_by b.size - i.toNat
decreasing_by
  have hk := nextMemberN_key b i w (nextMemberN_tag b i w (by assumption) (by assumption))
  have := L.Scan.lt_of_lt_ofNat hk.2
  rw [UInt64.le_iff_toNat_le] at hk
  rw [UInt64.lt_iff_toNat_lt] at _h
  omega

/-- `rec_obj(i)`, `i` at the `{`. -/
def recObjN (b : Array UInt8) (i : Word) : Obj := objRecN b (i + 1) 1 ⟨0, 0, 0, 0, 0⟩

section
variable (b : Array UInt8) (i w : Word) (o : Obj)
theorem objRecN_err (h : (nextMemberN b i w).tag = 0) : objRecN b i w o = .none := by
  rw [objRecN, ite_eq_left h]
theorem objRecN_close (h : (nextMemberN b i w).tag = 1) :
    objRecN b i w o = ⟨(nextMemberN b i w).pos + 1, o.x0, o.x1, o.x2, o.x3⟩ := by
  rw [objRecN, ite_eq_right (by simp [h]), ite_eq_left h]
theorem objRecN_key (h0 : (nextMemberN b i w).tag ≠ 0) (h1 : (nextMemberN b i w).tag ≠ 1) :
    objRecN b i w o =
      if (nextMemberN b i w).pos <
          exValN b (nextMemberN b i w).key (nextMemberN b i w).pos (nextMemberN b i w).val then
        objRecN b (exValN b (nextMemberN b i w).key (nextMemberN b i w).pos (nextMemberN b i w).val) 0
          (objPut (nextMemberN b i w).key (nextMemberN b i w).val
            (rdNatN b (nextMemberN b i w).val
              (exValN b (nextMemberN b i w).key (nextMemberN b i w).pos (nextMemberN b i w).val)) o)
      else .none := by
  rw [objRecN, ite_eq_right h0, ite_eq_right h1]
  simp only [dite_eq_ite]
end
grind_pattern [lang_grind] objRecN_err => objRecN b i w o, nextMemberN b i w
grind_pattern [lang_grind] objRecN_close => objRecN b i w o, nextMemberN b i w
grind_pattern [lang_grind] objRecN_key => objRecN b i w o, nextMemberN b i w

/-! ## One member of an expression line -/

/-- The fields a sub-object's slots give, for the payload key `k`. -/
def objFld (k : Word) (o : Obj) : Obj :=
  if k = 2 then ⟨o.e, 10, o.x0, o.x1, o.x1⟩
  else if k = 29 then ⟨o.e, 11, o.x0, o.x1, o.x1⟩
  else if k = 14 then ⟨o.e, 12, o.x0, o.x1, o.x1⟩
  else if k = 30 then ⟨o.e, 13, o.x0, o.x2, o.x1⟩
  else if k = 48 then ⟨o.e, 14, o.x0, o.x2, o.x1⟩
  else ⟨o.e, 15, o.x3, o.x1, o.x1⟩

/-- The model of `expr_val(k, ks, v)`: the value's end, then `pl` (`0` for an index), `a`, `c`,
`d`. -/
def exVN (b : Array UInt8) (k ks v : Word) : Obj :=
  if k = 21 ∨ k = 19 ∨ k = 18 then ⟨slotNatN b ks v, 0, rdNatN b v (slotNatN b ks v), 0, 0⟩
  else if k = 7 ∨ k = 55 then
    ⟨slotNatN b ks v, if k = 7 then 8 else 9, rdNatN b v (slotNatN b ks v), 0, 0⟩
  else if k = 2 ∨ k = 29 ∨ k = 14 ∨ k = 30 ∨ k = 9 ∨ k = 48 then objFld k (recObjN b v)
  else if k = 35 then
    ⟨quotedNatN b v, 16, rdNatN b (v + 1) (quotedNatN b v - 1), v + 1, quotedNatN b v - 1⟩
  else if k = 57 then ⟨L.Scan.Str.scanStringN b v, 17, 0, v + 1, L.Scan.Str.scanStringN b v - 1⟩
  else .none

/-! ## The line -/

/-- The fields after a member whose `expr_val` is `o`. -/
def fldPut (o : Obj) (f : Fld) : Fld :=
  if o.x0 = 0 then ⟨f.pl, o.x1, f.a, f.c, f.d⟩ else ⟨o.x0, f.idx, o.x1, o.x2, o.x3⟩

/-- The expression line loop. -/
def exprN (b : Array UInt8) (i w : Word) (f : Fld) : Fld :=
  if (nextMemberN b i w).tag = 0 then .none
  else if (nextMemberN b i w).tag = 1 then f
  else if _h : (nextMemberN b i w).pos <
      (exVN b (nextMemberN b i w).key (nextMemberN b i w).pos (nextMemberN b i w).val).e then
    exprN b (exVN b (nextMemberN b i w).key (nextMemberN b i w).pos (nextMemberN b i w).val).e 0
      (fldPut (exVN b (nextMemberN b i w).key (nextMemberN b i w).pos (nextMemberN b i w).val) f)
  else .none
termination_by b.size - i.toNat
decreasing_by
  have hk := nextMemberN_key b i w (nextMemberN_tag b i w (by assumption) (by assumption))
  have := L.Scan.lt_of_lt_ofNat hk.2
  rw [UInt64.le_iff_toNat_le] at hk
  rw [UInt64.lt_iff_toNat_lt] at _h
  omega

/-- The expression record of the line whose `{` is at `i - 1`. -/
def exprLineN (b : Array UInt8) (i : Word) : Fld := exprN b i 1 .none

section
variable (b : Array UInt8) (i w : Word) (f : Fld)
theorem exprN_err (h : (nextMemberN b i w).tag = 0) : exprN b i w f = .none := by
  rw [exprN, ite_eq_left h]
theorem exprN_close (h : (nextMemberN b i w).tag = 1) : exprN b i w f = f := by
  rw [exprN, ite_eq_right (by simp [h]), ite_eq_left h]
theorem exprN_key (h0 : (nextMemberN b i w).tag ≠ 0) (h1 : (nextMemberN b i w).tag ≠ 1) :
    exprN b i w f =
      if (nextMemberN b i w).pos <
          (exVN b (nextMemberN b i w).key (nextMemberN b i w).pos (nextMemberN b i w).val).e then
        exprN b (exVN b (nextMemberN b i w).key (nextMemberN b i w).pos (nextMemberN b i w).val).e 0
          (fldPut (exVN b (nextMemberN b i w).key (nextMemberN b i w).pos (nextMemberN b i w).val) f)
      else .none := by
  rw [exprN, ite_eq_right h0, ite_eq_right h1]
  simp only [dite_eq_ite]
end
grind_pattern [lang_grind] exprN_err => exprN b i w f, nextMemberN b i w
grind_pattern [lang_grind] exprN_close => exprN b i w f, nextMemberN b i w
grind_pattern [lang_grind] exprN_key => exprN b i w f, nextMemberN b i w

end L.Front.Fields
