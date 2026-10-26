import ConAgua.Front.IndAlloc
import ConAgua.Front.FieldsDeclSpec

/-!
# The fields pass of an `inductive` line: models and specs

Word models of `IndFields.lean`'s functions, in the front's style: the memory after as an
`Option` (`none` where the L code aborts), the input positions a well-founded measure, the
callees' models called by name. `ind_obj`'s loop, `ind_member`, `ind_list` and `ind_list`'s loop
call each other (a list value holds objects): their models are one `mutual` block (`objW`,
`objLoopW`, `memberW`, `listW`, `listLoopW`, measured by the input position and a rank), and
their specs one induction on the fuel over the conjunction (`mutual_specs`). `indFields_spec`:
`ind_fields(v)` is `indFieldsW`.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order
open L.Arena
open L.Scan.Utf8 (byteW)
open L.Scan.Member
open L.Scan.Values
open L.Scan.Lit (encBool scanBoolN)
open L.Scan.Leaves (numEndN)
open L.Front.Fields (rdNatN NONE)
open L.Front (lsCntN)

namespace L.Front.Ind

/-! ## Models of the leaves -/

/-- **The model of `if_reset`.** -/
def ifResetW (m : Mem) : Option Mem :=
  if m.len64 IFR = 0 ∨ m.len64 IFL = 0 then none else some ((m.set64 IFR 0 0).set64 IFL 0 0)

/-- **The model of `fld_alloc(kind, n)`.** -/
def fldAllocW (m : Mem) (kind n : Word) : Option (Word × Mem) :=
  if kind = 3 then allocW m IFL n else allocW m IFR n

/-- **The model of `fld_put(kind, p, s, x)`** (a write out of range leaves the memory alone; the
L code aborts there). -/
def fldPutW (m : Mem) (kind p s x : Word) : Mem :=
  if kind = 3 then m.set64 IFL (p + s) x else m.set64 IFR (p + s) x

/-- `ind_size(kind)`. -/
def indSizeN (kind : Word) : Word :=
  if kind = 0 ∨ kind = 2 then 11 else if kind = 1 then 10 else if kind = 3 then 3 else 6

/-- `ind_slot(kind, k)`: `(how, slot, sub)`. -/
def indSlotN (kind k : Word) : Word × Word × Word :=
  if k = 34 ∧ kind ≤ 2 then (1, 0, 0)
  else if k = 61 ∧ kind ≤ 2 then (1, 2, 0)
  else if k = 31 ∧ kind ≤ 2 then (3, 1, 0)
  else if kind = 0 then
    if k = 1 then (4, 0, 0) else if k = 11 then (5, 3, 0) else if k = 24 then (2, 5, 0)
    else if k = 25 then (2, 6, 0) else if k = 26 then (2, 7, 0) else if k = 40 then (1, 8, 0)
    else if k = 43 then (1, 9, 0) else if k = 44 then (1, 10, 0) else (0, 0, 0)
  else if kind = 1 then
    if k = 8 then (6, 6, 0) else if k = 22 then (6, 8, 0) else if k = 26 then (2, 3, 0)
    else if k = 39 then (1, 4, 0) else if k = 44 then (1, 5, 0) else (0, 0, 0)
  else if kind = 2 then
    if k = 1 then (4, 0, 0) else if k = 26 then (2, 3, 0) else if k = 27 then (2, 4, 0)
    else if k = 40 then (1, 5, 0) else if k = 41 then (1, 6, 0) else if k = 42 then (1, 7, 0)
    else if k = 44 then (1, 8, 0) else if k = 53 then (7, 9, 3) else (0, 0, 0)
  else if kind = 3 then
    if k = 10 then (1, 0, 0) else if k = 36 then (1, 1, 0) else if k = 52 then (1, 2, 0)
    else (0, 0, 0)
  else if k = 1 then (4, 0, 0) else if k = 26 then (8, 0, 0) else if k = 63 then (7, 0, 0)
  else if k = 11 then (7, 2, 1) else if k = 50 then (7, 4, 2) else (0, 0, 0)

/-- **The memory after `ifl_ids`' loop** from `i`. -/
def idsLoopM (b : Array UInt8) (m : Mem) (i : Word) : Option Mem :=
  if h : i < UInt64.ofNat b.size then
    if byteW b i = 93 then some m
    else if 48 ≤ byteW b i ∧ byteW b i ≤ 57 then
      if _hj : i < UInt64.ofNat (numEndN b i.toNat) then
        if rdNatN b i (UInt64.ofNat (numEndN b i.toNat)) = NONE then none
        else match pushLW m (rdNatN b i (UInt64.ofNat (numEndN b i.toNat))) with
          | none => none
          | some (_, m₁) => idsLoopM b m₁ (UInt64.ofNat (numEndN b i.toNat))
      else none
    else idsLoopM b m (i + 1)
  else some m
termination_by b.size - i.toNat
decreasing_by
  all_goals
    have := L.Scan.lt_of_lt_ofNat h
    first
      | (rw [UInt64.lt_iff_toNat_lt] at hj; omega)
      | (have := L.Scan.toNat_add_one_of_lt_ofNat h; omega)

/-- After `ifl_push`: the loop goes on at `e`. -/
def idsK (b : Array UInt8) (e : Word) : Option (Word × Mem) → Option Mem
  | none => none
  | some (_, m) => idsLoopM b m e

@[arena_grind =] theorem idsK_some (b : Array UInt8) (e o : Word) (m : Mem) :
    idsK b e (some (o, m)) = idsLoopM b m e := rfl

section idsArms
variable (b : Array UInt8) (m : Mem) (i : Word)

theorem idsLoopM_end (h : ¬ i < UInt64.ofNat b.size) : idsLoopM b m i = some m := by
  rw [idsLoopM, dite_eq_right h]
theorem idsLoopM_close (h : i < UInt64.ofNat b.size) (hc : byteW b i = 93) :
    idsLoopM b m i = some m := by
  rw [idsLoopM, dite_eq_left h, ite_eq_left hc]
theorem idsLoopM_digit (h : i < UInt64.ofNat b.size) (hc : byteW b i ≠ 93)
    (hd : 48 ≤ byteW b i ∧ byteW b i ≤ 57) (he : i < UInt64.ofNat (numEndN b i.toNat)) :
    idsLoopM b m i =
      if rdNatN b i (UInt64.ofNat (numEndN b i.toNat)) = NONE then none
      else idsK b (UInt64.ofNat (numEndN b i.toNat))
        (pushLW m (rdNatN b i (UInt64.ofNat (numEndN b i.toNat)))) := by
  rw [idsLoopM, dite_eq_left h, ite_eq_right hc, ite_eq_left hd, dite_eq_left he]
  split
  · rfl
  · unfold idsK; split <;> rfl
theorem idsLoopM_other (h : i < UInt64.ofNat b.size) (hc : byteW b i ≠ 93)
    (hd : ¬ (48 ≤ byteW b i ∧ byteW b i ≤ 57)) : idsLoopM b m i = idsLoopM b m (i + 1) := by
  rw [idsLoopM, dite_eq_left h, ite_eq_right hc, ite_eq_right hd]
end idsArms

grind_pattern [lang_grind] idsLoopM_end => idsLoopM b m i
grind_pattern [lang_grind] idsLoopM_close => idsLoopM b m i, b[i.toNat]
grind_pattern [lang_grind] idsLoopM_digit => idsLoopM b m i, b[i.toNat], numEndN b i.toNat
grind_pattern [lang_grind] idsLoopM_other => idsLoopM b m i, b[i.toNat]

/-- After `ifl_alloc(0)`: the loop from `v + 1`. -/
def idsK0 (b : Array UInt8) (v : Word) : Option (Word × Mem) → Option Mem
  | none => none
  | some (_, m) => idsLoopM b m (v + 1)

@[arena_grind =] theorem idsK0_none (b : Array UInt8) (v : Word) : idsK0 b v none = none := rfl
@[arena_grind =] theorem idsK0_some (b : Array UInt8) (v o : Word) (m : Mem) :
    idsK0 b v (some (o, m)) = idsLoopM b m (v + 1) := rfl

/-- **The memory after `ifl_ids(v)`** (its results: `IFL`'s top `+ 1` before, and
`lsCntN b (v + 1) 0`). -/
def idsM (b : Array UInt8) (m : Mem) (v : Word) : Option Mem := idsK0 b v (allocW m IFL 0)

/-- **The model of `ind_num`**: the end and the memory after. -/
def numW (b : Array UInt8) (m : Mem) (kind p ks v h s : Word) : Option (Word × Mem) :=
  if rdNatN b v (slotNatN b ks v) = NONE then none
  else if h = 6 then
    some (slotNatN b ks v, fldPutW (fldPutW m kind p s 1) kind p (s + 1) (rdNatN b v (slotNatN b ks v)))
  else some (slotNatN b ks v, fldPutW m kind p s (rdNatN b v (slotNatN b ks v)))

/-- **The model of `ind_bool`.** -/
def boolW (b : Array UInt8) (m : Mem) (kind p v h s : Word) : Option (Word × Mem) :=
  if (encBool (scanBoolN b v.toNat) v).headD 0 = 0 then none
  else if h = 2 then
    some ((encBool (scanBoolN b v.toNat) v).tail.tail.headD 0,
      fldPutW m kind p s ((encBool (scanBoolN b v.toNat) v).tail.headD 0))
  else some ((encBool (scanBoolN b v.toNat) v).tail.tail.headD 0, m)

/-- After `ifl_ids`: the slice into the record. -/
def nlK (kind p s o c e : Word) : Option Mem → Option (Word × Mem)
  | none => none
  | some m => some (e, fldPutW (fldPutW m kind p s o) kind p (s + 1) c)

@[arena_grind =] theorem nlK_none (kind p s o c e : Word) : nlK kind p s o c e none = none := rfl
@[arena_grind =] theorem nlK_some (kind p s o c e : Word) (m : Mem) :
    nlK kind p s o c e (some m) = some (e, fldPutW (fldPutW m kind p s o) kind p (s + 1) c) := rfl

/-- **The model of `ind_nlist`.** -/
def nlistW (b : Array UInt8) (m : Mem) (kind p v h s : Word) : Option (Word × Mem) :=
  if h = 3 then some ((natListEntryN b v).1, fldPutW m kind p s v)
  else if h = 5 then
    nlK kind p s (rdW (m.arr64 IFL) 0 + 1) (lsCntN b (v + 1) 0) (natListEntryN b v).1 (idsM b m v)
  else some ((natListEntryN b v).1, m)

/-- A constructor record's two flags cleared (`ind_list`, before reading the record). -/
def flagsW (m : Mem) (sub q : Word) : Mem :=
  if sub = 1 then (m.set64 IFR (q + 6) 0).set64 IFR (q + 8) 0 else m

/-! ## The objects and lists: one `mutual` block

The measure is the input position (`b.size - pos`) with a rank, lexicographic: a call at the same
or a later position goes to a lower rank, a call to a higher rank moves forward. -/

mutual
/-- **The model of `ind_obj(i, kind, p)`**: the end and the memory after. -/
def objW (b : Array UInt8) (m : Mem) (i kind p : Word) : Option (Word × Mem) :=
  objLoopW b m kind p (i + 1) 1
termination_by (b.size - (i + 1).toNat, 5)

/-- `ind_obj`'s member loop from `i` (`w`: a member is wanted). -/
def objLoopW (b : Array UInt8) (m : Mem) (kind p i w : Word) : Option (Word × Mem) :=
  if _h0 : (nextMemberN b i w).tag = 0 then none
  else if h1 : (nextMemberN b i w).tag = 1 then some ((nextMemberN b i w).pos + 1, m)
  else match memberW b m kind p (nextMemberN b i w).pos (nextMemberN b i w).key
      (nextMemberN b i w).val with
    | none => none
    | some (e, m₁) =>
      if _hlt : (nextMemberN b i w).pos < e then objLoopW b m₁ kind p e 0 else none
termination_by (b.size - i.toNat, 4)
decreasing_by
  all_goals
    have hk := nextMemberN_key b i w (nextMemberN_tag b i w h0 h1)
    have := L.Scan.lt_of_lt_ofNat hk.2
    rw [UInt64.le_iff_toNat_le] at hk
  · exact Prod.Lex.right' _ (by omega) (by decide)
  · rw [UInt64.lt_iff_toNat_lt] at hlt
    exact Prod.Lex.left _ _ (by omega)

/-- **The model of `ind_member(kind, p, ks, k, v)`.** -/
def memberW (b : Array UInt8) (m : Mem) (kind p ks k v : Word) : Option (Word × Mem) :=
  if (indSlotN kind k).1 = 1 ∨ (indSlotN kind k).1 = 6 then
    numW b m kind p ks v (indSlotN kind k).1 (indSlotN kind k).2.1
  else if (indSlotN kind k).1 = 2 ∨ (indSlotN kind k).1 = 8 then
    boolW b m kind p v (indSlotN kind k).1 (indSlotN kind k).2.1
  else if (indSlotN kind k).1 = 3 ∨ (indSlotN kind k).1 = 4 ∨ (indSlotN kind k).1 = 5 then
    nlistW b m kind p v (indSlotN kind k).1 (indSlotN kind k).2.1
  else if (indSlotN kind k).1 = 7 then
    if _hv : ks < v then
      match listW b m v (indSlotN kind k).2.2 with
      | none => none
      | some ((o, c, e), m₁) =>
        some (e, fldPutW (fldPutW m₁ kind p (indSlotN kind k).2.1 o) kind p
          ((indSlotN kind k).2.1 + 1) c)
    else none
  else none
termination_by (b.size - ks.toNat, 3)
decreasing_by
  rw [UInt64.lt_iff_toNat_lt] at hv
  exact Prod.Lex.right' _ (by omega) (by decide)

/-- **The model of `ind_list(v, sub)`**: `(off, cnt, end)` and the memory after. -/
def listW (b : Array UInt8) (m : Mem) (v sub : Word) : Option ((Word × Word × Word) × Mem) :=
  if _hv : v < UInt64.ofNat b.size then
    if byteW b v ≠ 91 then none
    else match fldAllocW m sub 0 with
      | none => none
      | some (o, m₁) => listLoopW b m₁ sub (indSizeN sub) o 0 (v + 1)
  else none
termination_by (b.size - v.toNat, 2)
decreasing_by
  have := L.Scan.lt_of_lt_ofNat hv
  have := L.Scan.toNat_add_one_of_lt_ofNat hv
  exact Prod.Lex.right' _ (by omega) (by decide)

/-- `ind_list`'s loop from `i`, `cnt` records read at `o`. -/
def listLoopW (b : Array UInt8) (m : Mem) (sub sz o cnt i : Word) :
    Option ((Word × Word × Word) × Mem) :=
  if hi : i < UInt64.ofNat b.size then
    if byteW b i = 93 then some ((o, cnt, i + 1), m)
    else if byteW b i = 123 then
      match fldAllocW m sub sz with
      | none => none
      | some (q, m₁) =>
        match objW b (flagsW m₁ sub q) i sub q with
        | none => none
        | some (e, m₂) =>
          if hie : i < e then listLoopW b m₂ sub sz o (cnt + 1) e else none
    else listLoopW b m sub sz o cnt (i + 1)
  else none
termination_by (b.size - i.toNat, 1)
decreasing_by
  all_goals
    have := L.Scan.lt_of_lt_ofNat hi
    have := L.Scan.toNat_add_one_of_lt_ofNat hi
  · exact Prod.Lex.left _ _ (by omega)
  · rw [UInt64.lt_iff_toNat_lt] at hie
    exact Prod.Lex.left _ _ (by omega)
  · exact Prod.Lex.left _ _ (by omega)
end

/-! ### The models' arms, with named continuations -/

/-- After `ind_member` in `ind_obj`'s loop. -/
def objK (b : Array UInt8) (kind p ks : Word) : Option (Word × Mem) → Option (Word × Mem)
  | none => none
  | some (e, m₁) => if ks < e then objLoopW b m₁ kind p e 0 else none

/-- After `ind_list` in `ind_member`. -/
def memK (kind p s : Word) : Option ((Word × Word × Word) × Mem) → Option (Word × Mem)
  | none => none
  | some ((o, c, e), m₁) => some (e, fldPutW (fldPutW m₁ kind p s o) kind p (s + 1) c)

/-- After `fld_alloc(sub, 0)` in `ind_list`. -/
def listK0 (b : Array UInt8) (sub v : Word) :
    Option (Word × Mem) → Option ((Word × Word × Word) × Mem)
  | none => none
  | some (o, m₁) => listLoopW b m₁ sub (indSizeN sub) o 0 (v + 1)

/-- After `ind_obj` in `ind_list`'s loop. -/
def listK2 (b : Array UInt8) (sub sz o cnt i : Word) :
    Option (Word × Mem) → Option ((Word × Word × Word) × Mem)
  | none => none
  | some (e, m₂) => if i < e then listLoopW b m₂ sub sz o (cnt + 1) e else none

/-- After `fld_alloc(sub, sz)` in `ind_list`'s loop. -/
def listK1 (b : Array UInt8) (sub sz o cnt i : Word) :
    Option (Word × Mem) → Option ((Word × Word × Word) × Mem)
  | none => none
  | some (q, m₁) => listK2 b sub sz o cnt i (objW b (flagsW m₁ sub q) i sub q)

section kArms
variable (b : Array UInt8) (kind p ks s sub sz o cnt i v e c q : Word) (m₁ : Mem)
  (r : Word × Word × Word)
@[arena_grind =] theorem objK_none : objK b kind p ks none = none := rfl
@[arena_grind =] theorem objK_some :
    objK b kind p ks (some (e, m₁)) = if ks < e then objLoopW b m₁ kind p e 0 else none := rfl
@[arena_grind =] theorem memK_none : memK kind p s none = none := rfl
@[arena_grind =] theorem memK_some :
    memK kind p s (some ((o, c, e), m₁)) =
      some (e, fldPutW (fldPutW m₁ kind p s o) kind p (s + 1) c) := rfl
@[arena_grind =] theorem listK0_none : listK0 b sub v none = none := rfl
@[arena_grind =] theorem listK0_some :
    listK0 b sub v (some (o, m₁)) = listLoopW b m₁ sub (indSizeN sub) o 0 (v + 1) := rfl
@[arena_grind =] theorem listK2_none : listK2 b sub sz o cnt i none = none := rfl
@[arena_grind =] theorem listK2_some :
    listK2 b sub sz o cnt i (some (e, m₁)) =
      if i < e then listLoopW b m₁ sub sz o (cnt + 1) e else none := rfl
@[arena_grind =] theorem listK1_none : listK1 b sub sz o cnt i none = none := rfl
@[arena_grind =] theorem listK1_some :
    listK1 b sub sz o cnt i (some (q, m₁)) =
      listK2 b sub sz o cnt i (objW b (flagsW m₁ sub q) i sub q) := rfl
end kArms

section mArms
variable (b : Array UInt8) (m : Mem) (kind p i w ks k v sub sz o cnt : Word)

theorem objW_eq : objW b m i kind p = objLoopW b m kind p (i + 1) 1 := by
  rw [objW]

theorem objLoopW_close (h : (nextMemberN b i w).tag = 1) :
    objLoopW b m kind p i w = some ((nextMemberN b i w).pos + 1, m) := by
  rw [objLoopW, dite_eq_right (by simp [h]), dite_eq_left h]
theorem objLoopW_key (h0 : (nextMemberN b i w).tag ≠ 0) (h1 : (nextMemberN b i w).tag ≠ 1) :
    objLoopW b m kind p i w = objK b kind p (nextMemberN b i w).pos
      (memberW b m kind p (nextMemberN b i w).pos (nextMemberN b i w).key (nextMemberN b i w).val) := by
  rw [objLoopW, dite_eq_right h0, dite_eq_right h1]
  unfold objK; split <;> simp_all

theorem memberW_eq : memberW b m kind p ks k v =
    if (indSlotN kind k).1 = 1 ∨ (indSlotN kind k).1 = 6 then
      numW b m kind p ks v (indSlotN kind k).1 (indSlotN kind k).2.1
    else if (indSlotN kind k).1 = 2 ∨ (indSlotN kind k).1 = 8 then
      boolW b m kind p v (indSlotN kind k).1 (indSlotN kind k).2.1
    else if (indSlotN kind k).1 = 3 ∨ (indSlotN kind k).1 = 4 ∨ (indSlotN kind k).1 = 5 then
      nlistW b m kind p v (indSlotN kind k).1 (indSlotN kind k).2.1
    else if (indSlotN kind k).1 = 7 then
      (if ks < v then memK kind p (indSlotN kind k).2.1 (listW b m v (indSlotN kind k).2.2)
       else none)
    else none := by
  rw [memberW]
  repeat' split
  all_goals first | rfl | (simp_all; done) | skip
  all_goals (unfold memK; simp_all)

theorem listW_eq : listW b m v sub =
    if v < UInt64.ofNat b.size then
      (if byteW b v ≠ 91 then none else listK0 b sub v (fldAllocW m sub 0))
    else none := by
  rw [listW]
  by_cases hv : v < UInt64.ofNat b.size
  · rw [dite_eq_left hv, ite_eq_left hv]; unfold listK0; split <;> simp_all
  · rw [dite_eq_right hv, ite_eq_right hv]

theorem listLoopW_close (h : i < UInt64.ofNat b.size) (hc : byteW b i = 93) :
    listLoopW b m sub sz o cnt i = some ((o, cnt, i + 1), m) := by
  rw [listLoopW, dite_eq_left h, ite_eq_left hc]
theorem listLoopW_open (h : i < UInt64.ofNat b.size) (hc : byteW b i ≠ 93) (ho : byteW b i = 123) :
    listLoopW b m sub sz o cnt i = listK1 b sub sz o cnt i (fldAllocW m sub sz) := by
  rw [listLoopW, dite_eq_left h, ite_eq_right hc, ite_eq_left ho]
  unfold listK1 listK2; split
  · rfl
  · split <;> simp_all
theorem listLoopW_other (h : i < UInt64.ofNat b.size) (hc : byteW b i ≠ 93) (ho : byteW b i ≠ 123) :
    listLoopW b m sub sz o cnt i = listLoopW b m sub sz o cnt (i + 1) := by
  rw [listLoopW, dite_eq_left h, ite_eq_right hc, ite_eq_right ho]
end mArms

grind_pattern [lang_grind] objW_eq => objW b m i kind p
grind_pattern [lang_grind] objLoopW_close => objLoopW b m kind p i w, nextMemberN b i w
grind_pattern [lang_grind] objLoopW_key => objLoopW b m kind p i w, nextMemberN b i w
grind_pattern [lang_grind] memberW_eq => memberW b m kind p ks k v
grind_pattern [lang_grind] listW_eq => listW b m v sub
grind_pattern [lang_grind] listLoopW_close => listLoopW b m sub sz o cnt i, b[i.toNat]
grind_pattern [lang_grind] listLoopW_open => listLoopW b m sub sz o cnt i, b[i.toNat]
grind_pattern [lang_grind] listLoopW_other => listLoopW b m sub sz o cnt i, b[i.toNat]

/-- What an allocation returns. -/
theorem allocW_eq (m : Mem) (a : ArrId) (n : Word) : allocW m a n = none ∨
    allocW m a n = some (rdW (m.arr64 a) 0 + 1, m.set64 a 0 (rdW (m.arr64 a) 0 + 1 - 1 + n)) := by
  unfold allocW; split
  · exact .inl rfl
  split
  · exact .inl rfl
  split
  · exact .inl rfl
  · exact .inr rfl

/-! ## Specs of the leaves -/

/-- Every function the fields pass calls, at its name in `p`. -/
structure IndFieldLookups (p : Prog) : Prop where
  skip_ws : p.lookup "skip_ws" = some L.Scan.Leaves.skipWs
  skip_digits : p.lookup "skip_digits" = some L.Scan.Leaves.skipDigits
  key_end : p.lookup "key_end" = some L.Scan.Leaves.keyEnd
  num_end : p.lookup "num_end" = some L.Scan.Leaves.numEnd
  key_at_g1 : p.lookup "key_at_g1" = some L.Scan.Key.keyAtG1
  key_at_g2 : p.lookup "key_at_g2" = some L.Scan.Key.keyAtG2
  key_at_g3 : p.lookup "key_at_g3" = some L.Scan.Key.keyAtG3
  key_at_g4 : p.lookup "key_at_g4" = some L.Scan.Key.keyAtG4
  key_at_g5 : p.lookup "key_at_g5" = some L.Scan.Key.keyAtG5
  key_at_g6 : p.lookup "key_at_g6" = some L.Scan.Key.keyAtG6
  key_at : p.lookup "key_at" = some L.Scan.Key.keyAt
  value_at : p.lookup "value_at" = some L.Scan.Key.valueAt
  next_member : p.lookup "next_member" = some nextMember
  slot_nat : p.lookup "slot_nat" = some slotNat
  read_nat : p.lookup "read_nat" = some L.Front.Fields.readNat
  scan_nat_list : p.lookup "scan_nat_list" = some scanNatList
  match_lit : p.lookup "match_lit" = some L.Scan.Lit.matchLit
  scan_bool : p.lookup "scan_bool" = some L.Scan.Lit.scanBool
  if_reset : p.lookup "if_reset" = some ifReset
  ifr_alloc : p.lookup "ifr_alloc" = some ifrAlloc
  ifl_alloc : p.lookup "ifl_alloc" = some iflAlloc
  ifl_push : p.lookup "ifl_push" = some iflPush
  fld_alloc : p.lookup "fld_alloc" = some fldAlloc
  fld_put : p.lookup "fld_put" = some fldPut
  ind_size : p.lookup "ind_size" = some indSize
  ind_slot : p.lookup "ind_slot" = some indSlot
  ifl_ids : p.lookup "ifl_ids" = some iflIds
  ind_num : p.lookup "ind_num" = some indNum
  ind_bool : p.lookup "ind_bool" = some indBool
  ind_nlist : p.lookup "ind_nlist" = some indNList
  ind_member : p.lookup "ind_member" = some indMember
  ind_obj : p.lookup "ind_obj" = some indObj
  ind_list : p.lookup "ind_list" = some indList
  ind_fields : p.lookup "ind_fields" = some indFields
  no_st8 : p.noSt8 = true

section specs
variable (p : Prog) (hL : IndFieldLookups p)
include hL

theorem ifReset_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "if_reset" []
    ⦃fun _ s' => LocEq s' s₀ ∧ ifResetW s₀.mem = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ hL.if_reset]
  simp only [callFn, ifReset]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, st64] <;> finish [ifResetW]

theorem fldAlloc_spec (n : Nat) (s₀ : St) (kind k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "fld_alloc" [kind, k]
    ⦃fun r s' => LocEq s' s₀ ∧ fldAllocW s₀.mem kind k = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hL.fld_alloc]
  simp only [callFn, fldAlloc]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        iflAlloc_spec p hL.ifl_alloc n, ifrAlloc_spec p hL.ifr_alloc n] <;> finish [fldAllocW]

theorem fldPut_spec (n : Nat) (s₀ : St) (kind q s x : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "fld_put" [kind, q, s, x]
    ⦃fun _ s' => LocEq s' s₀ ∧ s'.mem = fldPutW s₀.mem kind q s x; ⊤⦄ := by
  rw [invoke_eq _ hL.fld_put]
  simp only [callFn, fldPut]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, st64] <;> finish [fldPutW]

theorem indSize_spec (n : Nat) (s₀ : St) (kind : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ind_size" [kind]
    ⦃fun r s' => s' = s₀ ∧ r = [indSizeN kind]; ⊤⦄ := by
  rw [invoke_eq _ hL.ind_size]
  simp only [callFn, indSize]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs] <;> finish [indSizeN]

theorem indSlot_spec (n : Nat) (s₀ : St) (kind k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ind_slot" [kind, k]
    ⦃fun r s' => s' = s₀ ∧
      r = [(indSlotN kind k).1, (indSlotN kind k).2.1, (indSlotN kind k).2.2]; ⊤⦄ := by
  rw [invoke_eq _ hL.ind_slot]
  simp only [callFn, indSlot]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs] <;> finish [indSlotN]

variable (b : Array UInt8) (hb : b.size < 2 ^ 63)
include hb

theorem idsLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n iflIdsLoop
    ⦃fun r s' => r ≠ .brk ∧ r.retOr [0, 0] = [s₀.loc 2, lsCntN b (s₀.loc 1) (s₀.loc 3)] ∧
      idsLoopM b s₀.mem (s₀.loc 1) = some s'.mem; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := iflIdsLoop) rfl]
    have hb64 : b.size < 2 ^ 64 := by omega
    have hpush := fun s₁ x => Triple.keep hL.no_st8 (iflPush_spec p hL.ifl_alloc hL.ifl_push n s₁ x)
    sym (gen := 16) only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld8, ih,
        L.Scan.Leaves.numEnd_spec p hL.skip_digits hL.num_end b hb64 n,
        L.Front.Fields.readNat_spec p b hb hL.read_nat n, hpush] <;> finish [NONE]

theorem idsLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    step p (exec p n) iflIdsLoop
    ⦃fun r s' => r ≠ .brk ∧ r.retOr [0, 0] = [s₀.loc 2, lsCntN b (s₀.loc 1) (s₀.loc 3)] ∧
      idsLoopM b s₀.mem (s₀.loc 1) = some s'.mem; ⊤⦄ :=
  Triple.step_exec (idsLoop_spec p hL b hb (n + 1) s₀)

theorem iflIds_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (v : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ifl_ids" [v]
    ⦃fun r s' => LocEq s' s₀ ∧ r = [rdW (s₀.mem.arr64 IFL) 0 + 1, lsCntN b (v + 1) 0] ∧
      idsM b s₀.mem v = some s'.mem; ⊤⦄ := by
  rw [invoke_eq _ hL.ifl_ids]
  simp only [callFn, iflIds]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym (gen := 16) only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        iflAlloc_spec p hL.ifl_alloc n, idsLoop_step_spec p hL b hb n] <;> finish [idsM, allocW_eq]

theorem indNum_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (kind q ks v h s : Word)
    (hv : v.toNat ≤ b.size) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ind_num" [kind, q, ks, v, h, s]
    ⦃fun r s' => LocEq s' s₀ ∧ numW b s₀.mem kind q ks v h s = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hL.ind_num]
  simp only [callFn, indNum]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym (gen := 16) only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        slotNat_spec p b hb hL.skip_digits hL.num_end hL.slot_nat n,
        L.Front.Fields.readNat_spec p b hb hL.read_nat n, fldPut_spec p hL n] <;>
      finish [numW, NONE]

theorem indBool_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (kind q v h s : Word)
    (hv : v.toNat ≤ b.size) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ind_bool" [kind, q, v, h, s]
    ⦃fun r s' => LocEq s' s₀ ∧ boolW b s₀.mem kind q v h s = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hL.ind_bool]
  simp only [callFn, indBool]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have hb64 : b.size < 2 ^ 64 := by omega
    have hv5 : v.toNat + 5 < 2 ^ 64 := by omega
    sym (gen := 16) only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        L.Scan.Lit.scanBool_spec p hL.match_lit hL.scan_bool b hb64 n, fldPut_spec p hL n] <;>
      finish [boolW]

theorem indNList_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (kind q v h s : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ind_nlist" [kind, q, v, h, s]
    ⦃fun r s' => LocEq s' s₀ ∧ nlistW b s₀.mem kind q v h s = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hL.ind_nlist]
  simp only [callFn, indNList]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym (gen := 16) only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        scanNatList_spec p b hb hL.skip_digits hL.num_end hL.scan_nat_list n,
        iflIds_spec p hL b hb n, fldPut_spec p hL n] <;>
      finish [nlistW]

end specs

end L.Front.Ind

/-! ## The mutual specs -/

namespace L.Front.Ind

section mspecs
variable (p : Prog) (hL : IndFieldLookups p) (b : Array UInt8) (hb : b.size < 2 ^ 63)

/-- `ind_obj`'s loop at fuel `n`. -/
def ObjLoopS (n : Nat) : Prop := ∀ s₀ : St,
  ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄ exec p n indObjLoop
  ⦃fun r s' => r ≠ .brk ∧ objLoopW b s₀.mem (s₀.loc 1) (s₀.loc 2) (s₀.loc 0) (s₀.loc 3) =
    some ((r.retOr [0]).headD 0, s'.mem); ⊤⦄

/-- `ind_obj` at fuel `n`. -/
def ObjS (n : Nat) : Prop := ∀ (s₀ : St) (i kind q : Word), s₀.mem.arr8 IN = b →
  ⦃fun s => s = s₀⦄ invoke p (exec p n) "ind_obj" [i, kind, q]
  ⦃fun r s' => LocEq s' s₀ ∧ objW b s₀.mem i kind q = some (r.headD 0, s'.mem); ⊤⦄

/-- `ind_member` at fuel `n`. -/
def MemberS (n : Nat) : Prop := ∀ (s₀ : St) (kind q ks k v : Word), s₀.mem.arr8 IN = b →
  v.toNat ≤ b.size →
  ⦃fun s => s = s₀⦄ invoke p (exec p n) "ind_member" [kind, q, ks, k, v]
  ⦃fun r s' => LocEq s' s₀ ∧ memberW b s₀.mem kind q ks k v = some (r.headD 0, s'.mem); ⊤⦄

/-- `ind_list` at fuel `n`. -/
def ListS (n : Nat) : Prop := ∀ (s₀ : St) (v sub : Word), s₀.mem.arr8 IN = b →
  ⦃fun s => s = s₀⦄ invoke p (exec p n) "ind_list" [v, sub]
  ⦃fun r s' => LocEq s' s₀ ∧
    listW b s₀.mem v sub = some ((r.headD 0, r.tail.headD 0, r.tail.tail.headD 0), s'.mem); ⊤⦄

/-- `ind_list`'s loop at fuel `n`. -/
def ListLoopS (n : Nat) : Prop := ∀ s₀ : St,
  ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄ exec p n indListLoop
  ⦃fun r s' => r ≠ .brk ∧ listLoopW b s₀.mem (s₀.loc 1) (s₀.loc 8) (s₀.loc 3) (s₀.loc 4) (s₀.loc 2) =
    some (((r.retOr [0, 0, 0]).headD 0, (r.retOr [0, 0, 0]).tail.headD 0,
      (r.retOr [0, 0, 0]).tail.tail.headD 0), s'.mem); ⊤⦄

include hL hb

theorem objLoop_succ (n : Nat) (hmem : MemberS p b n) (hloop : ObjLoopS p b n) :
    ObjLoopS p b (n + 1) := by
  intro s₀
  rw [exec, step_while (w := indObjLoop) rfl]
  have hm' := fun s₁ kind q ks k v hm hv => Triple.keep hL.no_st8 (hmem s₁ kind q ks k v hm hv)
  have ih := hloop
  unfold ObjLoopS at ih
  sym (gen := 16) only [lang_grind, arena_grind] =>
    vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ih, hm',
      nextMember_spec p b hb hL.skip_ws hL.key_end hL.key_at_g1 hL.key_at_g2 hL.key_at_g3
        hL.key_at_g4 hL.key_at_g5 hL.key_at_g6 hL.key_at hL.value_at hL.next_member n] <;> finish

theorem obj_succ (n : Nat) (hloop : ObjLoopS p b (n + 1)) : ObjS p b (n + 1) := by
  intro s₀ i kind q hm
  rw [invoke_eq _ hL.ind_obj]
  simp only [callFn, indObj]
  have hstep : ∀ s₁ : St, ⦃fun s => s = s₁ ∧ s.mem.arr8 IN = b⦄ step p (exec p n) indObjLoop
      ⦃fun r s' => r ≠ .brk ∧ objLoopW b s₁.mem (s₁.loc 1) (s₁.loc 2) (s₁.loc 0) (s₁.loc 3) =
        some ((r.retOr [0]).headD 0, s'.mem); ⊤⦄ := fun s₁ => Triple.step_exec (hloop s₁)
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, hstep] <;> finish

theorem member_succ (n : Nat) (hlist : ListS p b n) : MemberS p b (n + 1) := by
  intro s₀ kind q ks k v hm hv
  unfold ListS at hlist
  rw [invoke_eq _ hL.ind_member]
  simp only [callFn, indMember]
  sym (gen := 16) only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, hlist,
      indSlot_spec p hL n, indNum_spec p hL b hb n, indBool_spec p hL b hb n,
      indNList_spec p hL b hb n, fldPut_spec p hL n] <;> finish

theorem listLoop_succ (n : Nat) (hobj : ObjS p b n) (hloop : ListLoopS p b n) :
    ListLoopS p b (n + 1) := by
  intro s₀
  rw [exec, step_while (w := indListLoop) rfl]
  have ho' := fun s₁ i kind q hm => Triple.keep hL.no_st8 (hobj s₁ i kind q hm)
  have ha' := fun s₁ kind k => Triple.keep hL.no_st8 (fldAlloc_spec p hL n s₁ kind k)
  have ih := hloop
  unfold ListLoopS at ih
  sym (gen := 16) only [lang_grind, arena_grind] =>
    vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld8, st64, ih, ho', ha'] <;>
    finish [flagsW]

theorem list_succ (n : Nat) (hloop : ListLoopS p b (n + 1)) : ListS p b (n + 1) := by
  intro s₀ v sub hm
  rw [invoke_eq _ hL.ind_list]
  simp only [callFn, indList]
  have hstep : ∀ s₁ : St, ⦃fun s => s = s₁ ∧ s.mem.arr8 IN = b⦄ step p (exec p n) indListLoop
      ⦃fun r s' => r ≠ .brk ∧
        listLoopW b s₁.mem (s₁.loc 1) (s₁.loc 8) (s₁.loc 3) (s₁.loc 4) (s₁.loc 2) =
        some (((r.retOr [0, 0, 0]).headD 0, (r.retOr [0, 0, 0]).tail.headD 0,
          (r.retOr [0, 0, 0]).tail.tail.headD 0), s'.mem); ⊤⦄ := fun s₁ => Triple.step_exec (hloop s₁)
  have ha' := fun s₁ kind k => Triple.keep hL.no_st8 (fldAlloc_spec p hL n s₁ kind k)
  sym (gen := 16) only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld8, hstep, ha',
      indSize_spec p hL n] <;> finish

theorem mutual_specs (n : Nat) :
    ObjLoopS p b n ∧ ObjS p b n ∧ MemberS p b n ∧ ListS p b n ∧ ListLoopS p b n := by
  induction n with
  | zero =>
    refine ⟨fun s₀ => ?_, fun s₀ i kind q _ => ?_, fun s₀ kind q ks k v _ _ => ?_,
      fun s₀ v sub _ => ?_, fun s₀ => ?_⟩
    · vcgen [exec] <;> grind
    · rw [invoke_eq _ hL.ind_obj]; simp only [callFn]; vcgen [exec] <;> grind
    · rw [invoke_eq _ hL.ind_member]; simp only [callFn]; vcgen [exec] <;> grind
    · rw [invoke_eq _ hL.ind_list]; simp only [callFn]; vcgen [exec] <;> grind
    · vcgen [exec] <;> grind
  | succ n ih =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih
    have l1 := objLoop_succ p hL b hb n h3 h1
    have l5 := listLoop_succ p hL b hb n h2 h5
    exact ⟨l1, obj_succ p hL b hb n l1, member_succ p hL b hb n h4, list_succ p hL b hb n l5, l5⟩

end mspecs

/-! ## `ind_fields` -/

/-- After `ind_obj(v, 4, p)`: the block record's six words. -/
def fieldsK2 (q : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => some ([rdW (m.arr64 IFR) q, rdW (m.arr64 IFR) (q + 1), rdW (m.arr64 IFR) (q + 2),
      rdW (m.arr64 IFR) (q + 3), rdW (m.arr64 IFR) (q + 4), rdW (m.arr64 IFR) (q + 5)], m)

/-- After `ifr_alloc(6)`. -/
def fieldsK1 (b : Array UInt8) (v : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (q, m) => fieldsK2 q (objW b m v 4 q)

/-- After `if_reset`. -/
def fieldsK0 (b : Array UInt8) (v : Word) : Option Mem → Option (List Word × Mem)
  | none => none
  | some m => fieldsK1 b v (allocW m IFR 6)

section fArms
variable (b : Array UInt8) (v q e : Word) (m : Mem)
@[arena_grind =] theorem fieldsK2_none : fieldsK2 q none = none := rfl
@[arena_grind =] theorem fieldsK2_some : fieldsK2 q (some (e, m)) =
    some ([rdW (m.arr64 IFR) q, rdW (m.arr64 IFR) (q + 1), rdW (m.arr64 IFR) (q + 2),
      rdW (m.arr64 IFR) (q + 3), rdW (m.arr64 IFR) (q + 4), rdW (m.arr64 IFR) (q + 5)], m) := rfl
@[arena_grind =] theorem fieldsK1_none : fieldsK1 b v none = none := rfl
@[arena_grind =] theorem fieldsK1_some : fieldsK1 b v (some (q, m)) = fieldsK2 q (objW b m v 4 q) := rfl
@[arena_grind =] theorem fieldsK0_none : fieldsK0 b v none = none := rfl
@[arena_grind =] theorem fieldsK0_some : fieldsK0 b v (some m) = fieldsK1 b v (allocW m IFR 6) := rfl
end fArms

/-- **The model of `ind_fields(v)`**: the six words and the memory after. -/
def indFieldsW (b : Array UInt8) (m : Mem) (v : Word) : Option (List Word × Mem) :=
  fieldsK0 b v (ifResetW m)

section fspec
variable (p : Prog) (hL : IndFieldLookups p) (b : Array UInt8) (hb : b.size < 2 ^ 63)
include hL hb

/-- **`ind_fields(v)` is `indFieldsW`.** -/
theorem indFields_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (v : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "ind_fields" [v]
    ⦃fun r s' => LocEq s' s₀ ∧ indFieldsW b s₀.mem v = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hL.ind_fields]
  simp only [callFn, indFields]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    have ho := (mutual_specs p hL b hb n).2.1
    unfold ObjS at ho
    have hr' := fun s₁ => Triple.keep hL.no_st8 (ifReset_spec p hL n s₁)
    have ha' := fun s₁ k => Triple.keep hL.no_st8 (ifrAlloc_spec p hL.ifr_alloc n s₁ k)
    sym (gen := 16) only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ho, hr', ha'] <;>
      finish [indFieldsW]

end fspec

end L.Front.Ind
