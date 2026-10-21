module

public import ConAgua.L.Notation
public import ConAgua.L.Logic
public import ConAgua.Scan.Common
public import ConAgua.Scan.Leaves
public import ConAgua.Scan.Utf8
public import ConAgua.Scan.Key
public import ConAgua.Scan.Values
meta import ConAgua.L.Semantics

@[expose] public section

/-!
# `next_member` and the generic object loop (`scan_fast.rs:1339`)

Every object of the dialect is read by a slot loop: `next_member` skips whitespace, takes
JSON's alternation at `,`, stops at `}`, and classifies the key at `"`; the record's loop then
checks the key against its key set and its `seen` mask and scans the value. Rust factors the
first half out as `next_member` (its deviation 3); con-leche writes it out in every loop.

In L, `next_member(i, w)` returns Rust's `Result<(Member, usize, bool), _>` as five words
`(tag, pos, w, key, val)`: tag `0` for an error, `1` for the closing brace at `pos`, `2` for the
key `key` (its code, `ConAgua.Scan.Key`) whose opening quote is at `pos` and whose value starts
at `val`.

**One model for all record loops.** Without the values they would store, con-leche's record
loops differ only in their key set: which key sets which bit of `seen`, how its value is
scanned, and which bits the closing brace requires. `objN bit val mask` is the loop for any key
set: `bit k` is key `k`'s bit (`0` if `k` is not a key of the record), `val k ks v` scans its
value at `v` (the key's quote at `ks`) and returns the position after it or `0`, `mask` is the
required bits. Each record's L loop (`ConAgua.Scan.Records`) is proved against `objN` with its
own `bit`/`val`/`mask`, and each con-leche loop is related to the same instance
(`ConAgua.Scan.RecordsLink`).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Scan.Member

open L.Scan.Utf8 (byteW)
open L.Scan.Leaves (keyEndN)
open L.Scan.Key (keyAtN valueAtN)

/-- The input buffer. -/
abbrev IN : ArrId := 0

/-! ## `next_member` -/

def nextMemberLoop : Stmt := lblk (i, w, c, ke, v, k) {
  while i < len(IN.u8) {
    c := IN.u8[i];
    if c == 32 || c == 9 || c == 13 {
      i += 1
    } else if c == 125 {
      return (1, i, w, 0, 0)
    } else if c == 44 {
      if w != 0 { return (0, 0, 0, 0, 0) };
      i += 1;
      w := 1
    } else if c == 34 {
      if w == 0 { return (0, 0, 0, 0, 0) };
      ke := call key_end(i + 1);
      if ke == 0 { return (0, 0, 0, 0, 0) };
      v := call value_at(i, ke);
      if v == i { return (0, 0, 0, 0, 0) };
      k := call key_at(i, ke - (i + 1));
      return (2, i, w, k, v)
    } else {
      return (0, 0, 0, 0, 0)
    }
  }
}

def nextMember : FunDecl := lfn (i, w) locals (c, ke, v, k) {
  ⟪nextMemberLoop⟫;
  return (0, 0, 0, 0, 0)
}

/-- What `next_member` returns. -/
structure Mbr where
  tag : Word
  pos : Word
  w : Word
  key : Word
  val : Word

/-- The five words of a `Mbr`. -/
def Mbr.enc (m : Mbr) : List Word := [m.tag, m.pos, m.w, m.key, m.val]

/-- The error. -/
def Mbr.err : Mbr := ⟨0, 0, 0, 0, 0⟩

/-- Rust's `next_member`, on words. -/
def nextMemberN (b : Array UInt8) (i w : Word) : Mbr :=
  if h : i < UInt64.ofNat b.size then
    if byteW b i = 32 ∨ byteW b i = 9 ∨ byteW b i = 13 then nextMemberN b (i + 1) w
    else if byteW b i = 125 then ⟨1, i, w, 0, 0⟩
    else if byteW b i = 44 then (if w ≠ 0 then .err else nextMemberN b (i + 1) 1)
    else if byteW b i = 34 then
      if w = 0 then .err
      else if UInt64.ofNat (keyEndN b (i + 1).toNat) = 0 then .err
      else if valueAtN b i (UInt64.ofNat (keyEndN b (i + 1).toNat)) = i then .err
      else ⟨2, i, w, keyAtN b i (UInt64.ofNat (keyEndN b (i + 1).toNat) - (i + 1)),
        valueAtN b i (UInt64.ofNat (keyEndN b (i + 1).toNat))⟩
    else .err
  else .err
termination_by b.size - i.toNat
decreasing_by
  all_goals
    have := L.Scan.lt_of_lt_ofNat h
    have := L.Scan.toNat_add_one_of_lt_ofNat h
    omega

/-- A key's quote is at or after where the search started, and inside the array. -/
theorem nextMemberN_key (b : Array UInt8) (i w : Word) (h : (nextMemberN b i w).tag = 2) :
    i ≤ (nextMemberN b i w).pos ∧ (nextMemberN b i w).pos < UInt64.ofNat b.size := by
  fun_induction nextMemberN b i w with
  | case1 i w hi _ ih =>
    refine ⟨?_, (ih h).2⟩
    have := (ih h).1
    have := L.Scan.toNat_add_one_of_lt_ofNat hi
    rw [UInt64.le_iff_toNat_le] at *
    omega
  | case4 i w hi _ _ _ _ ih =>
    refine ⟨?_, (ih h).2⟩
    have := (ih h).1
    have := L.Scan.toNat_add_one_of_lt_ofNat hi
    rw [UInt64.le_iff_toNat_le] at *
    omega
  | case8 => exact ⟨UInt64.le_refl _, by assumption⟩
  | _ => simp_all [Mbr.err]

/-! ## The generic object loop -/

/-- con-leche's record loop for the key set `(bit, val, mask)`, from `i` with `wantMember = w`
and the bits `seen`: the position after the closing brace, or `0`. -/
def objN (bit : Word → Word) (val : Word → Word → Word → Word) (mask : Word)
    (b : Array UInt8) (i w seen : Word) : Word :=
  if (nextMemberN b i w).tag = 0 then 0
  else if (nextMemberN b i w).tag = 1 then
    if (nextMemberN b i w).w ≠ 0 ∧ seen ≠ 0 then 0
    else if seen &&& mask ≠ mask then 0
    else (nextMemberN b i w).pos + 1
  else if (nextMemberN b i w).tag ≠ 2 then 0
  else if bit (nextMemberN b i w).key = 0 then 0
  else if seen &&& bit (nextMemberN b i w).key ≠ 0 then 0
  else if _h : (nextMemberN b i w).pos <
      val (nextMemberN b i w).key (nextMemberN b i w).pos (nextMemberN b i w).val then
    objN bit val mask b
      (val (nextMemberN b i w).key (nextMemberN b i w).pos (nextMemberN b i w).val) 0
      (seen ||| bit (nextMemberN b i w).key)
  else 0
termination_by b.size - i.toNat
decreasing_by
  have hk := nextMemberN_key b i w (by simp_all)
  have := L.Scan.lt_of_lt_ofNat hk.2
  rw [UInt64.le_iff_toNat_le] at hk
  rw [UInt64.lt_iff_toNat_lt] at _h
  omega

/-- Entering an object at its opening brace. -/
def objEntryN (bit : Word → Word) (val : Word → Word → Word → Word) (mask : Word)
    (b : Array UInt8) (i : Word) : Word :=
  if i < UInt64.ofNat b.size ∧ byteW b i = 123 then objN bit val mask b (i + 1) 1 0 else 0

/-! ## The generic list of objects -/

/-- con-leche's `scan*ListLoop` for lists of objects read by `item` (the position after the
item, or `0`): the position after the closing bracket, or `0`. `cnt` counts the items read
(con-leche's `acc`). -/
def objListN (item : Word → Word) (b : Array UInt8) (i cnt w : Word) : Word :=
  if h : i < UInt64.ofNat b.size then
    if byteW b i = 32 ∨ byteW b i = 9 ∨ byteW b i = 13 then objListN item b (i + 1) cnt w
    else if byteW b i = 93 then (if w ≠ 0 ∧ cnt ≠ 0 then 0 else i + 1)
    else if byteW b i = 44 then (if w ≠ 0 then 0 else objListN item b (i + 1) cnt 1)
    else if byteW b i = 123 then
      if w = 0 then 0
      else if i < item i then objListN item b (item i) (cnt + 1) 0
      else 0
    else 0
  else 0
termination_by b.size - i.toNat
decreasing_by
  all_goals
    have := L.Scan.lt_of_lt_ofNat h
    first
      | (rename_i hj; rw [UInt64.lt_iff_toNat_lt] at hj; omega)
      | (have := L.Scan.toNat_add_one_of_lt_ofNat h; omega)

/-- Entering a list at its opening bracket. -/
def objListEntryN (item : Word → Word) (b : Array UInt8) (i : Word) : Word :=
  if i < UInt64.ofNat b.size ∧ byteW b i = 91 then objListN item b (i + 1) 0 1 else 0

end L.Scan.Member
