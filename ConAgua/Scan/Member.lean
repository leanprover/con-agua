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

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:2427-2574 ConLeche.Frontend.scanLineLoop -/
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

/-! ### Arms of `nextMemberN` (one guarded equation per arm, DESIGN.md "Proof recipe") -/

section
variable (b : Array UInt8) (i w : Word)

attribute [local lang_grind] Mbr.enc Mbr.err

theorem nextMemberN_ws (h : i < UInt64.ofNat b.size)
    (hc : byteW b i = 32 ∨ byteW b i = 9 ∨ byteW b i = 13) :
    nextMemberN b i w = nextMemberN b (i + 1) w := by
  rw [nextMemberN, dite_eq_left h, ite_eq_left hc]
theorem nextMemberN_close (h : i < UInt64.ofNat b.size)
    (hc : ¬ (byteW b i = 32 ∨ byteW b i = 9 ∨ byteW b i = 13)) (h1 : byteW b i = 125) :
    nextMemberN b i w = ⟨1, i, w, 0, 0⟩ := by
  rw [nextMemberN, dite_eq_left h, ite_eq_right hc, ite_eq_left h1]
theorem nextMemberN_comma (h : i < UInt64.ofNat b.size)
    (hc : ¬ (byteW b i = 32 ∨ byteW b i = 9 ∨ byteW b i = 13)) (h1 : byteW b i ≠ 125)
    (h2 : byteW b i = 44) :
    nextMemberN b i w = if w ≠ 0 then .err else nextMemberN b (i + 1) 1 := by
  rw [nextMemberN, dite_eq_left h, ite_eq_right hc, ite_eq_right h1, ite_eq_left h2]
theorem nextMemberN_quote (h : i < UInt64.ofNat b.size)
    (hc : ¬ (byteW b i = 32 ∨ byteW b i = 9 ∨ byteW b i = 13)) (h1 : byteW b i ≠ 125)
    (h2 : byteW b i ≠ 44) (h3 : byteW b i = 34) :
    nextMemberN b i w =
      if w = 0 then .err
      else if UInt64.ofNat (keyEndN b (i + 1).toNat) = 0 then .err
      else if valueAtN b i (UInt64.ofNat (keyEndN b (i + 1).toNat)) = i then .err
      else ⟨2, i, w, keyAtN b i (UInt64.ofNat (keyEndN b (i + 1).toNat) - (i + 1)),
        valueAtN b i (UInt64.ofNat (keyEndN b (i + 1).toNat))⟩ := by
  rw [nextMemberN, dite_eq_left h, ite_eq_right hc, ite_eq_right h1, ite_eq_right h2, ite_eq_left h3]
theorem nextMemberN_other (h : i < UInt64.ofNat b.size)
    (hc : ¬ (byteW b i = 32 ∨ byteW b i = 9 ∨ byteW b i = 13)) (h1 : byteW b i ≠ 125)
    (h2 : byteW b i ≠ 44) (h3 : byteW b i ≠ 34) :
    nextMemberN b i w = .err := by
  rw [nextMemberN, dite_eq_left h, ite_eq_right hc, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]
theorem nextMemberN_end (h : ¬ i < UInt64.ofNat b.size) : nextMemberN b i w = .err := by
  rw [nextMemberN, dite_eq_right h]

grind_pattern [lang_grind] nextMemberN_ws => nextMemberN b i w, b[i.toNat]
grind_pattern [lang_grind] nextMemberN_close => nextMemberN b i w, b[i.toNat]
grind_pattern [lang_grind] nextMemberN_comma => nextMemberN b i w, b[i.toNat]
grind_pattern [lang_grind] nextMemberN_quote => nextMemberN b i w, b[i.toNat]
grind_pattern [lang_grind] nextMemberN_other => nextMemberN b i w, b[i.toNat]
grind_pattern [lang_grind] nextMemberN_end => nextMemberN b i w

end

/-! ### The spec -/

grind_pattern [lang_grind] L.Scan.Values.keyEndN_lt => keyEndN b j

section nextMember
variable (p : Prog) (b : Array UInt8) (hb : b.size < 2 ^ 63)
    (hpw : p.lookup "skip_ws" = some L.Scan.Leaves.skipWs)
    (hpk : p.lookup "key_end" = some L.Scan.Leaves.keyEnd)
    (hpa1 : p.lookup "key_at_g1" = some L.Scan.Key.keyAtG1)
    (hpa2 : p.lookup "key_at_g2" = some L.Scan.Key.keyAtG2)
    (hpa3 : p.lookup "key_at_g3" = some L.Scan.Key.keyAtG3)
    (hpa4 : p.lookup "key_at_g4" = some L.Scan.Key.keyAtG4)
    (hpa5 : p.lookup "key_at_g5" = some L.Scan.Key.keyAtG5)
    (hpa6 : p.lookup "key_at_g6" = some L.Scan.Key.keyAtG6)
    (hpa : p.lookup "key_at" = some L.Scan.Key.keyAt)
    (hpv : p.lookup "value_at" = some L.Scan.Key.valueAt)
    (hpm : p.lookup "next_member" = some nextMember)
include hb hpw hpk hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv

attribute [local lang_grind] Mbr.enc Mbr.err

theorem nextMemberLoop_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) :
    ⦃fun s => s = s₀⦄
    exec p n nextMemberLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr Mbr.err.enc = (nextMemberN b (s₀.loc 0) (s₀.loc 1)).enc; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := nextMemberLoop) rfl]
    have hb' : b.size < 2 ^ 64 := by omega
    sym only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld8, ih,
        L.Scan.Leaves.keyEnd_spec p hpk b hb' n, L.Scan.Key.valueAt_spec p hpw hpv b hb n,
        L.Scan.Key.keyAt_spec p hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa b hb n] <;> finish


include hpm in
theorem nextMember_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i w : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "next_member" [i, w]
    ⦃fun r s' => s' = s₀ ∧ r = [(nextMemberN b i w).tag, (nextMemberN b i w).pos,
      (nextMemberN b i w).w, (nextMemberN b i w).key, (nextMemberN b i w).val]; ⊤⦄ := by
  rw [invoke_eq _ hpm]
  simp only [callFn, nextMember]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind] =>
      vcgen [exec, step, evalE, evalArgs, fun s₀ hm => Triple.step_exec (nextMemberLoop_spec p b hb hpw hpk hpa1 hpa2 hpa3 hpa4 hpa5 hpa6 hpa hpv (n + 1) s₀ hm)] <;> finish

end nextMember

/-- The tag is `0`, `1` or `2`. -/
theorem nextMemberN_tag (b : Array UInt8) (i w : Word) (h0 : (nextMemberN b i w).tag ≠ 0)
    (h1 : (nextMemberN b i w).tag ≠ 1) : (nextMemberN b i w).tag = 2 := by
  fun_induction nextMemberN b i w <;> simp_all [Mbr.err]

grind_pattern [lang_grind] nextMemberN_tag => (nextMemberN b i w).tag

/-- What `next_member` stops at is inside the array. -/
theorem nextMemberN_pos_lt (b : Array UInt8) (i w : Word) (h : (nextMemberN b i w).tag ≠ 0) :
    (nextMemberN b i w).pos < UInt64.ofNat b.size := by
  fun_induction nextMemberN b i w <;> simp_all [Mbr.err]

/-- A key's value starts inside the array or at its end (the precondition of the value
scanners). -/
theorem nextMemberN_val_le (b : Array UInt8) (i w : Word) (hb : b.size < 2 ^ 63)
    (h : (nextMemberN b i w).tag = 2) : (nextMemberN b i w).val.toNat ≤ b.size := by
  fun_induction nextMemberN b i w with
  | case1 i w hi _ ih => exact ih h
  | case4 i w hi _ _ _ _ ih => exact ih h
  | case8 i w hi _ _ _ _ _ hke _ =>
    have := L.Scan.lt_of_lt_ofNat hi
    have hk := L.Scan.Values.keyEndN_lt b (i + 1).toNat (by intro h0; rw [h0] at hke; exact hke rfl)
    apply L.Scan.Key.valueAtN_le b _ _ (by omega) _ hb
    have h64 : keyEndN b (i + 1).toNat < 2 ^ 64 := by omega
    rw [UInt64.toNat_ofNat_of_lt' h64]; exact hk
  | _ => simp_all [Mbr.err]

grind_pattern [lang_grind] nextMemberN_val_le => (nextMemberN b i w).val

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
  have hk := nextMemberN_key b i w (nextMemberN_tag b i w (by assumption) (by assumption))
  have := L.Scan.lt_of_lt_ofNat hk.2
  rw [UInt64.le_iff_toNat_le] at hk
  rw [UInt64.lt_iff_toNat_lt] at _h
  omega

/-! ### Arms of `objN` -/

section
variable (bit : Word → Word) (val : Word → Word → Word → Word) (mask : Word) (b : Array UInt8)
  (i w seen : Word)

theorem objN_err (h : (nextMemberN b i w).tag = 0) : objN bit val mask b i w seen = 0 := by
  rw [objN, ite_eq_left h]
theorem objN_close (h : (nextMemberN b i w).tag = 1) :
    objN bit val mask b i w seen =
      if (nextMemberN b i w).w ≠ 0 ∧ seen ≠ 0 then 0
      else if seen &&& mask ≠ mask then 0
      else (nextMemberN b i w).pos + 1 := by
  rw [objN, ite_eq_right (by simp [h]), ite_eq_left h]
theorem objN_unknown (h0 : (nextMemberN b i w).tag ≠ 0) (h1 : (nextMemberN b i w).tag ≠ 1) (hb : bit (nextMemberN b i w).key = 0) :
    objN bit val mask b i w seen = 0 := by
  rw [objN, ite_eq_right h0, ite_eq_right h1, ite_eq_left hb]
theorem objN_dup (h0 : (nextMemberN b i w).tag ≠ 0) (h1 : (nextMemberN b i w).tag ≠ 1) (hb : bit (nextMemberN b i w).key ≠ 0)
    (hd : seen &&& bit (nextMemberN b i w).key ≠ 0) : objN bit val mask b i w seen = 0 := by
  rw [objN, ite_eq_right h0, ite_eq_right h1, ite_eq_right hb, ite_eq_left hd]
theorem objN_noprog (h0 : (nextMemberN b i w).tag ≠ 0) (h1 : (nextMemberN b i w).tag ≠ 1) (hb : bit (nextMemberN b i w).key ≠ 0)
    (hd : seen &&& bit (nextMemberN b i w).key = 0)
    (hp : ¬ (nextMemberN b i w).pos <
      val (nextMemberN b i w).key (nextMemberN b i w).pos (nextMemberN b i w).val) :
    objN bit val mask b i w seen = 0 := by
  rw [objN, ite_eq_right h0, ite_eq_right h1, ite_eq_right hb,
    ite_eq_right (by simp [hd]), dite_eq_right hp]
theorem objN_step (e seen' : Word) (h0 : (nextMemberN b i w).tag ≠ 0) (h1 : (nextMemberN b i w).tag ≠ 1)
    (hb : bit (nextMemberN b i w).key ≠ 0) (hd : seen &&& bit (nextMemberN b i w).key = 0)
    (he : val (nextMemberN b i w).key (nextMemberN b i w).pos (nextMemberN b i w).val = e)
    (hp : (nextMemberN b i w).pos < e) (hs : seen' = seen ||| bit (nextMemberN b i w).key) :
    objN bit val mask b i w seen = objN bit val mask b e 0 seen' := by
  subst he hs
  rw [objN, ite_eq_right h0, ite_eq_right h1, ite_eq_right hb,
    ite_eq_right (by simp [hd]), dite_eq_left hp]

grind_pattern [lang_grind] objN_err => objN bit val mask b i w seen, nextMemberN b i w
grind_pattern [lang_grind] objN_close => objN bit val mask b i w seen, nextMemberN b i w
grind_pattern [lang_grind] objN_unknown => objN bit val mask b i w seen, nextMemberN b i w
grind_pattern [lang_grind] objN_dup => objN bit val mask b i w seen, nextMemberN b i w
grind_pattern [lang_grind] objN_noprog => objN bit val mask b i w seen, nextMemberN b i w
grind_pattern [lang_grind] objN_step =>
  objN bit val mask b i w seen, nextMemberN b i w, objN bit val mask b e 0 seen'

end

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

/-! ### Arms of `objListN` -/

section
variable (item : Word → Word) (b : Array UInt8) (i cnt w : Word)

theorem objListN_ws (h : i < UInt64.ofNat b.size)
    (hc : byteW b i = 32 ∨ byteW b i = 9 ∨ byteW b i = 13) :
    objListN item b i cnt w = objListN item b (i + 1) cnt w := by
  rw [objListN, dite_eq_left h, ite_eq_left hc]
theorem objListN_close (h : i < UInt64.ofNat b.size)
    (hc : ¬ (byteW b i = 32 ∨ byteW b i = 9 ∨ byteW b i = 13)) (h1 : byteW b i = 93) :
    objListN item b i cnt w = if w ≠ 0 ∧ cnt ≠ 0 then 0 else i + 1 := by
  rw [objListN, dite_eq_left h, ite_eq_right hc, ite_eq_left h1]
theorem objListN_comma (h : i < UInt64.ofNat b.size)
    (hc : ¬ (byteW b i = 32 ∨ byteW b i = 9 ∨ byteW b i = 13)) (h1 : byteW b i ≠ 93)
    (h2 : byteW b i = 44) :
    objListN item b i cnt w = if w ≠ 0 then 0 else objListN item b (i + 1) cnt 1 := by
  rw [objListN, dite_eq_left h, ite_eq_right hc, ite_eq_right h1, ite_eq_left h2]
theorem objListN_open (h : i < UInt64.ofNat b.size)
    (hc : ¬ (byteW b i = 32 ∨ byteW b i = 9 ∨ byteW b i = 13)) (h1 : byteW b i ≠ 93)
    (h2 : byteW b i ≠ 44) (h3 : byteW b i = 123) :
    objListN item b i cnt w =
      if w = 0 then 0 else if i < item i then objListN item b (item i) (cnt + 1) 0 else 0 := by
  rw [objListN, dite_eq_left h, ite_eq_right hc, ite_eq_right h1, ite_eq_right h2, ite_eq_left h3]
theorem objListN_other (h : i < UInt64.ofNat b.size)
    (hc : ¬ (byteW b i = 32 ∨ byteW b i = 9 ∨ byteW b i = 13)) (h1 : byteW b i ≠ 93)
    (h2 : byteW b i ≠ 44) (h3 : byteW b i ≠ 123) : objListN item b i cnt w = 0 := by
  rw [objListN, dite_eq_left h, ite_eq_right hc, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]
theorem objListN_end (h : ¬ i < UInt64.ofNat b.size) : objListN item b i cnt w = 0 := by
  rw [objListN, dite_eq_right h]

grind_pattern [lang_grind] objListN_ws => objListN item b i cnt w, b[i.toNat]
grind_pattern [lang_grind] objListN_close => objListN item b i cnt w, b[i.toNat]
grind_pattern [lang_grind] objListN_comma => objListN item b i cnt w, b[i.toNat]
grind_pattern [lang_grind] objListN_open => objListN item b i cnt w, b[i.toNat]
grind_pattern [lang_grind] objListN_other => objListN item b i cnt w, b[i.toNat]
grind_pattern [lang_grind] objListN_end => objListN item b i cnt w

end

end L.Scan.Member
