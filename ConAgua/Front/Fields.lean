module

meta import ConAgua.L.Semantics
import ConAgua.Census.Attr
public import ConAgua.Scan.Member
public import ConAgua.Scan.Str
public import ConAgua.Scan.Values
import ConAgua.Front.Preserve
public import ConAgua.Front.ReadNatSwar
import ConAgua.L.GrindAttr
import ConAgua.Scan.Common
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# The fields of name and level lines (`scan_fast.rs`'s record values)

Stage B's scanner validates a line and stores nothing (`ConAgua.Scan.Line`). This file models the
values of the records the frontend applies first, names and levels, as a second pass over a line
the validator accepted: `recN` walks the line's members again (`nextMemberN`) and gives five words
`(pl, idx, a, c, d)`. It is the model `front_line`'s spec is stated with; the code reads the line
once (`ConAgua.Front.LineRec`, proved equal on the lines that scan in
`ConAgua.Front.LineRecLink`).

| `pl` | record | `a` | `c` | `d` |
|---|---|---|---|---|
| 1 | name `{"pre":p,"str":s}` | `p` | start of `s`'s body | its end (the closing quote) |
| 2 | name `{"i":n,"pre":p}` | `p` | `n` | |
| 3 | level `succ` | the operand | | |
| 4, 5 | level `max`, `imax` | first operand | second | |
| 6 | level `param` | the name | | |
| 7 | the `meta` header | | | |
| 0 | anything else (expressions, declarations), or a failure | | | |

`idx` is the value of the line's index key (`in`/`il`/`ie`). A number is read by `read_nat` (`rdNatN`),
con-leche's `readNat64` (`readNatAt` for at most 18 digits); a longer one reads as `NONE`
(`2^64 - 1`), which the caller refuses: no export index or name component has 19 digits, and
refusing is a defined failure. Up to 16 digits it converts eight digits per 8-byte load (`rdW1`,
`rdW2`, `swar8`); on a run of digits that is the byte loop's value (`rdNatN_digits`), which is all
the links to con-leche use.

The model trusts the validator: it checks no `seen` mask, no comma alternation, no key set (a
member that is not a name/level key ends it with `pl = 0`), and it reads a string's body as the
byte range between its quotes; `ConAgua.Front.FieldsLink` shows that on a line con-leche's
`scanLineFwd` accepts, the words are the record's fields. Each loop keeps con-leche's progress
guard (`e ≤ ks` stops it), which is also what makes its model terminate.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Front.Fields

open L.Scan.Utf8 (byteW)
open L.Scan.Member
open L.Scan.Values
open L.Scan.Leaves (numEndN)

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
@[no_expose, l_impl ConLeche.Frontend.readNatAt]
def readNat : FunDecl := lfn (v, e) locals (x, w, h, y) {
  if v + 18 < e { return 0xFFFFFFFFFFFFFFFF };
  w := e - v - 1;
  if 8 <= e && e <= len(IN.u8) {
    if w < 8 {
      h := le64!(IN.u8, e - 8) & (0x0F0F0F0F0F0F0F0F << ((7 - w) << 3));
      h := ((h * 2561) >> 8) & 0x00FF00FF00FF00FF;
      h := ((h * 6553601) >> 16) & 0x0000FFFF0000FFFF;
      return (h * 42949672960001) >> 32
    };
    if w < 16 && 16 <= e {
      h := le64!(IN.u8, e - 16) & (0x0F0F0F0F0F0F0F0F << ((15 - w) << 3));
      h := ((h * 2561) >> 8) & 0x00FF00FF00FF00FF;
      h := ((h * 6553601) >> 16) & 0x0000FFFF0000FFFF;
      y := le64!(IN.u8, e - 8) & 0x0F0F0F0F0F0F0F0F;
      y := ((y * 2561) >> 8) & 0x00FF00FF00FF00FF;
      y := ((y * 6553601) >> 16) & 0x0000FFFF0000FFFF;
      return ((h * 42949672960001) >> 32) * 100000000 + ((y * 42949672960001) >> 32)
    }
  };
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

/-- `read_nat` on 1‥8 digits ending at `e` (`w` their count minus one): the word of the 8 bytes
before `e`, masked to the digits' low nibbles, through `swar8`. -/
def rdW1 (b : Array UInt8) (e w : Word) : Word :=
  swar8 (le64 b (e - 8).toNat &&& ((0x0F0F0F0F0F0F0F0F : Word) <<< ((7 - w) <<< 3)))

/-- `read_nat` on 9‥16 digits: the first `w - 7` digits from the word before `e - 8`, the last
eight from the word before `e`. -/
def rdW2 (b : Array UInt8) (e w : Word) : Word :=
  swar8 (le64 b (e - 16).toNat &&& ((0x0F0F0F0F0F0F0F0F : Word) <<< ((15 - w) <<< 3))) * 100000000 +
    swar8 (le64 b (e - 8).toNat &&& 0x0F0F0F0F0F0F0F0F)

/-- `read_nat`'s dispatch after the 18-digit test (`w = e - v - 1`): a word or two inside the
input, else the byte loop. -/
def rdNatF (b : Array UInt8) (v e w : Word) : Word :=
  if 8 ≤ e ∧ e ≤ UInt64.ofNat b.size then
    if w < 8 then rdW1 b e w
    else if w < 16 ∧ 16 ≤ e then rdW2 b e w
    else rdLoopN b v e 0
  else rdLoopN b v e 0

/-- `read_nat(v, e)`. On digits it is `rdLoopN b v e 0` (`rdNatN_digits`). -/
def rdNatN (b : Array UInt8) (v e : Word) : Word := if v + 18 < e then NONE else rdNatF b v e (e - v - 1)

section
variable (b : Array UInt8) (v e w : Word)
theorem rdNatN_short (h : ¬ v + 18 < e) : rdNatN b v e = rdNatF b v e (e - v - 1) := by
  rw [rdNatN, ite_eq_right_iff.mpr (fun h' => absurd h' h)]
theorem rdNatF_out (h : ¬ (8 ≤ e ∧ e ≤ UInt64.ofNat b.size)) : rdNatF b v e w = rdLoopN b v e 0 := by
  rw [rdNatF, ite_eq_right_iff.mpr (fun h' => absurd h' h)]
theorem rdNatF_far (h : 8 ≤ e ∧ e ≤ UInt64.ofNat b.size) (h1 : ¬ w < 8) (h2 : ¬ (w < 16 ∧ 16 ≤ e)) :
    rdNatF b v e w = rdLoopN b v e 0 := by
  simp only [rdNatF, h, h1, h2, and_self, ↓reduceIte]
end

theorem retVal_of_retOr (r : Sig) (h1 : r ≠ .normal) (h2 : r ≠ .brk) (d : List Word) :
    r.retVal = r.retOr d := by
  cases r <;> simp_all [Sig.retVal, Sig.retOr]

section
variable (b : Array UInt8) (v e x : Word)
theorem rdLoopN_stop (h : ¬ v < e) : rdLoopN b v e x = x := by rw [rdLoopN, dite_eq_right h]
theorem rdLoopN_step (h : v < e) :
    rdLoopN b v e x = rdLoopN b (v + 1) e (x * 10 + ((byteW b v - 48) &&& 255)) := by
  rw [rdLoopN, dite_eq_left h]
end
grind_pattern [lang_grind] rdLoopN_stop => rdLoopN b v e x
grind_pattern [lang_grind] rdLoopN_step => rdLoopN b v e x, b[v.toNat]

/-! ### `read_nat` on digits: the word steps are the byte loop -/

theorem digit_bang (b : Array UInt8) (a z : Nat)
    (hd : ∀ j, a ≤ j → j < z → ∃ h : j < b.size, 48 ≤ b[j] ∧ b[j] ≤ 57) :
    ∀ j, a ≤ j → j < z → 48 ≤ b[j]!.toNat ∧ b[j]!.toNat ≤ 57 := by
  intro j h1 h2
  obtain ⟨h, d1, d2⟩ := hd j h1 h2
  rw [getElem!_pos b j h]
  exact ⟨d1, d2⟩

theorem ofNat_ten_pow (n : Nat) : UInt64.ofNat (10 ^ n) = 10 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.pow_succ, UInt64.ofNat_mul, ih, UInt64.pow_succ]; rfl

theorem rdLoopN_dval (b : Array UInt8) (n : Nat) : ∀ (v e x : Word), e.toNat = v.toNat + n →
    (∀ j, v.toNat ≤ j → j < e.toNat → 48 ≤ b[j]!.toNat ∧ b[j]!.toNat ≤ 57) →
    rdLoopN b v e x = x * 10 ^ n + UInt64.ofNat (dval b v.toNat n) := by
  induction n with
  | zero =>
    intro v e x he _
    rw [rdLoopN_stop _ _ _ _ (by rw [UInt64.lt_iff_toNat_lt]; omega)]
    simp [dval]
  | succ n ih =>
    intro v e x he hd
    have hlt : v < e := by rw [UInt64.lt_iff_toNat_lt]; omega
    have hv1 : (v + 1).toNat = v.toNat + 1 := by
      rw [UInt64.toNat_add]; simp; have := e.toNat_lt; omega
    obtain ⟨d1, d2⟩ := hd v.toNat (Nat.le_refl _) (by omega)
    have hdig : (byteW b v - 48) &&& 255 = UInt64.ofNat (b[v.toNat]!.toNat - 48) := by
      apply UInt64.toNat_inj.mp
      have hbw : byteW b v = (b[v.toNat]!).toUInt64 := by
        simp only [byteW, Array.getD_eq_getD_getElem?, getElem!_def]
        cases b[v.toNat]? <;> rfl
      rw [hbw, UInt64.toNat_and, UInt64.toNat_sub_of_le _ _ (by
        rw [UInt64.le_iff_toNat_le]; simp; omega)]
      simp only [UInt8.toNat_toUInt64, UInt64.reduceToNat, UInt64.toNat_ofNat']
      rw [show (255 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
      omega
    rw [rdLoopN_step _ _ _ _ hlt, hdig, ih (v + 1) e _ (by omega) (fun j h1 h2 => hd j (by omega) h2),
      hv1, dval]
    simp only [UInt64.ofNat_add, UInt64.ofNat_mul, ofNat_ten_pow, UInt64.pow_succ]
    grind

theorem w8_mask_seven : ((0x0F0F0F0F0F0F0F0F : Word) <<< ((7 - UInt64.ofNat (8 - 1)) <<< 3)) =
    0x0F0F0F0F0F0F0F0F := by decide

/-- On a run of digits (`v ≤ e`), `read_nat` is the byte loop: the word steps compute the same. -/
theorem rdNatN_digits (b : Array UInt8) (v e : Word) (hve : v.toNat ≤ e.toNat)
    (hd : ∀ j, v.toNat ≤ j → j < e.toNat → ∃ h : j < b.size, 48 ≤ b[j] ∧ b[j] ≤ 57) :
    rdNatN b v e = if v + 18 < e then NONE else rdLoopN b v e 0 := by
  have hd' := digit_bang b _ _ hd
  unfold rdNatN
  split
  · rfl
  rename_i h18
  have h18' : e.toNat ≤ v.toNat + 18 := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at h18; simp at h18; omega
  have hloop := rdLoopN_dval b (e.toNat - v.toNat) v e 0 (by omega) hd'
  rw [UInt64.zero_mul, UInt64.zero_add] at hloop
  unfold rdNatF
  by_cases hL0 : e.toNat = v.toNat
  · have : e = v := UInt64.toNat_inj.mp hL0
    subst this
    have h1 : ¬ e - e - 1 < 8 := by simp only [UInt64.sub_self]; decide
    have h2 : ¬ (e - e - 1 < 16 ∧ 16 ≤ e) := fun h => absurd h.1 (by simp only [UInt64.sub_self]; decide)
    simp only [h1, h2, ↓reduceIte, ite_self]
  have hw : e - v - 1 = UInt64.ofNat (e.toNat - v.toNat - 1) := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _
      (UInt64.le_iff_toNat_le.mpr hve)]; simp; omega), UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hve)]
    simp only [UInt64.reduceToNat, UInt64.toNat_ofNat']
    have := e.toNat_lt; rw [Nat.mod_eq_of_lt (by omega)]
  rw [hw]
  split
  · rename_i hin
    have h8 : (e - 8).toNat = e.toNat - 8 := by
      rw [UInt64.toNat_sub_of_le _ _ hin.1]; rfl
    split
    · rename_i hlt
      have hL : e.toNat - v.toNat ≤ 8 := by
        rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat'] at hlt
        simp only [UInt64.reduceToNat] at hlt; rw [Nat.mod_eq_of_lt (by have := e.toNat_lt; omega)] at hlt
        omega
      have h8' : 8 ≤ e.toNat := UInt64.le_iff_toNat_le.mp hin.1
      rw [rdW1, h8, w1_digits b (e.toNat - 8) (e.toNat - v.toNat) (by omega) hL
        (fun k h1 h2 => hd' _ (by omega) (by omega)), hloop,
        show e.toNat - 8 + (8 - (e.toNat - v.toNat)) = v.toNat by omega]
    split
    · rename_i hge hlt
      have hL : 9 ≤ e.toNat - v.toNat ∧ e.toNat - v.toNat ≤ 16 := by
        rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat'] at hge hlt
        simp only [UInt64.reduceToNat] at hge hlt
        rw [Nat.mod_eq_of_lt (by have := e.toNat_lt; omega)] at hge hlt
        omega
      have h16' : 16 ≤ e.toNat := UInt64.le_iff_toNat_le.mp hlt.2
      have h16 : (e - 16).toNat = e.toNat - 16 := by
        rw [UInt64.toNat_sub_of_le _ _ hlt.2]; rfl
      have hsh : (15 : Word) - UInt64.ofNat (e.toNat - v.toNat - 1) =
          7 - UInt64.ofNat (e.toNat - v.toNat - 8 - 1) := by
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_sub_of_le _ _ (by
              rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; simp; omega),
            UInt64.toNat_sub_of_le _ _ (by
              rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; simp; omega)]
        simp only [UInt64.toNat_ofNat', UInt64.reduceToNat]
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
      rw [rdW2, h16, h8, hsh, w1_digits b (e.toNat - 16) (e.toNat - v.toNat - 8) (by omega) (by omega)
        (fun k h1 h2 => hd' _ (by omega) (by omega)), ← w8_mask_seven,
        w1_digits b (e.toNat - 8) 8 (by omega) (by omega) (fun k h1 h2 => hd' _ (by omega) (by omega)),
        hloop, show dval b v.toNat (e.toNat - v.toNat) = dval b v.toNat ((e.toNat - v.toNat - 8) + 8) by
          rw [show (e.toNat - v.toNat - 8) + 8 = e.toNat - v.toNat by omega], dval_add,
        show e.toNat - 16 + (8 - (e.toNat - v.toNat - 8)) = v.toNat by omega,
        show e.toNat - 8 + (8 - 8) = v.toNat + (e.toNat - v.toNat - 8) by omega,
        UInt64.ofNat_add, UInt64.ofNat_mul]
      rfl
    · rfl
  · rfl

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
@[no_expose, l_impl ConLeche.Frontend.scanNatList]
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

/-! ## Names: `str`, `num` -/

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

/-! ## The line -/

/-- A line's fields. -/
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

/-- The name and level record of the line whose `{` is at `i - 1`. -/
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
include hb

omit hb in
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

omit hb in
theorem readNatLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    step p (exec p n) readNatLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      r.retOr [0] = [rdLoopN b (s₀.loc 0) (s₀.loc 1) (s₀.loc 2)]; ⊤⦄ :=
  Triple.step_exec (readNatLoop_spec p b (n + 1) s₀)

omit hb in
include hprn in
theorem readNat_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (v e : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "read_nat" [v, e]
    ⦃fun r s' => s' = s₀ ∧ r = [rdNatN b v e]; ⊤⦄ := by
  rw [invoke_eq _ hprn]
  simp only [callFn, readNat]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, L.evalC_spec, L.evalE_spec, evalArgs, setLoc, readNatLoop_step_spec p b n]
    all_goals simp only [Cond.pval, Expr.pval, St.setLoc_loc, St.setLoc_mem, Locals.init,
      List.getD_cons_zero, List.getD_cons_succ, List.getD_nil, Cmp.eval, BinOp.eval, Mem.src8, Mem.len8, hm,
      Bool.and_eq_true, decide_eq_true_eq, Nat.reduceEqDiff, ↓reduceIte] at *
    all_goals subst_vars
    all_goals (try rw [rdNatN_short _ _ _ ‹¬v + 18 < e›])
    all_goals (try rw [rdNatF_out _ _ _ _ ‹_›])
    all_goals (try rw [rdNatF_far _ _ _ _ ‹_› ‹_› ‹_›])
    all_goals first
      | (simp only [rdNatN, rdNatF, rdW1, rdW2, swar8, NONE, Sig.retVal, Sig.retOr, *, ↓reduceIte,
          and_self]; done)
      | grind [Sig.retVal, Sig.retOr]
      | (obtain ⟨-, hb, hr⟩ := ‹_ ∧ ¬_ = Sig.brk ∧ _›
         rw [retVal_of_retOr _ ‹_› hb [0]]; exact hr)

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
        L.Scan.Leaves.numEnd_spec p hpd hpn b hb64 n, readNat_spec p b hprn n] <;> finish

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

end specs

end L.Front.Fields
