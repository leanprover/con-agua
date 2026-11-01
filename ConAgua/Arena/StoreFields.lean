module

public import ConAgua.Arena.SlotGrow
public import ConAgua.L.PureEval
public import ConAgua.L.TRec
import ConAgua.L.GrindAttr
import ConAgua.L.ErrSpec
import Std.Tactic.BVDecide.Normalize.BitVec

@[expose] public section

/-!
# The store records: one accessor per field, one evaluation lemma per accessor (lane tieracc)

Every node store of the arena keeps its records in a word array and its node counts in `CTL`
(`L/TRec.lean`). This file is the **only** place outside the store library that knows the
layout:

* **The stores** (`LIT`, `APP`, …, `LVLS`) and their one-word columns (`APP_DER`, …, `FVAR_LP`), as
  `L.TRec` values, with a constant per field (`APP.f`, `APP.a`, …). L code reads them as
  `APP⟨t, i⟩.f`, `APP⟦h⟧.a`, `APP⟨t⟩.count` (`L/Notation.lean`).
* **The proof accessors** `tfld m R t i f` (field `f` of node `i` of tier `t`) and `tcnt m R t`
  (the node count of tier `t`), and the handle words: `hdW`, `hdA`, `tagW`, `tierW`, `idxW`, `idxA` and their
  laws, proved once through `toNat` (the bridge to the twin's `Idx` is `Handle.lean`).
* **One evaluation lemma per accessor**: `evalE_tld` / `tld_eq` (pass both to `vcgen`, as
  `ld64`), `evalE_cnt` / `tcntM_eq`, `evalE_tierE`, `evalE_idxE`, `evalE_idxAE`, `evalE_tagE`, and the pure forms
  `Expr.pval_tld`, `Expr.pval_cntE`, … (`lang_grind`); the frame lemmas `tfld_set64_ne`,
  `tcnt_set64_ne`, `tfld_setG`, ….

Proofs outside the store library state models and relations with `tfld` and `tcnt` and never
unfold them (`TRec.ad` stays folded). The layout (one tiered array per store, lane
`tierswitch`: tier `t` of array `a` is `tierA a t`) lives in `L/TRec.lean`, the definitions and
lemma proofs here, and the store library.

The array and control-word ids below are the memory map's (`AREC` = `APP.arr`, …): each store
file's `abbrev` must agree, `StoreFieldsCheck.lean` checks it.
-/

open Std.WP

namespace L.Arena

open L

/-! ## Handle words

The two shapes of con-ron's handle word (`ConRon/Arena/Handle.lean`, task #133; `L/TRec.lean`,
"Handle words"): bit 31 the tier, bit 30 set for a WIDE word (an expression `app`, index bits
29…0), clear for a NARROW one (tag bits 29…26, index bits 25…0). -/

/-- The tier bit (con-ron's `Idx.tier`). -/
def tierW (h : Word) : Word := (h >>> 31) &&& 1
/-- The index of a narrow word, bit 30 kept (a wide word reads `2^30` or more). -/
def idxW (h : Word) : Word := h &&& 0x43ffffff
/-- The index of a wide word (an `app`): `(2^30 + h) mod 2^31` (a narrow word reads `2^30` or
more). The constant comes first: with `h + 2^30`, a definitional unfolding on a symbolic `h`
(`whnf` of the `UInt64` sum, then `Nat.add` by a literal) peels the literal into a `Nat.succ`
chain of length 2^30 (lane ronsync: `WhnfModels2E` above 16 GB). -/
def idxA (h : Word) : Word := ((0x40000000 : Word) + h) &&& 0x7fffffff
/-- The index of any word, con-ron's `Idx.idxNat` (`idxGE`). -/
def idxG (h : Word) : Word := h &&& ((0x3ffffff : Word) + ((h >>> 30) &&& 1) * 0x3c000000)
/-- The shape bit: `1` for a wide word (con-ron's `Idx.isWide`). -/
def wideW (h : Word) : Word := (h >>> 30) &&& 1
/-- The constructor tag (con-ron's `Idx.tag`): `4` for a wide word, bits 29…26 of a narrow one,
as `tagE` computes it. -/
def tagW (h : Word) : Word :=
  (((h >>> 26) &&& 15 : Word) + ((h >>> 30) &&& 1 : Word) * ((4 : Word) - ((h >>> 26) &&& 15 : Word)))

/-- The narrow handle word of node `i` of tier `t` of the constructor with tag `g`. -/
def hdW (g t i : Word) : Word := t * 0x80000000 + g * 0x4000000 + i

/-- The wide handle word of `app` node `i` of tier `t`. -/
def hdA (t i : Word) : Word := 0x40000000 + t * 0x80000000 + i

/-! ### Decoding as numbers -/

/-- A single bit of a number, as a mask. -/
theorem nat_and_two_pow (n k : Nat) : n &&& 2 ^ k = 2 ^ k * (n / 2 ^ k % 2) := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow]
  rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ k) with h | h
  · rw [h]; simp only [Nat.mul_zero, Nat.zero_testBit]
    by_cases hi : k = i
    · subst hi; simp [Nat.testBit, Nat.shiftRight_eq_div_pow, h]
    · simp [hi]
  · rw [h, Nat.mul_one, Nat.testBit_two_pow]
    by_cases hi : k = i
    · subst hi; simp [Nat.testBit, Nat.shiftRight_eq_div_pow, h]
    · simp [hi]

/-- Bit 31 of a word (the tier bit of a handle word). -/
theorem bit31_toNat (w : Word) : ((w >>> 31) &&& 1).toNat = w.toNat / 2 ^ 31 % 2 := by
  simp [UInt64.toNat_and, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]

theorem tierW_toNat' (w : Word) : (tierW w).toNat = w.toNat / 2 ^ 31 % 2 := bit31_toNat w

theorem wideW_toNat (w : Word) : (wideW w).toNat = w.toNat / 2 ^ 30 % 2 := by
  simp [wideW, UInt64.toNat_and, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow,
    Nat.and_one_is_mod]

theorem idxW_toNat (w : Word) : (idxW w).toNat = w.toNat % 2 ^ 26 + 2 ^ 30 * (w.toNat / 2 ^ 30 % 2) := by
  simp only [idxW, UInt64.toNat_and]
  rw [show (0x43ffffff : Word).toNat = 2 ^ 30 ||| (2 ^ 26 - 1) from rfl, Nat.and_or_distrib_left,
    nat_and_two_pow, Nat.and_two_pow_sub_one_eq_mod,
    ← Nat.two_pow_add_eq_or_of_lt (by omega : w.toNat % 2 ^ 26 < 2 ^ 30)]
  omega

/-- The index of a narrow word. -/
theorem idxW_toNat_narrow (w : Word) (hw : w.toNat / 2 ^ 30 % 2 = 0) :
    (idxW w).toNat = w.toNat % 2 ^ 26 := by
  rw [idxW_toNat, hw]; omega

/-- A wide word's narrow index is out of every narrow array's range. -/
theorem idxW_wide (w : Word) (hw : w.toNat / 2 ^ 30 % 2 = 1) : 2 ^ 30 ≤ (idxW w).toNat := by
  rw [idxW_toNat, hw]; omega

theorem idxG_toNat (w : Word) :
    (idxG w).toNat = if w.toNat / 2 ^ 30 % 2 = 1 then w.toNat % 2 ^ 30 else w.toNat % 2 ^ 26 := by
  have hb : ((w >>> 30) &&& 1).toNat = w.toNat / 2 ^ 30 % 2 := by
    simp [UInt64.toNat_and, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]
  unfold idxG
  generalize (w >>> 30) &&& 1 = b at *
  split
  · have : b = 1 := UInt64.toNat_inj.mp (by simp; omega)
    subst this
    rw [show ((0x3ffffff : Word) + 1 * 0x3c000000) = (1073741823 : Word) from rfl, UInt64.toNat_and,
      show (1073741823 : Word).toNat = 2 ^ 30 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  · have : b = 0 := UInt64.toNat_inj.mp (by simp; omega)
    subst this
    rw [show ((0x3ffffff : Word) + 0 * 0x3c000000) = (67108863 : Word) from rfl, UInt64.toNat_and,
      show (67108863 : Word).toNat = 2 ^ 26 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- On a narrow word the generic index is the narrow one. -/
theorem idxG_narrow (w : Word) (hw : w.toNat / 2 ^ 30 % 2 = 0) : idxG w = idxW w := by
  apply UInt64.toNat_inj.mp
  rw [idxG_toNat, idxW_toNat_narrow w hw, hw]; simp

/-- A narrow index below `2^30` is a narrow word's. -/
theorem narrow_of_idxW_lt (w : Word) (hc : (idxW w).toNat < 2 ^ 30) : w.toNat / 2 ^ 30 % 2 = 0 := by
  rw [idxW_toNat] at hc; omega

theorem idxA_toNat (w : Word) : (idxA w).toNat = (w.toNat + 2 ^ 30) % 2 ^ 31 := by
  simp only [idxA, UInt64.toNat_and]
  rw [show (0x7fffffff : Word).toNat = 2 ^ 31 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    UInt64.toNat_add]
  simp; omega

/-- The index of a wide word. -/
theorem idxA_toNat_wide (w : Word) (hw : w.toNat / 2 ^ 30 % 2 = 1) :
    (idxA w).toNat = w.toNat % 2 ^ 30 := by
  rw [idxA_toNat]; omega

/-- A narrow word's wide index is out of the `app` array's range. -/
theorem idxA_narrow (w : Word) (hw : w.toNat / 2 ^ 30 % 2 = 0) : 2 ^ 30 ≤ (idxA w).toNat := by
  rw [idxA_toNat]; omega

theorem tagW_toNat (h : Word) :
    (tagW h).toNat = if h.toNat / 2 ^ 30 % 2 = 1 then 4 else h.toNat / 2 ^ 26 % 16 := by
  have hw : ((h >>> 30) &&& 1).toNat = h.toNat / 2 ^ 30 % 2 := by
    simp [UInt64.toNat_and, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]
  have hf : ((h >>> 26) &&& 15).toNat = h.toNat / 2 ^ 26 % 16 := by
    simp only [UInt64.toNat_and, UInt64.toNat_shiftRight]
    rw [show (15 : Word).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    simp [Nat.shiftRight_eq_div_pow]
  unfold tagW
  generalize (h >>> 30) &&& 1 = w at *
  generalize (h >>> 26) &&& 15 = f at *
  split
  · have : w = 1 := UInt64.toNat_inj.mp (by simp; omega)
    subst this
    rw [UInt64.one_mul, UInt64.add_comm, UInt64.sub_add_cancel]; rfl
  · have : w = 0 := UInt64.toNat_inj.mp (by simp; omega)
    subst this; simp; exact hf

/-- Bits 30…26 of a word, the index of `tagE`'s table read. -/
theorem tagIx_toNat (h : Word) : ((h >>> 26) &&& 31).toNat = h.toNat / 2 ^ 26 % 32 := by
  simp only [UInt64.toNat_and, UInt64.toNat_shiftRight]
  rw [show (31 : Word).toNat = 2 ^ 5 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  simp [Nat.shiftRight_eq_div_pow]

/-- `tagTbl` is `tagW` on bits 30…26. -/
theorem tagTbl_getElem (n : Nat) (hn : n < tagTbl.length) :
    tagTbl[n].toNat = if n / 16 % 2 = 1 then 4 else n % 16 := by
  have key : ∀ n, (hn : n < tagTbl.length) →
      tagTbl[n].toNat = if n / 16 % 2 = 1 then 4 else n % 16 := by decide
  exact key n hn

/-- The table read of `tagE` is the tag. -/
theorem tagTbl_tag (h : Word) (hl : ((h >>> 26) &&& 31).toNat < tagTbl.length) :
    tagTbl[((h >>> 26) &&& 31).toNat].toUInt64 = tagW h := by
  apply UInt64.toNat_inj.mp
  rw [UInt8.toNat_toUInt64, tagTbl_getElem _ hl, tagW_toNat, tagIx_toNat]
  have e1 : h.toNat / 2 ^ 26 % 32 / 16 % 2 = h.toNat / 2 ^ 30 % 2 := by omega
  have e2 : h.toNat / 2 ^ 26 % 32 % 16 = h.toNat / 2 ^ 26 % 16 := by omega
  rw [e1, e2]

theorem tagIx_lt (h : Word) : ((h >>> 26) &&& 31).toNat < tagTbl.length := by
  rw [tagIx_toNat]; simp only [tagTbl, List.length_cons, List.length_nil]; omega

theorem ldc_tagTbl (h : Word) : ldc tagTbl ((h >>> 26) &&& 31) = pure (tagW h) := by
  unfold ldc; rw [dite_eq_left (tagIx_lt h), tagTbl_tag h (tagIx_lt h)]

theorem rdc_tagTbl (h : Word) : rdc tagTbl ((h >>> 26) &&& 31) = tagW h := by
  unfold rdc
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (tagIx_lt h), Option.getD_some,
    tagTbl_tag h (tagIx_lt h)]

theorem tagW_lt (h : Word) (_hh : h.toNat < 2 ^ 32) : (tagW h).toNat < 16 := by
  rw [tagW_toNat]; split <;> omega

/-- A word whose tag is not `app`'s is narrow. -/
theorem narrow_of_tagW (h : Word) (hg : tagW h ≠ 4) : h.toNat / 2 ^ 30 % 2 = 0 := by
  have e := tagW_toNat h
  rcases Nat.mod_two_eq_zero_or_one (h.toNat / 2 ^ 30) with h0 | h1
  · exact h0
  · simp only [h1, ↓reduceIte] at e
    exact absurd (UInt64.toNat_inj.mp (by rw [e]; simp)) hg

/-- The tag of a narrow word. -/
theorem tagW_toNat_narrow (h : Word) (hw : h.toNat / 2 ^ 30 % 2 = 0) :
    (tagW h).toNat = h.toNat / 2 ^ 26 % 16 := by
  rw [tagW_toNat, hw]; simp

theorem mask32_toNat (w : Word) : (w &&& 4294967295).toNat = w.toNat % 2 ^ 32 := by
  simp only [UInt64.toNat_and]
  rw [show (4294967295 : Word).toNat = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem tierW_le (h : Word) : tierW h ≤ 1 := by
  simp only [tierW]; exact UInt64.and_le_right

theorem tierW_lt (p : Word) : (tierW p).toNat ≤ 1 := by
  rw [tierW_toNat']; omega

theorem idxW_lt (h : Word) : idxW h < 0x44000000 := by
  rw [UInt64.lt_iff_toNat_lt, idxW_toNat]
  have := Nat.mod_lt (h.toNat / 2 ^ 30) (show 2 > 0 by decide)
  have : (0x44000000 : Word).toNat = 2 ^ 30 + 2 ^ 26 := rfl
  omega

theorem idxA_lt (h : Word) : idxA h < 0x80000000 := by
  rw [UInt64.lt_iff_toNat_lt, idxA_toNat]
  have : (0x80000000 : Word).toNat = 2 ^ 31 := rfl
  omega

theorem idxG_lt (h : Word) : idxG h < 0x40000000 := by
  rw [UInt64.lt_iff_toNat_lt, idxG_toNat]
  have : (0x40000000 : Word).toNat = 2 ^ 30 := rfl
  split <;> omega

theorem mask_lt (w : Word) : (w &&& 4294967295).toNat < 2 ^ 32 := by
  rw [mask32_toNat]; omega

theorem bit31_or (f a : Word) :
    (((f ||| a) >>> 31) &&& 1 = 0) ↔ ((f >>> 31) &&& 1 = 0 ∧ (a >>> 31) &&& 1 = 0) := by
  have h : ∀ x : Word, ((x >>> 31) &&& 1 = 0) ↔ x.toNat.testBit 31 = false := by
    intro x
    rw [← UInt64.toNat_inj, bit31_toNat, Nat.testBit_eq_decide_div_mod_eq]
    simp
  rw [h, h, h, UInt64.toNat_or, Nat.testBit_or]; simp

/-! ### The laws of `hdW` (narrow) and `hdA` (wide) -/

section hdW
variable (g t i : Word) (hg : g.toNat < 16) (ht : t ≤ 1) (hi : i.toNat < 2 ^ 26)
include hg ht hi

theorem hdW_toNat : (hdW g t i).toNat = t.toNat * 2147483648 + g.toNat * 67108864 + i.toNat := by
  have ht' : t.toNat ≤ 1 := ht
  simp only [hdW, UInt64.toNat_add, UInt64.toNat_mul]
  simp; omega

theorem hdW_lt : (hdW g t i).toNat < 2 ^ 32 := by
  have ht' : t.toNat ≤ 1 := ht
  rw [hdW_toNat g t i hg ht hi]; omega

theorem hdW_narrow : (hdW g t i).toNat / 2 ^ 30 % 2 = 0 := by
  have ht' : t.toNat ≤ 1 := ht
  rw [hdW_toNat g t i hg ht hi]; omega

theorem hdW_tag : tagW (hdW g t i) = g := by
  have ht' : t.toNat ≤ 1 := ht
  apply UInt64.toNat_inj.mp
  rw [tagW_toNat_narrow _ (hdW_narrow g t i hg ht hi), hdW_toNat g t i hg ht hi]; omega

theorem hdW_tier : tierW (hdW g t i) = t := by
  have ht' : t.toNat ≤ 1 := ht
  apply UInt64.toNat_inj.mp; rw [tierW_toNat', hdW_toNat g t i hg ht hi]; omega

theorem hdW_idx : idxW (hdW g t i) = i := by
  have ht' : t.toNat ≤ 1 := ht
  apply UInt64.toNat_inj.mp
  rw [idxW_toNat_narrow _ (hdW_narrow g t i hg ht hi), hdW_toNat g t i hg ht hi]; omega

end hdW

section hdA
variable (t i : Word) (ht : t ≤ 1) (hi : i.toNat < 2 ^ 30)
include ht hi

theorem hdA_toNat : (hdA t i).toNat = t.toNat * 2147483648 + 1073741824 + i.toNat := by
  have ht' : t.toNat ≤ 1 := ht
  simp only [hdA, UInt64.toNat_add, UInt64.toNat_mul]
  simp; omega

theorem hdA_lt : (hdA t i).toNat < 2 ^ 32 := by
  have ht' : t.toNat ≤ 1 := ht
  rw [hdA_toNat t i ht hi]; omega

theorem hdA_wide : (hdA t i).toNat / 2 ^ 30 % 2 = 1 := by
  have ht' : t.toNat ≤ 1 := ht
  rw [hdA_toNat t i ht hi]; omega

theorem hdA_tag : tagW (hdA t i) = 4 := by
  apply UInt64.toNat_inj.mp
  rw [tagW_toNat, hdA_wide t i ht hi]; simp

theorem hdA_tier : tierW (hdA t i) = t := by
  have ht' : t.toNat ≤ 1 := ht
  apply UInt64.toNat_inj.mp; rw [tierW_toNat', hdA_toNat t i ht hi]; omega

theorem hdA_idx : idxA (hdA t i) = i := by
  have ht' : t.toNat ≤ 1 := ht
  apply UInt64.toNat_inj.mp
  rw [idxA_toNat, hdA_toNat t i ht hi]; omega

end hdA

/-! ## The stores -/

/-- `lit` (`REC`): kind (`0` nat, `1` string), pool offset, length, hash. -/
abbrev LIT : TRec := ⟨2, 4, 2, 0⟩
@[simp] abbrev LIT.kind : Word := 0
@[simp] abbrev LIT.o : Word := 1
@[simp] abbrev LIT.l : Word := 2
@[simp] abbrev LIT.h : Word := 3
/-- `app` (`AREC`): the handle words of `f` and `a`, packed in one word. -/
abbrev APP : TRec := ⟨4, 1, 4, 1⟩
@[simp] abbrev APP.f : Word := 0
@[simp] abbrev APP.a : Word := 1
/-- `succ` (`SREC`): the handle word of `u`. -/
abbrev SUCC : TRec := ⟨6, 1, 6, 0⟩
@[simp] abbrev SUCC.u : Word := 0
/-- `zero` (`ZREC`): one dummy word. -/
abbrev ZERO : TRec := ⟨8, 1, 8, 0⟩
/-- `max` (`MREC`): the handle words of `u` and `v`, packed in one word. -/
abbrev MAX : TRec := ⟨10, 1, 10, 1⟩
@[simp] abbrev MAX.u : Word := 0
@[simp] abbrev MAX.v : Word := 1
/-- `imax` (`IREC`): the handle words of `u` and `v`, packed in one word. -/
abbrev IMAX : TRec := ⟨12, 1, 12, 1⟩
@[simp] abbrev IMAX.u : Word := 0
@[simp] abbrev IMAX.v : Word := 1
/-- `param` (`PREC`): the name handle word `n`. -/
abbrev PARAM : TRec := ⟨14, 1, 14, 0⟩
@[simp] abbrev PARAM.n : Word := 0
/-- `sort` (`SOREC`): the level handle word `u`. -/
abbrev SORT : TRec := ⟨16, 1, 16, 0⟩
@[simp] abbrev SORT.u : Word := 0
/-- `const` (`CREC`): the handle words of the name `n` and the level list `us`, packed in one
word. -/
abbrev CONST : TRec := ⟨18, 1, 18, 1⟩
@[simp] abbrev CONST.n : Word := 0
@[simp] abbrev CONST.us : Word := 1
/-- `letE` (`LEREC`): the handle words of `ty`, `v` and `b`: `ty` and `v` packed in word `0`,
`b` in word `1`. -/
abbrev LET : TRec := ⟨20, 2, 20, 1⟩
@[simp] abbrev LET.ty : Word := 0
@[simp] abbrev LET.v : Word := 1
@[simp] abbrev LET.b : Word := 2
/-- `bvar` (`BREC`): the index. -/
abbrev BVAR : TRec := ⟨22, 1, 22, 0⟩
@[simp] abbrev BVAR.i : Word := 0
/-- `fvar` (`FVREC`): the index, the handle word of `ty`. -/
abbrev FVAR : TRec := ⟨25, 2, 26, 0⟩
@[simp] abbrev FVAR.i : Word := 0
@[simp] abbrev FVAR.ty : Word := 1
/-- `lam` (`LAREC`): the handle words of `ty` and `b`, packed in one word. -/
abbrev LAM : TRec := ⟨27, 1, 28, 1⟩
@[simp] abbrev LAM.ty : Word := 0
@[simp] abbrev LAM.b : Word := 1
/-- `forallE` (`FAREC`): the handle words of `ty` and `b`, packed in one word. -/
abbrev FORALL : TRec := ⟨29, 1, 30, 1⟩
@[simp] abbrev FORALL.ty : Word := 0
@[simp] abbrev FORALL.b : Word := 1
/-- `proj` (`PJREC`): the name handle word `n`, the index `i`, the handle word of `e`: `n` and
`e` packed in word `0`, `i` in word `1`. -/
abbrev PROJ : TRec := ⟨31, 2, 32, 2⟩
@[simp] abbrev PROJ.n : Word := 0
@[simp] abbrev PROJ.i : Word := 1
@[simp] abbrev PROJ.e : Word := 2
/-- Names, `anonymous` (`NAREC`): one dummy word. -/
abbrev NANON : TRec := ⟨33, 1, 34, 0⟩
/-- Names, `str` (`NSREC`): the prefix's handle word, pool offset, length, hash. -/
abbrev NSTR : TRec := ⟨35, 4, 36, 0⟩
@[simp] abbrev NSTR.p : Word := 0
@[simp] abbrev NSTR.o : Word := 1
@[simp] abbrev NSTR.l : Word := 2
@[simp] abbrev NSTR.h : Word := 3
/-- Names, `num` (`NNREC`): the prefix's handle word, the number. -/
abbrev NNUM : TRec := ⟨37, 2, 38, 0⟩
@[simp] abbrev NNUM.p : Word := 0
@[simp] abbrev NNUM.i : Word := 1
/-- Level lists (`LSREC`): pool offset, length, hash. -/
abbrev LVLS : TRec := ⟨39, 3, 40, 0⟩
@[simp] abbrev LVLS.o : Word := 0
@[simp] abbrev LVLS.l : Word := 1
@[simp] abbrev LVLS.h : Word := 2

/-! ## The one-word columns (`R⟨t, i⟩`): derived words, level-parameter bits -/

/-- The derived word of an `app` / `lam` / `forallE` / `letE` / `proj` node (`ADER`, …). -/
abbrev APP_DER : TRec := ⟨42, 1, 4, 0⟩
abbrev LAM_DER : TRec := ⟨43, 1, 28, 0⟩
abbrev FORALL_DER : TRec := ⟨44, 1, 30, 0⟩
abbrev LET_DER : TRec := ⟨45, 1, 20, 0⟩
abbrev PROJ_DER : TRec := ⟨46, 1, 32, 0⟩
/-- The level-parameter bit of a `succ` / `max` / `imax` level, a level list (`SHP`, …). -/
abbrev SUCC_HP : TRec := ⟨55, 1, 6, 0⟩
abbrev MAX_HP : TRec := ⟨56, 1, 10, 0⟩
abbrev IMAX_HP : TRec := ⟨57, 1, 12, 0⟩
abbrev LS_HP : TRec := ⟨58, 1, 40, 0⟩
/-- The level-parameter bit of a `sort` / `const` / `fvar` expression (`SOLP`, …). -/
abbrev SORT_LP : TRec := ⟨59, 1, 16, 0⟩
abbrev CONST_LP : TRec := ⟨60, 1, 18, 0⟩
abbrev FVAR_LP : TRec := ⟨61, 1, 26, 0⟩

/-! ## The proof accessors -/

/-- Field `f` of node `i` of tier `t` (`0` out of bounds): its half of the record word for a
packed field (`TRec.ex`). -/
def tfld (m : Mem) (R : TRec) (t i f : Word) : Word := R.ex f (rdW (m.arr64 (tierA R.arr t)) (R.ad i f))

@[simp] theorem TRec.ex_zero (R : TRec) (f : Word) : R.ex f 0 = 0 := by
  unfold TRec.ex
  by_cases h1 : R.hi = 0 <;> by_cases h2 : f = 0 <;> by_cases h3 : f = R.hi <;> simp [h1, h2, h3]

/-- An unpacked record's field is its word. -/
theorem tfld_hi0 (m : Mem) (R : TRec) (h : R.hi = 0) (t i f : Word) :
    tfld m R t i f = rdW (m.arr64 (tierA R.arr t)) (R.ad i f) := by
  simp [tfld, TRec.ex, h]

/-- The node count of tier `t`. -/
def tcnt (m : Mem) (R : TRec) (t : Word) : Word := rdW (m.arr64 CTL) (R.ca + t)

/-- The node count of tier `t` of the name table with tag `g` (`0` anonymous, `1` str, else
num): what L reads as `c := NANON⟨t⟩.count; if g == 1 { c := NSTR⟨t⟩.count }; if g == 2 { c :=
NNUM⟨t⟩.count }`. -/
def nameCnt (m : Mem) (g t : Word) : Word :=
  if g = 0 then tcnt m NANON t else if g = 1 then tcnt m NSTR t else tcnt m NNUM t

/-- The checked read of a field, as `vcgen` sees it after `evalE_tld`: `oob` out of bounds. -/
def tld (R : TRec) (t i f : Word) : M Word := do
  let m := (← get).mem
  if (R.ad i f).toNat < (m.arr64 (tierA R.arr t)).size then return tfld m R t i f else throw .oob

/-- The checked read of a node count. -/
def tcntM (R : TRec) (t : Word) : M Word := do
  let m := (← get).mem
  if (R.ca + t).toNat < (m.arr64 CTL).size then return tcnt m R t else throw .oob

/-! ## Evaluation -/

theorem evalE_adE (R : TRec) (i : Expr) (f : Word) :
    evalE (R.adE i f) = (do let j ← evalE i; pure (R.ad j f)) := by
  simp only [TRec.adE, TRec.ad]
  split <;> split <;>
    simp_all [evalE, BinOp.eval, bind_pure_comp, Functor.map_map]

theorem tld_eq (R : TRec) (t i f : Word) :
    (do let x ← ld64 (tierA R.arr t) (R.ad i f); pure (R.ex f x)) = tld R t i f := by
  simp only [ld64, tld, tfld, bind_assoc]
  congr 1; funext s
  split
  · simp_all [rdW]
  · rfl

theorem evalE_exE (R : TRec) (f : Word) (e : Expr) :
    evalE (R.exE f e) = (do let x ← evalE e; pure (R.ex f x)) := by
  unfold TRec.exE TRec.ex
  by_cases h1 : R.hi = 0 <;> by_cases h2 : f = 0 <;> by_cases h3 : f = R.hi <;>
    simp [h1, h2, h3, evalE, BinOp.eval, bind_pure_comp]

theorem pval_exE (s : St) (R : TRec) (f : Word) (e : Expr) :
    Expr.pval s (R.exE f e) = R.ex f (Expr.pval s e) := by
  unfold TRec.exE TRec.ex
  by_cases h1 : R.hi = 0 <;> by_cases h2 : f = 0 <;> by_cases h3 : f = R.hi <;>
    simp [h1, h2, h3, Expr.pval, BinOp.eval]

/-- The tier expression a load passes reads as the tier, up to the mask a tiered access applies. -/
theorem evalE_tierX_bind {β : Type} (t : Expr) (a : ArrId) (K : TieredArray → M β) :
    (do let u ← evalE (TRec.tierX t); K (tierA a u)) = (do let u ← evalE t; K (tierA a u)) := by
  unfold TRec.tierX
  split
  · simp only [evalE, BinOp.eval, bind_assoc, pure_bind, tierA_and_one]
  · rfl

theorem pval_tierX (s : St) (t : Expr) (a : ArrId) :
    tierA a (Expr.pval s (TRec.tierX t)) = tierA a (Expr.pval s t) := by
  unfold TRec.tierX
  split
  · simp only [Expr.pval, BinOp.eval, tierA_and_one]
  · rfl

/-- A packed field's half (`Expr.ld32h`) is its extraction `TRec.ex`. -/
theorem TRec.half32b_ex (R : TRec) (f w : Word) (h : R.packed f) : half32b (decide (f = R.hi)) w = R.ex f w := by
  obtain ⟨h1, h2 | h2⟩ := h
  · subst h2
    have : (0 : Word) ≠ R.hi := fun e => h1 e.symm
    simp [half32b, TRec.ex, h1, this]
  · subst h2
    by_cases h0 : R.hi = 0
    · exact absurd h0 h1
    · simp [half32b, TRec.ex, h0]

/-- Any other field is its word. -/
theorem TRec.ex_of_not_packed (R : TRec) (f w : Word) (h : ¬ R.packed f) : R.ex f w = w := by
  unfold TRec.ex TRec.packed at *
  by_cases h1 : R.hi = 0
  · simp [h1]
  · have : ¬ (f = 0 ∨ f = R.hi) := fun h' => h ⟨h1, h'⟩
    simp only [not_or] at this
    simp [h1, this.1, this.2]

/-- The load of a field, as the word load and the extraction (`TRec.ex`). -/
theorem evalE_ld_ex (R : TRec) (t i : Expr) (f : Word) :
    evalE (R.ld t i f) = evalE (R.exE f (.ld64t R.arr (TRec.tierX t) (R.adE i f))) := by
  rw [evalE_exE]
  unfold TRec.ld
  split
  · rename_i hp
    simp only [evalE, bind_assoc, TRec.half32b_ex R f _ hp]
  · rename_i hp
    simp only [TRec.ex_of_not_packed R f _ hp, bind_pure]

theorem evalE_tld (R : TRec) (t i : Expr) (f : Word) :
    evalE (R.ld t i f) = (do let tv ← evalE t; let j ← evalE i; tld R tv j f) := by
  rw [evalE_ld_ex]
  simp only [evalE_exE, evalE, bind_assoc]
  rw [evalE_tierX_bind t R.arr (fun A => do let j ← evalE (R.adE i f); let x ← ld64 A j; pure (R.ex f x))]
  simp only [evalE_adE, bind_assoc, pure_bind, tld_eq]

theorem evalE_cnt (R : TRec) (t : Expr) :
    evalE (R.cntE t) = (do let tv ← evalE t; tcntM R tv) := by
  simp only [TRec.cntE, evalE, BinOp.eval, bind_assoc, pure_bind, tcntM, ld64, tcnt, TRec.ctl]
  congr 1; funext tv; congr 1; funext s
  split
  · rename_i h; simp only [rdW, CTL]; rw [Array.getElem?_eq_getElem h]; rfl
  · rfl

theorem evalE_tierE (h : Expr) : evalE (tierE h) = (do let x ← evalE h; pure (tierW x)) := by
  simp [tierE, evalE, BinOp.eval, tierW, bind_pure_comp, Functor.map_map]

theorem evalE_idxE (h : Expr) : evalE (idxE h) = (do let x ← evalE h; pure (idxW x)) := by
  simp [idxE, evalE, BinOp.eval, idxW, bind_pure_comp]

theorem evalE_idxAE (h : Expr) : evalE (idxAE h) = (do let x ← evalE h; pure (idxA x)) := by
  simp [idxAE, evalE, BinOp.eval, idxA, bind_pure_comp]

/-- `idxGE`'s value: `idxG` with the operands in code-generator order. -/
theorem idxG_eq (h : Word) : (((h >>> 30) &&& 1) * 0x3c000000 + 0x3ffffff) &&& h = idxG h := by
  rw [UInt64.and_comm, UInt64.add_comm]; rfl

/-- `idxGE` reads `h` twice; an expression's value does not depend on how often it is read
(`evalE_spec`: it leaves the state alone). -/
theorem evalE_idxGE (h : Expr) : evalE (idxGE h) = (do let x ← evalE h; pure (idxG x)) := by
  apply StateT.ext; intro s
  cases hr : (evalE h).run s with
  | error err =>
    simp only [idxGE, evalE, StateT.run_bind, hr]; rfl
  | ok p =>
    obtain ⟨v, s'⟩ := p
    obtain ⟨hs, -⟩ := M.of_run' (P := fun t => t = s) rfl hr (evalE_spec h s)
    subst hs
    simp [idxGE, evalE, StateT.run_bind, hr, BinOp.eval]
    simp only [bind, Except.bind, hr, Functor.map, Except.map, idxG_eq]

theorem evalE_tagE (h : Expr) : evalE (tagE h) = (do let x ← evalE h; pure (tagW x)) := by
  simp only [tagE, evalE, BinOp.eval, bind_assoc, pure_bind, ldc_tagTbl]

theorem pval_ld_ex (s : St) (R : TRec) (t i : Expr) (f : Word) :
    Expr.pval s (R.ld t i f) = Expr.pval s (R.exE f (.ld64t R.arr (TRec.tierX t) (R.adE i f))) := by
  rw [pval_exE]
  unfold TRec.ld
  split
  · rename_i hp; simp only [Expr.pval, TRec.half32b_ex R f _ hp]
  · rename_i hp; simp only [TRec.ex_of_not_packed R f _ hp]

@[lang_grind =] theorem Expr.pval_tld (s : St) (R : TRec) (t i : Expr) (f : Word) :
    Expr.pval s (R.ld t i f) = tfld s.mem R (Expr.pval s t) (Expr.pval s i) f := by
  rw [pval_ld_ex]
  simp only [pval_exE, Expr.pval, tfld, rd64, rdW, Array.getD_eq_getD_getElem?, pval_tierX]
  congr 3
  simp only [TRec.adE, TRec.ad]
  split <;> split <;> simp_all [Expr.pval, BinOp.eval]

@[lang_grind =] theorem Expr.pval_cntE (s : St) (R : TRec) (t : Expr) :
    Expr.pval s (R.cntE t) = tcnt s.mem R (Expr.pval s t) := by
  simp [TRec.cntE, Expr.pval, tcnt, rd64, rdW, Array.getD_eq_getD_getElem?, BinOp.eval, TRec.ctl]

@[lang_grind =] theorem Expr.pval_tierE (s : St) (h : Expr) :
    Expr.pval s (tierE h) = tierW (Expr.pval s h) := by
  simp [tierE, Expr.pval, BinOp.eval, tierW]

@[lang_grind =] theorem Expr.pval_idxE (s : St) (h : Expr) :
    Expr.pval s (idxE h) = idxW (Expr.pval s h) := by
  simp [idxE, Expr.pval, BinOp.eval, idxW]

@[lang_grind =] theorem Expr.pval_idxAE (s : St) (h : Expr) :
    Expr.pval s (idxAE h) = idxA (Expr.pval s h) := by
  simp [idxAE, Expr.pval, BinOp.eval, idxA]

@[lang_grind =] theorem Expr.pval_idxGE (s : St) (h : Expr) :
    Expr.pval s (idxGE h) = idxG (Expr.pval s h) := by
  simp only [idxGE, Expr.pval, BinOp.eval, idxG_eq]

@[lang_grind =] theorem Expr.pval_tagE (s : St) (h : Expr) :
    Expr.pval s (tagE h) = tagW (Expr.pval s h) := by
  simp only [tagE, Expr.pval, BinOp.eval, rdc_tagTbl]

/-! ## Frames -/

/-- A field depends only on its record arrays (both tiers). -/
theorem tfld_arr_eq {m m' : Mem} {R : TRec} (h : m.arr64 R.arr = m'.arr64 R.arr)
    (h' : m.arr64 (tier1 R.arr) = m'.arr64 (tier1 R.arr)) (t i f : Word) :
    tfld m R t i f = tfld m' R t i f := by
  simp only [tfld]
  rcases tierA_eq_or R.arr t with e | e <;> rw [e] <;> simp only [h, h']

/-- A node count depends only on `CTL`. -/
theorem tcnt_arr_eq {m m' : Mem} (R : TRec) (h : m.arr64 CTL = m'.arr64 CTL) (t : Word) :
    tcnt m R t = tcnt m' R t := by
  simp only [tcnt, h]

theorem tfld_set64_ne (m : Mem) (R : TRec) (a : TieredArray) (k v t i f : Word) (h : a ≠ R.arr)
    (h' : a ≠ tier1 R.arr) :
    tfld (m.set64 a k v) R t i f = tfld m R t i f := by
  simp only [tfld]
  rcases tierA_eq_or R.arr t with e | e <;> rw [e] <;>
    simp only [Mem.arr64_set64_ne _ _ _ _ _ (Ne.symm h), Mem.arr64_set64_ne _ _ _ _ _ (Ne.symm h')]

theorem tcnt_set64_ne (m : Mem) (R : TRec) (a : TieredArray) (k v t : Word) (h : a ≠ CTL) :
    tcnt (m.set64 a k v) R t = tcnt m R t := by
  simp only [tcnt, Mem.arr64_set64_ne _ _ _ _ _ (Ne.symm h)]

@[lang_grind =] theorem tfld_setG (m : Mem) (R : TRec) (x : GVar) (v t i f : Word) :
    tfld (m.setG x v) R t i f = tfld m R t i f := rfl

@[lang_grind =] theorem tcnt_setG (m : Mem) (R : TRec) (x : GVar) (v t : Word) :
    tcnt (m.setG x v) R t = tcnt m R t := rfl

@[lang_grind =] theorem tfld_set8 (m : Mem) (R : TRec) (a : ArrId) (k v t i f : Word) :
    tfld (m.set8 a k v) R t i f = tfld m R t i f := rfl

@[lang_grind =] theorem tcnt_set8 (m : Mem) (R : TRec) (a : ArrId) (k v t : Word) :
    tcnt (m.set8 a k v) R t = tcnt m R t := rfl

end L.Arena

namespace L.Arena
section test
variable (m : Mem) (t i : Word)
example : tfld m APP t i APP.a = rdW (m.arr64 (tierA 4 t)) i >>> 32 := rfl
example : tfld m APP t i APP.f = rdW (m.arr64 (tierA 4 t)) i &&& 4294967295 := rfl
example : tfld m LET t i LET.b = rdW (m.arr64 (tierA 20 t)) (i * 2 + 1) := rfl
example : tfld m PROJ t i PROJ.i = rdW (m.arr64 (tierA 31 t)) (i * 2 + 1) := rfl
example : tfld m PROJ t i PROJ.e = rdW (m.arr64 (tierA 31 t)) (i * 2) >>> 32 := rfl
example : tfld m BVAR t i BVAR.i = rdW (m.arr64 (tierA 22 t)) i := rfl
example : tcnt m APP t = rdW (m.arr64 CTL) (4 + t) := rfl
end test
end L.Arena
