module

public import ConAgua.L.PureEval

@[expose] public section

/-!
# Records: proof support

A record access `R[i].f` is the word access `R.arr.u64[R.at i f]` (`Syntax.lean`, "Records"), so
the semantics and the compiler are those of word arrays. What is new is the vocabulary that keeps
the address arithmetic out of user proofs:

* `evalE_at`: `vcgen` evaluates the address to the named word `R.ad j f` (pass `evalE_at` next to
  `evalE`; `Record.at` is not unfolded by `vcgen`);
* `Mem.fld m R j f`: field `f` of record `j` (`0` out of bounds), the read a model is stated with;
  `fld_getElem` turns the `getElem` that `vcgen` leaves for a read into it;
* `fld_set64`: a field after a field store is the stored word or the old one, decided on the
  record numbers and field offsets (no address arithmetic), given that neither record's
  addresses wrap around (`Record.Ok`); `fld_set64_ne`, `fld_setG`, `fld_set8`: other arrays,
  globals and byte stores leave fields alone;
* `ad_lt`: the bounds check of a field access from a bound on the record number.

All of it is in `lang_grind`. Field offsets must be below the stride (`Field.off < R.stride`);
`grind` checks that for literal layouts.
-/

set_option experimental.vcgen true
open Std.WP
open scoped Lean.Order

namespace L

/-- The addresses of record `j` do not wrap around. -/
def Record.Ok (R : Record) (j : Word) : Prop := j.toNat * R.stride + R.stride < 2 ^ 64

attribute [lang_grind] Record.Ok

/-- Field `f` of record `j`, `0` out of bounds. -/
def Mem.fld (m : Mem) (R : Record) (j : Word) (f : Field) : Word :=
  (m.arr64 R.arr).getD (R.ad j f).toNat 0

theorem evalE_at (R : Record) (i : Expr) (f : Field) :
    evalE (R.at i f) = (do let j ← evalE i; pure (R.ad j f)) := by
  simp only [Record.at, evalE, Record.ad, BinOp.eval, bind_pure_comp]
  simp [Functor.map_map]

@[lang_grind =] theorem Expr.pval_at (s : St) (R : Record) (i : Expr) (f : Field) :
    Expr.pval s (R.at i f) = R.ad (Expr.pval s i) f := by
  simp [Record.at, Expr.pval, Record.ad, BinOp.eval]

/-- The address of a field, as a number, when the record's addresses do not wrap around. -/
theorem Record.ad_toNat (R : Record) (j : Word) (f : Field) (hj : R.Ok j) (hf : f.off < R.stride) :
    (R.ad j f).toNat = j.toNat * R.stride + f.off := by
  simp only [Record.Ok] at hj
  have hs : R.stride < 2 ^ 64 := by have := j.toNat_lt; omega
  have hfo : f.off < 2 ^ 64 := by omega
  simp only [Record.ad, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat_of_lt' hs,
    UInt64.toNat_ofNat_of_lt' hfo]
  rw [Nat.mod_eq_of_lt (by omega : j.toNat * R.stride < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]

/-- **Distinct fields or records have distinct addresses** (no wrap-around). -/
theorem Record.ad_inj (R : Record) {i j : Word} {f g : Field} (hi : R.Ok i) (hj : R.Ok j)
    (hf : f.off < R.stride) (hg : g.off < R.stride) (h : R.ad i f = R.ad j g) :
    i = j ∧ f.off = g.off := by
  have e := congrArg UInt64.toNat h
  rw [R.ad_toNat i f hi hf, R.ad_toNat j g hj hg] at e
  have hq : i.toNat = j.toNat := by
    have h1 := Nat.add_mul_div_right f.off i.toNat (show 0 < R.stride by omega)
    have h2 := Nat.add_mul_div_right g.off j.toNat (show 0 < R.stride by omega)
    rw [Nat.div_eq_of_lt hf, Nat.add_comm] at h1
    rw [Nat.div_eq_of_lt hg, Nat.add_comm] at h2
    rw [Nat.zero_add] at h1 h2
    rw [← h1, ← h2, e]
  refine ⟨UInt64.toNat_inj.mp hq, ?_⟩
  rw [hq] at e; omega

/-- A read of a field, as `vcgen` leaves it (`arr[addr]` with the bound), is `Mem.fld`. -/
theorem fld_getElem (m : Mem) (R : Record) (a : ArrId) (j : Word) (f : Field) (ha : a = R.arr)
    (h : (R.ad j f).toNat < (m.arr64 a).size) : (m.arr64 a)[(R.ad j f).toNat] = m.fld R j f := by
  subst ha; simp [Mem.fld, Array.getD, h]

grind_pattern [lang_grind] fld_getElem => (m.arr64 a)[(R.ad j f).toNat]

/-- **A field after a field store**: the stored word if it is the same record and field (and the
store was in bounds), else the old field. -/
theorem fld_set64 (m : Mem) (R : Record) (a : ArrId) (i j : Word) (f g : Field) (v : Word)
    (ha : a = R.arr) (hi : R.Ok i) (hj : R.Ok j) (hf : f.off < R.stride) (hg : g.off < R.stride) :
    (m.set64 a (R.ad i f) v).fld R j g =
      if i = j ∧ f.off = g.off ∧ (R.ad i f).toNat < (m.arr64 R.arr).size then v else m.fld R j g := by
  subst ha
  simp only [Mem.fld, Mem.set64, Mem.arr64, Array.getD_eq_getD_getElem?]
  by_cases ha : R.arr < m.words.size
  · simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, ha, ite_true]
    by_cases e : i = j ∧ f.off = g.off
    · obtain ⟨rfl, hfg⟩ := e
      have : R.ad i f = R.ad i g := by simp [Record.ad, hfg]
      rw [this]
      by_cases hb : (R.ad i g).toNat < (m.words[R.arr]).size <;>
        simp [hb, hfg, Array.getElem?_eq_getElem ha]
    · have hne : (R.ad i f).toNat ≠ (R.ad j g).toNat := fun h' =>
        e (R.ad_inj hi hj hf hg (UInt64.toNat_inj.mp h'))
      rw [ite_eq_right (fun h' => e ⟨h'.1, h'.2.1⟩)]
      simp [hne]
  · simp [Array.set!_eq_setIfInBounds, ha]

grind_pattern [lang_grind] fld_set64 => (m.set64 a (R.ad i f) v).fld R j g

/-- A store into another array leaves fields alone. -/
theorem fld_set64_ne (m : Mem) (R : Record) (a : ArrId) (k v j : Word) (g : Field) (h : a ≠ R.arr) :
    (m.set64 a k v).fld R j g = m.fld R j g := by
  simp only [Mem.fld, Mem.set64, Mem.arr64, Array.getD_eq_getD_getElem?]
  by_cases ha : a < m.words.size <;>
    simp [Array.set!_eq_setIfInBounds, ha, h]

grind_pattern [lang_grind] fld_set64_ne => (m.set64 a k v).fld R j g

@[lang_grind =] theorem fld_setG (m : Mem) (R : Record) (x : GVar) (v j : Word) (g : Field) :
    (m.setG x v).fld R j g = m.fld R j g := rfl

@[lang_grind =] theorem fld_set8 (m : Mem) (R : Record) (a : ArrId) (k v j : Word) (g : Field) :
    (m.set8 a k v).fld R j g = m.fld R j g := rfl

/-- Stores keep every word array's size. -/
@[lang_grind =] theorem Mem.size64_set64 (m : Mem) (a b : ArrId) (k v : Word) :
    ((m.set64 a k v).arr64 b).size = (m.arr64 b).size := by
  simp only [Mem.set64, Mem.arr64, Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds]
  by_cases h : a = b
  · subst h; by_cases ha : a < m.words.size <;> simp [ha]
  · simp [h]

/-- **The bound of a field access** from a bound `n` on the record number, with room for `n`
records. -/
theorem Record.ad_lt (R : Record) (m : Mem) (j : Word) (f : Field) (n : Nat) (hj : j.toNat < n)
    (hn : n * R.stride ≤ (m.arr64 R.arr).size) (hs : (m.arr64 R.arr).size < 2 ^ 64)
    (hf : f.off < R.stride) : (R.ad j f).toNat < (m.arr64 R.arr).size := by
  have hok : R.Ok j := by
    simp only [Record.Ok]
    have := Nat.mul_le_mul_right R.stride (show j.toNat + 1 ≤ n by omega)
    rw [Nat.succ_mul] at this; omega
  rw [R.ad_toNat j f hok hf]
  have := Nat.mul_le_mul_right R.stride (show j.toNat + 1 ≤ n by omega)
  rw [Nat.succ_mul] at this; omega

end L
