module

public import ConAgua.Arena.SlotGrow
public import ConAgua.L.PureEval

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
  (the node count of tier `t`), and the handle decoders `tierW`, `idxW`.
* **One evaluation lemma per accessor**: `evalE_tld` / `tld_eq` (pass both to `vcgen`, as
  `ld64`), `evalE_cnt` / `tcntM_eq`, `evalE_tierE`, `evalE_idxE`, and the pure forms
  `Expr.pval_tld`, `Expr.pval_cntE`, … (`lang_grind`); the frame lemmas `tfld_set64_ne`,
  `tcnt_set64_ne`, `tfld_setG`, ….

Proofs outside the store library state models and relations with `tfld` and `tcnt` and never
unfold them (`TRec.ad` stays folded). A layout change (one array per tier, lane `tierarr`)
changes `L/TRec.lean`, the definitions and lemma proofs here, and the store library.

The array and control-word ids below are the memory map's (`AREC` = `APP.arr`, …): each store
file's `abbrev` must agree, `StoreFieldsCheck.lean` checks it.
-/

open Std.WP

namespace L.Arena

open L

/-! ## Handle words -/

/-- The tier bit and the index of a handle word. -/
def tierW (h : Word) : Word := (h >>> 27) &&& 1
def idxW (h : Word) : Word := h &&& 134217727

/-! ## The stores -/

/-- `lit` (`REC`): kind (`0` nat, `1` string), pool offset, length, hash. -/
abbrev LIT : TRec := ⟨2, 4, 2⟩
@[simp] abbrev LIT.kind : Word := 0
@[simp] abbrev LIT.o : Word := 1
@[simp] abbrev LIT.l : Word := 2
@[simp] abbrev LIT.h : Word := 3
/-- `app` (`AREC`): the handle words of `f` and `a`. -/
abbrev APP : TRec := ⟨4, 2, 4⟩
@[simp] abbrev APP.f : Word := 0
@[simp] abbrev APP.a : Word := 1
/-- `succ` (`SREC`): the handle word of `u`. -/
abbrev SUCC : TRec := ⟨6, 1, 6⟩
@[simp] abbrev SUCC.u : Word := 0
/-- `zero` (`ZREC`): one dummy word. -/
abbrev ZERO : TRec := ⟨8, 1, 8⟩
/-- `max` (`MREC`): the handle words of `u` and `v`. -/
abbrev MAX : TRec := ⟨10, 2, 10⟩
@[simp] abbrev MAX.u : Word := 0
@[simp] abbrev MAX.v : Word := 1
/-- `imax` (`IREC`): the handle words of `u` and `v`. -/
abbrev IMAX : TRec := ⟨12, 2, 12⟩
@[simp] abbrev IMAX.u : Word := 0
@[simp] abbrev IMAX.v : Word := 1
/-- `param` (`PREC`): the name handle word `n`. -/
abbrev PARAM : TRec := ⟨14, 1, 14⟩
@[simp] abbrev PARAM.n : Word := 0
/-- `sort` (`SOREC`): the level handle word `u`. -/
abbrev SORT : TRec := ⟨16, 1, 16⟩
@[simp] abbrev SORT.u : Word := 0
/-- `const` (`CREC`): the handle words of the name `n` and the level list `us`. -/
abbrev CONST : TRec := ⟨18, 2, 18⟩
@[simp] abbrev CONST.n : Word := 0
@[simp] abbrev CONST.us : Word := 1
/-- `letE` (`LEREC`): the handle words of `ty`, `v` and `b`. -/
abbrev LET : TRec := ⟨20, 3, 20⟩
@[simp] abbrev LET.ty : Word := 0
@[simp] abbrev LET.v : Word := 1
@[simp] abbrev LET.b : Word := 2
/-- `bvar` (`BREC`): the index. -/
abbrev BVAR : TRec := ⟨22, 1, 22⟩
@[simp] abbrev BVAR.i : Word := 0
/-- `fvar` (`FVREC`): the index, the handle word of `ty`. -/
abbrev FVAR : TRec := ⟨25, 2, 26⟩
@[simp] abbrev FVAR.i : Word := 0
@[simp] abbrev FVAR.ty : Word := 1
/-- `lam` (`LAREC`): the handle words of `ty` and `b`. -/
abbrev LAM : TRec := ⟨27, 2, 28⟩
@[simp] abbrev LAM.ty : Word := 0
@[simp] abbrev LAM.b : Word := 1
/-- `forallE` (`FAREC`): the handle words of `ty` and `b`. -/
abbrev FORALL : TRec := ⟨29, 2, 30⟩
@[simp] abbrev FORALL.ty : Word := 0
@[simp] abbrev FORALL.b : Word := 1
/-- `proj` (`PJREC`): the name handle word `n`, the index `i`, the handle word of `e`. -/
abbrev PROJ : TRec := ⟨31, 3, 32⟩
@[simp] abbrev PROJ.n : Word := 0
@[simp] abbrev PROJ.i : Word := 1
@[simp] abbrev PROJ.e : Word := 2
/-- Names, `anonymous` (`NAREC`): one dummy word. -/
abbrev NANON : TRec := ⟨33, 1, 34⟩
/-- Names, `str` (`NSREC`): the prefix's handle word, pool offset, length, hash. -/
abbrev NSTR : TRec := ⟨35, 4, 36⟩
@[simp] abbrev NSTR.p : Word := 0
@[simp] abbrev NSTR.o : Word := 1
@[simp] abbrev NSTR.l : Word := 2
@[simp] abbrev NSTR.h : Word := 3
/-- Names, `num` (`NNREC`): the prefix's handle word, the number. -/
abbrev NNUM : TRec := ⟨37, 2, 38⟩
@[simp] abbrev NNUM.p : Word := 0
@[simp] abbrev NNUM.i : Word := 1
/-- Level lists (`LSREC`): pool offset, length, hash. -/
abbrev LVLS : TRec := ⟨39, 3, 40⟩
@[simp] abbrev LVLS.o : Word := 0
@[simp] abbrev LVLS.l : Word := 1
@[simp] abbrev LVLS.h : Word := 2

/-! ## The one-word columns (`R⟨t, i⟩`): derived words, level-parameter bits -/

/-- The derived word of an `app` / `lam` / `forallE` / `letE` / `proj` node (`ADER`, …). -/
abbrev APP_DER : TRec := ⟨42, 1, 4⟩
abbrev LAM_DER : TRec := ⟨43, 1, 28⟩
abbrev FORALL_DER : TRec := ⟨44, 1, 30⟩
abbrev LET_DER : TRec := ⟨45, 1, 20⟩
abbrev PROJ_DER : TRec := ⟨46, 1, 32⟩
/-- The level-parameter bit of a `succ` / `max` / `imax` level, a level list (`SHP`, …). -/
abbrev SUCC_HP : TRec := ⟨55, 1, 6⟩
abbrev MAX_HP : TRec := ⟨56, 1, 10⟩
abbrev IMAX_HP : TRec := ⟨57, 1, 12⟩
abbrev LS_HP : TRec := ⟨58, 1, 40⟩
/-- The level-parameter bit of a `sort` / `const` / `fvar` expression (`SOLP`, …). -/
abbrev SORT_LP : TRec := ⟨59, 1, 16⟩
abbrev CONST_LP : TRec := ⟨60, 1, 18⟩
abbrev FVAR_LP : TRec := ⟨61, 1, 26⟩

/-! ## The proof accessors -/

/-- Field `f` of node `i` of tier `t` (`0` out of bounds). -/
def tfld (m : Mem) (R : TRec) (t i f : Word) : Word := rdW (m.arr64 R.arr) (R.ad t i f)

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
  if (R.ad t i f).toNat < (m.arr64 R.arr).size then return tfld m R t i f else throw .oob

/-- The checked read of a node count. -/
def tcntM (R : TRec) (t : Word) : M Word := do
  let m := (← get).mem
  if (R.ca + t).toNat < (m.arr64 CTL).size then return tcnt m R t else throw .oob

/-! ## Evaluation -/

theorem evalE_adE (R : TRec) (t i : Expr) (f : Word) :
    evalE (R.adE t i f) = (do let j ← evalE i; let tv ← evalE t; pure (R.ad tv j f)) := by
  simp only [TRec.adE, TRec.ad]
  split <;> split <;>
    simp_all [evalE, BinOp.eval, bind_pure_comp, map_bind, Functor.map_map]

theorem tld_eq (R : TRec) (t i f : Word) : ld64 R.arr (R.ad t i f) = tld R t i f := by
  simp only [ld64, tld, tfld]
  congr 1; funext s
  split <;> simp_all [rdW]

theorem evalE_tld (R : TRec) (t i : Expr) (f : Word) :
    evalE (R.ld t i f) = (do let j ← evalE i; let tv ← evalE t; tld R tv j f) := by
  simp only [TRec.ld, evalE, evalE_adE, bind_assoc, pure_bind, tld_eq]

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

@[lang_grind =] theorem Expr.pval_tld (s : St) (R : TRec) (t i : Expr) (f : Word) :
    Expr.pval s (R.ld t i f) = tfld s.mem R (Expr.pval s t) (Expr.pval s i) f := by
  simp only [TRec.ld, Expr.pval, tfld, rd64, rdW, Array.getD_eq_getD_getElem?]
  congr 2
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

/-! ## Frames -/

/-- A field depends only on its record array. -/
theorem tfld_arr_eq {m m' : Mem} {R : TRec} (h : m.arr64 R.arr = m'.arr64 R.arr) (t i f : Word) :
    tfld m R t i f = tfld m' R t i f := by
  simp only [tfld, h]

/-- A node count depends only on `CTL`. -/
theorem tcnt_arr_eq {m m' : Mem} (R : TRec) (h : m.arr64 CTL = m'.arr64 CTL) (t : Word) :
    tcnt m R t = tcnt m' R t := by
  simp only [tcnt, h]

theorem tfld_set64_ne (m : Mem) (R : TRec) (a : ArrId) (k v t i f : Word) (h : a ≠ R.arr) :
    tfld (m.set64 a k v) R t i f = tfld m R t i f := by
  simp only [tfld, Mem.arr64_set64_ne _ _ _ _ _ (Ne.symm h)]

theorem tcnt_set64_ne (m : Mem) (R : TRec) (a : ArrId) (k v t : Word) (h : a ≠ CTL) :
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
example : tfld m APP t i APP.a = rdW (m.arr64 4) (i * 4 + t * 2 + 1) := rfl
example : tfld m APP t i APP.f = rdW (m.arr64 4) (i * 4 + t * 2) := rfl
example : tfld m BVAR t i BVAR.i = rdW (m.arr64 22) (i * 2 + t) := rfl
example : tcnt m APP t = rdW (m.arr64 1) (4 + t) := rfl
example : tfld m APP t i APP.a = rdW (m.arr64 4) (i * 4 + t * 2 + 1) := by simp [tfld, TRec.ad]
example : tfld m APP t i APP.f = rdW (m.arr64 4) (i * 4 + t * 2) := by simp [tfld, TRec.ad]
example : tfld m BVAR t i BVAR.i = rdW (m.arr64 22) (i * 2 + t) := by simp [tfld, TRec.ad]
end test
end L.Arena
