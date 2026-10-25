module

public import ConAgua.L.Syntax

public section

/-!
# Tiered store records (surface syntax)

A node store of the arena (`Arena/StoreFields.lean` lists them) keeps, per tier, an array of
records of `w` words, and the node count of each tier in a control word. Code outside the store
library reaches them only through the accessors below, written in L as

* `R⟨t, i⟩.f`: field `f` of node `i` of tier `t` (`R⟨t, i⟩` for a one-word column);
* `R⟦h⟧.f`, `R⟦h⟧`: the same for the node a handle word `h` names (tier bit 27, index the low 27
  bits);
* `R⟨t⟩.count`: the node count of tier `t`;
* `R⟨t, i⟩.f := e`: a field store (the store library's pushes only).

They expand (`Notation.lean`) to the builders `TRec.ld`, `TRec.st`, `TRec.cntE` of this file,
which fix the **layout** in one place: one tiered word array per store (lane tierswitch; tier
`t` of array `a` is array `L.tierA a t`), node `i` of tier `t` at
`arr⟨t⟩[i * w ..]`, the count at `CTL[ca + t]`. Proofs see the named words `TRec.ad`, `tfld`, `tcnt`.

**Packed records** (lane memlay, `hi ≠ 0`): field `0` and field `hi` (two handle words, below
`2^32`) share word `0` of the record, field `0` in bits 0–31 and field `hi` in bits 32–63; the
other fields `f` follow in words `1 ‥` (`f`, or `f - 1` above `hi`), whole. A field's word is
`TRec.wd`, its address `TRec.ad`; a load extracts the half (`TRec.ex`: `x & 0xFFFFFFFF`,
`x >> 32`). Records are written once, whole, by the store library's pushes (the combined word
`f₀ | f_hi << 32`); `TRec.st` stores a whole word (unpacked fields only).
-/

namespace L

/-- A tiered store record: the record array, the words per node `w`, the control-word
index `ca` of tier 0's node count (tier 1's is `ca + 1`), and the packing: `hi = 0` none, else
field `hi` is the high half of word `0` (field `0` its low half). -/
structure TRec where
  arr : ArrId
  w : Word
  ca : Word
  hi : Word
  deriving Repr, DecidableEq, Inhabited

/-- The control-word array (`CTL`). -/
@[expose, reducible] def TRec.ctl : ArrId := 1

/-- The word of the record that holds field `f`: `f` unpacked; packed, `0` for fields `0` and
`hi`, else `f` below `hi` and `f - 1` above. -/
@[expose] def TRec.wd (R : TRec) (f : Word) : Word :=
  if f = 0 ∨ R.hi = 0 then f else if f = R.hi then 0 else if f < R.hi then f else f - 1

@[simp] theorem TRec.wd_zero (R : TRec) : R.wd 0 = 0 := by simp [TRec.wd]

/-- The word address of field `f` of node `j` in its tier's array: `j * w + wd f`, written
without `j * 1` and `+ 0` (as the address expression `adE` computes it). -/
@[expose] def TRec.ad (R : TRec) (j f : Word) : Word :=
  let b := if R.w = 1 then j else j * R.w
  if R.wd f = 0 then b else b + R.wd f

/-- The address expression of field `f` of node `i` (in its tier's array). -/
@[expose] def TRec.adE (R : TRec) (i : Expr) (f : Word) : Expr :=
  let b : Expr := if R.w = 1 then i else .bin .mul i (.const R.w)
  if R.wd f = 0 then b else .bin .add b (.const (R.wd f))

/-- Field `f` of a record word `x`: the low or high half for a packed field, else `x`. -/
@[expose] def TRec.ex (R : TRec) (f x : Word) : Word :=
  if R.hi = 0 then x else if f = 0 then x &&& 4294967295 else if f = R.hi then x >>> 32 else x

/-- The extraction `ex` as an expression. -/
@[expose] def TRec.exE (R : TRec) (f : Word) (e : Expr) : Expr :=
  if R.hi = 0 then e else if f = 0 then .bin .and e (.const 4294967295)
  else if f = R.hi then .bin .shr e (.const 32) else e

/-- The tier expression a load passes: a handle's tier bit `(h >> 27) & 1` (`tierE h`) as
`h >> 27`, since the tiered access masks the tier with `1` itself. -/
@[expose] def TRec.tierX : Expr → Expr
  | .bin .and (.bin .shr h (.const 27)) (.const 1) => .bin .shr h (.const 27)
  | t => t

/-- `R⟨t, i⟩.f`: the load of field `f` of node `i` of tier `t` (tier `t` of the record array). -/
@[expose] def TRec.ld (R : TRec) (t i : Expr) (f : Word) : Expr :=
  R.exE f (.ld64t R.arr (TRec.tierX t) (R.adE i f))

/-- `R⟨t, i⟩.f := e`: the store of field `f` of node `i` of tier `t` (`t` simple; a whole
word: unpacked fields only). -/
@[expose] def TRec.st (R : TRec) (t i : Expr) (f : Word) (e : Expr) : Stmt :=
  .st64t R.arr t (R.adE i f) e

/-- `R⟨t⟩.count`: the node count of tier `t`. -/
@[expose] def TRec.cntE (R : TRec) (t : Expr) : Expr := .ld64 TRec.ctl (.bin .add (.const R.ca) t)

/-- The tier of a handle word: bit 27. -/
@[expose] def tierE (h : Expr) : Expr := .bin .and (.bin .shr h (.const 27)) (.const 1)

/-- The node index of a handle word: the low 27 bits. -/
@[expose] def idxE (h : Expr) : Expr := .bin .and h (.const 134217727)

end L
