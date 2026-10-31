module

public import ConAgua.L.Syntax

public section

/-!
# Tiered store records (surface syntax)

A node store of the arena (`Arena/StoreFields.lean` lists them) keeps, per tier, an array of
records of `w` words, and the node count of each tier in a control word. Code outside the store
library reaches them only through the accessors below, written in L as

* `R⟨t, i⟩.f`: field `f` of node `i` of tier `t` (`R⟨t, i⟩` for a one-word column);
* `R⟦h⟧.f`, `R⟦h⟧`: the same for the node a handle word `h` names (tier bit 31, index
  `idxE`, or `idxAE` for `APP`, below);
* `R⟨t⟩.count`: the node count of tier `t`;
* `R⟨t, i⟩.f := e`: a field store (the store library's pushes only).

They expand (`Notation.lean`) to the builders `TRec.ld`, `TRec.st`, `TRec.cntE` of this file,
which fix the **layout** in one place: one tiered word array per store (lane tierswitch; tier
`t` of array `a` is array `L.tierA a t`), node `i` of tier `t` at
`arr⟨t⟩[i * w ..]`, the count at `CTL[ca + t]`. Proofs see the named words `TRec.ad`, `tfld`, `tcnt`.

**Packed records** (lane memlay, `hi ≠ 0`): field `0` and field `hi` (two handle words, below
`2^32`) share word `0` of the record, field `0` in bits 0–31 and field `hi` in bits 32–63; the
other fields `f` follow in words `1 ‥` (`f`, or `f - 1` above `hi`), whole. A field's word is
`TRec.wd`, its address `TRec.ad`; a load of a packed field reads its half alone (`Expr.ld32h`, a
4-byte load), whose value is the word's `TRec.ex` (`x & 0xFFFFFFFF`, `x >> 32`). Records are
written once, whole, by the store library's pushes (the combined word `f₀ | f_hi << 32`);
`TRec.st` stores a whole word (unpacked fields only).
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

/-- The tier expression a load passes: a handle's tier bit `(h >> 31) & 1` (`tierE h`) as
`h >> 31`, since the tiered access masks the tier with `1` itself. -/
@[expose] def TRec.tierX : Expr → Expr
  | .bin .and (.bin .shr h (.const 31)) (.const 1) => .bin .shr h (.const 31)
  | t => t

/-- Is field `f` one half of word `0` (a packed record's field `0` or `hi`)? -/
@[expose] def TRec.packed (R : TRec) (f : Word) : Prop := R.hi ≠ 0 ∧ (f = 0 ∨ f = R.hi)

instance (R : TRec) (f : Word) : Decidable (R.packed f) := inferInstanceAs (Decidable (_ ∧ _))

/-- `R⟨t, i⟩.f`: the load of field `f` of node `i` of tier `t` (tier `t` of the record array): the
32-bit load of its half for a packed field, else the word. -/
@[expose] def TRec.ld (R : TRec) (t i : Expr) (f : Word) : Expr :=
  if R.packed f then .ld32h R.arr (TRec.tierX t) (R.adE i f) (decide (f = R.hi))
  else .ld64t R.arr (TRec.tierX t) (R.adE i f)

/-- `R⟨t, i⟩.f := e`: the store of field `f` of node `i` of tier `t` (`t` simple; a whole
word: unpacked fields only). -/
@[expose] def TRec.st (R : TRec) (t i : Expr) (f : Word) (e : Expr) : Stmt :=
  .st64t R.arr t (R.adE i f) e

/-- `R⟨t⟩.count`: the node count of tier `t`. -/
@[expose] def TRec.cntE (R : TRec) (t : Expr) : Expr := .ld64 TRec.ctl (.bin .add (.const R.ca) t)

/-! ### Handle words (con-ron's `Idx`, `ConRon/Arena/Handle.lean`)

A handle word has one of two shapes. Bit 31 is the tier in both; bit 30 says which:

    wide   (expression `app` only)        narrow (every other node)
    bit  31      tier                     bit  31      tier
    bit  30      1                        bit  30      0
    bits 29…0    index                    bits 29…26   ctor tag
                                          bits 25…0    index

The readers below are the twin's `Idx.tier`, `Idx.tag` and (per shape) `Idx.index`. -/

/-- The tier of a handle word: bit 31. -/
@[expose] def tierE (h : Expr) : Expr := .bin .and (.bin .shr h (.const 31)) (.const 1)

/-- The node index of a NARROW handle word: bits 25…0, with bit 30 kept, so that a wide word
reads an index of at least `2^30`, beyond every narrow array (whose cap is `2^26`): a node read
through it fails its count check, as the twin's `get` (whose `app` and `param` arms test the
shape) finds nothing. -/
@[expose] def idxE (h : Expr) : Expr := .bin .and h (.const 0x43ffffff)

/-- The node index of a WIDE handle word (an expression `app`): bits 30…0 of `2^30 + h`, so that
a narrow word reads an index of at least `2^30`, beyond the `app` array (cap `2^30`). The
constant comes first (`idxA`, `StoreFields.lean`, says why). -/
@[expose] def idxAE (h : Expr) : Expr :=
  .bin .and (.bin .add (.const 0x40000000) h) (.const 0x7fffffff)

/-- The node index of any handle word, con-ron's `Idx.idxNat` itself (bits 29…0 of a wide word,
25…0 of a narrow one): `h & (2^26 - 1 + w · (2^30 - 2^26))`, `w` the shape bit. The twin's
`derived` (`ETables.derAt`, `LTables.derAt`) reads the derived column at this index without a
shape test, so the derived reads of the `app` and `param` arms use it. -/
@[expose] def idxGE (h : Expr) : Expr :=
  .bin .and h (.bin .add (.const 0x3ffffff)
    (.bin .mul (.bin .and (.bin .shr h (.const 30)) (.const 1)) (.const 0x3c000000)))

/-- The constructor tag of a handle word, the twin's `Idx.tag`: `4` (`app`) for a wide word,
bits 29…26 of a narrow one; branch-free, `f + w * (4 - f)` with `f = (h >> 26) & 15` and the
shape bit `w = (h >> 30) & 1`. -/
@[expose] def tagE (h : Expr) : Expr :=
  .bin .add (.bin .and (.bin .shr h (.const 26)) (.const 15))
    (.bin .mul (.bin .and (.bin .shr h (.const 30)) (.const 1))
      (.bin .sub (.const 4) (.bin .and (.bin .shr h (.const 26)) (.const 15))))

end L
