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
which fix the **layout** in one place. Today the two tiers are interleaved in one word array
(node `i` of tier `t` at `arr[i * 2w + t * w ..]`, the count at `CTL[ca + t]`); a change of the
layout (one array per tier) changes these builders and the evaluation lemmas of
`Arena/StoreFields.lean`, nothing else. Proofs see the named words `TRec.ad`, `tfld`, `tcnt`.
-/

namespace L

/-- A tiered store record: the record array, the words per node `w`, and the control-word
index `ca` of tier 0's node count (tier 1's is `ca + 1`). -/
structure TRec where
  arr : ArrId
  w : Word
  ca : Word
  deriving Repr, DecidableEq, Inhabited

/-- The control-word array (`CTL`). -/
@[expose, reducible] def TRec.ctl : ArrId := 1

/-- The word address of field `f` of node `j` of tier `t`: `j * 2w + t * w + f`, written without
`t * 1` and `+ 0` (as the address expression `adE` computes it). -/
@[expose] def TRec.ad (R : TRec) (t j f : Word) : Word :=
  let b := if R.w = 1 then j * 2 + t else j * (2 * R.w) + t * R.w
  if f = 0 then b else b + f

/-- The address expression of field `f` of node `i` of tier `t`. -/
@[expose] def TRec.adE (R : TRec) (t i : Expr) (f : Word) : Expr :=
  let b : Expr := if R.w = 1 then .bin .add (.bin .mul i (.const 2)) t
    else .bin .add (.bin .mul i (.const (2 * R.w))) (.bin .mul t (.const R.w))
  if f = 0 then b else .bin .add b (.const f)

/-- `R⟨t, i⟩.f`: the load of field `f` of node `i` of tier `t`. -/
@[expose] def TRec.ld (R : TRec) (t i : Expr) (f : Word) : Expr := .ld64 R.arr (R.adE t i f)

/-- `R⟨t, i⟩.f := e`: the store of field `f` of node `i` of tier `t`. -/
@[expose] def TRec.st (R : TRec) (t i : Expr) (f : Word) (e : Expr) : Stmt :=
  .st64 R.arr (R.adE t i f) e

/-- `R⟨t⟩.count`: the node count of tier `t`. -/
@[expose] def TRec.cntE (R : TRec) (t : Expr) : Expr := .ld64 TRec.ctl (.bin .add (.const R.ca) t)

/-- The tier of a handle word: bit 27. -/
@[expose] def tierE (h : Expr) : Expr := .bin .and (.bin .shr h (.const 27)) (.const 1)

/-- The node index of a handle word: the low 27 bits. -/
@[expose] def idxE (h : Expr) : Expr := .bin .and h (.const 134217727)

end L
