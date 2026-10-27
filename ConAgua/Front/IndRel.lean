import ConAgua.Front.IndFields
import ConAgua.Front.ExprIface

/-!
# The records of an `inductive` line in `IFR`/`IFL`, related to con-leche's

What `ind_fields(v)` (`IndFields.lean`) leaves in the scratch arrays, as a relation to the
records con-leche's `scanIndDecl` reads: the interface between the fields pass (proved in
`IndFieldsSpec.lean`, `IndFieldsLink.lean`) and the apply step (`IndApply*.lean`), which reads
only what the twin's `validateIndD`/`installIndD` read. Every number is exact (the pass aborts on
a number of more than 18 digits, so it is below `10^18`); a universe parameter list is its
position in the input (`listN`, read again by `lp_put`); a list of records is a run of records of
one size; every word the relation reads lies below the array's top (word `0`), so appends above
it keep the relation (`IndFR.frame`).
-/

open L.Arena
open ConLeche.Frontend
open ConAgua.Front.FieldsLink
open L.Front.Fields (listN)

namespace L.Front.Ind

/-- Word `i` of word array `a` (`0` out of range). -/
def wd (m : Mem) (a : ArrId) (i : Nat) : Word := (m.arr64 a)[i]?.getD 0

/-- The top of `IFR`/`IFL` (word `0`), as a bound: the words in use are `1 ‥ top`. -/
def topN (m : Mem) (a : ArrId) : Nat := (wd m a 0).toNat

/-- A number field: the word is the number, which has at most 18 digits. -/
def NumW (w : Word) (n : Nat) : Prop := w.toNat = n ∧ n < 10 ^ 18

/-- A Boolean field. -/
def BoolW (w : Word) (x : Bool) : Prop := w = if x then 1 else 0

/-- An optional number at `IFR[i]` (flag) and `IFR[i + 1]` (value). -/
def OptW (m : Mem) (i : Nat) : Option Nat → Prop
  | none => wd m IFR i = 0
  | some n => wd m IFR i = 1 ∧ NumW (wd m IFR (i + 1)) n

/-- A constant's common data at `IFR[p]`: the name id, the position of `levelParams`' `[`, the
type id. -/
def CVF (b : ByteArray) (m : Mem) (p : Nat) (cv : CVRec) : Prop :=
  NumW (wd m IFR p) cv.name ∧ ItemsR (listN b.data (wd m IFR (p + 1))) cv.levelParams ∧
    NumW (wd m IFR (p + 2)) cv.type

/-- The numbers `ns` at `IFL[off ‥ off + ns.length)`, below `IFL`'s top. -/
def NumsF (m : Mem) (off : Nat) (ns : List Nat) : Prop :=
  1 ≤ off ∧ off + ns.length ≤ topN m IFL + 1 ∧
    ∀ k (h : k < ns.length), NumW (wd m IFL (off + k)) ns[k]

/-- A type record (11 words at `IFR[t]`): what `validateIndD`/`installIndD` read of it. -/
def TyF (b : ByteArray) (m : Mem) (t : Nat) (ty : IndTypeRec) : Prop :=
  CVF b m t ty.cv ∧ (wd m IFR (t + 4)).toNat = ty.ctors.length ∧
    NumsF m (wd m IFR (t + 3)).toNat ty.ctors ∧ BoolW (wd m IFR (t + 7)) ty.isUnsafe ∧
    NumW (wd m IFR (t + 9)) ty.numNested ∧ NumW (wd m IFR (t + 10)) ty.numParams

/-- A constructor record (10 words at `IFR[c]`). -/
def CtF (b : ByteArray) (m : Mem) (c : Nat) (ct : IndCtorRec) : Prop :=
  CVF b m c ct.cv ∧ NumW (wd m IFR (c + 4)) ct.numFields ∧
    NumW (wd m IFR (c + 5)) ct.numParams ∧ OptW m (c + 6) ct.cidx ∧ OptW m (c + 8) ct.induct

/-- A rule record (3 words at `IFL[q]`). -/
def RuleF (m : Mem) (q : Nat) (ru : RuleRec) : Prop :=
  NumW (wd m IFL q) ru.ctor ∧ NumW (wd m IFL (q + 1)) ru.nfields ∧ NumW (wd m IFL (q + 2)) ru.rhs

/-- A recursor record (11 words at `IFR[r]`), its rules a run of rule records in `IFL`, below
`IFL`'s top. -/
def RecF (b : ByteArray) (m : Mem) (r : Nat) (rc : IndRecRec) : Prop :=
  CVF b m r rc.cv ∧ BoolW (wd m IFR (r + 4)) rc.k ∧ NumW (wd m IFR (r + 5)) rc.numIndices ∧
    NumW (wd m IFR (r + 6)) rc.numMinors ∧ NumW (wd m IFR (r + 7)) rc.numMotives ∧
    NumW (wd m IFR (r + 8)) rc.numParams ∧ (wd m IFR (r + 10)).toNat = rc.rules.length ∧
    1 ≤ (wd m IFR (r + 9)).toNat ∧
    (wd m IFR (r + 9)).toNat + 3 * rc.rules.length ≤ topN m IFL + 1 ∧
    ∀ j (h : j < rc.rules.length), RuleF m ((wd m IFR (r + 9)).toNat + 3 * j) rc.rules[j]

/-- A list of records of size `sz` at `IFR[off]`, below `IFR`'s top. -/
def ListF {α : Type} (F : Nat → α → Prop) (m : Mem) (sz off : Nat) (xs : List α) : Prop :=
  1 ≤ off ∧ off + sz * xs.length ≤ topN m IFR + 1 ∧
    ∀ j (h : j < xs.length), F (off + sz * j) xs[j]

/-- **What `ind_fields(v)` returns**, `(to, tn, co, cn, ro, rn)`, against con-leche's block
`.ind tys cts rcs`: the three lists, as runs of records in `IFR`. -/
def IndFR (b : ByteArray) (m : Mem) (to tn co cn ro rn : Word) (tys : List IndTypeRec)
    (cts : List IndCtorRec) (rcs : List IndRecRec) : Prop :=
  tn.toNat = tys.length ∧ ListF (TyF b m) m 11 to.toNat tys ∧
    cn.toNat = cts.length ∧ ListF (CtF b m) m 10 co.toNat cts ∧
    rn.toNat = rcs.length ∧ ListF (RecF b m) m 11 ro.toNat rcs

end L.Front.Ind
