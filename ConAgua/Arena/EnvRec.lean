import ConAgua.Arena.StoreRel
import ConRon.Arena.CheckerSplit

/-!
# Declaration records in a word pool, and their decoders

The twin's environment values (`IConstantVal`, `IConstantInfo`, `IDeclaration`, `ValueGroup`,
`PendingCheck`) are nested: lists of handles, lists of recursor rules (each with two lists of its
own), an `IIndCaps` with four lists, an `IProjTable` with an `Array`. In L they are **records in
a word pool**: a record is a run of words at a pointer `p`, every list is a slice `(off, cnt)` of
the same pool (two words of the record), and a list of records is a slice of fixed-size records
(recursor rules, 11 words) or a slice of record pointers (an inductive block's constants). The
decoders below are the value relations (`decE`'s analogue): `decCI dn a p = some ci` says that
the record at `p` in the pool `a` denotes `ci`. They read only the pool, so a pool that only grows
above a top keeps every decoding below it (`PoolSlice`'s `Agree`).

Handle words must be below `2^32` (`hd?` refuses others), so a decoded handle is the word itself
and L may compare words where the twin compares handles. `PropWhen`'s names are con-leche `Name`
values in the twin; in L they are name handles, read back by `dn` (the store's `denoteN`, a
parameter here: the consumers relate it to the store).

## The layouts (offsets from the record pointer `p`)

`IConstantVal` (4 words, at `q`): `name`, `lps.off`, `lps.len`, `type`.

`IConstantInfo` (word `p` is the kind; **word `p + 1` is always the index key** `ci.name`):

| kind | constructor | words |
|---:|---|---|
| 0 | `axiomInfo cv` | cv at `p+1` |
| 1 | `defnInfo cv value hint` | cv at `p+1`; `value` `p+5`; hint `p+6` (0 opaque, 1 abbrev, 2 regular), height `p+7` |
| 2 | `thmInfo cv` | cv at `p+1` |
| 3 | `indInfo cv caps` | cv at `p+1`; caps at `p+5` (15 words, `decCaps`) |
| 4 | `ctorInfo cv np nf` | cv at `p+1`; `p+5`, `p+6` |
| 5 | `recInfo cv major pre rules` | cv at `p+1`; `p+5`, `p+6`; rules slice `p+7`, `p+8` (11-word records) |
| 6 | `projInfo tbl` | `tableName` `p+1`, `structName` `p+2`, lps `p+3`,`p+4`, `numParams` `p+5`, `ctor` `p+6`, `numFields` `p+7`, `structSort` `p+8`, bodies `p+9`,`p+10`, guards `p+11`,`p+12`, `off` `p+13` |

`IDeclaration` (word `p` the kind): 0 `axiomDecl` (cv at `p+1`), 1 `defnDecl` (cv, `value` `p+5`,
hint `p+6`, `p+7`), 2 `thmDecl` (cv, `value` `p+5`), 3 `opaqueDecl` (cv, `value` `p+5`),
4 `basisDecl` (kind `p+1`: 0‥4 = `eqK` … `quotK`), 5 `indDecl` (block: a slice of `IConstantInfo`
record pointers `p+1`, `p+2`; `numParams` `p+3`), 6 `quotDecl` (cv at `p+1`, kind `p+5`: 0‥4 =
`type` … `sound`).

`PendingCheck` (6 words): `vg.kind` (0 defn, 1 thm, 2 opaque), cv (4 words), `vg.jv`; then
`pos`, `vis` (8 words in all).
-/

namespace L.Arena

open ConRon.Arena

section dec
variable (a : Array Word)

/-- Word `i`, a natural number. -/
def nat? (i : Nat) : Option Nat := (a[i]?).map (·.toNat)

/-- Word `i`, a `Bool` (`0` is `false`). -/
def bool? (i : Nat) : Option Bool := (a[i]?).map (· != 0)

/-- Word `i`, a handle (a word below `2^32`). -/
def hd? {k : IdxKind} (i : Nat) : Option (Idx k) := do
  let w ← a[i]?
  if w.toNat < 2 ^ 32 then some (decI w) else none

/-- The handles at `off`, …, `off + len - 1`. -/
def hslice? {k : IdxKind} (off cnt : Nat) : Option (List (Idx k)) :=
  (List.range cnt).mapM fun j => hd? a (off + j)

/-- The handle list whose slice `(off, cnt)` is at words `i`, `i + 1`. -/
def hlist? {k : IdxKind} (i : Nat) : Option (List (Idx k)) := do
  hslice? a (← nat? a i) (← nat? a (i + 1))

/-- `IConstantVal` at `q`. -/
def decCV (q : Nat) : Option IConstantVal := do
  pure ⟨← hd? a q, ← hlist? a (q + 1), ← hd? a (q + 3)⟩

/-- A reducibility hint at `q` (kind) and `q + 1` (height). -/
def decHint (q : Nat) : Option ConLeche.ReducibilityHint := do
  match ← nat? a q with
  | 0 => pure .opaque
  | 1 => pure .abbrev
  | 2 => pure (.regular (← nat? a (q + 1)))
  | _ => none

/-- A recursor rule: an 11-word record at `q` (`ctor`, `nfields`, `ctorParams`, fire kind (0 plain,
1 nested), the fire's level slice, its pin slice, `rhs`, `k`, `eta`). -/
def decRule (q : Nat) : Option IRecRule := do
  let fire ← match ← nat? a (q + 3) with
    | 0 => some IRecRuleFire.plain
    | 1 => some (IRecRuleFire.nested (← hlist? a (q + 4)) (← hlist? a (q + 6)))
    | _ => none
  pure { ctor := ← hd? a q, nfields := ← nat? a (q + 1), ctorParams := ← nat? a (q + 2), fire,
         rhs := ← hd? a (q + 8), k := ← bool? a (q + 9), eta := ← bool? a (q + 10) }

/-- The rules of the slice `(off, cnt)` of 11-word records. -/
def decRules (off cnt : Nat) : Option (List IRecRule) :=
  (List.range cnt).mapM fun j => decRule a (off + 11 * j)

variable (dn : NIdx → Option ConLeche.Name)

/-- `PropWhen` at `q` (0 `never`, 1 `ifAllZero` with the name slice at `q + 1`, `q + 2`). -/
def decPW (q : Nat) : Option ConLeche.PropWhen := do
  match ← nat? a q with
  | 0 => pure .never
  | 1 => pure (.ifAllZero (← (← hlist? a (q + 1) : List NIdx).mapM dn))
  | _ => none

/-- `IIndCaps`: 15 words at `q` (`eta`, `etaCtor`, `etaParams`, `etaFields`, `unitlike`,
`unitParams`, `ruleK`, `sortZ` (3), `all` (2), `nparams`, `ctors` (2)). -/
def decCaps (q : Nat) : Option IIndCaps := do
  pure { eta := ← bool? a q, etaCtor := ← hd? a (q + 1), etaParams := ← nat? a (q + 2),
         etaFields := ← nat? a (q + 3), unitlike := ← bool? a (q + 4),
         unitParams := ← nat? a (q + 5), ruleK := ← bool? a (q + 6), sortZ := ← decPW a dn (q + 7),
         all := ← hlist? a (q + 10), nparams := ← nat? a (q + 12), ctors := ← hlist? a (q + 13) }

/-- `IProjTable` at `p` (a `projInfo` record; word `p` is its kind). -/
def decTbl (p : Nat) : Option IProjTable := do
  pure { tableName := ← hd? a (p + 1), structName := ← hd? a (p + 2),
         levelParams := ← hlist? a (p + 3), numParams := ← nat? a (p + 5), ctor := ← hd? a (p + 6),
         numFields := ← nat? a (p + 7), structSort := ← hd? a (p + 8),
         bodies := (← hlist? a (p + 9)).toArray, guards := ← hlist? a (p + 11),
         off := ← nat? a (p + 13) }

/-- **The constant record at `p`.** -/
def decCI (p : Nat) : Option IConstantInfo := do
  match ← nat? a p with
  | 0 => pure (.axiomInfo (← decCV a (p + 1)))
  | 1 => pure (.defnInfo (← decCV a (p + 1)) (← hd? a (p + 5)) (← decHint a (p + 6)))
  | 2 => pure (.thmInfo (← decCV a (p + 1)))
  | 3 => pure (.indInfo (← decCV a (p + 1)) (← decCaps a dn (p + 5)))
  | 4 => pure (.ctorInfo (← decCV a (p + 1)) (← nat? a (p + 5)) (← nat? a (p + 6)))
  | 5 => pure (.recInfo (← decCV a (p + 1)) (← nat? a (p + 5)) (← nat? a (p + 6))
      (← decRules a (← nat? a (p + 7)) (← nat? a (p + 8))))
  | 6 => pure (.projInfo (← decTbl a p))
  | _ => none

/-- The constants of a slice of record pointers. -/
def decCIs (off cnt : Nat) : Option (List IConstantInfo) :=
  (List.range cnt).mapM fun j => do decCI a dn (← nat? a (off + j))

/-- A basis kind (0‥4). -/
def decBasis : Nat → Option ConLeche.BasisKind
  | 0 => some .eqK | 1 => some .natK | 2 => some .emptyK | 3 => some .falseK | 4 => some .quotK
  | _ => none

/-- A quotient kind (0‥4). -/
def decQuot : Nat → Option ConLeche.QuotKind
  | 0 => some .type | 1 => some .ctor | 2 => some .lift | 3 => some .ind | 4 => some .sound
  | _ => none

/-- **The declaration record at `p`.** -/
def decDecl (p : Nat) : Option IDeclaration := do
  match ← nat? a p with
  | 0 => pure (.axiomDecl (← decCV a (p + 1)))
  | 1 => pure (.defnDecl (← decCV a (p + 1)) (← hd? a (p + 5)) (← decHint a (p + 6)))
  | 2 => pure (.thmDecl (← decCV a (p + 1)) (← hd? a (p + 5)))
  | 3 => pure (.opaqueDecl (← decCV a (p + 1)) (← hd? a (p + 5)))
  | 4 => pure (.basisDecl (← decBasis (← nat? a (p + 1))))
  | 5 => pure (.indDecl (← decCIs a dn (← nat? a (p + 1)) (← nat? a (p + 2))) (← nat? a (p + 3)))
  | 6 => pure (.quotDecl (← decQuot (← nat? a (p + 5))) (← decCV a (p + 1)))
  | _ => none

/-- A value kind (0 defn, 1 thm, 2 opaque). -/
def decVK : Nat → Option ValueKind
  | 0 => some .defn | 1 => some .thm | 2 => some .opaque
  | _ => none

/-- A value group: 6 words at `q`. -/
def decVG (q : Nat) : Option ValueGroup := do
  pure ⟨← decVK (← nat? a q), ← decCV a (q + 1), ← hd? a (q + 5)⟩

end dec

end L.Arena
