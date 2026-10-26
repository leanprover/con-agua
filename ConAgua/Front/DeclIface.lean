module

public import ConAgua.Front.ExprIface

@[expose] public section


/-!
# Declaration lines: what the fields pass hands the apply step

A declaration line `{"axiom":{…}}`, `{"def":{…}}`, `{"thm":{…}}`, `{"opaque":{…}}`, `{"quot":{…}}`
or `{"inductive":{…}}` has no index key. Its fields are eight words (`DFld`):

| field | meaning |
|---|---|
| `pl` | `20` axiom, `21` def, `22` thm, `23` opaque, `24` quot, `25` inductive (not applied yet), `0` failure |
| `name` | the name id |
| `lps` | the position of `levelParams`' `[` (its items: `listN`) |
| `type` | the type's expression id |
| `value` | the value's expression id (def, thm, opaque) |
| `hk`, `hn` | def `hints`: `1` abbrev, `2` opaque, `3` regular with height `hn` |
| `flag` | axiom/opaque `isUnsafe` (`1` true, `0` false); def `safety` (`1`: the raw body is `safe`, `0` another string without a backslash, `2` a string with one); quot `kind` (`1`‥`4` for the raw bodies `type`, `ctor`, `lift`, `ind`, `0` another string without a backslash, `5` one with) |

A string is compared on its raw bytes: a body without a backslash is its own decoding, and a body
with one is reported as such (the apply step refuses it; con-leche would decode it first).
-/

namespace L.Front.Fields

/-- What the declaration fields pass returns. -/
structure DFld where
  pl : Word
  name : Word
  lps : Word
  type : Word
  value : Word
  hk : Word
  hn : Word
  flag : Word

/-- The eight words. -/
def DFld.enc (f : DFld) : List Word := [f.pl, f.name, f.lps, f.type, f.value, f.hk, f.hn, f.flag]

/-- Not a declaration line, or a failure. -/
def DFld.none : DFld := ⟨0, 0, 0, 0, 0, 0, 0, 0⟩

end L.Front.Fields

namespace ConAgua.Front.FieldsLink
open ConLeche.Frontend ConAgua.Scan
open L (Word)
open L.Front.Fields

/-- A declaration's common data. -/
def CVR (b : ByteArray) (cv : CVRec) (f : DFld) : Prop :=
  ItemR f.name cv.name ∧ ItemsR (listN b.data f.lps) cv.levelParams ∧ ItemR f.type cv.type

/-- A definition's hints. -/
def HintsR : HintsRec → Word → Word → Prop
  | .abbrev, hk, _ => hk = 1
  | .opaque, hk, _ => hk = 2
  | .regular n, hk, hn => hk = 3 ∧ ItemR hn n

/-- A `quot` record's kind: the flag names it, or is `0`/`5`. -/
def QuotR (k : String) (flag : Word) : Prop :=
  (flag = 1 → k = "type") ∧ (flag = 2 → k = "ctor") ∧ (flag = 3 → k = "lift") ∧
    (flag = 4 → k = "ind")

/-- What a declaration line's words say about con-leche's declaration record. -/
def DeclR (b : ByteArray) : DeclRec → DFld → Prop
  | .ax cv u, f => f.pl = 20 ∧ CVR b cv f ∧ f.flag = (if u then 1 else 0)
  | .defn cv v h s, f => f.pl = 21 ∧ CVR b cv f ∧ ItemR f.value v ∧ HintsR h f.hk f.hn ∧
      (f.flag = 1 → s = "safe")
  | .thm cv v, f => f.pl = 22 ∧ CVR b cv f ∧ ItemR f.value v
  | .opaq cv v u, f => f.pl = 23 ∧ CVR b cv f ∧ ItemR f.value v ∧ f.flag = (if u then 1 else 0)
  | .quot cv k, f => f.pl = 24 ∧ CVR b cv f ∧ QuotR k f.flag
  | .ind tys cts rcs, f => f.pl = 25 ∧ ∃ v : USize, f.name = v.toUInt64 ∧
      ∃ e, scanIndDecl b v = .ok (.ind tys cts rcs) e

/-- What a declaration line's words say about con-leche's line record. -/
def DRecR (b : ByteArray) : LineRec → DFld → Prop
  | .decl d, f => DeclR b d f
  | _, _ => False

end ConAgua.Front.FieldsLink
