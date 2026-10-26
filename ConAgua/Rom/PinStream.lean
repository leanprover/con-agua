import ConAgua.Arena.Prelude

/-!
# The pin-data buffer: its encoding (lane `romload`)

The checker reads the `Nat`-operation pin variants (`NatOpPinSet`) from a **byte buffer the harness
loads** (byte array `PB`, like the input file in byte array `0`), not from its program. The buffer
is untrusted: the final theorem holds at whatever pin list the bytes decode to, and bytes that do
not decode make the run abort (decline). DESIGN.md, "The pin data as an input (lane `romload`)".

The buffer is `romData ++ encPinSets pins`:
* `romData` (`ConAgua/Arena/Prelude.lean`), the data the twin interns at startup **exactly** (pin
  names, basis blocks, axiom shapes); `check` compares it byte for byte with its own copy (the
  program's constant data) before reading anything, so this part is not trusted either;
* `encPinSets pins`: the variant count (8 bytes), then per variant its eight pinned expressions
  (each at a fresh memo, as `internExpr`), its eight certificate lists (the length, then the
  expressions at one memo, as `internExprList`) and its eight type-pin lists (the length, then per
  pin its name and its type at a fresh memo, as `internTypePins`), in `NatOpPinSet`'s field order. Expressions are
  `encExprM`'s (`ConAgua/Arena/RomExpr.lean`): prefix order, the twin's memo hits as back
  references.

The generator (`ConAgua/Rom/Gen.lean`, `lake exe romgen OUT`) writes the buffer for con-leche's
first variant (`natOpPinSets.head`, the repository toolchain's).
-/

namespace L.Rom

/-- Expressions at one memo, one after the other (the count is the reader's). -/
def encExprList (seen : List ConLeche.Expr) : List ConLeche.Expr → List UInt8
  | [] => []
  | e :: es => (encExprM seen e).1 ++ encExprList (encExprM seen e).2 es

/-- One certificate list: its length, then the expressions at a fresh memo. -/
def encProofs (es : List ConLeche.Expr) : List UInt8 := u64B es.length ++ encExprList [] es

/-- Type pins: per pin its name, then its type at a fresh memo (the count is the reader's). -/
def encTypePinList : List (ConLeche.Name × ConLeche.Expr) → List UInt8
  | [] => []
  | p :: ps => encName p.1 ++ (encExprM [] p.2).1 ++ encTypePinList ps

/-- One type-pin list: its length, then its pins. -/
def encTypePins (ps : List (ConLeche.Name × ConLeche.Expr)) : List UInt8 :=
  u64B ps.length ++ encTypePinList ps

/-- One variant: the eight pins, the eight certificate lists, the eight type-pin lists. -/
def encPinSet (ps : ConLeche.NatOpPinSet) : List UInt8 :=
  (encExprM [] ps.divPin).1 ++ (encExprM [] ps.modPin).1 ++ (encExprM [] ps.gcdPin).1 ++
  (encExprM [] ps.landPin).1 ++ (encExprM [] ps.lorPin).1 ++ (encExprM [] ps.xorPin).1 ++
  (encExprM [] ps.shiftLeftPin).1 ++ (encExprM [] ps.shiftRightPin).1 ++
  encProofs ps.divProofs ++ encProofs ps.modProofs ++ encProofs ps.gcdProofs ++
  encProofs ps.landProofs ++ encProofs ps.lorProofs ++ encProofs ps.xorProofs ++
  encProofs ps.shiftLeftProofs ++ encProofs ps.shiftRightProofs ++
  encTypePins ps.divTypePins ++ encTypePins ps.modTypePins ++ encTypePins ps.gcdTypePins ++
  encTypePins ps.landTypePins ++ encTypePins ps.lorTypePins ++ encTypePins ps.xorTypePins ++
  encTypePins ps.shiftLeftTypePins ++ encTypePins ps.shiftRightTypePins

/-- The variants: their count, then each. -/
def encPinSets (pins : List ConLeche.NatOpPinSet) : List UInt8 :=
  u64B pins.length ++ pins.flatMap encPinSet

/-- **The pin-data buffer** for the variant list `pins`. -/
def pinBuffer (pins : List ConLeche.NatOpPinSet) : List UInt8 := romData ++ encPinSets pins

end L.Rom
