import ConAgua.Arena.RomCI
import ConAgua.Census.Attr

/-!
# Constant blocks from the ROM: `rom_blk(pos)` builds the twin's `internCIList` as `EREC` records

The ROM's item streams (`RomItems.lean`) give the store effect of the twin's constant interners;
their *values* (`IConstantInfo`s) were not built. A consumer that reads a constant block the twin
interns at the point of use (`andPinDecls`, the `And` pin of `andPinOk`) needs them as `EREC`
records (`decCI`, `EnvRec.lean`). The ROM holds such a block as a **block encoding**
(`encBlk`):

* the record area's size `W` and the record count `C`;
* the **fills**: words with no store effect, each written to a slot of the area (tag `6`
  `k w`: `EREC[b + k] := w`; tag `7` `k j`: `EREC[b + k] := b + j`, a pointer into the area), ended
  by tag `8`;
* the **items**, in the twin's order (`itemsCIs`: a fresh memo (tag `4`), then names (`0`) and
  expressions (`3`), levels (`1`) and level lists (`2`)), each with the slot its handle goes to:
  `t k payload`, ended by tag `5`.

`rom_blk(pos)` allocates the area (`erec_alloc(W)`, offset `b`), runs the fills and the items, and
returns `(b, C)`: the first `C` words of the area are the pointers to the records. The layout
(`blkCIs`) puts each record and its slices (universe parameters, `all`, `ctors`, rules) in the
area; the items are exactly `itemsCIs cs` (`blkCIs_items`), so the store effect is
`internCIList`'s (`sim_ciList`).

Supported: no `projInfo`, rules with `.plain` firing, `sortZ` `.never` or `.ifAllZero []` (the
`And` block: `blkCIs andPin` is `some`).
-/

open ConRon.Arena ConRon.Arena.Frontend

namespace L.Rom

open L.Arena

/-! ## The layout -/

/-- A word with no store effect: a literal or a pointer into the area. -/
inductive Fill where
  | lit (w : Nat)
  | ptr (j : Nat)
  deriving DecidableEq, Repr

/-- A block under construction: the words used, the fills, the items with their slots. -/
structure Blk where
  top : Nat := 0
  fills : List (Nat × Fill) := []
  items : List (Nat × Item) := []

namespace Blk

/-- `n` fresh words: their offset, and the block. -/
def alloc (b : Blk) (n : Nat) : Nat × Blk := (b.top, { b with top := b.top + n })
def lit (b : Blk) (k w : Nat) : Blk := { b with fills := b.fills ++ [(k, .lit w)] }
def ptr (b : Blk) (k j : Nat) : Blk := { b with fills := b.fills ++ [(k, .ptr j)] }
def it (b : Blk) (k : Nat) (i : Item) : Blk := { b with items := b.items ++ [(k, i)] }

end Blk

/-- `Bool` as a word. -/
def boolW (x : Bool) : Nat := if x then 1 else 0

/-- The names `ns` as items to the slots `s, s + 1, …`. -/
def blkNames (b : Blk) (s : Nat) : List ConLeche.Name → Blk
  | [] => b
  | n :: ns => blkNames (b.it s (.nm n)) (s + 1) ns

/-- A name list as a slice: the pointer at `k`, the count at `k + 1`, the names in fresh words. -/
def blkSlice (b : Blk) (k : Nat) (ns : List ConLeche.Name) : Blk :=
  let (s, b) := b.alloc ns.length
  blkNames ((b.ptr k s).lit (k + 1) ns.length) s ns

/-- A constant value at `p` (`decCV`): name, universe parameters, type, in the twin's order. -/
def blkCV (b : Blk) (p : Nat) (cv : ConLeche.ConstantVal) : Blk :=
  (blkSlice (b.it p (.nm cv.name)) (p + 1) cv.levelParams).it (p + 3) (.ex cv.type)

/-- `IIndCaps` at `q` (`decCaps`, 15 words). -/
def blkCaps (b : Blk) (q : Nat) (c : ConLeche.IndCaps) : Option Blk := do
  let b := (b.lit q (boolW c.eta)).it (q + 1) (.nm c.etaCtor)
  let b := (((((b.lit (q + 2) c.etaParams).lit (q + 3) c.etaFields).lit (q + 4) (boolW c.unitlike)).lit
    (q + 5) c.unitParams).lit (q + 6) (boolW c.ruleK))
  let b ← match c.sortZ with
    | .never => some (b.lit (q + 7) 0)
    | .ifAllZero [] => some (((b.lit (q + 7) 1).lit (q + 8) 0).lit (q + 9) 0)
    | .ifAllZero (_ :: _) => none
  let b := blkSlice b (q + 10) c.all
  let b := b.lit (q + 12) c.nparams
  pure (blkSlice b (q + 13) c.ctors)

/-- One rule at `r` (`decRule`, 11 words): `ctor`, then (`.plain` only) `rhs`. -/
def blkRule (b : Blk) (r : Nat) (rl : ConLeche.RecRule) : Option Blk := do
  let b := b.it r (.nm rl.ctor)
  let b := ((b.lit (r + 1) rl.nfields).lit (r + 2) rl.ctorParams)
  let b ← match rl.fire with
    | .plain => some (((((b.lit (r + 3) 0).lit (r + 4) 0).lit (r + 5) 0).lit (r + 6) 0).lit (r + 7) 0)
    | .nested _ _ => none
  let b := b.it (r + 8) (.ex rl.rhs)
  pure ((b.lit (r + 9) (boolW rl.k)).lit (r + 10) (boolW rl.eta))

/-- The rules at `r, r + 11, …`. -/
def blkRules (b : Blk) (r : Nat) : List ConLeche.RecRule → Option Blk
  | [] => some b
  | rl :: rs => do blkRules (← blkRule b r rl) (r + 11) rs

/-- A constant record (`decCI`), its pointer to slot `i`. -/
def blkCI (b : Blk) (i : Nat) : ConLeche.ConstantInfo → Option Blk
  | .axiomInfo v =>
    let (p, b) := b.alloc 5
    some (blkCV ((b.ptr i p).lit p 0) (p + 1) v)
  | .defnInfo v e h =>
    let (p, b) := b.alloc 8
    let b := (blkCV ((b.ptr i p).lit p 1) (p + 1) v).it (p + 5) (.ex e)
    some <| match h with
      | .opaque => (b.lit (p + 6) 0).lit (p + 7) 0
      | .abbrev => (b.lit (p + 6) 1).lit (p + 7) 0
      | .regular n => (b.lit (p + 6) 2).lit (p + 7) n
  | .thmInfo v =>
    let (p, b) := b.alloc 5
    some (blkCV ((b.ptr i p).lit p 2) (p + 1) v)
  | .indInfo v c =>
    let (p, b) := b.alloc 20
    blkCaps (blkCV ((b.ptr i p).lit p 3) (p + 1) v) (p + 5) c
  | .ctorInfo v nP nF =>
    let (p, b) := b.alloc 7
    some (((blkCV ((b.ptr i p).lit p 4) (p + 1) v).lit (p + 5) nP).lit (p + 6) nF)
  | .recInfo v mI rP rs =>
    let (p, b) := b.alloc 9
    let b := (((blkCV ((b.ptr i p).lit p 5) (p + 1) v).lit (p + 5) mI).lit (p + 6) rP)
    let (r, b) := b.alloc (11 * rs.length)
    blkRules ((b.ptr (p + 7) r).lit (p + 8) rs.length) r rs
  | .projInfo _ => none

/-- The records from slot `i` on. -/
def blkCIsFrom (b : Blk) (i : Nat) : List ConLeche.ConstantInfo → Option Blk
  | [] => some b
  | c :: cs => do blkCIsFrom (← blkCI b i c) (i + 1) cs

/-- **The block's layout**: `|cs|` pointer slots, then the records; a fresh memo first. -/
def blkCIs (cs : List ConLeche.ConstantInfo) : Option Blk :=
  blkCIsFrom { top := cs.length, items := [] } 0 cs

/-! ## The encoding -/

/-- The fills, then their end tag `8`. -/
def encFills : List (Nat × Fill) → List UInt8
  | [] => [8]
  | (k, .lit w) :: fs => 6 :: (u64B k ++ u64B w ++ encFills fs)
  | (k, .ptr j) :: fs => 7 :: (u64B k ++ u64B j ++ encFills fs)

/-- The items with their slots, threading the memo's `seen` (a reset empties it); the end tag
`5` last. -/
def encSlots (seen : List ConLeche.Expr) : List (Nat × Item) → List UInt8
  | [] => [5]
  | (_, .reset) :: is => 4 :: encSlots [] is
  | (k, .nm n) :: is => 0 :: (u64B k ++ encName n ++ encSlots seen is)
  | (k, .lv u) :: is => 1 :: (u64B k ++ encLevel u ++ encSlots seen is)
  | (k, .lvs us) :: is => 2 :: (u64B k ++ encLevels us ++ encSlots seen is)
  | (k, .ex e) :: is => 3 :: (u64B k ++ (encExprM seen e).1 ++ encSlots (encExprM seen e).2 is)

/-- **A block's bytes**: `W`, `C`, the fills, a memo reset, the items. -/
def encBlk (c : Nat) (b : Blk) : List UInt8 :=
  u64B b.top ++ u64B c ++ encFills b.fills ++ 4 :: encSlots [] b.items

/-- The `And` pin's block bytes (empty if the layout does not support it; it does:
`andPinBlk_some`). -/
def andPinBytes : List UInt8 :=
  match blkCIs ConLeche.andPin with
  | some b => encBlk ConLeche.andPin.length b
  | none => []

/-! ## `rom_blk(pos)` -/

section prog
variable (rom : List UInt8)

/-- `rom_blk_fill(pos, b, n)`: the fills at `pos` into the area `EREC[b ‥ b + n)`; the position
after their end tag. -/
-- con-ron: ConRon/Arena/Intern.lean:62-65 ConRon.Arena.internCIList
def romBlkFill : FunDecl := lfn (pos, b, n) locals (t, k, w, r) {
  t := rom.c8[pos];
  if t == 8 { return pos + 1 };
  k := call rom_u64(pos + 1);
  w := call rom_u64(pos + 9);
  if n <= k { abort };
  if t == 6 { EREC.u64[b + k] := w } else if t == 7 { EREC.u64[b + k] := b + w } else { abort };
  r := call rom_blk_fill(pos + 17, b, n);
  return r
}

/-- `rom_blk_items(pos, b, n)`: the items at `pos`, each handle to its slot of the area; the
position after the end tag. -/
-- con-ron: ConRon/Arena/Intern.lean:62-65 ConRon.Arena.internCIList
def romBlkItems : FunDecl := lfn (pos, b, n) locals (t, k, h, q, r) {
  t := rom.c8[pos];
  if t == 5 { return pos + 1 };
  if t == 4 {
    CTL.u64[132] := 0;
    h := call rset_clear();
    r := call rom_blk_items(pos + 1, b, n);
    return r
  };
  k := call rom_u64(pos + 1);
  if n <= k { abort };
  if t == 0 { (h, q) := call rom_name(pos + 9) } else if t == 1 { (h, q) := call rom_level(pos + 9) }
  else if t == 2 { (h, q) := call rom_levels(pos + 9) } else if t == 3 { (h, q) := call rom_expr(pos + 9) }
  else { abort };
  EREC.u64[b + k] := h;
  r := call rom_blk_items(q, b, n);
  return r
}

/-- `rom_blk(pos)`: the block at `pos` as `EREC` records; `(b, C)`, the `EREC` slice of the
pointers to them. -/
-- con-ron: ConRon/Arena/Intern.lean:62-65 ConRon.Arena.internCIList
def romBlk : FunDecl := lfn (pos) locals (n, c, b, q) {
  n := call rom_u64(pos);
  c := call rom_u64(pos + 8);
  if n < c { abort };
  b := call erec_alloc(n);
  q := call rom_blk_fill(pos + 16, b, n);
  q := call rom_blk_items(q, b, n);
  return (b, c)
}

end prog

end L.Rom
