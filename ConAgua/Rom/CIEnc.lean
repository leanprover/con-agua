import ConAgua.Arena.RomExpr

/-!
# The constants of the ROM stubs, encoded with their structure (lane `integrate`)

The `checkDecl` arms call `rom_basis_decls(kind)`, `rom_basis_decls_a(kind)`, `rom_ci(id)`,
`rom_cv(id)` and `rom_expr_pin(id)` (`DeclArmsNat.lean`'s `romStubs`; `rom_expr_pin` is the stub
`rom_expr(id)`, renamed because `rom_expr` is the expression reader's name). Each stands for the
twin's intern of a con-leche constant and returns an `EREC` record of it (`EnvRec.lean`'s
`decCI`/`decCV`). The startup walk's item stream (`itemsAllPins`) interns the same constants but
carries no structure, so the ROM holds them a second time, **structured** (`romCIData`, in
`romData` between the reserved names and the item stream; `ConAgua/Rom/CIRead.lean` reads it):

* a table of `ciSlots` 8-byte offsets, relative to the region's start: slots `0‥4` the raw basis
  blocks (`BasisKind.decls`, kinds `eqK`, `natK`, `emptyK`, `falseK`, `quotK`), `5‥9` the
  annotated ones (`declsA`), `10‥17` the `rom_ci` constants (`romCiT`'s order), `18‥27` the
  `rom_cv` constant values (`romCvT`'s order), `28‥29` the `rom_expr_pin` expressions, `30` the
  pinned `And` block (`andPin`, `rom_and_pin`);
* the entries: a block is its length, then its constants at ONE expression memo (`internCIList`);
  a constant, a constant value or an expression is encoded at a fresh memo (`internCI`,
  `internCV`, `internExpr`).

Every number is 8 bytes (`u64B`); names, levels and expressions are the existing encodings
(`encName`, `encLevel`, `encExprM` with the twin's memo threaded as `seen`). The parts come in the
twin's intern order (`Arena/Frontend/Readback.lean`): the constant value (name, level
parameters, type), then the kind's parts. A constant: its kind (`decCI`'s numbering, `0‥5`; a
projection table has no encoding: none of these constants is one), the constant value, then

* defn: the value, the hint kind (`0` opaque, `1` abbrev, `2` regular) and its height;
* ind: `eta`, `etaParams`, `etaFields`, `unitlike`, `unitParams`, `ruleK`, `nparams`, the `sortZ`
  tag (`0` never, `1` ifAllZero), then the names `etaCtor`, `all` (count, names), `ctors` (count,
  names), and the `sortZ` names (count, names; the twin keeps them as values and interns none, the
  reader interns them last: for the pinned `Quot`, the one name `u` is a level parameter already
  interned);
* ctor: `numParams`, `numFields`;
* rec: `majorIdx`, `numParams`, the rule count, per rule: `ctor`, `nfields`, `ctorParams`, `k`,
  `eta`, the fire tag (`0` plain, `1` nested: the level count, the levels, the pin count, the pins
  at the block's memo), `rhs`.
-/

open ConRon.Arena

namespace L.Rom

open L.Arena

/-- A name list: its length, then the names. -/
def encNameL (ns : List ConLeche.Name) : List UInt8 := u64B ns.length ++ encNames ns

/-- Expressions at one memo (threaded `seen`); the bytes and the list after. -/
def encExprsM (seen : List ConLeche.Expr) : List ConLeche.Expr → List UInt8 × List ConLeche.Expr
  | [] => ([], seen)
  | e :: es =>
    let r := encExprM seen e
    let r' := encExprsM r.2 es
    (r.1 ++ r'.1, r'.2)

/-- A constant value at the memo `seen`. -/
def encCV (seen : List ConLeche.Expr) (cv : ConLeche.ConstantVal) : List UInt8 × List ConLeche.Expr :=
  let r := encExprM seen cv.type
  (encName cv.name ++ encNameL cv.levelParams ++ r.1, r.2)

/-- A flag as a word. -/
def bw (b : Bool) : List UInt8 := u64B (if b then 1 else 0)

/-- An inductive's capabilities (no expression). -/
def encCaps (c : ConLeche.IndCaps) : List UInt8 :=
  let (tag, zs) := match c.sortZ with
    | .never => (0, [])
    | .ifAllZero ns => (1, ns)
  bw c.eta ++ u64B c.etaParams ++ u64B c.etaFields ++ bw c.unitlike ++ u64B c.unitParams ++
    bw c.ruleK ++ u64B c.nparams ++ u64B tag ++ encName c.etaCtor ++ encNameL c.all ++
    encNameL c.ctors ++ encNameL zs

/-- A recursor rule at the memo `seen`. -/
def encRule (seen : List ConLeche.Expr) (rl : ConLeche.RecRule) : List UInt8 × List ConLeche.Expr :=
  let hd := encName rl.ctor ++ u64B rl.nfields ++ u64B rl.ctorParams ++ bw rl.k ++ bw rl.eta
  match rl.fire with
  | .plain =>
    let r := encExprM seen rl.rhs
    (hd ++ u64B 0 ++ r.1, r.2)
  | .nested lvls pins =>
    let p := encExprsM seen pins
    let r := encExprM p.2 rl.rhs
    (hd ++ u64B 1 ++ encLevels lvls ++ u64B pins.length ++ p.1 ++ r.1, r.2)

/-- Rules at one memo. -/
def encRules (seen : List ConLeche.Expr) : List ConLeche.RecRule → List UInt8 × List ConLeche.Expr
  | [] => ([], seen)
  | rl :: rs =>
    let r := encRule seen rl
    let r' := encRules r.2 rs
    (r.1 ++ r'.1, r'.2)

/-- A constant at the memo `seen`. -/
def encCI (seen : List ConLeche.Expr) : ConLeche.ConstantInfo → List UInt8 × List ConLeche.Expr
  | .axiomInfo v => let r := encCV seen v; (u64B 0 ++ r.1, r.2)
  | .defnInfo v e h =>
    let r := encCV seen v
    let x := encExprM r.2 e
    let hb := match h with
      | .opaque => u64B 0 ++ u64B 0
      | .abbrev => u64B 1 ++ u64B 0
      | .regular n => u64B 2 ++ u64B n
    (u64B 1 ++ r.1 ++ x.1 ++ hb, x.2)
  | .thmInfo v => let r := encCV seen v; (u64B 2 ++ r.1, r.2)
  | .indInfo v c => let r := encCV seen v; (u64B 3 ++ r.1 ++ encCaps c, r.2)
  | .ctorInfo v nP nF => let r := encCV seen v; (u64B 4 ++ r.1 ++ u64B nP ++ u64B nF, r.2)
  | .recInfo v mI rP rs =>
    let r := encCV seen v
    let x := encRules r.2 rs
    (u64B 5 ++ r.1 ++ u64B mI ++ u64B rP ++ u64B rs.length ++ x.1, x.2)

/-- Constants at one memo. -/
def encCIsM (seen : List ConLeche.Expr) : List ConLeche.ConstantInfo → List UInt8 × List ConLeche.Expr
  | [] => ([], seen)
  | c :: cs =>
    let r := encCI seen c
    let r' := encCIsM r.2 cs
    (r.1 ++ r'.1, r'.2)

/-- A block: its length, then its constants at one fresh memo (`internCIList`). -/
def encBlock (cs : List ConLeche.ConstantInfo) : List UInt8 := u64B cs.length ++ (encCIsM [] cs).1

/-- The basis kinds by `rom_basis_decls`' word. -/
def basisKinds : List ConLeche.BasisKind := [.eqK, .natK, .emptyK, .falseK, .quotK]

/-- `rom_ci`'s constants by id (`romCiT`). -/
def romCiVals : List ConLeche.ConstantInfo :=
  [ConLeche.eqA, ConLeche.natA, ConLeche.iffA, ConLeche.iffIntroA, ConLeche.iffRecA,
   ConLeche.nonemptyA, ConLeche.nonemptyIntroA, ConLeche.nonemptyRecA]

/-- `rom_cv`'s constant values by id (`romCvT`). -/
def romCvVals : List ConLeche.ConstantVal :=
  [ConLeche.propextA, ConLeche.choiceA, ConLeche.trueCvA, ConLeche.trueIntroCvA,
   ConLeche.trustCompilerA, ConLeche.boolCvA, ConLeche.reduceNatCvA, ConLeche.reduceBoolCvA,
   ConLeche.ofReduceNatA, ConLeche.ofReduceBoolA]

/-- `rom_expr_pin`'s expressions by id (`romExprT`). -/
def romExprVals : List ConLeche.Expr := [ConLeche.reduceNatDeclPin, ConLeche.reduceBoolDeclPin]

/-- The entries, in slot order. -/
def ciEntries : List (List UInt8) :=
  basisKinds.map (fun k => encBlock (ConLeche.BasisKind.decls k)) ++
  basisKinds.map (fun k => encBlock (ConLeche.BasisKind.declsA k)) ++
  romCiVals.map (fun c => (encCI [] c).1) ++
  romCvVals.map (fun v => (encCV [] v).1) ++
  romExprVals.map (fun e => (encExprM [] e).1) ++
  [encBlock ConLeche.andPin]

/-- The number of slots. -/
def ciSlots : Nat := 31

/-- Slot offsets (relative to the region's start), after a table of `n` slots. -/
def ciTable (start : Nat) : List (List UInt8) → List UInt8
  | [] => []
  | e :: es => u64B start ++ ciTable (start + e.length) es

/-- **The structured region**: the offset table, then the entries. -/
def romCIData : List UInt8 := ciTable (8 * ciSlots) ciEntries ++ ciEntries.flatten

end L.Rom
