module

public import ConAgua.L.Syntax

@[expose] public section

/-!
# L: semantics

The meaning of an L program is a Lean function into the monad `M := StateT St (Except Err)`.
It is executable (`#eval`), and it is what `vcgen` steps through in a proof.

* `St` is the memory (`Mem`: the byte arrays and the word arrays) plus the current frame's locals.
* `Err` is every way a run can fail. None of them is a result: a result is a list of words
  returned by the function, so "ran out of fuel" or "read out of bounds" can never read as "accept".
* Fuel. `exec p n` is the `n`-th Kleene iterate of the one-step interpreter `step p`:
  `exec p 0` throws `outOfFuel`, and `exec p (n+1) = step p (exec p n)`. `step p k` interprets a
  statement by structural recursion and hands the next loop iteration and every callee body to
  `k`. So fuel bounds the nesting of loop iterations and calls along a path. A partial-correctness
  triple (exception post `⊤`) is proved by induction on `n` and never mentions fuel.
-/

namespace L

/-- The memory: a fixed set of byte arrays and word arrays, indexed by `ArrId`, and the global
variables. The arrays' lengths are fixed for the run (a growable vector is a fixed-capacity array
plus a length kept in a word). Every global variable has a value (`0` unless written). -/
structure Mem where
  bytes : Array (Array UInt8) := #[]
  words : Array (Array Word) := #[]
  glob : GVar → Word := fun _ => 0
  deriving Inhabited

/-- The locals of one frame. -/
abbrev Locals := Var → Word

/-- The locals of a new frame: the arguments, then zeros. -/
def Locals.init (vs : List Word) : Locals := fun x => vs.getD x 0

/-- The interpreter state. -/
structure St where
  mem : Mem
  loc : Locals

/-- The ways a run can fail. -/
inductive Err where
  /-- The fuel (nesting of loop iterations and calls) ran out. -/
  | outOfFuel
  /-- An array access out of bounds, or to an array that does not exist. -/
  | oob
  /-- A call to an undefined function. -/
  | noFun (f : FnName)
  /-- An `abort e` statement, with the value `k` of `e`: the error's code (`Stmt.abort`). -/
  | abort (k : Word)
  deriving Repr, DecidableEq, Inhabited

/-- The code an error reports (the compiled program's `rax` on its error exit): an abort's own
value, `0` for every other error. -/
def Err.code : Err → Word
  | .abort k => k
  | _ => 0

/-- An error that reports code `0` and is not running out of fuel (the compiled program's
`ca_error` exit). -/
def Err.plain (e : Err) : Prop := e ≠ .outOfFuel ∧ e.code = 0

@[simp] theorem Err.plain_oob : Err.plain .oob := ⟨nofun, rfl⟩
@[simp] theorem Err.plain_noFun (f : FnName) : Err.plain (.noFun f) := ⟨nofun, rfl⟩
@[simp] theorem Err.not_plain_outOfFuel : ¬ Err.plain .outOfFuel := fun h => h.1 rfl
@[simp] theorem Err.plain_abort (k : Word) : Err.plain (.abort k) ↔ k = 0 :=
  ⟨fun h => h.2, fun h => ⟨nofun, h⟩⟩

abbrev M := StateT St (Except Err)

/-- How a statement ends. -/
inductive Sig where
  | normal
  | brk
  | ret (vs : List Word)
  deriving Repr, DecidableEq, Inhabited

/-- The values returned by a block that ends with this signal and is followed by `return d`.
(Loop specs use it: their post is one equation `r.retOr [d] = […]`, with no case split.) -/
def Sig.retOr : Sig → List Word → List Word
  | .normal, d => d
  | .brk, d => d
  | .ret vs, _ => vs

/-- The values a function returns when its body ends with this signal. -/
def Sig.retVal (r : Sig) : List Word := r.retOr []

def BinOp.eval : BinOp → Word → Word → Word
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .and, a, b => a &&& b
  | .or, a, b => a ||| b
  | .xor, a, b => a ^^^ b
  | .shl, a, b => a <<< b
  | .shr, a, b => a >>> b
  | .mulhi, a, b => UInt64.ofNat (a.toNat * b.toNat / 2 ^ 64)

def Cmp.eval : Cmp → Word → Word → Bool
  | .eq, a, b => a == b
  | .ne, a, b => a != b
  | .ult, a, b => decide (a < b)
  | .ule, a, b => decide (a ≤ b)
  | .slt, a, b => decide (a.toInt64 < b.toInt64)
  | .sle, a, b => decide (a.toInt64 ≤ b.toInt64)

/-- A comparison as a word. -/
def Cmp.evalW (c : Cmp) (a b : Word) : Word := if c.eval a b then 1 else 0

/-! ## Memory access -/

/-- Byte array `a`; an array that does not exist reads as empty. -/
def Mem.arr8 (m : Mem) (a : ArrId) : Array UInt8 := m.bytes.getD a #[]

/-- Word array `a`; an array that does not exist reads as empty. -/
def Mem.arr64 (m : Mem) (a : ArrId) : Array Word := m.words.getD a #[]

def Mem.len8 (m : Mem) (a : ArrId) : Word := UInt64.ofNat (m.arr8 a).size

def Mem.len64 (m : Mem) (a : ArrId) : Word := UInt64.ofNat (m.arr64 a).size

/-- Byte array `a` with byte `i` set to the low byte of `v` (no change out of bounds). -/
def Mem.set8 (m : Mem) (a : ArrId) (i v : Word) : Mem :=
  { m with bytes := m.bytes.set! a ((m.arr8 a).set! i.toNat v.toUInt8) }

/-- Word array `a` with word `i` set to `v` (no change out of bounds). -/
def Mem.set64 (m : Mem) (a : ArrId) (i v : Word) : Mem :=
  { m with words := m.words.set! a ((m.arr64 a).set! i.toNat v) }

/-- Global `g` set to `v`. -/
def Mem.setG (m : Mem) (g : GVar) (v : Word) : Mem :=
  { m with glob := fun h => if h = g then v else m.glob h }

/-! ## Blocks (lane blkcopy) -/

/-- The bytes of a byte source. -/
def Mem.src8 (m : Mem) : BSrc → Array UInt8
  | .arr a => m.arr8 a
  | .rom d => d.toArray

/-- The little-endian word of the bytes `k, …, k + 7` of `b` (as the machine's 8-byte load
reads them: Kraken's `Nat.ofBytes`). -/
def le64 (b : Array UInt8) (k : Nat) : Word :=
  UInt64.ofNat (((List.range 8).map fun j => b[k + j]!).foldr (fun x acc => acc * 256 + x.toNat) 0)

/-- `D[di + j] := S[si + j]` for `j < n`, ascending (each word read after the writes before it). -/
def Mem.copy64 (m : Mem) (d : ArrId) (di : Word) (s : ArrId) (si : Word) : Nat → Mem
  | 0 => m
  | n + 1 => (m.set64 d di ((m.arr64 s)[si.toNat]!)).copy64 d (di + 1) s (si + 1) n

/-- `D[di + j] := b[si + j]` (zero-extended) for `j < n`, ascending. -/
def Mem.copy8w (m : Mem) (d : ArrId) (di : Word) (b : Array UInt8) (si : Word) : Nat → Mem
  | 0 => m
  | n + 1 => (m.set64 d di (b[si.toNat]!).toUInt64).copy8w d (di + 1) b (si + 1) n

/-- The first `j` in `[i, e)` with `c[b[j]] ≠ 0`, else `e` (for `i ≤ e`). -/
def scanN (b : Array UInt8) (c : List UInt8) (i e : Nat) : Nat :=
  if i < e then (if c[(b[i]!).toNat]! ≠ 0 then i else scanN b c (i + 1) e) else i
termination_by e - i

/-! ## The interpreter -/

/-- Byte `i` of byte array `a`, zero-extended; `oob` out of bounds. (A `dite` rather than an
`Option`: the verification condition then holds the bound and the element `arr[i.toNat]`
directly, which is the shape the load proofs are written against.) -/
def ld8 (a : ArrId) (i : Word) : M Word := do
  let m := (← get).mem
  if h : i.toNat < (m.arr8 a).size then return (m.arr8 a)[i.toNat].toUInt64 else throw .oob

/-- Word `i` of word array `a`; `oob` out of bounds. -/
def ld64 (a : ArrId) (i : Word) : M Word := do
  let m := (← get).mem
  if h : i.toNat < (m.arr64 a).size then return (m.arr64 a)[i.toNat] else throw .oob

/-- Byte `i` of the constant byte string `d`, zero-extended; `oob` out of bounds. -/
def ldc (d : List UInt8) (i : Word) : M Word :=
  if h : i.toNat < d.length then return d[i.toNat].toUInt64 else throw .oob

/-- The little-endian word at byte `i` of `s`; `oob` unless `i + 8` bytes exist. -/
def ld8x8 (s : BSrc) (i : Word) : M Word := do
  let b := (← get).mem.src8 s
  if i.toNat + 8 ≤ b.size then return le64 b i.toNat else throw .oob

/-- Store the low byte of `v` at byte `i` of byte array `a`; `oob` out of bounds. -/
def st8 (a : ArrId) (i v : Word) : M Unit := do
  let s ← get
  if i.toNat < (s.mem.arr8 a).size then set { s with mem := s.mem.set8 a i v } else throw .oob

/-- Store `v` at word `i` of word array `a`; `oob` out of bounds. -/
def st64 (a : ArrId) (i v : Word) : M Unit := do
  let s ← get
  if i.toNat < (s.mem.arr64 a).size then set { s with mem := s.mem.set64 a i v } else throw .oob

def evalE : Expr → M Word
  | .const w => pure w
  | .var x => do return (← get).loc x
  | .bin op a b => do
    let x ← evalE a
    let y ← evalE b
    return op.eval x y
  | .ld8 a i => do ld8 a (← evalE i)
  | .ld64 a i => do ld64 a (← evalE i)
  | .len8 a => do return (← get).mem.len8 a
  | .len64 a => do return (← get).mem.len64 a
  | .cmpw c a b => do
    let x ← evalE a
    let y ← evalE b
    return c.evalW x y
  | .ldc d i => do ldc d (← evalE i)
  | .glob g => do return (← get).mem.glob g
  | .ld64t a t i => do
    let u ← evalE t
    ld64 (tierA a u) (← evalE i)
  | .len64t a t => do
    let u ← evalE t
    return (← get).mem.len64 (tierA a u)
  | .ld8x8 s i => do ld8x8 s (← evalE i)

/-- The array a block operand names. -/
def warr : WArr → M ArrId
  | .plain a => pure a
  | .tier a t => do return tierA a (← evalE t)

def evalC : Cond → M Bool
  | .cmp c a b => do
    let x ← evalE a
    let y ← evalE b
    return c.eval x y
  | .and p q => do if (← evalC p) then evalC q else return false
  | .or p q => do if (← evalC p) then return true else evalC q
  | .not p => do return !(← evalC p)

def evalArgs : List Expr → M (List Word)
  | [] => pure []
  | e :: es => do
    let v ← evalE e
    let vs ← evalArgs es
    return v :: vs

/-- `x := v` in the current frame. -/
def St.setLoc (s : St) (x : Var) (v : Word) : St :=
  { s with loc := fun y => if y = x then v else s.loc y }

def setLoc (x : Var) (v : Word) : M Unit := modify (·.setLoc x v)

/-- `g := v` for a global `g`. -/
def St.setG (s : St) (g : GVar) (v : Word) : St := { s with mem := s.mem.setG g v }

def setG (g : GVar) (v : Word) : M Unit := modify (·.setG g v)

/-- `xᵢ := vs[i]` (`0` past the end of `vs`), in order. -/
def St.setLocs (s : St) : List Var → List Word → St
  | [], _ => s
  | x :: xs, vs => (s.setLoc x (vs.headD 0)).setLocs xs vs.tail

def setLocs (xs : List Var) (vs : List Word) : M Unit := modify (·.setLocs xs vs)

def lookupFn (p : Prog) (f : FnName) : M FunDecl :=
  match p.lookup f with
  | some fd => pure fd
  | none => throw (.noFun f)

/-- Call `fd` with arguments `vs`, running its body with `k`: a fresh frame, then the caller's
locals back. -/
def callFn (k : Stmt → M Sig) (fd : FunDecl) (vs : List Word) : M (List Word) := do
  let s ← get
  set ({ s with loc := Locals.init vs } : St)
  let r ← k fd.body
  modify fun s' => { s' with loc := s.loc }
  return r.retVal

/-- Call function `f` of `p`, running its body with `k`. Callee specs are stated about
`invoke p (exec p n) f vs`, for every `n`. -/
def invoke (p : Prog) (k : Stmt → M Sig) (f : FnName) (vs : List Word) : M (List Word) := do
  let fd ← lookupFn p f
  callFn k fd vs

/-- One step of the interpreter: structural in the statement; the next loop iteration and every
callee body go to `k`. -/
def step (p : Prog) (k : Stmt → M Sig) : Stmt → M Sig
  | .skip => pure .normal
  | .set x e => do
    let v ← evalE e
    setLoc x v
    return .normal
  | .st8 a i e => do
    let j ← evalE i
    let v ← evalE e
    st8 a j v
    return .normal
  | .st64 a i e => do
    let j ← evalE i
    let v ← evalE e
    st64 a j v
    return .normal
  | .seq s t => do
    match ← step p k s with
    | .normal => step p k t
    | r => return r
  | .ite c s t => do
    if (← evalC c) then step p k s else step p k t
  | .while c s => do
    if (← evalC c) then
      match ← step p k s with
      | .normal => k (.while c s)
      | .brk => return .normal
      | .ret v => return .ret v
    else return .normal
  | .brk => return .brk
  | .ret es => do return .ret (← evalArgs es)
  | .call xs f args => do
    let vs ← evalArgs args
    let rs ← invoke p k f vs
    setLocs xs rs
    return .normal
  | .abort e => do throw (.abort (← evalE e))
  | .gset g e => do
    let v ← evalE e
    setG g v
    return .normal
  | .st64t a t i e => do
    let u ← evalE t
    let j ← evalE i
    let v ← evalE e
    st64 (tierA a u) j v
    return .normal
  | .copy64 d di s si n => do
    let da ← warr d
    let i ← evalE di
    let sa ← warr s
    let j ← evalE si
    let k ← evalE n
    let st ← get
    if i.toNat + k.toNat ≤ (st.mem.arr64 da).size ∧ j.toNat + k.toNat ≤ (st.mem.arr64 sa).size then
      set { st with mem := st.mem.copy64 da i sa j k.toNat }
      return .normal
    else throw .oob
  | .copy8w d di s si n => do
    let da ← warr d
    let i ← evalE di
    let j ← evalE si
    let k ← evalE n
    let st ← get
    if i.toNat + k.toNat ≤ (st.mem.arr64 da).size ∧ j.toNat + k.toNat ≤ (st.mem.src8 s).size then
      set { st with mem := st.mem.copy8w da i (st.mem.src8 s) j k.toNat }
      return .normal
    else throw .oob
  | .scan8 x s i e c => do
    let vi ← evalE i
    let ve ← evalE e
    let b := (← get).mem.src8 s
    if vi ≤ ve ∧ ve.toNat ≤ b.size then
      setLoc x (UInt64.ofNat (scanN b c vi.toNat ve.toNat))
      return .normal
    else throw .oob

/-- The interpreter with `n` units of fuel. -/
def exec (p : Prog) : Nat → Stmt → M Sig
  | 0, _ => throw .outOfFuel
  | n + 1, s => step p (exec p n) s

/-- Run function `f` of `p` on memory `m`: its results and the final memory. -/
def run (p : Prog) (fuel : Nat) (f : FnName) (vs : List Word) (m : Mem) : Except Err (List Word × Mem) :=
  ((invoke p (exec p fuel) f vs).run { mem := m, loc := Locals.init [] }).map fun (r, s) => (r, s.mem)

end L
