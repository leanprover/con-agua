module

public import ConAgua.L.Syntax

@[expose] public section

/-!
# L: semantics

The meaning of an L program is a Lean function into the monad `M := StateT St (Except Err)`.
It is executable (`#eval`), and it is what `vcgen` steps through in a proof.

* `St` is the memory (`Mem`: the byte arrays and the word arrays) plus the current frame's locals.
* `Err` is every way a run can fail. None of them is a result: a result is a `Word` returned by
  the function, so "ran out of fuel" or "read out of bounds" can never read as "accept".
* Fuel. `exec p n` is the `n`-th Kleene iterate of the one-step interpreter `step p`:
  `exec p 0` throws `outOfFuel`, and `exec p (n+1) = step p (exec p n)`. `step p k` interprets a
  statement by structural recursion and hands the next loop iteration and every callee body to
  `k`. So fuel bounds the nesting of loop iterations and calls along a path. A partial-correctness
  triple (exception post `⊤`) is proved by induction on `n` and never mentions fuel.
-/

namespace L

/-- The memory: a fixed set of byte arrays and word arrays, indexed by `ArrId`. Their lengths are
fixed for the run (a growable vector is a fixed-capacity array plus a length kept in a word). -/
structure Mem where
  bytes : Array (Array UInt8) := #[]
  words : Array (Array Word) := #[]
  deriving Repr, Inhabited

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
  /-- An `abort` statement. -/
  | abort
  deriving Repr, DecidableEq, Inhabited

abbrev M := StateT St (Except Err)

/-- How a statement ends. -/
inductive Sig where
  | normal
  | brk
  | ret (v : Word)
  deriving Repr, DecidableEq, Inhabited

/-- The value returned by a block that ends with this signal and is followed by `return d`.
(Loop specs use it: their post is one equation `r.retOr d = …`, with no case split.) -/
def Sig.retOr : Sig → Word → Word
  | .normal, d => d
  | .brk, d => d
  | .ret v, _ => v

/-- The value a function returns when its body ends with this signal. -/
def Sig.retVal (r : Sig) : Word := r.retOr 0

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

/-! ## The interpreter -/

/-- Byte `i` of byte array `a`, zero-extended; `oob` out of bounds. (A `dite` rather than an
`Option`: the verification condition then holds the bound and the element `arr[i.toNat]`
directly; see docs/gaps/grind-getElem-map-toNat-timeout.lean.) -/
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

def lookupFn (p : Prog) (f : FnName) : M FunDecl :=
  match p.lookup f with
  | some fd => pure fd
  | none => throw (.noFun f)

/-- Call `fd` with arguments `vs`, running its body with `k`: a fresh frame, then the caller's
locals back. -/
def callFn (k : Stmt → M Sig) (fd : FunDecl) (vs : List Word) : M Word := do
  let s ← get
  set ({ s with loc := Locals.init vs } : St)
  let r ← k fd.body
  modify fun s' => { s' with loc := s.loc }
  return r.retVal

/-- Call function `f` of `p`, running its body with `k`. Callee specs are stated about
`invoke p (exec p n) f vs`, for every `n`. -/
def invoke (p : Prog) (k : Stmt → M Sig) (f : FnName) (vs : List Word) : M Word := do
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
  | .ret e => do return .ret (← evalE e)
  | .call x f args => do
    let vs ← evalArgs args
    let r ← invoke p k f vs
    setLoc x r
    return .normal
  | .abort => throw .abort

/-- The interpreter with `n` units of fuel. -/
def exec (p : Prog) : Nat → Stmt → M Sig
  | 0, _ => throw .outOfFuel
  | n + 1, s => step p (exec p n) s

/-- Run function `f` of `p` on memory `m`: its result and the final memory. -/
def run (p : Prog) (fuel : Nat) (f : FnName) (vs : List Word) (m : Mem) : Except Err (Word × Mem) :=
  ((invoke p (exec p fuel) f vs).run { mem := m, loc := Locals.init [] }).map fun (r, s) => (r, s.mem)

end L
