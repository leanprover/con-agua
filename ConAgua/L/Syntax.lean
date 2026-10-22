module

public section

/-!
# L: abstract syntax

L is the small first-order language the checker is written in (see `DESIGN.md`, "The language L").
Values are 64-bit words with wrapping arithmetic. A function has numbered locals, the first
`nparams` of which are its parameters. Memory is a fixed set of arrays: byte arrays (the input
buffer) and word arrays, each named by a static index, and a store of global word variables
(`GVar`), also named by static indices. Expressions have no side effects and
make no calls; a call is a statement. Conditions are a separate type, with short-circuit `&&`/`||`
so that a guard such as `i < len && b[i] == c` cannot read out of bounds.
-/

namespace L

/-- The value type: a 64-bit word. -/
abbrev Word := UInt64

/-- A local variable: an index into the current frame. -/
abbrev Var := Nat

/-- An array: a static index into the byte arrays or into the word arrays. -/
abbrev ArrId := Nat

/-- A function name. -/
abbrev FnName := String

/-- A global variable: a word in the global store (`Mem.glob`), named by a static number.
Declare one as a Lean constant, `abbrev HTOP : L.GVar := ⟨3⟩`, and use it in L code as `HTOP`
(read) and `HTOP := e` (write). Distinct globals need distinct numbers. -/
structure GVar where
  id : Nat
  deriving Repr, Inhabited

/-- Equality of globals is equality of their numbers (reduces under `decide`). -/
instance : DecidableEq GVar := fun a b =>
  decidable_of_iff (a.id = b.id) (by cases a; cases b; simp)

/-- Binary word operators. All wrap; shift counts are taken mod 64 (as on x64). `mulhi` is the
high word of the unsigned 128-bit product (`mul` is the low word). -/
inductive BinOp where
  | add | sub | mul | and | or | xor | shl | shr | mulhi
  deriving Repr, DecidableEq, Inhabited

/-- Comparisons. `ult`/`ule` are unsigned, `slt`/`sle` read the words as two's complement. -/
inductive Cmp where
  | eq | ne | ult | ule | slt | sle
  deriving Repr, DecidableEq, Inhabited

/-- Word expressions. Reading an array can fail (out of bounds); nothing else can. -/
inductive Expr where
  | const (w : Word)
  | var (x : Var)
  | bin (op : BinOp) (a b : Expr)
  /-- Byte `i` of byte array `a`, zero-extended. -/
  | ld8 (a : ArrId) (i : Expr)
  /-- Word `i` of word array `a`. -/
  | ld64 (a : ArrId) (i : Expr)
  /-- The length (in elements) of byte array `a`. -/
  | len8 (a : ArrId)
  /-- The length (in elements) of word array `a`. -/
  | len64 (a : ArrId)
  /-- A comparison as a word: `1` if it holds, else `0`. -/
  | cmpw (c : Cmp) (a b : Expr)
  /-- Byte `i` of the constant byte string `d` (read-only data, part of the program). -/
  | ldc (d : List UInt8) (i : Expr)
  /-- The global variable `g`. -/
  | glob (g : GVar)
  deriving Repr, DecidableEq, Inhabited

/-- Conditions. `and`/`or` short-circuit. -/
inductive Cond where
  | cmp (c : Cmp) (a b : Expr)
  | and (p q : Cond)
  | or (p q : Cond)
  | not (p : Cond)
  deriving Repr, DecidableEq, Inhabited

/-- Statements. -/
inductive Stmt where
  | skip
  /-- `x := e` -/
  | set (x : Var) (e : Expr)
  /-- `a.u8[i] := e` (the low byte of `e`) -/
  | st8 (a : ArrId) (i e : Expr)
  /-- `a.u64[i] := e` -/
  | st64 (a : ArrId) (i e : Expr)
  | seq (s t : Stmt)
  | ite (c : Cond) (s t : Stmt)
  /-- `while c { s }`. Each iteration costs one unit of fuel. -/
  | while (c : Cond) (s : Stmt)
  /-- Leave the innermost loop. -/
  | brk
  /-- Return from the function with the values `es` (usually one). -/
  | ret (es : List Expr)
  /-- `(x₀, x₁, …) := f(args)`: `xᵢ` gets the callee's `i`-th result, `0` if it returned fewer.
  A call costs one unit of fuel. -/
  | call (xs : List Var) (f : FnName) (args : List Expr)
  /-- Stop the whole program with an error (Rust's `panic!`, an overflow check, …). -/
  | abort
  /-- `g := e` for a global variable `g`. -/
  | gset (g : GVar) (e : Expr)
  deriving Repr, Inhabited

/-- A function: `nparams` parameters, `nlocals ≥ nparams` locals (params first, the rest start
at `0`), and a body. Falling off the end of the body (or a `break` outside a loop) returns no
values (so every result the caller reads is `0`). -/
structure FunDecl where
  nparams : Nat
  nlocals : Nat
  body : Stmt
  deriving Repr, Inhabited

/-- A program: its functions, by name. The first binding of a name wins. -/
abbrev Prog := List (FnName × FunDecl)

end L
