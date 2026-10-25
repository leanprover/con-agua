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

/-- **Tiered arrays** (lane tierarr). Tier `1` of word array `a` is word array `a + tierOff`;
an access with a run-time tier word `t` uses `tierA a t` (the tier is masked: `t & 1`). So a
program sees one array per tier, as con-ron's per-tier tables, and the compiler finds tier `1`'s
descriptor at a fixed distance from tier `0`'s. -/
@[expose] def tierOff : Nat := 256

/-- The array of tier `t` of the tiered array `a`. -/
@[expose] def tierA (a : ArrId) (t : UInt64) : ArrId := a + tierOff * (t &&& 1).toNat

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

/-- The byte source of a block read (lane blkcopy): byte array `a`, or
the constant bytes `d` (read-only data, part of the program, like `ldc`). -/
inductive BSrc where
  | arr (a : ArrId)
  | rom (d : List UInt8)
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
  /-- Word `i` of tier `t` of the tiered array `a`: word array `tierA a t` (`a` for `t & 1 = 0`,
  `a + tierOff` for `t & 1 = 1`; lane tierarr). -/
  | ld64t (a : ArrId) (t i : Expr)
  /-- The length of tier `t` of the tiered array `a`. -/
  | len64t (a : ArrId) (t : Expr)
  /-- The little-endian word of the bytes `i, …, i + 7` of `s` (lane blkcopy). -/
  | ld8x8 (s : BSrc) (i : Expr)
  deriving Repr, DecidableEq, Inhabited

/-- A word array as the destination or source of a block copy: array `a`, or tier `t` of the
tiered array `a` (`tierA a t`; `t` must be simple, as for `st64t`). -/
inductive WArr where
  | plain (a : ArrId)
  | tier (a : ArrId) (t : Expr)
  deriving Repr, DecidableEq, Inhabited

/-- The array id of a block operand (tier `0`'s for a tiered one). -/
@[expose] def WArr.arr : WArr → ArrId
  | .plain a => a
  | .tier a _ => a

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
  /-- Stop the whole program with an error (Rust's `panic!`, an overflow check, …) whose code is
  the value of `e` (`Err.abort`): the low two bits are the class (`0` other, `1` reject, `2`
  decline), the rest a reason. A bare `abort` is `abort 0`. -/
  | abort (e : Expr)
  /-- `g := e` for a global variable `g`. -/
  | gset (g : GVar) (e : Expr)
  /-- `a⟨t⟩.u64[i] := e`: word `i` of tier `t` of the tiered array `a`. -/
  | st64t (a : ArrId) (t i e : Expr)
  /-- `copy D[di ..] := S[si ..] for n`: words `si, …, si + n - 1` of `S` to `di, …` of `D`, in
  ascending order; bounds checked once, before anything is written (lane blkcopy). -/
  | copy64 (d : WArr) (di : Expr) (s : WArr) (si n : Expr)
  /-- `copy D[di ..] := S.u8[si ..] for n`: the bytes zero-extended into words. -/
  | copy8w (d : WArr) (di : Expr) (s : BSrc) (si n : Expr)
  /-- `x := scan S.u8[i .. e] until c`: the first `j` in `[i, e)` with `c[S[j]] ≠ 0`, else `e`
  (`c`: a 256-byte class table, constant data). -/
  | scan8 (x : Var) (s : BSrc) (i e : Expr) (c : List UInt8)
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

/-! ## Records (surface syntax)

A record layout lives in a word array: record `i` is the words `i * stride + f` for its fields'
offsets `f < stride`. `R[i].f` and `R[i].f := e` (`Notation.lean`) are ordinary word-array
accesses `R.arr.u64[R.at i f]`: nothing new in the semantics or the compiler. The address is
built by the named function `Record.at`, so a verification condition shows the named word
`Record.ad R j f` (`L/Records.lean`), and the lemmas there decide aliasing once and for all. -/

/-- A record layout: word array `arr`, `stride` words per record. Declare one as
`abbrev NODE : L.Record := ⟨5, 3⟩` and its fields as `abbrev NODE.tag : L.Field := ⟨0⟩`, … (offsets
below the stride, distinct). -/
structure Record where
  arr : ArrId
  stride : Nat
  deriving Repr, DecidableEq, Inhabited

/-- A field: its offset in the record. -/
structure Field where
  off : Nat
  deriving Repr, DecidableEq, Inhabited

/-- The word address of field `f` of record `j`. -/
@[expose] def Record.ad (R : Record) (j : Word) (f : Field) : Word := j * R.stride.toUInt64 + f.off.toUInt64

/-- The address expression of field `f` of record `i`: `i * stride + off`. -/
@[expose] def Record.at (R : Record) (i : Expr) (f : Field) : Expr :=
  .bin .add (.bin .mul i (.const R.stride.toUInt64)) (.const f.off.toUInt64)

end L
