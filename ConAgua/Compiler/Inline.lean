module

public import ConAgua.Compiler.WF

@[expose] public section

/-!
# Inlining small leaves (an L → L pass before the code generator)

`inlineProg S R t p` replaces, in every function of `p`, each call `xs := g(args)` of a **leaf**
`g` (a function whose body makes no call) of at most `S` nodes by `g`'s body, `R` times over
(round `r + 1` sees the leaves that round `r` made). The body runs on the caller's frame, its
locals shifted past the caller's (`Stmt.sh`), and its exits become assignments to `xs`
(`conv`):

* `zs := 0` for the callee's locals that it may read before it assigns them (`needZero`, as the
  compiler zeroes them), then `ps := args` for its parameters, then the converted body;
* a `return es` becomes `xs := es` (the missing results `0`), a `break` outside a loop
  `xs := 0, …`, and falling off the end too; the code after an exit is not reached: the
  conversion passes the rest of the body as a continuation, and an `if` with an exit in one branch
  only gets the continuation in its other branch.

A call is inlined only if the conversion succeeds (an `if` with exits in both branches that does
not always exit, a `return` in a loop, or a call in the callee is not converted), the callee gets
as many arguments as it has parameters, and the caller's frame stays small enough for the
compiler (`frameWords`). Every inlined call of a function uses the same region of the caller's
frame, past the caller's locals: the callee's locals are dead after the call, and those it reads
before assigning are zeroed.

The callees are found through `t`, a tree from a function's name (`nameCode`) to its position in
`p` (`Prog.idxTree`), so that the kernel, which evaluates this pass when it checks the compiled
checker, compares numbers, not strings.

Correctness, `ConAgua/Compiler/InlineCorrect.lean`: a run of the inlined program that does not
run out of fuel is a run of `p` with the same result and memory, with `R` more units of fuel.
-/

namespace L.Compiler

/-! ## Shifting locals -/

/-- `e` with every local `x` renamed to `x + o`. -/
def Expr.sh (o : Nat) : Expr → Expr
  | .const w => .const w
  | .var x => .var (x + o)
  | .bin op a b => .bin op (Expr.sh o a) (Expr.sh o b)
  | .ld8 a i => .ld8 a (Expr.sh o i)
  | .ld64 a i => .ld64 a (Expr.sh o i)
  | .len8 a => .len8 a
  | .len64 a => .len64 a
  | .cmpw c a b => .cmpw c (Expr.sh o a) (Expr.sh o b)
  | .ldc d i => .ldc d (Expr.sh o i)
  | .glob g => .glob g
  | .ld64t a t i => .ld64t a (Expr.sh o t) (Expr.sh o i)
  | .len64t a t => .len64t a (Expr.sh o t)
  | .ld8x8 s i => .ld8x8 s (Expr.sh o i)
  | .ld32t a t i => .ld32t a (Expr.sh o t) (Expr.sh o i)
  | .ld32h a t i h => .ld32h a (Expr.sh o t) (Expr.sh o i) h

def WArr.sh (o : Nat) : WArr → WArr
  | .plain a => .plain a
  | .tier a t => .tier a (Expr.sh o t)

def Cond.sh (o : Nat) : Cond → Cond
  | .cmp c a b => .cmp c (Expr.sh o a) (Expr.sh o b)
  | .and p q => .and (Cond.sh o p) (Cond.sh o q)
  | .or p q => .or (Cond.sh o p) (Cond.sh o q)
  | .not p => .not (Cond.sh o p)

/-- A call-free statement with its locals shifted by `o`; `none` if it has a call, a `return`, or
(outside a loop: `inLoop = false`) a `break`. -/
def Stmt.sh (o : Nat) (inLoop : Bool) : Stmt → Option Stmt
  | .skip => some .skip
  | .set x e => some (.set (x + o) (Expr.sh o e))
  | .st8 a i e => some (.st8 a (Expr.sh o i) (Expr.sh o e))
  | .st64 a i e => some (.st64 a (Expr.sh o i) (Expr.sh o e))
  | .seq s t => do some (.seq (← Stmt.sh o inLoop s) (← Stmt.sh o inLoop t))
  | .ite c s t => do some (.ite (Cond.sh o c) (← Stmt.sh o inLoop s) (← Stmt.sh o inLoop t))
  | .while c s => do some (.while (Cond.sh o c) (← Stmt.sh o true s))
  | .brk => if inLoop then some .brk else none
  | .ret _ => none
  | .call .. => none
  | .abort e => some (.abort (Expr.sh o e))
  | .gset g e => some (.gset g (Expr.sh o e))
  | .st64t a t i e => some (.st64t a (Expr.sh o t) (Expr.sh o i) (Expr.sh o e))
  | .copy64 d di s si n => some (.copy64 (WArr.sh o d) (Expr.sh o di) (WArr.sh o s) (Expr.sh o si) (Expr.sh o n))
  | .copy8w d di s si n => some (.copy8w (WArr.sh o d) (Expr.sh o di) s (Expr.sh o si) (Expr.sh o n))
  | .scan8 x s i e c => some (.scan8 (x + o) s (Expr.sh o i) (Expr.sh o e) c)
  | .st32t a t i e => some (.st32t a (Expr.sh o t) (Expr.sh o i) (Expr.sh o e))

/-! ## Exits as assignments -/

/-- An expression whose evaluation cannot fail (no array read). -/
def Expr.safe : Expr → Bool
  | .const _ | .var _ | .len8 _ | .len64 _ | .glob _ => true
  | .bin _ a b | .cmpw _ a b => Expr.safe a && Expr.safe b
  | _ => false

/-- `xs := es`, in order, `0` for the missing values; `none` if `es` has more values than `xs` and
one of the extra ones could fail (a `return` evaluates all its values). -/
def retAssign : List Var → List Expr → Option Stmt
  | [], es => if es.all Expr.safe then some .skip else none
  | x :: xs, [] => do some (.seq (.set x (.const 0)) (← retAssign xs []))
  | x :: xs, e :: es => do some (.seq (.set x e) (← retAssign xs es))

/-- The statement always ends in an exit (`return`, `abort`, `break`), never normally. -/
def Stmt.allExit : Stmt → Bool
  | .ret _ | .abort _ | .brk => true
  | .seq s t => Stmt.allExit s || Stmt.allExit t
  | .ite _ s t => Stmt.allExit s && Stmt.allExit t
  | _ => false

/-- The callee's statement `u`, at the top level of its body (not in a loop), shifted by `o`, with
its exits turned into `xs := …` and its normal end continued by `k` (already converted). -/
def conv (o : Nat) (xs : List Var) : Stmt → Stmt → Option Stmt
  | .skip, k => some (.seq .skip k)
  | .set x e, k => some (.seq (.set (x + o) (Expr.sh o e)) k)
  | .st8 a i e, k => some (.seq (.st8 a (Expr.sh o i) (Expr.sh o e)) k)
  | .st64 a i e, k => some (.seq (.st64 a (Expr.sh o i) (Expr.sh o e)) k)
  | .seq a b, k => do conv o xs a (← conv o xs b k)
  | .ite c s t, k =>
    if Stmt.allExit s then do some (.ite (Cond.sh o c) (← conv o xs s .skip) (← conv o xs t k))
    else if Stmt.allExit t then do some (.ite (Cond.sh o c) (← conv o xs s k) (← conv o xs t .skip))
    else do some (.seq (← Stmt.sh o false (.ite c s t)) k)
  | .while c s, k => do some (.seq (.while (Cond.sh o c) (← Stmt.sh o true s)) k)
  | .brk, _ => retAssign xs []
  | .ret es, _ => retAssign xs (es.map (Expr.sh o))
  | .call .., _ => none
  | .abort e, _ => some (.abort (Expr.sh o e))
  | .gset g e, k => some (.seq (.gset g (Expr.sh o e)) k)
  | .st64t a t i e, k => some (.seq (.st64t a (Expr.sh o t) (Expr.sh o i) (Expr.sh o e)) k)
  | .copy64 d di s si n, k =>
    some (.seq (.copy64 (WArr.sh o d) (Expr.sh o di) (WArr.sh o s) (Expr.sh o si) (Expr.sh o n)) k)
  | .copy8w d di s si n, k =>
    some (.seq (.copy8w (WArr.sh o d) (Expr.sh o di) s (Expr.sh o si) (Expr.sh o n)) k)
  | .scan8 x s i e c, k => some (.seq (.scan8 (x + o) s (Expr.sh o i) (Expr.sh o e) c) k)
  | .st32t a t i e, k => some (.seq (.st32t a (Expr.sh o t) (Expr.sh o i) (Expr.sh o e)) k)

/-- `x + o := 0` for the locals `x` of `zs`. -/
def zeroS (o : Nat) : List Var → Stmt
  | [] => .skip
  | x :: zs => .seq (.set (x + o) (.const 0)) (zeroS o zs)

/-- `i + o := a₀, i + 1 + o := a₁, …`. -/
def paramS (o : Nat) : Nat → List Expr → Stmt
  | _, [] => .skip
  | i, a :: as => .seq (.set (i + o) a) (paramS o (i + 1) as)

/-- The code of the call `xs := g(args)` with `g`'s declaration `fd` inlined at offset `o`. -/
def inlBody (o : Nat) (fd : FunDecl) (xs : List Var) (args : List Expr) : Option Stmt :=
  if args.length = fd.nparams then do
    let b ← conv o xs fd.body (← retAssign xs [])
    some (.seq (zeroS o (needZero fd.nparams fd.body)) (.seq (paramS o 0 args) b))
  else none

/-! ## The pass -/

/-- A bound on the locals a statement names: every one is below it. -/
def Expr.vb : Expr → Nat
  | .var x => x + 1
  | .bin _ a b | .cmpw _ a b | .ld64t _ a b | .ld32t _ a b | .ld32h _ a b _ => max (Expr.vb a) (Expr.vb b)
  | .ld8 _ i | .ld64 _ i | .ldc _ i | .len64t _ i | .ld8x8 _ i => Expr.vb i
  | _ => 0

def WArr.vb : WArr → Nat
  | .plain _ => 0
  | .tier _ t => Expr.vb t

def Cond.vb : Cond → Nat
  | .cmp _ a b => max (Expr.vb a) (Expr.vb b)
  | .and p q | .or p q => max (Cond.vb p) (Cond.vb q)
  | .not p => Cond.vb p

def Exprs.vb : List Expr → Nat
  | [] => 0
  | e :: es => max (Expr.vb e) (Exprs.vb es)

def Vars.vb : List Var → Nat
  | [] => 0
  | x :: xs => max (x + 1) (Vars.vb xs)

def Stmt.vb : Stmt → Nat
  | .skip | .brk => 0
  | .set x e => max (x + 1) (Expr.vb e)
  | .st8 _ i e | .st64 _ i e => max (Expr.vb i) (Expr.vb e)
  | .seq s t => max (Stmt.vb s) (Stmt.vb t)
  | .ite c s t => max (Cond.vb c) (max (Stmt.vb s) (Stmt.vb t))
  | .while c s => max (Cond.vb c) (Stmt.vb s)
  | .ret es => Exprs.vb es
  | .call xs _ args => max (Vars.vb xs) (Exprs.vb args)
  | .abort e | .gset _ e => Expr.vb e
  | .st64t _ t i e | .st32t _ t i e => max (Expr.vb t) (max (Expr.vb i) (Expr.vb e))
  | .copy64 d di s si n => max (WArr.vb d) (max (Expr.vb di) (max (WArr.vb s) (max (Expr.vb si) (Expr.vb n))))
  | .copy8w d di _ si n => max (WArr.vb d) (max (Expr.vb di) (max (Expr.vb si) (Expr.vb n)))
  | .scan8 x _ i e _ => max (x + 1) (max (Expr.vb i) (Expr.vb e))

/-- The size of an expression, a condition, a statement, in nodes (the inlining threshold). -/
def Expr.size : Expr → Nat
  | .bin _ a b | .cmpw _ a b | .ld64t _ a b | .ld32t _ a b | .ld32h _ a b _ => 1 + Expr.size a + Expr.size b
  | .ld8 _ i | .ld64 _ i | .ldc _ i | .len64t _ i | .ld8x8 _ i => 1 + Expr.size i
  | _ => 1

def Cond.size : Cond → Nat
  | .cmp _ a b => 1 + Expr.size a + Expr.size b
  | .and p q | .or p q => 1 + Cond.size p + Cond.size q
  | .not p => 1 + Cond.size p

def Exprs.size : List Expr → Nat
  | [] => 0
  | e :: es => Expr.size e + Exprs.size es

def Stmt.size : Stmt → Nat
  | .seq s t => Stmt.size s + Stmt.size t
  | .ite c s t => 1 + Cond.size c + Stmt.size s + Stmt.size t
  | .while c s => 2 + Cond.size c + Stmt.size s
  | .set _ e | .gset _ e | .abort e => 1 + Expr.size e
  | .ret es | .call _ _ es => 1 + Exprs.size es
  | .st8 _ i e | .st64 _ i e => 1 + Expr.size i + Expr.size e
  | .st64t _ t i e | .st32t _ t i e => 1 + Expr.size t + Expr.size i + Expr.size e
  | _ => 2

/-- The callees to inline: `g`'s declaration, if `g` is a leaf of at most `S` nodes. -/
abbrev Env := FnName → Option FunDecl

/-- Every call to a callee of `env` inlined, at offset `o`. -/
def inlS (env : Env) (o : Nat) : Stmt → Stmt
  | .seq s t => .seq (inlS env o s) (inlS env o t)
  | .ite c s t => .ite c (inlS env o s) (inlS env o t)
  | .while c s => .while c (inlS env o s)
  | .call xs g args =>
    match env g with
    | some fd => (inlBody o fd xs args).getD (.call xs g args)
    | none => .call xs g args
  | s => s

/-- The most locals of a callee of `env` that the statement calls. -/
def regS (env : Env) : Stmt → Nat
  | .seq s t | .ite _ s t => max (regS env s) (regS env t)
  | .while _ s => regS env s
  | .call _ g _ => match env g with
    | some fd => fd.nlocals
    | none => 0
  | _ => 0

/-- A function with its calls to the callees of `env` inlined, past its own locals; unchanged if
its frame would get too large for the compiler. -/
def inlFn (env : Env) (fd : FunDecl) : FunDecl :=
  let o := max fd.nlocals (Stmt.vb fd.body)
  let fd' : FunDecl := { nparams := fd.nparams, nlocals := o + regS env fd.body, body := inlS env o fd.body }
  if 8 * frameWords fd' + 8 < maxOff then fd' else fd

/-- Positions in the program by name (`nameCode`); `none` if a name occurs twice. -/
def Prog.idxTreeFrom : Nat → Prog → Option NTree
  | _, [] => some .leaf
  | i, (f, _) :: p => (Prog.idxTreeFrom (i + 1) p).bind (·.insert (nameCode f) i)

def Prog.idxTree (p : Prog) : Option NTree := Prog.idxTreeFrom 0 p

/-- A leaf of at most `S` nodes. -/
def leafOk (S : Nat) (fd : FunDecl) : Bool := !Stmt.calls fd.body && decide (Stmt.size fd.body ≤ S)

/-- The callees of one round: the leaves of `p` of at most `S` nodes, found through `t`. -/
def envOf (S : Nat) (t : NTree) (p : Prog) : Env := fun g =>
  match t.find (nameCode g) with
  | some i => match p[i]? with
    | some (_, fd) => if leafOk S fd then some fd else none
    | none => none
  | none => none

/-- One round. -/
def inlRound (S : Nat) (t : NTree) (p : Prog) : Prog :=
  p.map fun x => (x.1, inlFn (envOf S t p) x.2)

/-- `R` rounds. -/
def inlineProg (S : Nat) (t : NTree) : Nat → Prog → Prog
  | 0, p => p
  | r + 1, p => inlineProg S t r (inlRound S t p)

end L.Compiler
