module

public import ConAgua.L.Syntax

@[expose] public section

/-!
# Bounds-check elimination: the analysis

A forward analysis of one function body, with no knowledge of other functions. At each point of
the body it computes **facts** that hold in every L state that reaches the point:

* `lt`: `i < len(K)`, where `K` (`AKey`) names the array an access is checked against (a byte
  array, a word array, a tier of a tiered array given by a local expression, or the 32-bit view
  of either) and `i` is built from locals, constants and operators (`Expr.pure`);
* `hi`: `x < n`, an exclusive upper bound of a local.

Where facts come from: a condition, in the branch where it holds (`i < len(K)`, or `len(K) ≤ i`
negated); an access that ran (its check passed: the index is below the length); an assignment
`x := e` with a bounded `e` (`hiE`: constants, `&`, `>>` by a constant, `+` without wraparound).
What removes a fact: a write to a local it mentions (`set`, a call's results, `scan8`); at a loop
head, every local the body writes; after a loop, the exit condition holds only if the body has no
`break`. The branches of an `if` are joined; `return`, `break` and `abort` end a path (`none`).
Array lengths never change while L code runs: no statement changes them.

The code generator (`Compile.lean`, `Ctx.fa`, `Ctx.safe`) emits an access without its bounds
check when its fact holds, or when the index's bound is at most the array's minimum length.
Everything here is structural recursion over the statement, so that the kernel evaluates it when
it checks the compiled program (`asm_lit`). Soundness: `BceSound.lean` (the facts hold),
`BcePost.lean` (they are preserved by the statements).
-/

namespace L.Compiler

/-- The array (or view) an access is checked against. -/
inductive AKey where
  /-- Byte array `a`. -/
  | b (a : ArrId)
  /-- Word array `s`. -/
  | w (s : TieredArray)
  /-- Tier `tv` of the tiered word array `a` (`tv` pure). -/
  | t (a : ArrId) (tv : Expr)
  /-- The 32-bit elements of word array `s` (two per word). -/
  | h (s : TieredArray)
  /-- The 32-bit elements of tier `tv` of `a`. -/
  | u (a : ArrId) (tv : Expr)
  deriving Repr, Inhabited

/-- Built from locals, constants and operators: its value depends on the locals alone. -/
def Expr.pure : Expr → Bool
  | .const _ | .var _ => true
  | .bin _ a b => Expr.pure a && Expr.pure b
  | _ => false

/-- Equality of pure expressions (`false` for any other). -/
def Expr.beqP : Expr → Expr → Bool
  | .const a, .const b => a.toNat == b.toNat
  | .var x, .var y => x == y
  | .bin o a b, .bin o' a' b' => o == o' && Expr.beqP a a' && Expr.beqP b b'
  | _, _ => false

/-- The pure expression `e` reads local `x`. -/
def Expr.mentions (x : Var) : Expr → Bool
  | .var y => x == y
  | .bin _ a b => Expr.mentions x a || Expr.mentions x b
  | _ => false

def AKey.pure : AKey → Bool
  | .t _ tv | .u _ tv => Expr.pure tv
  | _ => true

def AKey.mentions (x : Var) : AKey → Bool
  | .t _ tv | .u _ tv => Expr.mentions x tv
  | _ => false

def AKey.beq : AKey → AKey → Bool
  | .b a, .b a' => a == a'
  | .w s, .w s' => s.arr == s'.arr && s.hi == s'.hi
  | .t a tv, .t a' tv' => a == a' && Expr.beqP tv tv'
  | .h s, .h s' => s.arr == s'.arr && s.hi == s'.hi
  | .u a tv, .u a' tv' => a == a' && Expr.beqP tv tv'
  | _, _ => false

/-- The key of a 64-bit access to tier `t` of `a`: a constant tier is its word array. -/
def keyT (a : ArrId) : Expr → Option AKey
  | .const c => some (.w (tierA a c))
  | t => if Expr.pure t then some (.t a t) else none

/-- The key of a 32-bit access to tier `t` of `a`. -/
def key32 (a : ArrId) : Expr → Option AKey
  | .const c => some (.h (tierA a c))
  | t => if Expr.pure t then some (.u a t) else none

/-- The facts at a program point. -/
structure Facts where
  lt : List (AKey × Expr) := []
  hi : List (Var × Nat) := []
  deriving Repr, Inhabited

/-- An exclusive upper bound of `e`'s value, from the bounds `hi` of the locals. -/
def hiE (hi : List (Var × Nat)) : Expr → Option Nat
  | .const k => some (k.toNat + 1)
  | .var x => hi.lookup x
  | .bin .and a b =>
    match hiE hi a with
    | some x => some (match hiE hi b with | some y => min x y | none => x)
    | none => hiE hi b
  | .bin .shr a (.const s) => some ((((hiE hi a).getD (2 ^ 64)) - 1) >>> (s.toNat % 64) + 1)
  | .bin .add a b =>
    match hiE hi a, hiE hi b with
    | some x, some y => if x + y - 1 ≤ 2 ^ 64 then some (x + y - 1) else none
    | _, _ => none
  | _ => none

/-- The key of a length expression. -/
def lenKey : Expr → Option AKey
  | .len8 a => some (.b a)
  | .len64 a => some (.w a)
  | .len64t a t => keyT a t
  | _ => none

/-- The checked accesses of `e` (each one's key and index): when `e` evaluates, each passed its
check. -/
def Expr.loads : Expr → List (AKey × Expr)
  | .bin _ a b | .cmpw _ a b => Expr.loads a ++ Expr.loads b
  | .ld8 a i => (.b a, i) :: Expr.loads i
  | .ld64 a i => (.w a, i) :: Expr.loads i
  | .ld64t a t i | .ld32h a t i _ =>
    (match keyT a t with | some k => [(k, i)] | none => []) ++ Expr.loads t ++ Expr.loads i
  | .ld32t a t i => (match key32 a t with | some k => [(k, i)] | none => []) ++ Expr.loads t ++ Expr.loads i
  | .ldc _ i | .ld8x8 _ i => Expr.loads i
  | .len64t _ t => Expr.loads t
  | _ => []

/-- The accesses of `c` that ran whatever its value. -/
def Cond.loadsAny : Cond → List (AKey × Expr)
  | .cmp _ a b => Expr.loads a ++ Expr.loads b
  | .and p _ | .or p _ | .not p => Cond.loadsAny p

/-- The accesses of `c` that ran when `c` came out `pol`. -/
def Cond.loads : Cond → Bool → List (AKey × Expr)
  | .cmp _ a b, _ => Expr.loads a ++ Expr.loads b
  | .and p q, true => Cond.loads p true ++ Cond.loads q true
  | .and p _, false => Cond.loadsAny p
  | .or p _, true => Cond.loadsAny p
  | .or p q, false => Cond.loads p false ++ Cond.loads q false
  | .not p, pol => Cond.loads p (!pol)

namespace Facts

/-- At most this many `lt` facts are kept. -/
def maxLt : Nat := 48

/-- Add `e < len(k)`. -/
def addLt (fa : Facts) (k : AKey) (e : Expr) : Facts :=
  if Expr.pure e && AKey.pure k && !fa.lt.any (fun f => AKey.beq f.1 k && Expr.beqP f.2 e) then
    { fa with lt := ((k, e) :: fa.lt).take maxLt }
  else fa

def addLoads (fa : Facts) : List (AKey × Expr) → Facts
  | [] => fa
  | (k, e) :: l => addLoads (fa.addLt k e) l

/-- Forget what mentions local `x`. -/
def kill (fa : Facts) (x : Var) : Facts :=
  { lt := fa.lt.filter fun f => !AKey.mentions x f.1 && !Expr.mentions x f.2
    hi := fa.hi.filter fun f => f.1 != x }

def killAll (fa : Facts) : List Var → Facts
  | [] => fa
  | x :: xs => killAll (fa.kill x) xs

/-- What holds when `c` comes out `pol` (besides its accesses): `a < len` facts. -/
def cond (fa : Facts) : Cond → Bool → Facts
  | .cmp .ult a b, true => match lenKey b with | some k => fa.addLt k a | none => fa
  | .cmp .ule a b, false => match lenKey a with | some k => fa.addLt k b | none => fa
  | .and p q, true => (fa.cond p true).cond q true
  | .or p q, false => (fa.cond p false).cond q false
  | .not p, pol => fa.cond p (!pol)
  | _, _ => fa

def condAll (fa : Facts) (c : Cond) (pol : Bool) : Facts :=
  (fa.addLoads (Cond.loads c pol)).cond c pol

/-- `x := e`: `e`'s accesses ran, `x`'s old facts go, its new bound comes. -/
def set (fa : Facts) (x : Var) (e : Expr) : Facts :=
  let fa' := (fa.addLoads (Expr.loads e)).kill x
  match hiE fa.hi e with
  | some n => { fa' with hi := (x, n) :: fa'.hi }
  | none => fa'

end Facts

/-- The facts that hold on both paths. -/
def joinF : Option Facts → Option Facts → Option Facts
  | none, b => b
  | a, none => a
  | some f, some g => some {
      lt := f.lt.filter fun x => g.lt.any fun y => AKey.beq x.1 y.1 && Expr.beqP x.2 y.2
      hi := f.hi.filterMap fun (x, n) => (g.hi.lookup x).map fun m => (x, max n m) }

/-- The locals `s` may write. -/
def Stmt.writes : Stmt → List Var
  | .set x _ | .scan8 x .. => [x]
  | .call xs .. => xs
  | .seq s t | .ite _ s t => Stmt.writes s ++ Stmt.writes t
  | .while _ s => Stmt.writes s
  | _ => []

/-- A `break` of this loop level. -/
def Stmt.hasBrk : Stmt → Bool
  | .brk => true
  | .seq s t | .ite _ s t => Stmt.hasBrk s || Stmt.hasBrk t
  | _ => false

/-- The facts at the head of loop `while c s` entered with `fa`. -/
def headF (fa : Option Facts) (s : Stmt) : Option Facts := fa.map (·.killAll (Stmt.writes s))

/-- The facts after `s`, `none` if it does not end normally. -/
def postF : Option Facts → Stmt → Option Facts
  | none, _ => none
  | some fa, s =>
  match s with
  | .skip => some fa
  | .set x e => some (fa.set x e)
  | .st8 a i e => some ((fa.addLoads (Expr.loads i ++ Expr.loads e)).addLt (.b a) i)
  | .st64 a i e => some ((fa.addLoads (Expr.loads i ++ Expr.loads e)).addLt (.w a) i)
  | .st64t a t i e =>
    let fa := fa.addLoads (Expr.loads t ++ Expr.loads i ++ Expr.loads e)
    some (match keyT a t with | some k => fa.addLt k i | none => fa)
  | .st32t a t i e =>
    let fa := fa.addLoads (Expr.loads t ++ Expr.loads i ++ Expr.loads e)
    some (match key32 a t with | some k => fa.addLt k i | none => fa)
  | .gset _ e => some (fa.addLoads (Expr.loads e))
  | .seq s t => postF (postF (some fa) s) t
  | .ite c s t => joinF (postF (some (fa.condAll c true)) s) (postF (some (fa.condAll c false)) t)
  | .while c s =>
    let f' := fa.killAll (Stmt.writes s)
    if Stmt.hasBrk s then some f' else some (f'.condAll c false)
  | .brk | .ret _ | .abort _ => none
  | .call xs _ args => some ((fa.addLoads (args.flatMap Expr.loads)).killAll xs)
  | .scan8 x .. => some (fa.kill x)
  | .copy64 .. | .copy8w .. => some fa

/-- Index `i` of an access with key `k` (if any) is in range at a point with facts `fa`: its fact
holds, or its bound is at most `mn`, a minimum length of the array. -/
def safeIdx (fa : Option Facts) (k : Option AKey) (i : Expr) (mn : Nat) : Bool :=
  match fa with
  | none => false
  | some fa =>
    (match hiE fa.hi i with | some n => decide (n ≤ mn) | none => false) ||
    (match k with
     | some k => fa.lt.any fun f => AKey.beq f.1 k && Expr.beqP f.2 i
     | none => false)

end L.Compiler
