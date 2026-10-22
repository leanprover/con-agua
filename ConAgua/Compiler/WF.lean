module

public import ConAgua.Compiler.Compile

@[expose] public section

/-!
# Static well-formedness of L programs

What the compiler needs of a program, as a decidable check (`Prog.wf tab p = true`): locals are
in range, arrays exist in `tab`, call targets exist and get as many arguments as they have
parameters, function names are distinct, and frames and table offsets are small enough to be
immediates. (`L` itself gives a meaning to every program; these are the programs the compiler
accepts.) Every constant byte string of an `ldc` occurs in the table's constant data, no `return` gives
and no call reads more than `tab.nres` results, and every global variable is below `tab.ng`.
-/

namespace L.Compiler

/-- Frame and table offsets stay below this, so that every displacement and immediate fits in
32 bits. -/
def maxOff : Nat := 2 ^ 28

def Expr.wf (nl : Nat) (tab : Tab) : Expr → Bool
  | .const _ => true
  | .var x => x < nl
  | .bin _ a b => Expr.wf nl tab a && Expr.wf nl tab b
  | .ld8 a i => a < tab.nb && Expr.wf nl tab i
  | .ld64 a i => a < tab.nw && Expr.wf nl tab i
  | .len8 a => a < tab.nb
  | .len64 a => a < tab.nw
  | .cmpw _ a b => Expr.wf nl tab a && Expr.wf nl tab b
  | .ldc d i => d.isPrefixOf (tab.rom.drop (romIdx d tab.rom)) && Expr.wf nl tab i
  | .glob g => g.id < tab.ng

def Cond.wf (nl : Nat) (tab : Tab) : Cond → Bool
  | .cmp _ a b => Expr.wf nl tab a && Expr.wf nl tab b
  | .and p q | .or p q => Cond.wf nl tab p && Cond.wf nl tab q
  | .not p => Cond.wf nl tab p

def Stmt.wf (p : Prog) (nl : Nat) (tab : Tab) : Stmt → Bool
  | .skip | .brk | .abort => true
  | .set x e => x < nl && Expr.wf nl tab e
  | .st8 a i e => a < tab.nb && Expr.wf nl tab i && Expr.wf nl tab e
  | .st64 a i e => a < tab.nw && Expr.wf nl tab i && Expr.wf nl tab e
  | .seq s t => Stmt.wf p nl tab s && Stmt.wf p nl tab t
  | .ite c s t => Cond.wf nl tab c && Stmt.wf p nl tab s && Stmt.wf p nl tab t
  | .while c s => Cond.wf nl tab c && Stmt.wf p nl tab s
  | .ret es => es.all (Expr.wf nl tab) && es.length ≤ tab.nres
  | .call xs f args => xs.all (· < nl) && xs.length ≤ tab.nres &&
      args.all (Expr.wf nl tab) &&
      match p.lookup f with
      | some fd => args.length == fd.nparams
      | none => false
  | .gset g e => g.id < tab.ng && Expr.wf nl tab e

def FunDecl.wf (p : Prog) (tab : Tab) (fd : FunDecl) : Bool :=
  fd.nparams ≤ fd.nlocals && Stmt.wf p fd.nlocals tab fd.body && 8 * frameWords fd + 8 < maxOff

/-- The program is well formed for the table layout `tab`. -/
def Prog.wf (tab : Tab) (p : Prog) : Bool :=
  p.all (fun (_, fd) => FunDecl.wf p tab fd) && decide (p.map (·.1)).Nodup &&
    16 + 16 * (tab.nb + tab.nw) + 8 * tab.romWords + 8 * tab.nxres + 8 * tab.ng < maxOff

/-! ## The arrays a program names

For checking programs whose memory layout is not fixed elsewhere: `Prog.wfAuto p` is `Prog.wf` for
the smallest table `p` fits (one more byte/word array than the largest id it names). -/

def arrsMax (a b : Nat × Nat) : Nat × Nat := (max a.1 b.1, max a.2 b.2)

def Expr.arrs : Expr → Nat × Nat
  | .bin _ a b | .cmpw _ a b => arrsMax (Expr.arrs a) (Expr.arrs b)
  | .ld8 a i => arrsMax (a + 1, 0) (Expr.arrs i)
  | .ld64 a i => arrsMax (0, a + 1) (Expr.arrs i)
  | .len8 a => (a + 1, 0)
  | .len64 a => (0, a + 1)
  | .ldc _ i => Expr.arrs i
  | _ => (0, 0)

def Cond.arrs : Cond → Nat × Nat
  | .cmp _ a b => arrsMax (Expr.arrs a) (Expr.arrs b)
  | .and p q | .or p q => arrsMax (Cond.arrs p) (Cond.arrs q)
  | .not p => Cond.arrs p

def Stmt.arrs : Stmt → Nat × Nat
  | .skip | .brk | .abort => (0, 0)
  | .set _ e => Expr.arrs e
  | .st8 a i e => arrsMax (a + 1, 0) (arrsMax (Expr.arrs i) (Expr.arrs e))
  | .st64 a i e => arrsMax (0, a + 1) (arrsMax (Expr.arrs i) (Expr.arrs e))
  | .seq s t => arrsMax (Stmt.arrs s) (Stmt.arrs t)
  | .ite c s t => arrsMax (Cond.arrs c) (arrsMax (Stmt.arrs s) (Stmt.arrs t))
  | .while c s => arrsMax (Cond.arrs c) (Stmt.arrs s)
  | .ret es | .call _ _ es => es.foldl (fun acc e => arrsMax acc (Expr.arrs e)) (0, 0)
  | .gset _ e => Expr.arrs e

def Prog.arrs (p : Prog) : Nat × Nat := p.foldl (fun acc (_, fd) => arrsMax acc (Stmt.arrs fd.body)) (0, 0)

/-- `Prog.wf` for the smallest table that has every array `p` names. -/
def Prog.wfAuto (p : Prog) : Bool := Prog.wf (Prog.tab p (Prog.arrs p).1 (Prog.arrs p).2) p

end L.Compiler
