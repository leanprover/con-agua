module

public import ConAgua.Compiler.Compile

@[expose] public section

/-!
# Static well-formedness of L programs

What the compiler needs of a program, as a decidable check (`Prog.wf tab p = true`): locals are
in range, arrays exist in `tab`, call targets exist and get as many arguments as they have
parameters, function names are distinct, and frames and table offsets are small enough to be
immediates. (`L` itself gives a meaning to every program; these are the programs the compiler
accepts.)
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
  | .ret e => Expr.wf nl tab e
  | .call x f args => x < nl && args.all (Expr.wf nl tab) &&
      match p.lookup f with
      | some fd => args.length == fd.nparams
      | none => false

def FunDecl.wf (p : Prog) (tab : Tab) (fd : FunDecl) : Bool :=
  fd.nparams ≤ fd.nlocals && Stmt.wf p fd.nlocals tab fd.body && 8 * frameWords fd + 8 < maxOff

/-- The program is well formed for the table layout `tab`. -/
def Prog.wf (tab : Tab) (p : Prog) : Bool :=
  p.all (fun (_, fd) => FunDecl.wf p tab fd) && decide (p.map (·.1)).Nodup &&
    16 + 16 * (tab.nb + tab.nw) < maxOff

end L.Compiler
