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

/-- A byte source exists: a byte array of `tab`, or constant bytes in its constant data (short
enough to be an immediate). -/
def BSrc.wf (tab : Tab) : BSrc → Bool
  | .arr a => a < tab.nb
  | .rom d => d.isPrefixOf (tab.rom.drop (romIdx d tab.rom)) && d.length < 2 ^ 31

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
  | .ld64t a t i => a < tab.wK && Expr.wf nl tab t && Expr.wf nl tab i
  | .len64t a t => a < tab.wK && Expr.wf nl tab t
  | .ld8x8 s i => BSrc.wf tab s && Expr.wf nl tab i

def Cond.wf (nl : Nat) (tab : Tab) : Cond → Bool
  | .cmp _ a b => Expr.wf nl tab a && Expr.wf nl tab b
  | .and p q | .or p q => Cond.wf nl tab p && Cond.wf nl tab q
  | .not p => Cond.wf nl tab p

/-- A block operand: an array of `tab`, or a tiered one with an operand tier. -/
def WArr.wf (nl : Nat) (tab : Tab) : WArr → Bool
  | .plain a => a < tab.nw
  | .tier a t => a < tab.wK && Expr.isOpnd t && Expr.wf nl tab t

/-- A block's operands need no code (`Expr.isOpnd`). -/
def Expr.opndWf (nl : Nat) (tab : Tab) (e : Expr) : Bool := Expr.isOpnd e && Expr.wf nl tab e

def Stmt.wf (p : Prog) (nl : Nat) (tab : Tab) : Stmt → Bool
  | .skip | .brk => true
  | .abort e => Expr.wf nl tab e
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
  | .st64t a t i e => a < tab.wK && Expr.isSimple t && Expr.wf nl tab t &&
      Expr.wf nl tab i && Expr.wf nl tab e
  | .copy64 d di s si n => WArr.wf nl tab d && Expr.opndWf nl tab di && WArr.wf nl tab s &&
      Expr.opndWf nl tab si && Expr.opndWf nl tab n
  | .copy8w d di s si n => WArr.wf nl tab d && Expr.opndWf nl tab di && BSrc.wf tab s &&
      Expr.opndWf nl tab si && Expr.opndWf nl tab n
  | .scan8 x s i e c => x < nl && BSrc.wf tab s && Expr.opndWf nl tab i && Expr.opndWf nl tab e &&
      c.length == 256 && c.isPrefixOf (tab.rom.drop (romIdx c tab.rom))

/-! ## The checks, guarded against kernel evaluation

`FunDecl.wf` and `Prog.wf` look call targets up by `String` comparison, which the kernel does
byte by byte: `decide +kernel` on a large program's `Prog.wf` took tens of seconds and up to
19 GB (DESIGN.md, "Slow declarations", "Program well-formedness, per function"). They are
therefore wrapped in `kernelOpaque`, which neither the kernel nor `decide` can unfold
(`Lean.opaqueId true` is stuck), so evaluating them by accident fails at once. Their contents are
`FunDecl.wfSpec`/`Prog.wfSpec` (`FunDecl.wf_eq`, `Prog.wf_eq`); a concrete program's check goes
through `Prog.wfFast` (`WFFast.lean`) or `prog_wf` (`WFSplit.lean`). Compiled code (`#guard`)
evaluates them as before. -/

/-- `x`, in a form the kernel cannot reduce (`Lean.opaqueId true` does not reduce, so neither
does the `cond` on it); `kernelOpaque_eq` proves it equal to `x`. -/
def kernelOpaque {α : Sort _} (x : α) : α := cond (Lean.opaqueId true) x x

theorem kernelOpaque_eq {α : Sort _} (x : α) : kernelOpaque x = x := by
  unfold kernelOpaque; cases Lean.opaqueId true <;> rfl

def FunDecl.wfSpec (p : Prog) (tab : Tab) (fd : FunDecl) : Bool :=
  fd.nparams ≤ fd.nlocals && Stmt.wf p fd.nlocals tab fd.body && 8 * frameWords fd + 8 < maxOff

/-- A function is well formed in program `p` (guarded: see above). -/
def FunDecl.wf (p : Prog) (tab : Tab) (fd : FunDecl) : Bool := kernelOpaque (FunDecl.wfSpec p tab fd)

theorem FunDecl.wf_eq (p : Prog) (tab : Tab) (fd : FunDecl) :
    FunDecl.wf p tab fd = FunDecl.wfSpec p tab fd := kernelOpaque_eq _

def Prog.wfSpec (tab : Tab) (p : Prog) : Bool :=
  p.all (fun (_, fd) => FunDecl.wf p tab fd) && decide (p.map (·.1)).Nodup &&
    16 + 16 * (tab.nb + tab.nw) + 8 * tab.romWords + 8 * tab.nxres + 8 * tab.ng < maxOff

/-- The program is well formed for the table layout `tab` (guarded: see above). -/
def Prog.wf (tab : Tab) (p : Prog) : Bool := kernelOpaque (Prog.wfSpec tab p)

theorem Prog.wf_eq (tab : Tab) (p : Prog) : Prog.wf tab p = Prog.wfSpec tab p := kernelOpaque_eq _

/-! ## The arrays a program names

For checking programs whose memory layout is not fixed elsewhere: `Prog.wfAuto p` is `Prog.wf` for
the smallest table `p` fits (one more byte/word array than the largest id it names). -/

def arrsMax (a b : Nat × Nat) : Nat × Nat := (max a.1 b.1, max a.2 b.2)

def BSrc.arrs : BSrc → Nat × Nat
  | .arr a => (a + 1, 0)
  | .rom _ => (0, 0)

def Expr.arrs : Expr → Nat × Nat
  | .bin _ a b | .cmpw _ a b => arrsMax (Expr.arrs a) (Expr.arrs b)
  | .ld8 a i => arrsMax (a + 1, 0) (Expr.arrs i)
  | .ld64 a i => arrsMax (0, a + 1) (Expr.arrs i)
  | .len8 a => (a + 1, 0)
  | .len64 a => (0, a + 1)
  | .ldc _ i => Expr.arrs i
  | .ld64t a t i => arrsMax (0, a + tierOff + 1) (arrsMax (Expr.arrs t) (Expr.arrs i))
  | .len64t a t => arrsMax (0, a + tierOff + 1) (Expr.arrs t)
  | .ld8x8 s i => arrsMax (BSrc.arrs s) (Expr.arrs i)
  | _ => (0, 0)

def WArr.arrs : WArr → Nat × Nat
  | .plain a => (0, a + 1)
  | .tier a t => arrsMax (0, a + tierOff + 1) (Expr.arrs t)

def Cond.arrs : Cond → Nat × Nat
  | .cmp _ a b => arrsMax (Expr.arrs a) (Expr.arrs b)
  | .and p q | .or p q => arrsMax (Cond.arrs p) (Cond.arrs q)
  | .not p => Cond.arrs p

def Stmt.arrs : Stmt → Nat × Nat
  | .skip | .brk => (0, 0)
  | .set _ e | .abort e => Expr.arrs e
  | .st8 a i e => arrsMax (a + 1, 0) (arrsMax (Expr.arrs i) (Expr.arrs e))
  | .st64 a i e => arrsMax (0, a + 1) (arrsMax (Expr.arrs i) (Expr.arrs e))
  | .seq s t => arrsMax (Stmt.arrs s) (Stmt.arrs t)
  | .ite c s t => arrsMax (Cond.arrs c) (arrsMax (Stmt.arrs s) (Stmt.arrs t))
  | .while c s => arrsMax (Cond.arrs c) (Stmt.arrs s)
  | .ret es | .call _ _ es => es.foldl (fun acc e => arrsMax acc (Expr.arrs e)) (0, 0)
  | .gset _ e => Expr.arrs e
  | .st64t a t i e => arrsMax (0, a + tierOff + 1) (arrsMax (Expr.arrs t) (arrsMax (Expr.arrs i) (Expr.arrs e)))
  | .copy64 d di s si n => arrsMax (WArr.arrs d) (arrsMax (Expr.arrs di) (arrsMax (WArr.arrs s)
      (arrsMax (Expr.arrs si) (Expr.arrs n))))
  | .copy8w d di s si n => arrsMax (WArr.arrs d) (arrsMax (Expr.arrs di) (arrsMax (BSrc.arrs s)
      (arrsMax (Expr.arrs si) (Expr.arrs n))))
  | .scan8 _ s i e _ => arrsMax (BSrc.arrs s) (arrsMax (Expr.arrs i) (Expr.arrs e))

def Prog.arrs (p : Prog) : Nat × Nat := p.foldl (fun acc (_, fd) => arrsMax acc (Stmt.arrs fd.body)) (0, 0)

/-- `Prog.wf` for the smallest table that has every array `p` names. -/
def Prog.wfAuto (p : Prog) : Bool := Prog.wf (Prog.tab p (Prog.arrs p).1 (Prog.arrs p).2) p

end L.Compiler
