module

public import ConAgua.L.Semantics
public import Kraken.X64.Syntax

@[expose] public section

/-!
# The naive compiler from L to Kraken x64

See DESIGN.md, "The compiler". One pass, no register allocation: an expression is evaluated into
`rax`, with intermediate values in fixed per-frame temporary slots.

**Machine state during L code.**
* `r15` = `T`, the address of the run's descriptor table (`Tab`); pinned.
* `r14` = the fuel counter; decremented at every loop back-edge and every call.
* `rsp` = the current frame; constant while a body runs. Local `x` is the word at `rsp + 8x`,
  temporary `t` is at `rsp + 8(nlocals + t)`. The frame has `frameWords` words.
* `rbp` = the trampoline's saved stack pointer; never written by L code.
* `rax` = expression result, `rcx`/`rdx` = scratch, `rsi` = argument pointer at a call.

**Exits.** `ca_error` and `ca_exhausted` are global; they restore the caller's `rsp` from `rbp`
and return to the harness with `rdx` = 2 resp. 1. A normal return has `rdx` = 0 and the result
in `rax`.
-/

namespace L.Compiler

/-! ## The descriptor table -/

/-- The layout of the descriptor table at `T`:
* `[T]` the initial stack pointer (top of the stack region), `[T + 8]` its lower limit;
* `[T + 16 + 16a]` / `[T + 24 + 16a]` base / length of byte array `a < nb`;
* then the same for word arrays `a < nw`;
* then the arguments of the entry function, one word each. -/
structure Tab where
  nb : Nat
  nw : Nat
  deriving Repr, DecidableEq

def Tab.stackTop : Int := 0
def Tab.stackLimit : Int := 8
def Tab.base8 (_ : Tab) (a : ArrId) : Int := 16 + 16 * a
def Tab.len8 (_ : Tab) (a : ArrId) : Int := 24 + 16 * a
def Tab.base64 (t : Tab) (a : ArrId) : Int := 16 + 16 * (t.nb + a)
def Tab.len64 (t : Tab) (a : ArrId) : Int := 24 + 16 * (t.nb + a)
def Tab.args (t : Tab) : Int := 16 + 16 * (t.nb + t.nw)

/-! ## Instruction helpers -/

/-- A 64-bit instruction. -/
abbrev i64 (op : Operation .W64) : Directive := .instr (.regular .W64 .W64 op)
/-- An 8-bit instruction. -/
abbrev i8 (op : Operation .W8) : Directive := .instr (.regular .W64 .W8 op)

/-- `[b + d]` -/
abbrev mb (b : Reg64) (d : Int) : AddrExpr := ⟨some (.reg b), none, .int64 (Int64.ofInt d)⟩
/-- `[b + s·i]` -/
abbrev mbi (b i : Reg64) (s : Width) : AddrExpr := ⟨some (.reg b), some ⟨i, s⟩, .int64 0⟩

abbrev rr (r : Reg64) : Reg .W64 := .low r .W64
abbrev oR (r : Reg64) : Operand .W64 := .regOrMem (.reg (rr r))
abbrev oM {w} (a : AddrExpr) : Operand w := .regOrMem (.mem a)
abbrev oI {w} (i : Int) : Operand w := .imm (.int64 (Int64.ofInt i))

abbrev movRI (r : Reg64) (w : Word) : Directive := i64 (.mov (.reg (rr r)) (.imm (.int64 w.toInt64)))
abbrev movRR (d s : Reg64) : Directive := i64 (.mov (.reg (rr d)) (oR s))
abbrev movRM (d : Reg64) (a : AddrExpr) : Directive := i64 (.mov (.reg (rr d)) (oM a))
abbrev movMR (a : AddrExpr) (s : Reg64) : Directive := i64 (.mov (.mem a) (oR s))
abbrev jmpL (l : Label) : Directive := i64 (.jmp (.rel (.sub (.label l) .after_current_instruction)))
abbrev jccL (cc : CondCode) (l : Label) : Directive := i64 (.jcc cc l)

/-- The global exit labels. -/
def errorL : Label := "ca_error"
def exhaustedL : Label := "ca_exhausted"
def finishL : Label := "ca_finish"
def enterL : Label := "ca_enter"
/-- The entry label of function `f`. -/
def fnL (f : FnName) : Label := "ca_f_" ++ f

/-! ## Temporaries

`compileE e t` evaluates `e` into `rax` and may write the temporaries `t, t+1, …, t + tempsE e - 1`. -/

def tempsE : Expr → Nat
  | .bin _ a b => max (tempsE a) (1 + tempsE b)
  | .ld8 _ i | .ld64 _ i => tempsE i
  | _ => 0

def tempsC : Cond → Nat
  | .cmp _ a b => max (tempsE a) (1 + tempsE b)
  | .and p q | .or p q => max (tempsC p) (tempsC q)
  | .not p => tempsC p

def tempsArgs : Nat → List Expr → Nat
  | _, [] => 0
  | i, e :: es => max (max (i + 1) (i + tempsE e)) (tempsArgs (i + 1) es)

def tempsS : Stmt → Nat
  | .skip | .brk | .abort => 0
  | .set _ e | .ret e => tempsE e
  | .st8 _ i e | .st64 _ i e => max (tempsE i) (1 + tempsE e)
  | .seq s t => max (tempsS s) (tempsS t)
  | .ite c s t => max (tempsC c) (max (tempsS s) (tempsS t))
  | .while c s => max (tempsC c) (tempsS s)
  | .call _ _ args => tempsArgs 0 args

/-- The number of words in the frame of `fd`. -/
def frameWords (fd : FunDecl) : Nat := fd.nlocals + tempsS fd.body

/-! ## Code generation -/

/-- What a code fragment needs to know about its function. -/
structure Ctx where
  tab : Tab
  /-- The function's name (for its labels). -/
  fn : FnName
  /-- The number of locals; temporary `t` is the word at `rsp + 8(nl + t)`. -/
  nl : Nat
  /-- Where `break` jumps. -/
  brk : Label
  deriving Repr

/-- A local label of function `f`; `path` is lowercase (the node's position), `m` an uppercase
marker, so that distinct nodes and markers give distinct labels. -/
def lbl (f : FnName) (path : String) (m : String) : Label :=
  ".Lca_" ++ f ++ "_" ++ path ++ m

def Ctx.lbl (ctx : Ctx) (path : String) (m : String) : Label := L.Compiler.lbl ctx.fn path m

/-- Where `return` jumps (with the result in `rax`). -/
def Ctx.retL (ctx : Ctx) : Label := ctx.lbl "" "R"

/-- Where a function body that falls off its end (or breaks outside a loop) goes: `rax := 0`. -/
def Ctx.endL (ctx : Ctx) : Label := ctx.lbl "" "Z"

def Ctx.tmp (ctx : Ctx) (t : Nat) : AddrExpr := mb .rsp (8 * (ctx.nl + t))

def binInstr : BinOp → Directive
  | .add => i64 (.add (.reg (rr .rax)) (oR .rcx))
  | .sub => i64 (.sub (.reg (rr .rax)) (oR .rcx))
  | .mul => i64 (.imul (some (.reg (rr .rax))) (.reg (rr .rax)) (oR .rcx))
  | .and => i64 (.and (.reg (rr .rax)) (oR .rcx))
  | .or => i64 (.or (.reg (rr .rax)) (oR .rcx))
  | .xor => i64 (.xor (.reg (rr .rax)) (oR .rcx))
  | .shl => i64 (.shl (.reg (rr .rax)) .cl)
  | .shr => i64 (.shr (.reg (rr .rax)) .cl)

/-- `rax := e`. -/
def compileE (ctx : Ctx) : Expr → Nat → Program
  | .const w, _ => [movRI .rax w]
  | .var x, _ => [movRM .rax (mb .rsp (8 * x))]
  | .bin op a b, t =>
    compileE ctx a t ++ [movMR (ctx.tmp t) .rax] ++ compileE ctx b (t + 1) ++
      [movRR .rcx .rax, movRM .rax (ctx.tmp t), binInstr op]
  | .ld8 a i, t =>
    compileE ctx i t ++
      [i64 (.cmp (.reg (rr .rax)) (oM (mb .r15 (ctx.tab.len8 a)))), jccL .nc errorL,
       movRM .rcx (mb .r15 (ctx.tab.base8 a)),
       i64 (.movzx (.reg (rr .rax)) (w' := .W8) (.mem (mbi .rcx .rax .W8)))]
  | .ld64 a i, t =>
    compileE ctx i t ++
      [i64 (.cmp (.reg (rr .rax)) (oM (mb .r15 (ctx.tab.len64 a)))), jccL .nc errorL,
       movRM .rcx (mb .r15 (ctx.tab.base64 a)),
       movRM .rax (mbi .rcx .rax .W64)]
  | .len8 a, _ => [movRM .rax (mb .r15 (ctx.tab.len8 a))]
  | .len64 a, _ => [movRM .rax (mb .r15 (ctx.tab.len64 a))]

/-- The condition code under which `cmp rax, rcx` (with `rax` = left, `rcx` = right) makes the
comparison true. -/
def cmpCC : Cmp → CondCode
  | .eq => .z | .ne => .nz | .ult => .c | .ule => .be | .slt => .l | .sle => .le

/-- The negation of a condition code. -/
def CondCode.neg : CondCode → CondCode
  | .o => .no | .no => .o | .c => .nc | .nc => .c | .z => .nz | .nz => .z | .be => .a | .a => .be
  | .s => .ns | .ns => .s | .p => .np | .np => .p | .l => .ge | .ge => .l | .le => .g | .g => .le

/-- Jump to `l` if `c` evaluates to `b`; fall through otherwise. -/
def compileC (ctx : Ctx) (path : String) : Cond → Bool → Label → Nat → Program
  | .cmp op a b, pol, l, t =>
    compileE ctx a t ++ [movMR (ctx.tmp t) .rax] ++ compileE ctx b (t + 1) ++
      [movRR .rcx .rax, movRM .rax (ctx.tmp t), i64 (.cmp (.reg (rr .rax)) (oR .rcx)),
       jccL (if pol then cmpCC op else CondCode.neg (cmpCC op)) l]
  | .and p q, false, l, t => compileC ctx (path ++ "p") p false l t ++ compileC ctx (path ++ "q") q false l t
  | .and p q, true, l, t =>
    compileC ctx (path ++ "p") p false (ctx.lbl path "S") t ++ compileC ctx (path ++ "q") q true l t ++
      [.label (ctx.lbl path "S")]
  | .or p q, true, l, t => compileC ctx (path ++ "p") p true l t ++ compileC ctx (path ++ "q") q true l t
  | .or p q, false, l, t =>
    compileC ctx (path ++ "p") p true (ctx.lbl path "S") t ++ compileC ctx (path ++ "q") q false l t ++
      [.label (ctx.lbl path "S")]
  | .not p, pol, l, t => compileC ctx (path ++ "n") p (!pol) l t

/-- Evaluate the arguments into temporaries `i, i+1, …`. -/
def compileArgs (ctx : Ctx) : Nat → List Expr → Program
  | _, [] => []
  | i, e :: es => compileE ctx e i ++ [movMR (ctx.tmp i) .rax] ++ compileArgs ctx (i + 1) es

/-- Decrement the fuel counter; leave through `ca_exhausted` if it was zero. -/
def burnFuel : Program :=
  [i64 (.sub (.reg (rr .r14)) (oI 1)), jccL .c exhaustedL]

def compileS (ctx : Ctx) (path : String) : Stmt → Program
  | .skip => []
  | .set x e => compileE ctx e 0 ++ [movMR (mb .rsp (8 * x)) .rax]
  | .st8 a i e =>
    compileE ctx i 0 ++ [movMR (ctx.tmp 0) .rax] ++ compileE ctx e 1 ++
      [movRR .rdx .rax, movRM .rax (ctx.tmp 0),
       i64 (.cmp (.reg (rr .rax)) (oM (mb .r15 (ctx.tab.len8 a)))), jccL .nc errorL,
       movRM .rcx (mb .r15 (ctx.tab.base8 a)),
       i8 (.mov (.mem (mbi .rcx .rax .W8)) (.regOrMem (.reg (.low .rdx .W8))))]
  | .st64 a i e =>
    compileE ctx i 0 ++ [movMR (ctx.tmp 0) .rax] ++ compileE ctx e 1 ++
      [movRR .rdx .rax, movRM .rax (ctx.tmp 0),
       i64 (.cmp (.reg (rr .rax)) (oM (mb .r15 (ctx.tab.len64 a)))), jccL .nc errorL,
       movRM .rcx (mb .r15 (ctx.tab.base64 a)),
       movMR (mbi .rcx .rax .W64) .rdx]
  | .seq s t => compileS ctx (path ++ "l") s ++ compileS ctx (path ++ "r") t
  | .ite c s t =>
    compileC ctx (path ++ "c") c false (ctx.lbl path "E") 0 ++ compileS ctx (path ++ "t") s ++
      [jmpL (ctx.lbl path "X"), .label (ctx.lbl path "E")] ++ compileS ctx (path ++ "e") t ++
      [.label (ctx.lbl path "X")]
  | .while c s =>
    [.label (ctx.lbl path "H")] ++ compileC ctx (path ++ "c") c false (ctx.lbl path "X") 0 ++
      compileS { ctx with brk := ctx.lbl path "X" } (path ++ "b") s ++ burnFuel ++
      [jmpL (ctx.lbl path "H"), .label (ctx.lbl path "X")]
  | .brk => [jmpL ctx.brk]
  | .ret e => compileE ctx e 0 ++ [jmpL ctx.retL]
  | .call x f args =>
    compileArgs ctx 0 args ++ [i64 (.lea (rr .rsi) (ctx.tmp 0))] ++ burnFuel ++
      [i64 (.call (.rel (.sub (.label (fnL f)) .after_current_instruction))),
       movMR (mb .rsp (8 * x)) .rax]
  | .abort => [jmpL errorL]

/-- Copy `n` parameters from `[rsi + 8i]` to the frame slots `i, i+1, …`. -/
def copyParams : Nat → Nat → Program
  | _, 0 => []
  | i, n + 1 => [movRM .rax (mb .rsi (8 * i)), movMR (mb .rsp (8 * i)) .rax] ++ copyParams (i + 1) n

/-- Zero `n` frame slots from `j` on. -/
def zeroLocals : Nat → Nat → Program
  | _, 0 => []
  | j, n + 1 => i64 (.mov (.mem (mb .rsp (8 * j))) (oI 0)) :: zeroLocals (j + 1) n

/-- A function: stack check, frame, parameters, body, epilogue. On entry `rsp` points at the
return address and `rsi` at the arguments. -/
def compileFn (tab : Tab) (f : FnName) (fd : FunDecl) : Program :=
  let F := frameWords fd
  let ctx : Ctx := { tab, fn := f, nl := fd.nlocals, brk := lbl f "" "Z" }
  [.label (fnL f),
   movRR .rax .rsp, i64 (.sub (.reg (rr .rax)) (oM (mb .r15 Tab.stackLimit))),
   i64 (.cmp (.reg (rr .rax)) (oI (8 * F + 8))), jccL .c exhaustedL,
   i64 (.sub (.reg (rr .rsp)) (oI (8 * F)))] ++
  copyParams 0 fd.nparams ++ zeroLocals fd.nparams (fd.nlocals - fd.nparams) ++
  compileS ctx "" fd.body ++
  [.label ctx.endL, movRI .rax 0, .label ctx.retL,
   i64 (.add (.reg (rr .rsp)) (oI (8 * F))), i64 .ret]

/-- The trampoline `ca_enter(T, fuel)` (System V: `rdi`, `rsi`; returns `rax`, `rdx`). It saves
`rbp`, `r14`, `r15`, switches to the L stack `[T]`, and calls `entry` with the arguments at
`T + Tab.args`. -/
def trampoline (tab : Tab) (entry : FnName) : Program :=
  [.label enterL,
   i64 (.push (oR .rbp)), i64 (.push (oR .r14)), i64 (.push (oR .r15)),
   movRR .rbp .rsp, movRR .r15 .rdi, movRR .r14 .rsi,
   movRM .rsp (mb .r15 Tab.stackTop),
   i64 (.lea (rr .rsi) (mb .r15 tab.args))] ++ burnFuel ++
  [i64 (.call (.rel (.sub (.label (fnL entry)) .after_current_instruction))),
   movRI .rdx 0, jmpL finishL,
   .label exhaustedL, movRI .rdx 1, jmpL finishL,
   .label errorL, movRI .rdx 2,
   .label finishL, movRR .rsp .rbp,
   i64 (.pop (.reg (rr .r15))), i64 (.pop (.reg (rr .r14))), i64 (.pop (.reg (rr .rbp))),
   i64 .ret]

/-- The whole program: the trampoline, then every function. -/
def compileProg (tab : Tab) (p : Prog) (entry : FnName) : Program :=
  trampoline tab entry ++ p.flatMap fun (f, fd) => compileFn tab f fd

end L.Compiler
