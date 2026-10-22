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

/-- The number of result registers. -/
def maxRes : Nat := 6

/-- The layout of the descriptor table at `T`:
* `[T]` the initial stack pointer (top of the stack region), `[T + 8]` its lower limit;
* `[T + 16 + 16a]` / `[T + 24 + 16a]` base / length of byte array `a < nb`;
* then the same for word arrays `a < nw`;
* then the constant data `rom` (the byte strings of the program's `ldc` reads), padded to whole
  words;
* then the result area: results `maxRes, maxRes + 1, …, nres - 1` of a call, one word each (empty
  if `nres ≤ maxRes`);
* then the global variables `0, …, ng - 1`, one word each;
* then the arguments of the entry function, one word each.

(`nres` is not part of the table in memory: it says how many results the code passes.) -/
structure Tab where
  nb : Nat
  nw : Nat
  rom : List UInt8 := []
  /-- The number of results in use: the most results any `return` gives or any call reads. The
  first `maxRes` go in registers (`resReg 0`, …), the rest in the table's result area. -/
  nres : Nat := 1
  /-- The number of global variables: global `g` (with `g.id < ng`) is the word at `globOff g`. -/
  ng : Nat := 0
  /-- `rom.length`, stored: the offsets past the constant data (`resOff`, `globOff`, `args`) are
  then arithmetic on the table's fields, and the kernel does not count the bytes of a large ROM
  each time it evaluates the code generator (DESIGN.md, "Kernel-checked compiler output"). -/
  romLen : Nat := rom.length
  romLen_eq : romLen = rom.length := by rfl
  deriving Repr, DecidableEq

def Tab.stackTop : Int := 0
def Tab.stackLimit : Int := 8
def Tab.base8 (_ : Tab) (a : ArrId) : Int := 16 + 16 * a
def Tab.len8 (_ : Tab) (a : ArrId) : Int := 24 + 16 * a
def Tab.base64 (t : Tab) (a : ArrId) : Int := 16 + 16 * (t.nb + a)
def Tab.len64 (t : Tab) (a : ArrId) : Int := 24 + 16 * (t.nb + a)
/-- The words the constant data takes. -/
def Tab.romWords (t : Tab) : Nat := (t.romLen + 7) / 8

theorem Tab.rom_length_le (t : Tab) : t.rom.length ≤ 8 * t.romWords := by
  simp only [Tab.romWords, t.romLen_eq]; omega
def Tab.romBase (t : Tab) : Int := 16 + 16 * (t.nb + t.nw)
/-- The results past the registers. -/
def Tab.nxres (t : Tab) : Nat := t.nres - maxRes
/-- The result area: result `i ≥ maxRes` is the word at `resOff i`. -/
def Tab.resBase (t : Tab) : Int := 16 + 16 * (t.nb + t.nw) + 8 * t.romWords
def Tab.resOff (t : Tab) (i : Nat) : Int := t.resBase + 8 * ((i - maxRes : Nat) : Int)
/-- The global variables: global `g` is the word at `globOff g`. -/
def Tab.globBase (t : Tab) : Int := 16 + 16 * (t.nb + t.nw) + 8 * t.romWords + 8 * t.nxres
def Tab.globOff (t : Tab) (g : GVar) : Int := t.globBase + 8 * (g.id : Int)
def Tab.args (t : Tab) : Int := 16 + 16 * (t.nb + t.nw) + 8 * t.romWords + 8 * t.nxres + 8 * t.ng

/-- The first position of `d` in `rom` (`0` if there is none; `WF` checks that it is one). -/
def romIdx (d : List UInt8) : List UInt8 → Nat
  | [] => 0
  | b :: rom => if d.isPrefixOf (b :: rom) then 0 else romIdx d rom + 1

/-- The constant byte strings of an expression, a condition, a statement, a program. -/
def Expr.roms : Expr → List (List UInt8)
  | .bin _ a b | .cmpw _ a b => Expr.roms a ++ Expr.roms b
  | .ld8 _ i | .ld64 _ i => Expr.roms i
  | .ldc d i => d :: Expr.roms i
  | _ => []

def Cond.roms : Cond → List (List UInt8)
  | .cmp _ a b => Expr.roms a ++ Expr.roms b
  | .and p q | .or p q => Cond.roms p ++ Cond.roms q
  | .not p => Cond.roms p

def Stmt.roms : Stmt → List (List UInt8)
  | .skip | .brk | .abort => []
  | .set _ e => Expr.roms e
  | .st8 _ i e | .st64 _ i e => Expr.roms i ++ Expr.roms e
  | .seq s t => Stmt.roms s ++ Stmt.roms t
  | .ite c s t => Cond.roms c ++ Stmt.roms s ++ Stmt.roms t
  | .while c s => Cond.roms c ++ Stmt.roms s
  | .ret es => es.flatMap Expr.roms
  | .call _ _ args => args.flatMap Expr.roms
  | .gset _ e => Expr.roms e

/-- Insert `d` before the first longer string (structural, so the kernel evaluates it). -/
def romInsert (d : List UInt8) : List (List UInt8) → List (List UInt8)
  | [] => [d]
  | e :: es => if d.length ≤ e.length then d :: e :: es else e :: romInsert d es

/-- Byte strings by length, shortest first (a stable insertion sort). -/
def romSort : List (List UInt8) → List (List UInt8)
  | [] => []
  | d :: ds => romInsert d (romSort ds)

/-- The constant data of a program: its byte strings, each once, shortest first (so that finding
a short string, `romIdx`, does not scan a long one: this keeps the static check of a program
with a large ROM cheap, `WFSplit.lean`). -/
def Prog.rom (p : Prog) : List UInt8 :=
  (romSort ((p.flatMap fun (_, fd) => Stmt.roms fd.body).foldl
    (fun acc d => if acc.contains d then acc else acc ++ [d]) [])).flatten

/-- The most results a statement returns or reads from a call. -/
def Stmt.nres : Stmt → Nat
  | .seq s t | .ite _ s t => max (Stmt.nres s) (Stmt.nres t)
  | .while _ s => Stmt.nres s
  | .ret es => es.length
  | .call xs _ _ => xs.length
  | _ => 0

/-- One more than the largest global variable an expression, a condition, a statement names. -/
def Expr.nglob : Expr → Nat
  | .bin _ a b | .cmpw _ a b => max (Expr.nglob a) (Expr.nglob b)
  | .ld8 _ i | .ld64 _ i | .ldc _ i => Expr.nglob i
  | .glob g => g.id + 1
  | _ => 0

def Cond.nglob : Cond → Nat
  | .cmp _ a b => max (Expr.nglob a) (Expr.nglob b)
  | .and p q | .or p q => max (Cond.nglob p) (Cond.nglob q)
  | .not p => Cond.nglob p

def Stmt.nglob : Stmt → Nat
  | .skip | .brk | .abort => 0
  | .set _ e => Expr.nglob e
  | .st8 _ i e | .st64 _ i e => max (Expr.nglob i) (Expr.nglob e)
  | .seq s t => max (Stmt.nglob s) (Stmt.nglob t)
  | .ite c s t => max (Cond.nglob c) (max (Stmt.nglob s) (Stmt.nglob t))
  | .while c s => max (Cond.nglob c) (Stmt.nglob s)
  | .ret es | .call _ _ es => es.foldl (fun acc e => max acc (Expr.nglob e)) 0
  | .gset g e => max (g.id + 1) (Expr.nglob e)

/-- The table layout of a program with `nb` byte arrays and `nw` word arrays. -/
def Prog.tab (p : Prog) (nb nw : Nat) : Tab :=
  { nb, nw, rom := Prog.rom p, nres := (p.map fun (_, fd) => Stmt.nres fd.body).foldl max 1,
    ng := (p.map fun (_, fd) => Stmt.nglob fd.body).foldl max 0 }

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
  | .bin _ a b | .cmpw _ a b => max (tempsE a) (1 + tempsE b)
  | .ld8 _ i | .ld64 _ i | .ldc _ i => tempsE i
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
  | .set _ e => tempsE e
  | .ret es => tempsArgs 0 es
  | .st8 _ i e | .st64 _ i e => max (tempsE i) (1 + tempsE e)
  | .seq s t => max (tempsS s) (tempsS t)
  | .ite c s t => max (tempsC c) (max (tempsS s) (tempsS t))
  | .while c s => max (tempsC c) (tempsS s)
  | .call _ _ args => tempsArgs 0 args
  | .gset _ e => tempsE e

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

/-- A node's position in a function body, as a number: the root is `0`, and child `d` (a digit
`1 … 9`) of `path` is `Path.ch path d = 10 * path + d`, so a position prints as its sequence of
digits. Numbers rather than strings, so that the kernel can evaluate the code generator cheaply
(`Nat` literals; DESIGN.md, "Kernel-checked compiler output"). -/
abbrev Path := Nat

/-- Child `d` of `path`. -/
def Path.ch (path : Path) (d : Nat) : Path := 10 * path + d

/-- A local label of function `f`; `path` is the node's position (decimal, its digits never `0`
except for the root), `m` an uppercase marker, so that distinct nodes and markers give distinct
labels. -/
def lbl (f : FnName) (path : Path) (m : String) : Label :=
  ".Lca_" ++ f ++ "_" ++ toString path ++ m

def Ctx.lbl (ctx : Ctx) (path : Path) (m : String) : Label := L.Compiler.lbl ctx.fn path m

/-- Where `return` jumps (with the result in `rax`). -/
def Ctx.retL (ctx : Ctx) : Label := ctx.lbl 0 "R"

/-- Where a function body that falls off its end (or breaks outside a loop) goes: `rax := 0`. -/
def Ctx.endL (ctx : Ctx) : Label := ctx.lbl 0 "Z"

def Ctx.tmp (ctx : Ctx) (t : Nat) : AddrExpr := mb .rsp (8 * (ctx.nl + t))

def binInstr : BinOp → Directive
  | .add => i64 (.add (.reg (rr .rax)) (oR .rcx))
  | .sub => i64 (.sub (.reg (rr .rax)) (oR .rcx))
  | .mul => i64 (.imul none (.reg (rr .rax)) (oR .rcx))
  | .and => i64 (.and (.reg (rr .rax)) (oR .rcx))
  | .or => i64 (.or (.reg (rr .rax)) (oR .rcx))
  | .xor => i64 (.xor (.reg (rr .rax)) (oR .rcx))
  | .shl => i64 (.shl (.reg (rr .rax)) .cl)
  | .shr => i64 (.shr (.reg (rr .rax)) .cl)
  | .mulhi => i64 (.mul (.reg (rr .rcx)))

/-- `rax := rax op rcx`: one instruction, and for `mulhi` a move from `rdx`. -/
def binCode : BinOp → Program
  | .mulhi => [binInstr .mulhi, movRR .rax .rdx]
  | op => [binInstr op]

/-- The condition code under which `cmp rax, rcx` (with `rax` = left, `rcx` = right) makes the
comparison true. -/
def cmpCC : Cmp → CondCode
  | .eq => .z | .ne => .nz | .ult => .c | .ule => .be | .slt => .l | .sle => .le

/-- Result `i` of a function is returned in `resReg i` (`i < maxRes`), the others in the table's
result area (`Tab.resOff`). -/
def resReg : Nat → Reg64
  | 0 => .rax | 1 => .rdi | 2 => .r8 | 3 => .r9 | 4 => .r10 | _ => .r11

/-- `rax := e`. -/
def compileE (ctx : Ctx) : Expr → Nat → Program
  | .const w, _ => [movRI .rax w]
  | .var x, _ => [movRM .rax (mb .rsp (8 * x))]
  | .bin op a b, t =>
    compileE ctx a t ++ [movMR (ctx.tmp t) .rax] ++ compileE ctx b (t + 1) ++
      ([movRR .rcx .rax, movRM .rax (ctx.tmp t)] ++ binCode op)
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
  | .cmpw op a b, t =>
    compileE ctx a t ++ [movMR (ctx.tmp t) .rax] ++ compileE ctx b (t + 1) ++
      [movRR .rcx .rax, movRM .rax (ctx.tmp t), i64 (.cmp (.reg (rr .rax)) (oR .rcx)),
       movRI .rax 0, movRI .rdx 1, i64 (.cmovcc (cmpCC op) (rr .rax) (.reg (rr .rdx)))]
  | .ldc d i, t =>
    compileE ctx i t ++
      [i64 (.cmp (.reg (rr .rax)) (oI d.length)), jccL .nc errorL,
       i64 (.lea (rr .rcx) (mb .r15 (ctx.tab.romBase + romIdx d ctx.tab.rom))),
       i64 (.movzx (.reg (rr .rax)) (w' := .W8) (.mem (mbi .rcx .rax .W8)))]
  | .glob g, _ => [movRM .rax (mb .r15 (ctx.tab.globOff g))]

/-- The negation of a condition code. -/
def CondCode.neg : CondCode → CondCode
  | .o => .no | .no => .o | .c => .nc | .nc => .c | .z => .nz | .nz => .z | .be => .a | .a => .be
  | .s => .ns | .ns => .s | .p => .np | .np => .p | .l => .ge | .ge => .l | .le => .g | .g => .le

/-- Jump to `l` if `c` evaluates to `b`; fall through otherwise. -/
def compileC (ctx : Ctx) (path : Path) : Cond → Bool → Label → Nat → Program
  | .cmp op a b, pol, l, t =>
    compileE ctx a t ++ [movMR (ctx.tmp t) .rax] ++ compileE ctx b (t + 1) ++
      [movRR .rcx .rax, movRM .rax (ctx.tmp t), i64 (.cmp (.reg (rr .rax)) (oR .rcx)),
       jccL (if pol then cmpCC op else CondCode.neg (cmpCC op)) l]
  | .and p q, false, l, t => compileC ctx (path.ch 7) p false l t ++ compileC ctx (path.ch 8) q false l t
  | .and p q, true, l, t =>
    compileC ctx (path.ch 7) p false (ctx.lbl path "S") t ++ compileC ctx (path.ch 8) q true l t ++
      [.label (ctx.lbl path "S")]
  | .or p q, true, l, t => compileC ctx (path.ch 7) p true l t ++ compileC ctx (path.ch 8) q true l t
  | .or p q, false, l, t =>
    compileC ctx (path.ch 7) p true (ctx.lbl path "S") t ++ compileC ctx (path.ch 8) q false l t ++
      [.label (ctx.lbl path "S")]
  | .not p, pol, l, t => compileC ctx (path.ch 9) p (!pol) l t

/-- Evaluate the arguments into temporaries `i, i+1, …`. -/
def compileArgs (ctx : Ctx) : Nat → List Expr → Program
  | _, [] => []
  | i, e :: es => compileE ctx e i ++ [movMR (ctx.tmp i) .rax] ++ compileArgs ctx (i + 1) es

/-- Decrement the fuel counter; leave through `ca_exhausted` if it was zero. -/
def burnFuel : Program :=
  [i64 (.sub (.reg (rr .r14)) (oI 1)), jccL .c exhaustedL]

/-- Set results `i, …, i + n - 1`: from the temporaries below `k`, `0` from `k` on. A result
`i ≥ maxRes` goes through `rcx` to the result area. -/
def loadRes (ctx : Ctx) (k : Nat) : Nat → Nat → Program
  | _, 0 => []
  | i, n + 1 =>
    (if i < maxRes then [if i < k then movRM (resReg i) (ctx.tmp i) else movRI (resReg i) 0]
     else if i < k then [movRM .rcx (ctx.tmp i), movMR (mb .r15 (ctx.tab.resOff i)) .rcx]
     else [i64 (.mov (.mem (mb .r15 (ctx.tab.resOff i))) (oI 0))]) ++ loadRes ctx k (i + 1) n

/-- Store results `i, i + 1, …` into the locals `xs` (a result `i ≥ maxRes` from the result area,
through `rcx`). -/
def storeRes (tab : Tab) : List Var → Nat → Program
  | [], _ => []
  | x :: xs, i =>
    (if i < maxRes then [movMR (mb .rsp (8 * x)) (resReg i)]
     else [movRM .rcx (mb .r15 (tab.resOff i)), movMR (mb .rsp (8 * x)) .rcx]) ++ storeRes tab xs (i + 1)

def compileS (ctx : Ctx) (path : Path) : Stmt → Program
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
  | .seq s t => compileS ctx (path.ch 1) s ++ compileS ctx (path.ch 2) t
  | .ite c s t =>
    compileC ctx (path.ch 3) c false (ctx.lbl path "E") 0 ++ compileS ctx (path.ch 4) s ++
      [jmpL (ctx.lbl path "X"), .label (ctx.lbl path "E")] ++ compileS ctx (path.ch 5) t ++
      [.label (ctx.lbl path "X")]
  | .while c s =>
    [.label (ctx.lbl path "H")] ++ compileC ctx (path.ch 3) c false (ctx.lbl path "X") 0 ++
      compileS { ctx with brk := ctx.lbl path "X" } (path.ch 6) s ++ burnFuel ++
      [jmpL (ctx.lbl path "H"), .label (ctx.lbl path "X")]
  | .brk => [jmpL ctx.brk]
  | .ret es => compileArgs ctx 0 es ++ loadRes ctx es.length 0 ctx.tab.nres ++ [jmpL ctx.retL]
  | .call xs f args =>
    compileArgs ctx 0 args ++ [i64 (.lea (rr .rsi) (ctx.tmp 0))] ++ burnFuel ++
      [i64 (.call (.rel (.sub (.label (fnL f)) .after_current_instruction))),
       ] ++ storeRes ctx.tab xs 0
  | .abort => [jmpL errorL]
  | .gset g e => compileE ctx e 0 ++ [movMR (mb .r15 (ctx.tab.globOff g)) .rax]

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
  let ctx : Ctx := { tab, fn := f, nl := fd.nlocals, brk := lbl f 0 "Z" }
  [.label (fnL f),
   movRR .rax .rsp, i64 (.sub (.reg (rr .rax)) (oM (mb .r15 Tab.stackLimit))),
   i64 (.cmp (.reg (rr .rax)) (oI (8 * F + 8))), jccL .c exhaustedL,
   i64 (.sub (.reg (rr .rsp)) (oI (8 * F)))] ++
  copyParams 0 fd.nparams ++ zeroLocals fd.nparams (fd.nlocals - fd.nparams) ++
  compileS ctx 0 fd.body ++
  [.label ctx.endL] ++ loadRes ctx 0 0 tab.nres ++ [.label ctx.retL,
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
