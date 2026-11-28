module

public import ConAgua.Compiler.Compile
public import Kraken.X64.Syntax

@[expose] public section

namespace L.Compiler

/-! ## Instruction helpers -/

/-- A 64-bit instruction. -/
abbrev i64 (op : Operation .W64) : Directive := .instr (.regular .W64 .W64 op)
/-- An 8-bit instruction. -/
abbrev i8 (op : Operation .W8) : Directive := .instr (.regular .W64 .W8 op)
/-- A 32-bit instruction (lane p32). -/
abbrev i32 (op : Operation .W32) : Directive := .instr (.regular .W64 .W32 op)

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
/-- `movl d32, [b + 4 i]`: a 4-byte load, zero-extended into `d` (lane p32). -/
abbrev ld32X (d b i : Reg64) : Directive := i32 (.mov (.reg (.low d .W32)) (oM (mbi b i .W32)))
/-- `movl d32, [b + 8 i + 4 hi]`: one half of word `i` (lane p32use). -/
abbrev ld32H (d b i : Reg64) (hi : Bool) : Directive :=
  i32 (.mov (.reg (.low d .W32)) (oM ⟨some (.reg b), some ⟨i, .W64⟩, .int64 (Int64.ofInt (if hi then 4 else 0))⟩))
/-- `movl [b + 4 i], v32`: a 4-byte store of the low half of `v` (lane p32). -/
abbrev st32X (b i v : Reg64) : Directive := i32 (.mov (.mem (mbi b i .W32)) (.regOrMem (.reg (.low v .W32))))
abbrev jmpL (l : Label) : Directive := i64 (.jmp (.rel (.sub (.label l) .after_current_instruction)))
abbrev jccL (cc : CondCode) (l : Label) : Directive := i64 (.jcc cc l)

/-- The global exit labels: `ca_error` reports code `0`, `ca_abort` the code in `rax`. -/
def errorL : Label := "ca_error"
def abortL : Label := "ca_abort"
def exhaustedL : Label := "ca_exhausted"
def finishL : Label := "ca_finish"
/-- Where the trampoline zeroes the results that the entry function does not set. -/
def okL : Label := "ca_ok"
def enterL : Label := "ca_enter"
/-- The entry label of function `f`. -/
def fnL (f : FnName) : Label := "ca_f_" ++ f

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
  /-- The results this function sets at every return: its longest `return` (`Stmt.nret`). -/
  nr : Nat := tab.nres
  /-- The result counts of the program's functions, by `nameCode` (`Prog.nrt`), for the call
  sites: a call sets only the callee's results, and the caller zeroes the locals it reads past
  them. -/
  nrt : NTree := .leaf
  /-- The function calls nothing: then it may keep locals in registers (`alloc`), and may have no
  frame. -/
  leaf : Bool := false
  /-- The locals kept in registers (`leafAlloc`); the others are in the frame. -/
  alloc : List (Var × Reg64) := []
  /-- The frame's size in words, if the function may make tail calls (it calls, so it has a
  frame): a tail call pops the frame and jumps. -/
  tailF : Option Nat := none
  /-- The tier local (lane tiercost): a parameter of a leaf whose tier bit `x & 1` is kept in
  `rsi`, so that its tiered accesses address `[r15 + 8 rsi + d]` with no code for the tier. -/
  treg : Option Var := none
  /-- The largest frame (in words) of the leaves without a stack check that the function calls
  (`Stmt.need`): its own stack check leaves room for that frame below the return address. -/
  need : Nat := 0
  /-- The facts of the bounds-check analysis at the current statement (`Bce.lean`): an access
  whose index they prove in range has no bounds check (`Ctx.ck`). `none`: unreachable. -/
  fa : Option Facts := some {}
  deriving Repr

/-- The registers a leaf keeps locals in: the argument registers (`argRegs`), then `rbx`, `r12`,
`r13` (the trampoline saves them for its caller); neither the scratch registers `rax`/`rcx`/`rdx`,
nor `rsp`, `rbp` (the trampoline's), `r14` (fuel), `r15` (the table). The non-parameter locals
take `r13`, `r12`, `rbx` first (`leafAlloc`). -/
def allocRegs : List Reg64 := [.rdi, .r8, .r9, .r10, .r11, .rsi, .rbx, .r12, .r13]

/-- The argument registers: a call with at most 6 arguments passes argument `i` in
`argRegs[i]`; more go through memory at `rsi`. -/
def argRegs : List Reg64 := [.rdi, .r8, .r9, .r10, .r11, .rsi]

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

/-- No local lives in `rbx`: `if c abort k` may carry its code there. -/
def Ctx.rbxFree (ctx : Ctx) : Bool := !(ctx.alloc.any (·.2 == .rbx))

/-- An access with key `k` and index `i` to an array of minimum length `mn` needs its bounds check:
the facts do not prove `i` in range (`safeIdx`). -/
def Ctx.ck (ctx : Ctx) (k : Option AKey) (i : Expr) (mn : Nat) : Bool := !safeIdx ctx.fa k i mn

/-- The bounds check of index register `r` against the length at `ln`, if `ck`. -/
def chkR (ck : Bool) (r : Reg64) (ln : AddrExpr) : Program :=
  if ck then [i64 (.cmp (.reg (rr r)) (oM ln)), jccL .nc errorL] else []

/-- The bounds check of index register `r` against the constant length `n`, if `ck`. -/
def chkI (ck : Bool) (r : Reg64) (n : Nat) : Program :=
  if ck then [i64 (.cmp (.reg (rr r)) (oI n)), jccL .nc errorL] else []

/-- `d := byte [r15 + d + off]`, zero-extended: a read of the constant data at `off` from the
table (`ldc`, indexed by `d`). -/
abbrev ldcA (d : Reg64) (off : Int) : Directive :=
  i64 (.movzx (.reg (rr d)) (w' := .W8) (.mem ⟨some (.reg .r15), some ⟨d, .W8⟩, .int64 (Int64.ofInt off)⟩))

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

/-! ### Simple operands (lane `compopt`, prototype A)

A right operand that is a variable, a global, an array length or a constant is not evaluated into
`rax` and spilled: it is used in place, as a memory operand or an immediate (`simpleOp`), or loaded
straight into `rcx`/`rdx` (`loadInto`). -/

/-- The operand that reads `e` without code, if there is one. -/
def simpleOp (ctx : Ctx) : Expr → Option (Operand .W64)
  | .var x =>
    match ctx.alloc.lookup x with
    | some r => some (oR r)
    | none => some (oM (mb .rsp (8 * x)))
  | .glob g => some (oM (mb .r15 (ctx.tab.globOff g)))
  | .len8 a => some (oM (mb .r15 (ctx.tab.len8 a)))
  | .len64 a => some (oM (mb .r15 (ctx.tab.len64 a)))
  | .const w => if fitsImm32 w then some (.imm (.int64 w.toInt64)) else none
  | _ => none

/-- `r := e` in one instruction, for a simple `e` (any constant). -/
def loadInto (ctx : Ctx) (r : Reg64) : Expr → Option Program
  | .const w => some [movRI r w]
  | e => (simpleOp ctx e).map fun o => [i64 (.mov (.reg (rr r)) o)]

/-- `dst := dst op o` in one instruction, for the operations x64 has in the two-operand form
`op r/m, r/m/imm` (add, sub, and, or, xor). -/
def aluDirect : BinOp → RegOrMem .W64 → Operand .W64 → Option Directive
  | .add, m, o => some (i64 (.add m o))
  | .sub, m, o => some (i64 (.sub m o))
  | .and, m, o => some (i64 (.and m o))
  | .or, m, o => some (i64 (.or m o))
  | .xor, m, o => some (i64 (.xor m o))
  | _, _, _ => none

/-- `rax := rax op o` in one instruction, where x64 has the form. -/
def binDirect : BinOp → Operand .W64 → Option Directive
  | .mul, .regOrMem m => some (i64 (.imul none (.reg (rr .rax)) (.regOrMem m)))
  | op, o => aluDirect op (.reg (rr .rax)) o

/-- `rax := rax op b` for a simple `b`, without temporaries. -/
def binSimple (ctx : Ctx) (op : BinOp) (b : Expr) : Option Program :=
  match op, b with
  | .shl, .const k => some [i64 (.shl (.reg (rr .rax)) (.imm8 (.int64 (Int64.ofInt (k.toNat % 64)))))]
  | .shr, .const k => some [i64 (.shr (.reg (rr .rax)) (.imm8 (.int64 (Int64.ofInt (k.toNat % 64)))))]
  | .mul, .const k =>
    -- strength reduction: a power of two is a shift
    if k.toNat == 2 ^ Nat.log2 k.toNat then
      some [i64 (.shl (.reg (rr .rax)) (.imm8 (.int64 (Int64.ofInt (Nat.log2 k.toNat)))))]
    else (loadInto ctx .rcx (.const k)).map (· ++ binCode .mul)
  | _, _ =>
    match (simpleOp ctx b).bind (binDirect op) with
    | some d => some [d]
    | none => (loadInto ctx .rcx b).map (· ++ binCode op)

/-- `cmp rax, b` for a simple `b`. -/
def cmpSimple (ctx : Ctx) (b : Expr) : Option Program :=
  match simpleOp ctx b with
  | some o => some [i64 (.cmp (.reg (rr .rax)) o)]
  | none => (loadInto ctx .rcx b).map (· ++ [i64 (.cmp (.reg (rr .rax)) (oR .rcx))])

/-- The condition code under which `cmp b, a` (the operands swapped) makes `a op b` true. -/
def swapCC : Cmp → CondCode
  | .eq => .z | .ne => .nz | .ult => .a | .ule => .nc | .slt => .g | .sle => .ge

/-- `cmp m, o` exists: not memory with memory. -/
def cmpOk : RegOrMem .W64 → Operand .W64 → Bool
  | .mem _, .regOrMem (.mem _) => false
  | _, _ => true

/-- `a op b` compared in place (lane leafgen, step G1), for simple `a` and `b`: one `cmp` of a
register or memory operand with a register, memory or immediate operand (not memory with memory),
the operands swapped for a constant `a`. The instruction, and the condition code under which the
comparison holds. -/
def cmpIn (ctx : Ctx) (op : Cmp) (a b : Expr) : Option (CondCode × Directive) :=
  match simpleOp ctx a, simpleOp ctx b with
  | some (.regOrMem m), some o => if cmpOk m o then some (cmpCC op, i64 (.cmp m o)) else none
  | some o, some (.regOrMem m) => if cmpOk m o then some (swapCC op, i64 (.cmp m o)) else none
  | _, _ => none

/-- `r := r & 1`: from a tier word in `r`, the tier, which indexes the descriptor words (tier `1`
of array `a` is at the position after tier `0`'s, its descriptor words 8 bytes after `a`'s:
`Tab.pos64_tierA`). -/
def tierDesc (r : Reg64) : Program :=
  [i64 (.and (.reg (rr r)) (.imm (.int64 (1 : Word).toInt64)))]

/-- `[r15 + 8 r + d]`: a descriptor word of tier `r` (`tierDesc`). -/
abbrev tdesc (r : Reg64) (d : Int) : AddrExpr := ⟨some (.reg .r15), some ⟨r, .W64⟩, .int64 (Int64.ofInt d)⟩

/-- Is `t` the tier local (whose tier is in `rsi`)? -/
def Ctx.isT (ctx : Ctx) : Expr → Bool
  | .var x => ctx.treg == some x
  | _ => false

/-- `rsi := rax & 1`: the tier of a new value of the tier local. -/
def tregSet : Program :=
  [movRR .rsi .rax, i64 (.and (.reg (rr .rsi)) (.imm (.int64 (1 : Word).toInt64)))]

/-! ### Blocks (lane blkcopy) -/

/-- The operand of a block operand `e` (`Expr.isOpnd e`). -/
def opnd (ctx : Ctx) (e : Expr) : Operand .W64 := (simpleOp ctx e).getD (oI 0)

/-- `r := len(s)`: the length of a byte source. -/
def srcLen (ctx : Ctx) (r : Reg64) : BSrc → Directive
  | .arr a => movRM r (mb .r15 (ctx.tab.len8 a))
  | .rom d => movRI r (UInt64.ofNat d.length)

/-- `rcx :=` the address of byte `0` of a byte source. -/
def srcBase (ctx : Ctx) : BSrc → Directive
  | .arr a => movRM .rcx (mb .r15 (ctx.tab.base8 a))
  | .rom d => i64 (.lea (rr .rcx) (mb .r15 (ctx.tab.romBase + romIdx d ctx.tab.rom)))

/-- `r := T + 8 (r & 1)`: from a tier word in `r`, the address of the tier's descriptor words
relative to tier `0`'s (`Tab.pos64_tierA`). -/
def tierBlk (r : Reg64) : Program :=
  [i64 (.and (.reg (rr r)) (.imm (.int64 (1 : Word).toInt64))),
   i64 (.shl (.reg (rr r)) (.imm8 (.int64 (Int64.ofInt 3)))),
   i64 (.add (.reg (rr r)) (oR .r15))]

/-- The code that points `r` at the descriptor words of a block operand (`tierBlk`), and that
register (`r15` for a plain array: no code). -/
def warrDesc (ctx : Ctx) (r : Reg64) : WArr → Program × Reg64
  | .plain _ => ([], .r15)
  | .tier _ t => ([i64 (.mov (.reg (rr r)) (opnd ctx t))] ++ tierBlk r, r)

/-- From `rax` = a length: `n ≤ rax` and `o ≤ rax - n`, else to `ca_error` (`o + n ≤ len`
without a carry). -/
def lenChk (ctx : Ctx) (o n : Expr) : Program :=
  [i64 (.cmp (.reg (rr .rax)) (opnd ctx n)), jccL .c errorL,
   i64 (.sub (.reg (rr .rax)) (opnd ctx n)), i64 (.cmp (.reg (rr .rax)) (opnd ctx o)), jccL .c errorL]

/-- `r := base + 8 o` for a word array whose descriptor words are at `R`, through `rax`. -/
def wordPtr (ctx : Ctx) (r R : Reg64) (a : ArrId) (o : Expr) : Program :=
  [movRM r (mb R (ctx.tab.base64 a)), i64 (.mov (.reg (rr .rax)) (opnd ctx o)),
   i64 (.shl (.reg (rr .rax)) (.imm8 (.int64 (Int64.ofInt 3)))),
   i64 (.add (.reg (rr .rax)) (oR r)), movRR r .rax]

/-- The copy loop of `copy64`: from `rcx` (source), `rdx` (destination) up to the end in `e`. -/
def copy64Loop (Lb : Label) (e : AddrExpr) : Program :=
  [.label Lb, movRM .rax (mb .rcx 0), movMR (mb .rdx 0) .rax,
   i64 (.add (.reg (rr .rcx)) (oI 8)), i64 (.add (.reg (rr .rdx)) (oI 8)),
   i64 (.cmp (.reg (rr .rcx)) (oM e)), jccL .c Lb]

/-- `copy D[di ..] := S[si ..] for n`: the source checked and pointed at by `rcx`, the
destination by `rdx`, the end of the source in temporary `0`, then 6 instructions per word. -/
def copy64Code (ctx : Ctx) (path : Path) (d : WArr) (di : Expr) (s : WArr) (si n : Expr) : Program :=
  (warrDesc ctx .rcx s).1 ++ [movRM .rax (mb (warrDesc ctx .rcx s).2 (ctx.tab.len64 s.arr))] ++
  lenChk ctx si n ++ wordPtr ctx .rcx (warrDesc ctx .rcx s).2 s.arr si ++
  (warrDesc ctx .rdx d).1 ++ [movRM .rax (mb (warrDesc ctx .rdx d).2 (ctx.tab.len64 d.arr))] ++
  lenChk ctx di n ++ wordPtr ctx .rdx (warrDesc ctx .rdx d).2 d.arr di ++
  [i64 (.mov (.reg (rr .rax)) (opnd ctx n)),
   i64 (.shl (.reg (rr .rax)) (.imm8 (.int64 (Int64.ofInt 3)))),
   i64 (.add (.reg (rr .rax)) (oR .rcx)), movMR (ctx.tmp 0) .rax,
   i64 (.cmp (.reg (rr .rcx)) (oM (ctx.tmp 0))), jccL .nc (ctx.lbl path "X")] ++
  copy64Loop (ctx.lbl path "L") (ctx.tmp 0) ++ [.label (ctx.lbl path "X")]

/-- The copy loop of `copy8w`. -/
def copy8wLoop (Lb : Label) (e : AddrExpr) : Program :=
  [.label Lb, i64 (.movzx (.reg (rr .rax)) (w' := .W8) (.mem (mb .rcx 0))), movMR (mb .rdx 0) .rax,
   i64 (.add (.reg (rr .rcx)) (oI 1)), i64 (.add (.reg (rr .rdx)) (oI 8)),
   i64 (.cmp (.reg (rr .rcx)) (oM e)), jccL .c Lb]

/-- `copy D[di ..] := S.u8[si ..] for n`, 6 instructions per byte. -/
def copy8wCode (ctx : Ctx) (path : Path) (d : WArr) (di : Expr) (s : BSrc) (si n : Expr) : Program :=
  [srcLen ctx .rax s] ++ lenChk ctx si n ++
  [srcBase ctx s, i64 (.mov (.reg (rr .rax)) (opnd ctx si)), i64 (.add (.reg (rr .rax)) (oR .rcx)),
   movRR .rcx .rax] ++
  (warrDesc ctx .rdx d).1 ++ [movRM .rax (mb (warrDesc ctx .rdx d).2 (ctx.tab.len64 d.arr))] ++
  lenChk ctx di n ++ wordPtr ctx .rdx (warrDesc ctx .rdx d).2 d.arr di ++
  [i64 (.mov (.reg (rr .rax)) (opnd ctx n)), i64 (.add (.reg (rr .rax)) (oR .rcx)), movMR (ctx.tmp 0) .rax,
   i64 (.cmp (.reg (rr .rcx)) (oM (ctx.tmp 0))), jccL .nc (ctx.lbl path "X")] ++
  copy8wLoop (ctx.lbl path "L") (ctx.tmp 0) ++ [.label (ctx.lbl path "X")]

/-- The address `[r15 + rdx + off]` (the class table, indexed by a byte). -/
abbrev tblAddr (off : Int) : AddrExpr := ⟨some (.reg .r15), some ⟨.rdx, .W8⟩, .int64 (Int64.ofInt off)⟩

/-- The loop of `scan8`: per byte the byte, its class (constant data at `[r15 + off]`) and the
tests, 7 instructions. -/
def scanLoop (Lb Xb : Label) (off : Int) (eo : Operand .W64) : Program :=
  [.label Lb,
   i64 (.movzx (.reg (rr .rdx)) (w' := .W8) (.mem (mbi .rcx .rax .W8))),
   i64 (.movzx (.reg (rr .rdx)) (w' := .W8) (.mem (tblAddr off))),
   i64 (.cmp (.reg (rr .rdx)) (oI 0)), jccL .nz Xb,
   i64 (.add (.reg (rr .rax)) (oI 1)), i64 (.cmp (.reg (rr .rax)) eo), jccL .c Lb]

/-- `x := scan S.u8[i .. e] until c`: `rcx` = the source, `rax` = the position. -/
def scan8Code (ctx : Ctx) (path : Path) (s : BSrc) (i e : Expr) (c : List UInt8) : Program :=
  [srcLen ctx .rdx s, i64 (.mov (.reg (rr .rax)) (opnd ctx e)), i64 (.cmp (.reg (rr .rax)) (oR .rdx)),
   jccL .a errorL,
   i64 (.mov (.reg (rr .rax)) (opnd ctx i)), i64 (.cmp (.reg (rr .rax)) (opnd ctx e)), jccL .a errorL,
   srcBase ctx s,
   i64 (.cmp (.reg (rr .rax)) (opnd ctx e)), jccL .nc (ctx.lbl path "X")] ++
  scanLoop (ctx.lbl path "L") (ctx.lbl path "X") (ctx.tab.romBase + romIdx c ctx.tab.rom) (opnd ctx e) ++
  [.label (ctx.lbl path "X")]

/-! ### The register-stack code generator (lane leafgen, step G2)

`gen ctx e d fr`: code that evaluates `e` into register `d`, with the registers `fr` as scratch
and nothing else: no frame temporaries, no memory writes. Operands are used in place (registers,
memory, immediates, `lea`), a constant index is folded into the address. `none` where it does
not apply: then the statement falls back to the old code (`compileE`). `d` and `fr` are distinct
registers of `Ctx.pool`. Structural recursion (the kernel evaluates it, `asm_lit`): the binary
forms get the code generators of their operands as functions (`genBin`, `genLd`, `genCmp`). -/

/-- The scratch registers of a function: `rax rcx rdx`, then the argument registers that hold no
local (and not `rsi` when it holds the tier). -/
def Ctx.pool (ctx : Ctx) : List Reg64 :=
  [.rax, .rcx, .rdx] ++ [Reg64.r11, .r10, .r9, .r8, .rdi, .rsi].filter fun r =>
    !(ctx.alloc.any (·.2 == r)) && !(r == .rsi && ctx.treg.isSome)

/-- The register of a local kept in one. -/
def regOf (ctx : Ctx) : Expr → Option Reg64
  | .var x => ctx.alloc.lookup x
  | _ => none

/-- `d := d op o` in one instruction, where x64 has the two-operand form. -/
def aluOp (op : BinOp) (d : Reg64) (o : Operand .W64) : Option Directive :=
  match op with
  | .mul => some (i64 (.imul none (.reg (rr d)) o))
  | _ => aluDirect op (.reg (rr d)) o

def _root_.L.BinOp.comm : BinOp → Bool
  | .add | .mul | .and | .or | .xor => true
  | _ => false

/-- A code generator for one operand: target register, scratch registers. -/
abbrev GenF := Reg64 → List Reg64 → Option Program

/-- `d := a + k`, `d := a - k`, `d := a + y` in one `lea`, for `a` (and `y`) kept in registers. -/
def genLea (ctx : Ctx) (op : BinOp) (a b : Expr) (d : Reg64) : Option Program :=
  match op, regOf ctx a, b with
  | .add, some r, .const k => if fitsImm32 k then some [i64 (.lea (rr d) (mb r k.toInt64.toInt))] else none
  | .sub, some r, .const k => if fitsImm32 (0 - k) then some [i64 (.lea (rr d) (mb r (0 - k).toInt64.toInt))] else none
  | .add, some r, .var y => (ctx.alloc.lookup y).map fun s => [i64 (.lea (rr d) ⟨some (.reg r), some ⟨s, .W8⟩, .int64 0⟩)]
  | _, _, _ => none

/-- `d := a op b` for the two-operand forms: `lea`; `b` in place; `a` in place for a commutative
`op`; else `a` into `d`, `b` into a scratch register. -/
def genAlu (ctx : Ctx) (op : BinOp) (a b : Expr) (ga gb : GenF) (d : Reg64) (fr : List Reg64) :
    Option Program :=
  match genLea ctx op a b d with
  | some c => some c
  | none =>
  match simpleOp ctx b with
  | some ob => (ga d fr).bind fun ca => (aluOp op d ob).map fun i => ca ++ [i]
  | none =>
  match (if op.comm then simpleOp ctx a else none) with
  | some oa => (gb d fr).bind fun cb => (aluOp op d oa).map fun i => cb ++ [i]
  | none =>
  match fr with
  | t :: fr' => (ga d fr).bind fun ca => (gb t fr').bind fun cb =>
      (aluOp op d (oR t)).map fun i => ca ++ cb ++ [i]
  | [] => none

/-- `d := mulhi a b`: `a` into `rax`, `b` into a register `t`, `mul t` (`rdx:rax := rax * t`),
`d := rdx`; `rax` and `rdx` among the target and scratch registers. -/
def genMulhi (ga gb : GenF) (d : Reg64) (fr : List Reg64) : Option Program :=
  if (d == .rax || fr.contains .rax) && fr.contains .rdx then
    match (d :: fr).filter (fun r => r != .rax && r != .rdx) with
    | t :: _ =>
      (ga .rax ((d :: fr).filter (· != .rax))).bind fun ca =>
      (gb t ((d :: fr).filter fun r => r != .rax && r != t)).map fun cb =>
        ca ++ cb ++ [i64 (.mul (.reg (rr t))), movRR d .rdx]
    | [] => none
  else none

/-- `d := a op b`. -/
def genBin (ctx : Ctx) (op : BinOp) (a b : Expr) (ga gb : GenF) (d : Reg64) (fr : List Reg64) :
    Option Program :=
  match op, b with
  | .shl, .const k => (ga d fr).map (· ++ [i64 (.shl (.reg (rr d)) (.imm8 (.int64 (Int64.ofInt (k.toNat % 64)))))])
  | .shr, .const k => (ga d fr).map (· ++ [i64 (.shr (.reg (rr d)) (.imm8 (.int64 (Int64.ofInt (k.toNat % 64)))))])
  | .mul, .const k =>
    if k.toNat == 2 ^ Nat.log2 k.toNat then
      (ga d fr).map (· ++ [i64 (.shl (.reg (rr d)) (.imm8 (.int64 (Int64.ofInt (Nat.log2 k.toNat)))))])
    else genAlu ctx .mul a (.const k) ga gb d fr
  | .mulhi, _ => genMulhi ga gb d fr
  | .shl, _ | .shr, _ => none
  | op, b => genAlu ctx op a b ga gb d fr

/-- `d :=` the element at `m`: a byte (zero-extended) or a word. -/
def ldA (byte : Bool) (d : Reg64) (m : AddrExpr) : Directive :=
  if byte then i64 (.movzx (.reg (rr d)) (w' := .W8) (.mem m)) else movRM d m

/-- `[b + i]` (bytes) or `[b + 8 i]` (words). -/
def mbx (b i : Reg64) (byte : Bool) : AddrExpr := ⟨some (.reg b), some ⟨i, if byte then .W8 else .W64⟩, .int64 0⟩

/-- `d := A[i]`, where `[ln]` is `A`'s length and `[bs]` its base: the bounds check, then the load,
with a constant index folded into the displacement and a local's register as the index. A
constant index below `mn`, a minimum length of `A` (`Tab.min64`), needs no check. -/
def genLd (ctx : Ctx) (ln bs : AddrExpr) (byte : Bool) (mn : Nat) (ck : Bool) (i : Expr) (gi : GenF)
    (d : Reg64) (fr : List Reg64) : Option Program :=
  match i with
  | .const k =>
    if k.toNat < 2 ^ 28 then
      if k.toNat < mn || !ck then
        some [movRM d bs, ldA byte d (mb d (if byte then k.toNat else 8 * k.toNat))]
      else
      some [i64 (.cmp (.mem ln) (oI k.toNat)), jccL .be errorL, movRM d bs,
        ldA byte d (mb d (if byte then k.toNat else 8 * k.toNat))]
    else none
  | i =>
    match regOf ctx i with
    | some r => some (chkR ck r ln ++ [movRM d bs, ldA byte d (mbx d r byte)])
    | none =>
      match fr with
      | t :: _ => (gi d fr).map fun ci =>
          ci ++ (chkR ck d ln ++ [movRM t bs, ldA byte d (mbx t d byte)])
      | [] => none

/-- `d := A[i]` for the table-relative array `A` at `T + c` (`Tab.tbl64`), `[ln]` its length: the
bounds check (none for a constant index below the minimum length `mn`), then one load addressed
from `r15`, `[r15 + c + 8k]` or `[r15 + 8 i + c]`. -/
def genLdT (ctx : Ctx) (ln : AddrExpr) (c mn : Nat) (ck : Bool) (i : Expr) (gi : GenF) (d : Reg64)
    (fr : List Reg64) : Option Program :=
  match i with
  | .const k =>
    if c + 8 * k.toNat < 2 ^ 31 then
      if k.toNat < mn || !ck then some [movRM d (mb .r15 (c + 8 * k.toNat : Nat))]
      else some [i64 (.cmp (.mem ln) (oI k.toNat)), jccL .be errorL, movRM d (mb .r15 (c + 8 * k.toNat : Nat))]
    else none
  | i =>
    if c < 2 ^ 31 then
      match regOf ctx i with
      | some r => some (chkR ck r ln ++ [movRM d (tdesc r c)])
      | none => (gi d fr).map fun ci =>
          ci ++ (chkR ck d ln ++ [movRM d (tdesc d c)])
    else none

/-- `d := A.u32[x]` (lane p32), where `[ln]` is `A`'s length in 32-bit elements (`Tab.len32`)
and `[bs]` its base: the bounds check `x < len32`, the base into the scratch register `t`, the
4-byte load at `t + 4 x` (zero-extended). -/
def ld32Code (ck : Bool) (x t d : Reg64) (ln bs : AddrExpr) : Program :=
  chkR ck x ln ++ [movRM t bs, ld32X d t x]

/-- `d := A[x]`'s half `hi` (lane p32use), where `[ln]` is `A`'s length in words and `[bs]` its
base: the bounds check `x < len` (as for a word load), the base into the scratch register `t`,
the 4-byte load at `t + 8 x + 4 hi` (zero-extended). -/
def ld32hCode (ck : Bool) (x t d : Reg64) (ln bs : AddrExpr) (hi : Bool) : Program :=
  chkR ck x ln ++ [movRM t bs, ld32H d t x hi]

/-- `d := A[i]`'s half `hi` through the register stack: the index a local's register or computed
into `d`, then `ld32hCode` with the first scratch register. -/
def genLd32h (ctx : Ctx) (ln bs : AddrExpr) (hi : Bool) (ck : Bool) (i : Expr) (gi : GenF) (d : Reg64)
    (fr : List Reg64) : Option Program :=
  match fr with
  | t :: _ =>
    match regOf ctx i with
    | some r => some (ld32hCode ck r t d ln bs hi)
    | none => (gi d fr).map fun ci => ci ++ ld32hCode ck d t d ln bs hi
  | [] => none

/-- `d := A.u32[i]` through the register stack: the index a local's register or computed into `d`,
then `ld32Code` with the first scratch register. -/
def genLd32 (ctx : Ctx) (ln bs : AddrExpr) (ck : Bool) (i : Expr) (gi : GenF) (d : Reg64) (fr : List Reg64) :
    Option Program :=
  match fr with
  | t :: _ =>
    match regOf ctx i with
    | some r => some (ld32Code ck r t d ln bs)
    | none => (gi d fr).map fun ci => ci ++ ld32Code ck d t d ln bs
  | [] => none

/-- Flags for `a op b` and the condition code under which it holds: in place (`cmpIn`), else
the operand that is not simple into a scratch register, else both. -/
def genCmp (ctx : Ctx) (op : Cmp) (a b : Expr) (ga gb : GenF) (fr : List Reg64) :
    Option (CondCode × Program) :=
  match cmpIn ctx op a b with
  | some (cc, i) => some (cc, [i])
  | none =>
  match fr with
  | t :: fr' =>
    match simpleOp ctx b with
    | some ob => (ga t fr').map fun ca => (cmpCC op, ca ++ [i64 (.cmp (.reg (rr t)) ob)])
    | none =>
    match simpleOp ctx a with
    | some oa => (gb t fr').map fun cb => (swapCC op, cb ++ [i64 (.cmp (.reg (rr t)) oa)])
    | none =>
    match fr' with
    | u :: fr'' => (ga t fr').bind fun ca => (gb u fr'').map fun cb =>
        (cmpCC op, ca ++ cb ++ [i64 (.cmp (.reg (rr t)) (oR u))])
    | [] => none
  | [] => none

def gen (ctx : Ctx) : Expr → Reg64 → List Reg64 → Option Program
  | .const w, d, _ => some [movRI d w]
  | .var x, d, _ =>
    match ctx.alloc.lookup x with
    | some r => some [movRR d r]
    | none => some [movRM d (mb .rsp (8 * x))]
  | .glob g, d, _ => some [movRM d (mb .r15 (ctx.tab.globOff g))]
  | .len8 a, d, _ => some [movRM d (mb .r15 (ctx.tab.len8 a))]
  | .len64 a, d, _ => some [movRM d (mb .r15 (ctx.tab.len64 a))]
  | .bin op a b, d, fr => genBin ctx op a b (gen ctx a) (gen ctx b) d fr
  | .ld8 a i, d, fr =>
    genLd ctx (mb .r15 (ctx.tab.len8 a)) (mb .r15 (ctx.tab.base8 a)) true 0 (ctx.ck (some (.b a)) i 0) i
      (gen ctx i) d fr
  | .ld64 a i, d, fr =>
    match ctx.tab.tbl64 a with
    | some c => genLdT ctx (mb .r15 (ctx.tab.len64 a)) c (ctx.tab.min64 a)
      (ctx.ck (some (.w a)) i (ctx.tab.min64 a)) i (gen ctx i) d fr
    | none =>
    genLd ctx (mb .r15 (ctx.tab.len64 a)) (mb .r15 (ctx.tab.base64 a)) false (ctx.tab.min64 a)
      (ctx.ck (some (.w a)) i (ctx.tab.min64 a)) i (gen ctx i) d fr
  | .ld64t a t i, d, fr =>
    if ctx.isT t then
      genLd ctx (tdesc .rsi (ctx.tab.len64 a)) (tdesc .rsi (ctx.tab.base64 a)) false (ctx.tab.min64t a)
        (ctx.ck (keyT a t) i (ctx.tab.min64t a)) i (gen ctx i) d fr
    else
      match fr with
      | s :: fr' => (gen ctx t s fr').bind fun ct =>
          (genLd ctx (tdesc s (ctx.tab.len64 a)) (tdesc s (ctx.tab.base64 a)) false (ctx.tab.min64t a)
            (ctx.ck (keyT a t) i (ctx.tab.min64t a)) i (gen ctx i) d fr').map
            fun c => ct ++ tierDesc s ++ c
      | [] => none
  | .len64t a t, d, fr =>
    if ctx.isT t then some [movRM d (tdesc .rsi (ctx.tab.len64 a))]
    else (gen ctx t d fr).map fun ct => ct ++ tierDesc d ++ [movRM d (tdesc d (ctx.tab.len64 a))]
  | .ldc dd i, d, fr => (gen ctx i d fr).map fun ci =>
    ci ++ (chkI (ctx.ck none i dd.length) d dd.length ++ [ldcA d (ctx.tab.romBase + romIdx dd ctx.tab.rom)])
  | .cmpw op a b, d, fr =>
    match fr with
    | t :: _ => (genCmp ctx op a b (gen ctx a) (gen ctx b) (d :: fr)).map fun (cc, code) =>
        code ++ [movRI d 0, movRI t 1, i64 (.cmovcc cc (rr d) (.reg (rr t)))]
    | [] => none
  | .ld8x8 _ _, _, _ => none
  | .ld32t a t i, d, fr =>
    if ctx.isT t then
      genLd32 ctx (tdesc .rsi (ctx.tab.len32 a)) (tdesc .rsi (ctx.tab.base64 a))
        (ctx.ck (key32 a t) i (2 * ctx.tab.min64t a)) i (gen ctx i) d fr
    else
    match t.constTier? with
    | some c =>
      genLd32 ctx (mb .r15 (ctx.tab.len32 (tierA a c))) (mb .r15 (ctx.tab.base64 (tierA a c)))
        (ctx.ck (key32 a t) i (2 * ctx.tab.min64 (tierA a c))) i (gen ctx i) d fr
    | none =>
      match fr with
      | s :: fr' => (gen ctx t s fr').bind fun ct =>
          (genLd32 ctx (tdesc s (ctx.tab.len32 a)) (tdesc s (ctx.tab.base64 a))
            (ctx.ck (key32 a t) i (2 * ctx.tab.min64t a)) i (gen ctx i) d fr').map
            fun c => ct ++ tierDesc s ++ c
      | [] => none
  | .ld32h a t i hi, d, fr =>
    if ctx.isT t then
      genLd32h ctx (tdesc .rsi (ctx.tab.len64 a)) (tdesc .rsi (ctx.tab.base64 a)) hi
        (ctx.ck (keyT a t) i (ctx.tab.min64t a)) i (gen ctx i) d fr
    else
      match fr with
      | s :: fr' => (gen ctx t s fr').bind fun ct =>
          (genLd32h ctx (tdesc s (ctx.tab.len64 a)) (tdesc s (ctx.tab.base64 a)) hi
            (ctx.ck (keyT a t) i (ctx.tab.min64t a)) i (gen ctx i) d fr').map
            fun c => ct ++ tierDesc s ++ c
      | [] => none

/-- `x := rax`. -/
def storeRax (ctx : Ctx) (x : Var) : Directive :=
  match ctx.alloc.lookup x with
  | some r => movRR r .rax
  | none => movMR (mb .rsp (8 * x)) .rax

/-- `rax := e`. -/
def compileE (ctx : Ctx) : Expr → Nat → Program
  | .const w, _ => [movRI .rax w]
  | .var x, _ =>
    match ctx.alloc.lookup x with
    | some r => [movRR .rax r]
    | none => [movRM .rax (mb .rsp (8 * x))]
  | .bin op a b, t =>
    match binSimple ctx op b with
    | some code => compileE ctx a t ++ code
    | none =>
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
    match cmpIn ctx op a b with
    | some (cc, d) => [d, movRI .rax 0, movRI .rdx 1, i64 (.cmovcc cc (rr .rax) (.reg (rr .rdx)))]
    | none =>
    match cmpSimple ctx b with
    | some code => compileE ctx a t ++ code ++
      [movRI .rax 0, movRI .rdx 1, i64 (.cmovcc (cmpCC op) (rr .rax) (.reg (rr .rdx)))]
    | none =>
    compileE ctx a t ++ [movMR (ctx.tmp t) .rax] ++ compileE ctx b (t + 1) ++
      [movRR .rcx .rax, movRM .rax (ctx.tmp t), i64 (.cmp (.reg (rr .rax)) (oR .rcx)),
       movRI .rax 0, movRI .rdx 1, i64 (.cmovcc (cmpCC op) (rr .rax) (.reg (rr .rdx)))]
  | .ldc d i, t =>
    compileE ctx i t ++
      [i64 (.cmp (.reg (rr .rax)) (oI d.length)), jccL .nc errorL,
       i64 (.lea (rr .rcx) (mb .r15 (ctx.tab.romBase + romIdx d ctx.tab.rom))),
       i64 (.movzx (.reg (rr .rax)) (w' := .W8) (.mem (mbi .rcx .rax .W8)))]
  | .glob g, _ => [movRM .rax (mb .r15 (ctx.tab.globOff g))]
  | .ld64t a t i, k =>
    if ctx.isT t then
      compileE ctx i k ++
      [i64 (.cmp (.reg (rr .rax)) (oM (tdesc .rsi (ctx.tab.len64 a)))), jccL .nc errorL,
       movRM .rcx (tdesc .rsi (ctx.tab.base64 a)),
       movRM .rax (mbi .rcx .rax .W64)]
    else
    (match loadInto ctx .rdx t with
     | some ld => compileE ctx i k ++ ld
     | none => compileE ctx t k ++ [movMR (ctx.tmp k) .rax] ++ compileE ctx i (k + 1) ++
         [movRM .rdx (ctx.tmp k)]) ++ tierDesc .rdx ++
      [i64 (.cmp (.reg (rr .rax)) (oM (tdesc .rdx (ctx.tab.len64 a)))), jccL .nc errorL,
       movRM .rcx (tdesc .rdx (ctx.tab.base64 a)),
       movRM .rax (mbi .rcx .rax .W64)]
  | .len64t a t, k =>
    if ctx.isT t then [movRM .rax (tdesc .rsi (ctx.tab.len64 a))]
    else compileE ctx t k ++ tierDesc .rax ++ [movRM .rax (tdesc .rax (ctx.tab.len64 a))]
  | .ld8x8 s i, k =>
    compileE ctx i k ++
      [srcLen ctx .rdx s, i64 (.cmp (.reg (rr .rdx)) (oI 8)), jccL .c errorL,
       i64 (.sub (.reg (rr .rdx)) (oI 8)), i64 (.cmp (.reg (rr .rax)) (oR .rdx)), jccL .a errorL,
       srcBase ctx s, movRM .rax (mbi .rcx .rax .W8)]
  | .ld32t a t i, k =>
    if ctx.isT t then
      compileE ctx i k ++ ld32Code true .rax .rcx .rax (tdesc .rsi (ctx.tab.len32 a)) (tdesc .rsi (ctx.tab.base64 a))
    else
    match t.constTier? with
    | some c =>
      compileE ctx i k ++
        ld32Code true .rax .rcx .rax (mb .r15 (ctx.tab.len32 (tierA a c))) (mb .r15 (ctx.tab.base64 (tierA a c)))
    | none =>
    (match loadInto ctx .rdx t with
     | some ld => compileE ctx i k ++ ld
     | none => compileE ctx t k ++ [movMR (ctx.tmp k) .rax] ++ compileE ctx i (k + 1) ++
         [movRM .rdx (ctx.tmp k)]) ++ tierDesc .rdx ++
      ld32Code true .rax .rcx .rax (tdesc .rdx (ctx.tab.len32 a)) (tdesc .rdx (ctx.tab.base64 a))
  | .ld32h a t i hi, k =>
    if ctx.isT t then
      compileE ctx i k ++ ld32hCode true .rax .rcx .rax (tdesc .rsi (ctx.tab.len64 a)) (tdesc .rsi (ctx.tab.base64 a)) hi
    else
    (match loadInto ctx .rdx t with
     | some ld => compileE ctx i k ++ ld
     | none => compileE ctx t k ++ [movMR (ctx.tmp k) .rax] ++ compileE ctx i (k + 1) ++
         [movRM .rdx (ctx.tmp k)]) ++ tierDesc .rdx ++
      ld32hCode true .rax .rcx .rax (tdesc .rdx (ctx.tab.len64 a)) (tdesc .rdx (ctx.tab.base64 a)) hi

/-- The negation of a condition code. -/
def CondCode.neg : CondCode → CondCode
  | .o => .no | .no => .o | .c => .nc | .nc => .c | .z => .nz | .nz => .z | .be => .a | .a => .be
  | .s => .ns | .ns => .s | .p => .np | .np => .p | .l => .ge | .ge => .l | .le => .g | .g => .le

/-- Jump to `l` if `c` evaluates to `b`; fall through otherwise. -/
def compileC (ctx : Ctx) (path : Path) : Cond → Bool → Label → Nat → Program
  | .cmp op a b, pol, l, t =>
    match genCmp ctx op a b (gen ctx a) (gen ctx b) ctx.pool with
    | some (cc, code) => code ++ [jccL (if pol then cc else CondCode.neg cc) l]
    | none =>
    match cmpSimple ctx b with
    | some code => compileE ctx a t ++ code ++
      [jccL (if pol then cmpCC op else CondCode.neg (cmpCC op)) l]
    | none =>
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

/-- Does `e` read register `r` (a local kept there)? -/
def Expr.readsReg (al : List (Var × Reg64)) (r : Reg64) : Expr → Bool
  | .var x => al.lookup x == some r
  | .bin _ a b | .cmpw _ a b => Expr.readsReg al r a || Expr.readsReg al r b
  | .ld8 _ i | .ld64 _ i | .ldc _ i => Expr.readsReg al r i
  | .ld64t _ t i => Expr.readsReg al r t || Expr.readsReg al r i
  | .len64t _ t => Expr.readsReg al r t
  | .ld8x8 _ i => Expr.readsReg al r i
  | .ld32t _ t i => Expr.readsReg al r t || Expr.readsReg al r i
  | .ld32h _ t i _ => Expr.readsReg al r t || Expr.readsReg al r i
  | _ => false

/-- `r := e` through the register stack (`r` not in the scratch registers `fr`): straight into
`r` when `e` does not read `r`, else into `rax` and moved. -/
def genInto (ctx : Ctx) (r : Reg64) (fr : List Reg64) (e : Expr) : Option Program :=
  if Expr.readsReg ctx.alloc r e then
    if fr.contains .rax then (gen ctx e .rax (fr.filter (· != .rax))).map (· ++ [movRR r .rax]) else none
  else gen ctx e r fr

/-- `r := e` (`r` not `rax`) with scratch `fr` (`genInto`); else one instruction for a simple
`e`, else through `rax`. -/
def valInto (ctx : Ctx) (r : Reg64) (fr : List Reg64) (e : Expr) : Program :=
  match genInto ctx r fr e with
  | some code => code
  | none =>
  match loadInto ctx r e with
  | some code => code
  | none => compileE ctx e 0 ++ [movRR r .rax]

/-- `rax := e` with scratch `fr` (`gen`), else `compileE`. -/
def valRax (ctx : Ctx) (fr : List Reg64) (e : Expr) : Program :=
  match gen ctx e .rax fr with
  | some code => code
  | none => compileE ctx e 0

/-- Results `i, i + 1, …` (`i ≥ 1`) of a `return` straight into their registers, with scratch
`fr` (the registers written are taken out of it). -/
def retRegs (ctx : Ctx) : List Reg64 → Nat → List Expr → Program
  | _, _, [] => []
  | fr, i, e :: es =>
    valInto ctx (resReg i) (fr.filter (· != resReg i)) e ++ retRegs ctx (fr.filter (· != resReg i)) (i + 1) es

/-- No value computed after result `i` is written (the later results, and result 0, computed
last) reads its register. -/
def retSafe (al : List (Var × Reg64)) (e0 : Expr) : Nat → List Expr → Bool
  | _, [] => true
  | i, _ :: es => !(e0 :: es).any (Expr.readsReg al (resReg i)) && retSafe al e0 (i + 1) es

/-- `retDirect` applies: the `n` results fit the registers, and no value reads a result register
written before it. -/
def retOk (al : List (Var × Reg64)) (es : List Expr) (n : Nat) : Bool :=
  match es with
  | [] => decide (n ≤ maxRes)
  | e0 :: rest => decide (n ≤ maxRes) && decide (es.length ≤ n) && retSafe al e0 1 rest

/-- The scratch registers left after `retRegs ctx fr i es`. -/
def retFree : List Reg64 → Nat → List Expr → List Reg64
  | fr, _, [] => fr
  | fr, i, _ :: es => retFree (fr.filter (· != resReg i)) (i + 1) es

/-- Set results `i, …, i + n - 1` (registers) to `0`. -/
def zeroRes : Nat → Nat → Program
  | _, 0 => []
  | i, n + 1 => movRI (resReg i) 0 :: zeroRes (i + 1) n

/-- `return es` with each value computed straight into its result register (no temporaries):
results `1, 2, …` first, then result 0 (`rax`, which computing any value clobbers), then zeros
up to `n`; when the results fit the registers and no value reads a result register written
before it. -/
def retDirect (ctx : Ctx) (es : List Expr) (n : Nat) : Option Program :=
  if retOk ctx.alloc es n then
    match es with
    | [] => some (zeroRes 0 n)
    | e0 :: rest => some (retRegs ctx ctx.pool 1 rest ++
        valRax ctx (retFree ctx.pool 1 rest |>.filter (· != .rax)) e0 ++ zeroRes es.length (n - es.length))
  else none

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

/-- Zero the locals `xs` (the results a call reads past the callee's `nrOf`). -/
def zeroVars : List Var → Program
  | [] => []
  | x :: xs => i64 (.mov (.mem (mb .rsp (8 * x))) (oI 0)) :: zeroVars xs

/-- Store results `i, i + 1, …` into the locals `xs` (a result `i ≥ maxRes` from the result area,
through `rcx`). -/
def storeRes (tab : Tab) : List Var → Nat → Program
  | [], _ => []
  | x :: xs, i =>
    (if i < maxRes then [movMR (mb .rsp (8 * x)) (resReg i)]
     else [movRM .rcx (mb .r15 (tab.resOff i)), movMR (mb .rsp (8 * x)) .rcx]) ++ storeRes tab xs (i + 1)

/-- `x := x op k` as one read-modify-write instruction on the frame slot (`op` add, sub, and, or,
xor; `k` an imm32 constant). -/
def setInPlace (ctx : Ctx) (x : Var) : Expr → Option Directive
  | .bin op (.var y) (.const k) =>
    if y == x && fitsImm32 k then
      aluDirect op (match ctx.alloc.lookup x with
        | some r => .reg (rr r)
        | none => .mem (mb .rsp (8 * x))) (.imm (.int64 k.toInt64))
    else none
  | _ => none

/-- A store's value: an imm32 constant or a local's register in place, else evaluated into a
scratch register; the code, the operand, and the scratch registers left. -/
def genStV (ctx : Ctx) (e : Expr) (fr : List Reg64) : Option (Program × Operand .W64 × List Reg64) :=
  match (match simpleOp ctx e with
    | some (.imm k) => some (Operand.imm k)
    | some (.regOrMem (.reg r)) => some (.regOrMem (.reg r))
    | _ => none) with
  | some o => some ([], o, fr)
  | none =>
    match fr with
    | v :: fr' => (gen ctx e v fr').map fun c => (c, oR v, fr')
    | [] => none

/-- `A.u64[i] := e` through the register stack, where `[ln]` is `A`'s length and `[bs]` its base:
the value (`genStV`), the index (a constant folded into the displacement, a local's register, or
evaluated into a scratch register), the bounds check (none for a constant index below the minimum
length `mn`), the base into a scratch register, the store. -/
def genSt (ctx : Ctx) (ln bs : AddrExpr) (mn : Nat) (ck : Bool) (i e : Expr) (fr : List Reg64) : Option Program :=
  match genStV ctx e fr with
  | none => none
  | some (cv, src, fr1) =>
    match i with
    | .const k =>
      if k.toNat < 2 ^ 28 then
        match fr1 with
        | t :: _ =>
          if k.toNat < mn || !ck then some (cv ++ [movRM t bs, i64 (.mov (.mem (mb t (8 * k.toNat))) src)])
          else some (cv ++ [i64 (.cmp (.mem ln) (oI k.toNat)), jccL .be errorL, movRM t bs,
            i64 (.mov (.mem (mb t (8 * k.toNat))) src)])
        | [] => none
      else none
    | i =>
      match regOf ctx i with
      | some r =>
        match fr1 with
        | t :: _ => some (cv ++ (chkR ck r ln ++ [movRM t bs, i64 (.mov (.mem (mbi t r .W64)) src)]))
        | [] => none
      | none =>
        match fr1 with
        | x :: t :: fr2 => (gen ctx i x (t :: fr2)).map fun ci =>
            cv ++ ci ++ (chkR ck x ln ++ [movRM t bs, i64 (.mov (.mem (mbi t x .W64)) src)])
        | _ => none

/-- `A.u64[i] := e` for the table-relative array `A` at `T + c` (`Tab.tbl64`), `[ln]` its length:
the value (`genStV`), the index (a constant folded into the displacement, a local's register, or
evaluated into a scratch register), the bounds check (none for a constant index below `mn`), one
store addressed from `r15`. -/
def genStT (ctx : Ctx) (ln : AddrExpr) (c mn : Nat) (ck : Bool) (i e : Expr) (fr : List Reg64) : Option Program :=
  match genStV ctx e fr with
  | none => none
  | some (cv, src, fr1) =>
    match i with
    | .const k =>
      if c + 8 * k.toNat < 2 ^ 31 then
        if k.toNat < mn || !ck then some (cv ++ [i64 (.mov (.mem (mb .r15 (c + 8 * k.toNat : Nat))) src)])
        else some (cv ++ [i64 (.cmp (.mem ln) (oI k.toNat)), jccL .be errorL,
          i64 (.mov (.mem (mb .r15 (c + 8 * k.toNat : Nat))) src)])
      else none
    | i =>
      if c < 2 ^ 31 then
        match regOf ctx i with
        | some r => some (cv ++ (chkR ck r ln ++ [i64 (.mov (.mem (tdesc r c)) src)]))
        | none =>
          match fr1 with
          | x :: fr2 => (gen ctx i x fr2).map fun ci =>
              cv ++ ci ++ (chkR ck x ln ++ [i64 (.mov (.mem (tdesc x c)) src)])
          | [] => none
      else none

/-- `A.u64[i] := e` through the register stack for a plain word array: `genStT` for the
table-relative array, else `genSt`. -/
def genSt64 (ctx : Ctx) (a : ArrId) (i e : Expr) : Option Program :=
  match ctx.tab.tbl64 a with
  | some c => genStT ctx (mb .r15 (ctx.tab.len64 a)) c (ctx.tab.min64 a) (ctx.ck (some (.w a)) i (ctx.tab.min64 a))
    i e ctx.pool
  | none => genSt ctx (mb .r15 (ctx.tab.len64 a)) (mb .r15 (ctx.tab.base64 a)) (ctx.tab.min64 a)
    (ctx.ck (some (.w a)) i (ctx.tab.min64 a)) i e ctx.pool

/-- `x := x op b` in place (lane leafgen, step G2): `op r, b` on the local's register `r` (`b` an
operand in place or evaluated into a scratch register; shifts by a constant), or `op [slot], b`
(`b` an immediate or a register) on its frame slot. -/
def genInPlace (ctx : Ctx) (x : Var) : Expr → Option Program
  | .bin op (.var y) b =>
    if y != x then none else
    match ctx.alloc.lookup x with
    | some r =>
      match op, b with
      | .shl, .const k => some [i64 (.shl (.reg (rr r)) (.imm8 (.int64 (Int64.ofInt (k.toNat % 64)))))]
      | .shr, .const k => some [i64 (.shr (.reg (rr r)) (.imm8 (.int64 (Int64.ofInt (k.toNat % 64)))))]
      | .shl, _ | .shr, _ | .mulhi, _ => none
      | op, b =>
        match simpleOp ctx b with
        | some ob => (aluOp op r ob).map ([·])
        | none =>
          match ctx.pool with
          | t :: fr => (gen ctx b t fr).bind fun cb => (aluOp op r (oR t)).map fun i => cb ++ [i]
          | [] => none
    | none =>
      match simpleOp ctx b with
      | some (.imm k) => (aluDirect op (.mem (mb .rsp (8 * x))) (.imm k)).map ([·])
      | some (.regOrMem (.reg s)) => (aluDirect op (.mem (mb .rsp (8 * x))) (.regOrMem (.reg s))).map ([·])
      | _ =>
        match ctx.pool with
        | t :: fr => (gen ctx b t fr).bind fun cb =>
            (aluDirect op (.mem (mb .rsp (8 * x))) (oR t)).map fun i => cb ++ [i]
        | [] => none
  | _ => none

/-- `x := e` through the register stack: in place, into the local's register (`genInto`), an
immediate store, or into `rax` and stored. -/
def genSet (ctx : Ctx) (x : Var) (e : Expr) : Option Program :=
  match genInPlace ctx x e with
  | some c => some c
  | none =>
  match ctx.alloc.lookup x with
  | some r => genInto ctx r ctx.pool e
  | none =>
    match simpleOp ctx e with
    | some (.imm k) => some [i64 (.mov (.mem (mb .rsp (8 * x))) (.imm k))]
    | _ => (gen ctx e .rax (ctx.pool.filter (· != .rax))).map (· ++ [movMR (mb .rsp (8 * x)) .rax])

/-- Arguments `es` into the registers `rs`, with scratch `fr` (the registers written are taken
out of it). -/
def compileRegArgs (ctx : Ctx) : List Reg64 → List Reg64 → List Expr → Program
  | fr, r :: rs, e :: es =>
    valInto ctx r (fr.filter (· != r)) e ++ compileRegArgs ctx (fr.filter (· != r)) rs es
  | _, _, _ => []

/-- `es` is `xs.map .var`. -/
def retVars : List Expr → List Var → Bool
  | [], [] => true
  | .var y :: es, x :: xs => y == x && retVars es xs
  | _, _ => false

/-- No element twice (`Bool`, for the kernel). -/
def nodupB {α} [BEq α] : List α → Bool
  | [] => true
  | a :: l => !l.contains a && nodupB l

/-- `x⃗ := f(a⃗); return x⃗` as a tail call: when all of this function's results come from `f` (`x⃗`
distinct, as many as the function returns, and `f` sets them all) and the arguments go in
registers, pop the frame, burn fuel and jump to `f`, which returns to this function's caller. -/
def tailCode (ctx : Ctx) : Stmt → Stmt → Option Program
  | .call xs f args, .ret es =>
    match ctx.tailF with
    | some F =>
      if retVars es xs && nodupB xs && xs.length == ctx.nr && decide (ctx.nr ≤ nrOf ctx.nrt ctx.tab f) &&
          decide (args.length ≤ argRegs.length) then
        some (compileRegArgs ctx ctx.pool argRegs args ++ burnFuel ++
          [i64 (.add (.reg (rr .rsp)) (oI (8 * F))), jmpL (fnL f)])
      else none
    | none => none
  | _, _ => none

/-- `A.u32[rax] := edx` (lane p32), where `[ln]` is `A`'s length in 32-bit elements
(`Tab.len32`) and `[bs]` its base: the bounds check `rax < len32`, the base into `rcx`, the 4-byte
store at `rcx + 4 rax`. -/
def st32Code (ln bs : AddrExpr) : Program :=
  [i64 (.cmp (.reg (rr .rax)) (oM ln)), jccL .nc errorL, movRM .rcx bs, st32X .rcx .rax .rdx]

def compileS (ctx : Ctx) (path : Path) : Stmt → Program
  | .skip => []
  | .set x e =>
    if ctx.treg == some x then compileE ctx e 0 ++ tregSet ++ [storeRax ctx x] else
    match genSet ctx x e with
    | some code => code
    | none =>
    match setInPlace ctx x e with
    | some d => [d]
    | none =>
      match ctx.alloc.lookup x with
      | some r =>
        match loadInto ctx r e with
        | some code => code
        | none => compileE ctx e 0 ++ [movRR r .rax]
      | none =>
        match simpleOp ctx e with
        | some (.imm k) => [i64 (.mov (.mem (mb .rsp (8 * x))) (.imm k))]
        | _ => compileE ctx e 0 ++ [movMR (mb .rsp (8 * x)) .rax]
  | .st8 a i e =>
    (match loadInto ctx .rdx e with
     | some code => compileE ctx i 0 ++ code
     | none => compileE ctx i 0 ++ [movMR (ctx.tmp 0) .rax] ++ compileE ctx e 1 ++
      [movRR .rdx .rax, movRM .rax (ctx.tmp 0)]) ++
      [
       i64 (.cmp (.reg (rr .rax)) (oM (mb .r15 (ctx.tab.len8 a)))), jccL .nc errorL,
       movRM .rcx (mb .r15 (ctx.tab.base8 a)),
       i8 (.mov (.mem (mbi .rcx .rax .W8)) (.regOrMem (.reg (.low .rdx .W8))))]
  | .st64 a i e =>
    match genSt64 ctx a i e with
    | some code => code
    | none =>
    (match loadInto ctx .rdx e with
     | some code => compileE ctx i 0 ++ code
     | none => compileE ctx i 0 ++ [movMR (ctx.tmp 0) .rax] ++ compileE ctx e 1 ++
      [movRR .rdx .rax, movRM .rax (ctx.tmp 0)]) ++
      [
       i64 (.cmp (.reg (rr .rax)) (oM (mb .r15 (ctx.tab.len64 a)))), jccL .nc errorL,
       movRM .rcx (mb .r15 (ctx.tab.base64 a)),
       movMR (mbi .rcx .rax .W64) .rdx]
  | .seq s t =>
    match tailCode ctx s t with
    | some code => code
    | none => compileS ctx (path.ch 1) s ++ compileS { ctx with fa := postF ctx.fa s } (path.ch 2) t
  | .ite c (.abort (.const k)) .skip =>
    -- `if c abort k`: one conditional jump to an error exit (`ca_abort` with the code in `rbx`)
    if k = 0 then compileC ctx (path.ch 3) c true errorL 0
    else if ctx.rbxFree then [movRI .rbx k] ++ compileC ctx (path.ch 3) c true abortL 0
    else
      -- a leaf keeps a local in `rbx`: the general `if`
      compileC ctx (path.ch 3) c false (ctx.lbl path "E") 0 ++
        compileS { ctx with fa := ctx.fa.map (·.condAll c true) } (path.ch 4) (.abort (.const k)) ++
        [jmpL (ctx.lbl path "X"), .label (ctx.lbl path "E")] ++
        compileS { ctx with fa := ctx.fa.map (·.condAll c false) } (path.ch 5) .skip ++
        [.label (ctx.lbl path "X")]
  | .ite c s t =>
    compileC ctx (path.ch 3) c false (ctx.lbl path "E") 0 ++
      compileS { ctx with fa := ctx.fa.map (·.condAll c true) } (path.ch 4) s ++
      [jmpL (ctx.lbl path "X"), .label (ctx.lbl path "E")] ++
      compileS { ctx with fa := ctx.fa.map (·.condAll c false) } (path.ch 5) t ++
      [.label (ctx.lbl path "X")]
  | .while c s =>
    [.label (ctx.lbl path "H")] ++ compileC { ctx with fa := headF ctx.fa s } (path.ch 3) c false (ctx.lbl path "X") 0 ++
      compileS { ctx with brk := ctx.lbl path "X", fa := (headF ctx.fa s).map (·.condAll c true) } (path.ch 6) s ++
      burnFuel ++ [jmpL (ctx.lbl path "H"), .label (ctx.lbl path "X")]
  | .brk => [jmpL ctx.brk]
  | .ret es =>
    match retDirect ctx es ctx.nr with
    | some code => code ++ [jmpL ctx.retL]
    | none => compileArgs ctx 0 es ++ loadRes ctx es.length 0 ctx.nr ++ [jmpL ctx.retL]
  | .call xs f args =>
    (if args.length ≤ argRegs.length then compileRegArgs ctx ctx.pool argRegs args
     else compileArgs ctx 0 args ++ [i64 (.lea (rr .rsi) (ctx.tmp 0))]) ++ burnFuel ++
      [i64 (.call (.rel (.sub (.label (fnL f)) .after_current_instruction))),
       ] ++ storeRes ctx.tab (xs.take (nrOf ctx.nrt ctx.tab f)) 0 ++ zeroVars (xs.drop (nrOf ctx.nrt ctx.tab f))
  | .abort (.const 0) => [jmpL errorL]
  | .abort e => compileE ctx e 0 ++ [movRR .rbx .rax, jmpL abortL]
  | .gset g e => compileE ctx e 0 ++ [movMR (mb .r15 (ctx.tab.globOff g)) .rax]
  | .st64t a t i e =>
    match (if ctx.isT t then
        genSt ctx (tdesc .rsi (ctx.tab.len64 a)) (tdesc .rsi (ctx.tab.base64 a)) (ctx.tab.min64t a)
          (ctx.ck (keyT a t) i (ctx.tab.min64t a)) i e ctx.pool
      else none) with
    | some code => code
    | none =>
    (match loadInto ctx .rdx e with
     | some code => compileE ctx i 0 ++ code
     | none => compileE ctx i 0 ++ [movMR (ctx.tmp 0) .rax] ++ compileE ctx e 1 ++
      [movRR .rdx .rax, movRM .rax (ctx.tmp 0)]) ++
      (if ctx.isT t then
        [i64 (.cmp (.reg (rr .rax)) (oM (tdesc .rsi (ctx.tab.len64 a)))), jccL .nc errorL,
         movRM .rcx (tdesc .rsi (ctx.tab.base64 a)),
         movMR (mbi .rcx .rax .W64) .rdx]
      else
      (loadInto ctx .rcx t).getD [jmpL errorL] ++ tierDesc .rcx ++
      [i64 (.cmp (.reg (rr .rax)) (oM (tdesc .rcx (ctx.tab.len64 a)))), jccL .nc errorL,
       movRM .rcx (tdesc .rcx (ctx.tab.base64 a)),
       movMR (mbi .rcx .rax .W64) .rdx])
  | .copy64 d di s si n => copy64Code ctx path d di s si n
  | .copy8w d di s si n => copy8wCode ctx path d di s si n
  | .scan8 x s i e c =>
    scan8Code ctx path s i e c ++ (if ctx.treg == some x then tregSet else []) ++ [storeRax ctx x]
  | .st32t a t i e =>
    (match loadInto ctx .rdx e with
     | some code => compileE ctx i 0 ++ code
     | none => compileE ctx i 0 ++ [movMR (ctx.tmp 0) .rax] ++ compileE ctx e 1 ++
      [movRR .rdx .rax, movRM .rax (ctx.tmp 0)]) ++
      (if ctx.isT t then st32Code (tdesc .rsi (ctx.tab.len32 a)) (tdesc .rsi (ctx.tab.base64 a))
      else
      match t.constTier? with
      | some c => st32Code (mb .r15 (ctx.tab.len32 (tierA a c))) (mb .r15 (ctx.tab.base64 (tierA a c)))
      | none =>
      (loadInto ctx .rcx t).getD [jmpL errorL] ++ tierDesc .rcx ++
        st32Code (tdesc .rcx (ctx.tab.len32 a)) (tdesc .rcx (ctx.tab.base64 a)))

/-- The temporaries of a statement's code (`compileS`). -/
def tempsS (al : List (Var × Reg64)) (nr : Nat) : Stmt → Nat
  | .skip | .brk => 0
  | .set _ e | .abort e => tempsE e
  | .ret es => if retOk al es nr then tempsEs es else max 1 (tempsArgs 0 es)
  | .st8 _ i e | .st64 _ i e => if Expr.isSimple e then tempsE i else max (tempsE i) (1 + tempsE e)
  | .seq s t => max (tempsS al nr s) (tempsS al nr t)
  | .ite c s t => max (tempsC c) (max (tempsS al nr s) (tempsS al nr t))
  | .while c s => max (tempsC c) (tempsS al nr s)
  | .call _ _ args => if args.length ≤ argRegs.length then tempsEs args else tempsArgs 0 args
  | .gset _ e => tempsE e
  | .st64t _ _ i e => if Expr.isSimple e then tempsE i else max (tempsE i) (1 + tempsE e)
  | .copy64 .. | .copy8w .. => 1
  | .scan8 .. => 0
  | .st32t _ _ i e => if Expr.isSimple e then tempsE i else max (tempsE i) (1 + tempsE e)

/-- Copy `n` parameters from `[rsi + 8i]` to the frame slots `i, i+1, …`. -/
def copyParams : Nat → Nat → Program
  | _, 0 => []
  | i, n + 1 => [movRM .rax (mb .rsi (8 * i)), movMR (mb .rsp (8 * i)) .rax] ++ copyParams (i + 1) n

/-- The parameters passed in registers `rs` (from parameter `i` on): those kept in a register are
there already (`AllocOk`), the others go to their frame slots. -/
def storeParams (ctx : Ctx) : Nat → List Reg64 → Program
  | _, [] => []
  | i, r :: rs =>
    (match ctx.alloc.lookup i with
     | some _ => []
     | none => [movMR (mb .rsp (8 * i)) r]) ++ storeParams ctx (i + 1) rs

/-- Zero those of the `n` locals from `j` on that `need` lists (`needZero`: the others are
assigned before they are read, `L/DefAssignSim.lean`). -/
def zeroLocals (ctx : Ctx) (need : List Var) : Nat → Nat → Program
  | _, 0 => []
  | j, n + 1 =>
    (if need.contains j then
      [match ctx.alloc.lookup j with
       | some r => movRI r 0
       | none => i64 (.mov (.mem (mb .rsp (8 * j))) (oI 0))] else []) ++ zeroLocals ctx need (j + 1) n

/-! ### Locals in registers (leaf functions) -/

def Expr.uses (w : Nat) (acc : Array Nat) : Expr → Array Nat
  | .var x => acc.modify x (· + w)
  | .bin _ a b | .cmpw _ a b => Expr.uses w (Expr.uses w acc a) b
  | .ld8 _ i | .ld64 _ i | .ldc _ i => Expr.uses w acc i
  | .ld64t _ t i => Expr.uses w (Expr.uses w acc t) i
  | .len64t _ t => Expr.uses w acc t
  | .ld8x8 _ i => Expr.uses w acc i
  | .ld32t _ t i => Expr.uses w (Expr.uses w acc t) i
  | .ld32h _ t i _ => Expr.uses w (Expr.uses w acc t) i
  | _ => acc

def WArr.uses (w : Nat) (acc : Array Nat) : WArr → Array Nat
  | .plain _ => acc
  | .tier _ t => Expr.uses w acc t

def Cond.uses (w : Nat) (acc : Array Nat) : Cond → Array Nat
  | .cmp _ a b => Expr.uses w (Expr.uses w acc a) b
  | .and p q | .or p q => Cond.uses w (Cond.uses w acc p) q
  | .not p => Cond.uses w acc p

/-- Uses of each local, a use inside `k` loops weighing `8^k`. -/
def Stmt.uses (w : Nat) (acc : Array Nat) : Stmt → Array Nat
  | .set x e => Expr.uses w (acc.modify x (· + w)) e
  | .st8 _ i e | .st64 _ i e => Expr.uses w (Expr.uses w acc i) e
  | .seq s t => Stmt.uses w (Stmt.uses w acc s) t
  | .ite c s t => Stmt.uses w (Stmt.uses w (Cond.uses w acc c) s) t
  | .while c s => Stmt.uses (8 * w) (Cond.uses (8 * w) acc c) s
  | .ret es | .call _ _ es => es.foldl (Expr.uses w) acc
  | .gset _ e => Expr.uses w acc e
  | .st64t _ t i e => Expr.uses w (Expr.uses w (Expr.uses w acc t) i) e
  | .copy64 d di s si n =>
    Expr.uses w (Expr.uses w (WArr.uses w (Expr.uses w (WArr.uses w acc d) di) s) si) n
  | .copy8w d di _ si n => Expr.uses w (Expr.uses w (Expr.uses w (WArr.uses w acc d) di) si) n
  | .scan8 x _ i e _ => Expr.uses w (Expr.uses w (acc.modify x (· + w)) i) e
  | .st32t _ t i e => Expr.uses w (Expr.uses w (Expr.uses w acc t) i) e
  | _ => acc

/-! ### The tier local (lane tiercost) -/

/-- A use of `t` as a tier: the local `x` if `t` is one. -/
def tierUse (w : Nat) (acc : Array Nat) : Expr → Array Nat
  | .var x => acc.modify x (· + w)
  | _ => acc

/-- The uses of each local as the tier of a tiered access, a use inside `k` loops weighing `8^k`. -/
def Expr.tierUses (w : Nat) (acc : Array Nat) : Expr → Array Nat
  | .bin _ a b | .cmpw _ a b => Expr.tierUses w (Expr.tierUses w acc a) b
  | .ld8 _ i | .ld64 _ i | .ldc _ i | .ld8x8 _ i => Expr.tierUses w acc i
  | .ld64t _ t i => Expr.tierUses w (tierUse w acc t) i
  | .len64t _ t => tierUse w acc t
  | .ld32t _ t i => Expr.tierUses w (tierUse w acc t) i
  | .ld32h _ t i _ => Expr.tierUses w (tierUse w acc t) i
  | _ => acc

def Cond.tierUses (w : Nat) (acc : Array Nat) : Cond → Array Nat
  | .cmp _ a b => Expr.tierUses w (Expr.tierUses w acc a) b
  | .and p q | .or p q => Cond.tierUses w (Cond.tierUses w acc p) q
  | .not p => Cond.tierUses w acc p

def Stmt.tierUses (w : Nat) (acc : Array Nat) : Stmt → Array Nat
  | .set _ e | .gset _ e => Expr.tierUses w acc e
  | .st8 _ i e | .st64 _ i e => Expr.tierUses w (Expr.tierUses w acc i) e
  | .seq s t => Stmt.tierUses w (Stmt.tierUses w acc s) t
  | .ite c s t => Stmt.tierUses w (Stmt.tierUses w (Cond.tierUses w acc c) s) t
  | .while c s => Stmt.tierUses (8 * w) (Cond.tierUses (8 * w) acc c) s
  | .ret es | .call _ _ es => es.foldl (Expr.tierUses w) acc
  | .st64t _ t i e => Expr.tierUses w (Expr.tierUses w (tierUse w acc t) i) e
  | .scan8 _ _ i e _ => Expr.tierUses w (Expr.tierUses w acc i) e
  | .st32t _ t i e => Expr.tierUses w (Expr.tierUses w (tierUse w acc t) i) e
  | _ => acc

/-- Local `i` is used as a tier at least twice (weighted), and at least as often as `b`. -/
def betterTier (u : Array Nat) (i : Nat) : Option Var → Bool
  | some y => 2 ≤ u[i]! && u[y]! ≤ u[i]!
  | none => 2 ≤ u[i]!

/-- The parameter used most often as a tier (at least twice, weighted), if any. -/
def bestTier (u : Array Nat) : Nat → Option Var → Option Var
  | 0, b => b
  | i + 1, b => bestTier u i (if betterTier u i b then some i else b)

/-- The tier local of a leaf with at most 5 parameters: the parameter used most often as a tier.
Its tier is kept in `rsi` (the sixth argument register, which no local of such a function then
uses), set on entry (from its argument register) and at each write. -/
def tregOf (fd : FunDecl) : Option Var :=
  if Stmt.calls fd.body || argRegs.length ≤ fd.nparams || fd.nlocals < fd.nparams then none else
  bestTier (Stmt.tierUses 1 (Array.replicate fd.nparams 0) fd.body) fd.nparams none

/-- Insert local `x` before the first local used less (or as often, with a larger index). -/
def rankIns (u : Array Nat) (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if u[x]! > u[y]! || (u[x]! == u[y]! && x ≤ y) then x :: y :: ys else y :: rankIns u x ys

/-- Locals by use, most used first (an insertion sort: structural, so that the kernel evaluates
it when it checks the compiled checker, `asm_lit`). -/
def rankInsSort (u : Array Nat) : List Nat → List Nat
  | [] => []
  | x :: xs => rankIns u x (rankInsSort u xs)

/-- The most used locals of a leaf function with at most 6 parameters, in registers: a parameter
keeps its argument register, the other locals take the remaining registers (those that are not
result registers first, `r13`, `r12`, `rbx`: fewer conflicts at a `return`). -/
def leafAlloc (fd : FunDecl) : List (Var × Reg64) :=
  if Stmt.calls fd.body || argRegs.length < fd.nparams then [] else
  let u := Stmt.uses 1 (Array.replicate fd.nlocals 0) fd.body
  -- parameters count as used
  let u := (List.range fd.nparams).foldl (fun a i => a.modify i (· + 1)) u
  let ranked := rankInsSort u ((List.range fd.nlocals).filter (fun x => u[x]! > 0))
  -- the tier local stays in its frame slot (its tier is in `rsi`)
  let chosen := (ranked.filter fun y => tregOf fd != some y).take allocRegs.length
  let ps := (chosen.filter (· < fd.nparams)).map fun i => (i, argRegs.getD i .rdi)
  let free := [Reg64.r13, .r12, .rbx, .rsi, .r11, .r10, .r9, .r8, .rdi].filter fun r =>
    allocRegs.contains r && !ps.any (·.2 == r) && (r != .rsi || (tregOf fd).isNone)
  ps ++ (chosen.filter (fd.nparams ≤ ·)).zip free

/-- An allocation the proof can use: registers from `allocRegs`, no register twice, a parameter
`i` in `argRegs[i]`. -/
def allocOk (np : Nat) (al : List (Var × Reg64)) : Bool :=
  al.all (fun (x, r) => allocRegs.contains r && (np ≤ x || argRegs[x]? == some r)) &&
  nodupB (al.map (·.2)) && nodupB (al.map (·.1)) && (al.isEmpty || decide (np ≤ argRegs.length))

/-- The tier local, if any, has no register, and no local is in `rsi` (`leafAlloc` leaves them out). -/
def tregFree (t : Option Var) (al : List (Var × Reg64)) : Bool :=
  match t with
  | some x => (al.lookup x).isNone && al.all (·.2 != .rsi)
  | none => true

/-- The locals of function `fd` kept in registers: a leaf's `leafAlloc` (when `allocOk`), but not
its tier local (`tregOf`), whose tier is in `rsi`. -/
def fnAlloc (fd : FunDecl) : List (Var × Reg64) :=
  if !Stmt.calls fd.body && allocOk fd.nparams (leafAlloc fd) && tregFree (tregOf fd) (leafAlloc fd)
    then leafAlloc fd else []

/-- The frame of function `fd` in words: its locals and the temporaries of its body. -/
def fnFrame (fd : FunDecl) : Nat := fd.nlocals + tempsS (fnAlloc fd) (Stmt.nret fd.body) fd.body

/-- The context of the body of function `f` (`fnAlloc`); `sk` is the table of the leaves without
a stack check (`Prog.skt`), for its own stack check (`Ctx.need`). -/
def fnCtx (tab : Tab) (t sk : NTree) (f : FnName) (fd : FunDecl) : Ctx :=
  { tab, fn := f, nl := fd.nlocals, brk := lbl f 0 "Z", nr := Stmt.nret fd.body, nrt := t,
    leaf := !Stmt.calls fd.body, alloc := fnAlloc fd, treg := tregOf fd,
    tailF := if Stmt.calls fd.body then some (fnFrame fd) else none, need := Stmt.need sk fd.body }

/-- A leaf that keeps every local in a register and needs no temporaries has no frame (and no
stack check). -/
def frameless (fd : FunDecl) : Bool :=
  !Stmt.calls fd.body && (List.range fd.nlocals).all (fun x => ((fnAlloc fd).lookup x).isSome) &&
    tempsS (fnAlloc fd) (Stmt.nret fd.body) fd.body == 0

/-- Function `f` is a leaf with a frame but no stack check of its own (unless it is the entry,
which the trampoline calls with no room checked): its callers check for its frame. -/
def skipsCheck (entry f : FnName) (fd : FunDecl) : Bool :=
  f != entry && !Stmt.calls fd.body && !frameless fd

/-- The frames (`fnFrame`) of the functions without a stack check (`skipsCheck`), by `nameCode`;
`none` if such a name occurs twice. -/
def Prog.skTree (entry : FnName) : Prog → Option NTree
  | [] => some .leaf
  | (f, fd) :: p => (Prog.skTree entry p).bind fun t =>
    if skipsCheck entry f fd then t.insert (nameCode f) (fnFrame fd) else some t

/-- `Prog.skTree`, or the empty tree (then every function checks the stack). -/
def Prog.skt (p : Prog) (entry : FnName) : NTree := (Prog.skTree entry p).getD .leaf

/-- `rsi := x & 1` on entry, for the tier local `x` (a parameter, in its argument register). -/
def tregEntry (ctx : Ctx) : Program :=
  match ctx.treg with
  | some x => [movRR .rsi (argRegs.getD x .rdi), i64 (.and (.reg (rr .rsi)) (.imm (.int64 (1 : Word).toInt64)))]
  | none => []

/-- A function's code between its prologue and its epilogue: parameters, zeroed locals (those
that may be read before they are assigned), body, results. -/
def fnBody0 (ctx : Ctx) (fd : FunDecl) : Program :=
  (if fd.nparams ≤ argRegs.length then storeParams ctx 0 (argRegs.take fd.nparams)
   else copyParams 0 fd.nparams) ++
  zeroLocals ctx (needZero fd.nparams fd.body) fd.nparams (fd.nlocals - fd.nparams) ++
  compileS ctx 0 fd.body ++ [.label ctx.endL] ++ loadRes ctx 0 0 ctx.nr ++ [.label ctx.retL]

/-- A function's code between its prologue and its epilogue: the tier local's tier into `rsi`
(from its argument register, before the parameters are stored), then `fnBody0`. -/
def fnBody (ctx : Ctx) (fd : FunDecl) : Program := tregEntry ctx ++ fnBody0 ctx fd

/-- A function: stack check, frame, parameters, body, epilogue. On entry `rsp` points at the
return address, and the arguments are in `argRegs` (at most 6) or at `rsi`. It sets its first
`Stmt.nret fd.body` results; `t` holds every function's count (`Prog.nrt`), for the call sites.
A leaf whose frame `F` is its entry in `sk` (`Prog.skt`) has no stack check: its callers check
for room for it (`Ctx.need`), on top of their own frame and return address. -/
def compileFn (tab : Tab) (t sk : NTree) (f : FnName) (fd : FunDecl) : Program :=
  let ctx := fnCtx tab t sk f fd
  let F := fd.nlocals + tempsS ctx.alloc ctx.nr fd.body
  if frameless fd then [.label (fnL f)] ++ fnBody ctx fd ++ [i64 .ret]
  else if ctx.leaf && sk.find (nameCode f) == some F then
  [.label (fnL f), i64 (.sub (.reg (rr .rsp)) (oI (8 * F)))] ++ fnBody ctx fd ++
  [i64 (.add (.reg (rr .rsp)) (oI (8 * F))), i64 .ret]
  else
  [.label (fnL f),
   movRR .rax .rsp, i64 (.sub (.reg (rr .rax)) (oM (mb .r15 Tab.stackLimit))),
   i64 (.cmp (.reg (rr .rax)) (oI (8 * F + 8 + 8 * ctx.need))), jccL .c exhaustedL,
   i64 (.sub (.reg (rr .rsp)) (oI (8 * F)))] ++ fnBody ctx fd ++
  [i64 (.add (.reg (rr .rsp)) (oI (8 * F))), i64 .ret]

/-- The entry's arguments `i, i + 1, …` from the table into the registers `rs`. -/
def loadArgs (tab : Tab) : Nat → List Reg64 → Program
  | _, [] => []
  | i, r :: rs => movRM r (mb .r15 (tab.args + 8 * i)) :: loadArgs tab (i + 1) rs

/-- The trampoline's save area: the four words just past the table (after the `np` entry
arguments), where it keeps the caller's `r15`, `rbx`, `r12`, `r13`. -/
def Tab.save (t : Tab) (np : Nat) : Int := t.args + 8 * (np : Int)

/-- The trampoline `ca_enter(T, fuel)` (System V: `rdi`, `rsi`; returns `rax`, `rdx`). It saves
the caller's callee-saved registers (`rbp`, `r14` and `T` on the machine stack, `r15`, `rbx`,
`r12`, `r13` in the four words past the table, `Tab.save`), switches to the L stack `[T]`, and
calls `entry` with the arguments at `T + Tab.args`; `entry` sets `c` results, the trampoline
zeroes the others up to `tab.nres` (`ca_ok`). Every exit goes through `ca_finish`, which takes
`T` back from the machine stack and restores all of them, so the L code may use any register. -/
def trampoline (tab : Tab) (entry : FnName) (c np : Nat) : Program :=
  [.label enterL,
   movMR (mb .rdi (tab.save np)) .r15, movMR (mb .rdi (tab.save np + 8)) .rbx,
   movMR (mb .rdi (tab.save np + 16)) .r12, movMR (mb .rdi (tab.save np + 24)) .r13,
   i64 (.push (oR .rbp)), i64 (.push (oR .r14)), i64 (.push (oR .rdi)),
   movRR .rbp .rsp, movRR .r15 .rdi, movRR .r14 .rsi,
   movRM .rsp (mb .r15 Tab.stackTop),
   i64 (.lea (rr .rsi) (mb .r15 tab.args))] ++
  (if np ≤ argRegs.length then loadArgs tab 0 (argRegs.take np) else []) ++ burnFuel ++
  [i64 (.call (.rel (.sub (.label (fnL entry)) .after_current_instruction))),
   jmpL okL,
   .label exhaustedL, movRI .rdx 1, jmpL finishL,
   .label errorL, movRI .rbx 0,
   .label abortL, movRR .rax .rbx, movRI .rdx 2,
   .label finishL, movRR .rsp .rbp,
   i64 (.pop (.reg (rr .r15))),
   movRM .rbx (mb .r15 (tab.save np + 8)), movRM .r12 (mb .r15 (tab.save np + 16)),
   movRM .r13 (mb .r15 (tab.save np + 24)), movRM .r15 (mb .r15 (tab.save np)),
   i64 (.pop (.reg (rr .r14))), i64 (.pop (.reg (rr .rbp))),
   i64 .ret,
   .label okL] ++ loadRes { tab, fn := entry, nl := 0, brk := okL } 0 c (tab.nres - c) ++
  [movRI .rdx 0, jmpL finishL]

/-- Hand-written bodies: a function whose name has the code `c` (`nameCode`) gets the code `X.lookup c`
instead of `compileFn`'s. Each body keeps its L function (the L-level proofs are about that) and is
proved against the per-function contract of the compiler proof (`FnSimAt`, `AsmOk`). -/
abbrev AsmTab := List (Nat × Program)

/-- The code of function `f`: its hand-written body in `X`, or else the compiled one. -/
def fnCode (X : AsmTab) (tab : Tab) (t sk : NTree) (f : FnName) (fd : FunDecl) : Program :=
  match X.lookup (nameCode f) with
  | some c => c
  | none => compileFn tab t sk f fd

/-- Every function of `p`, with the result counts `t` and the leaves without a stack check `sk`
(the bodies of `X` in place of the compiled ones). -/
def compileFns (X : AsmTab) (tab : Tab) (t sk : NTree) (p : Prog) : Program :=
  p.flatMap fun (f, fd) => fnCode X tab t sk f fd

/-- The number of parameters of the entry function. -/
def entryNp (p : Prog) (entry : FnName) : Nat := ((p.lookup entry).map (·.nparams)).getD 0

/-- The whole program, with the result counts `t` and the leaves without a stack check `sk`: the
trampoline, then every function. -/
def compileProgT (X : AsmTab) (tab : Tab) (t sk : NTree) (p : Prog) (entry : FnName) : Program :=
  trampoline tab entry (nrOf t tab entry) (entryNp p entry) ++ compileFns X tab t sk p

/-- The whole program, with the hand-written bodies `X`: the trampoline, then every function. -/
def compileProgX (X : AsmTab) (tab : Tab) (p : Prog) (entry : FnName) : Program :=
  compileProgT X tab (Prog.nrt p) (Prog.skt p entry) p entry

/-- The whole program: the trampoline, then every function, all compiled. -/
def compileProg (tab : Tab) (p : Prog) (entry : FnName) : Program :=
  compileProgX [] tab p entry

end L.Compiler
