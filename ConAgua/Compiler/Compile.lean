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
* `rbx`, `r12`, `r13`: free; the trampoline saves and restores them for its caller.
* `rax` = expression result, `rcx`/`rdx` = scratch, `rsi` = argument pointer at a call.

**Exits.** `ca_error`, `ca_abort` and `ca_exhausted` are global; they restore the caller's `rsp`
from `rbp` and return to the harness with `rdx` = 2, 2 resp. 1. `ca_abort` is an error whose code
(`Err.code`) is in `rbx` (`abort e`, `if c abort k`: `rbx` is no local's register, so `if c abort
k` sets it before the test and keeps its one conditional jump), `ca_error` one with code `0` (a
bounds check, a bare `abort`); both return the code in `rax`. A normal return has `rdx` = 0 and the result in `rax`.
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
/-- The number of word arrays with both tiers in the table (`a` and `a + tierOff` below `nw`). -/
def Tab.wK (t : Tab) : Nat := min (t.nw - tierOff) tierOff
/-- The position of word array `a`'s descriptor words (lane tiercost): a permutation of
`[0, nw)` that puts tier `1` of a tiered array right after tier `0` (`wpos (a + tierOff) =
wpos a + 1` for `a < wK`), so that a tiered access addresses `[r15 + 8 (t & 1) + d]`. -/
def Tab.wpos (t : Tab) (a : ArrId) : Nat :=
  if a < t.wK then 2 * a
  else if a < tierOff then a + t.wK
  else if a < tierOff + t.wK then 2 * (a - tierOff) + 1
  else a
/-- The array whose descriptor words are at position `p` (`wpos`'s inverse). -/
def Tab.wposInv (t : Tab) (p : Nat) : ArrId :=
  if p < 2 * t.wK then (if p % 2 = 0 then p / 2 else tierOff + p / 2)
  else if p < tierOff + t.wK then p - t.wK
  else p
/-- The word arrays' bases, then their lengths, each at position `wpos a`. -/
def Tab.base64 (t : Tab) (a : ArrId) : Int := 16 + 16 * t.nb + 8 * t.wpos a
def Tab.len64 (t : Tab) (a : ArrId) : Int := 16 + 16 * t.nb + 8 * t.nw + 8 * t.wpos a
theorem Tab.wpos_lt (t : Tab) {a : ArrId} (h : a < t.nw) : t.wpos a < t.nw := by
  simp only [Tab.wpos, Tab.wK, tierOff]; grind

theorem Tab.wposInv_wpos (t : Tab) {a : ArrId} (h : a < t.nw) : t.wposInv (t.wpos a) = a := by
  simp only [Tab.wpos, Tab.wposInv, Tab.wK, tierOff]; grind

theorem Tab.wpos_wposInv (t : Tab) {p : Nat} (h : p < t.nw) : t.wpos (t.wposInv p) = p := by
  simp only [Tab.wpos, Tab.wposInv, Tab.wK, tierOff]; grind

theorem Tab.wposInv_lt (t : Tab) {p : Nat} (h : p < t.nw) : t.wposInv p < t.nw := by
  simp only [Tab.wposInv, Tab.wK, tierOff]; grind

theorem Tab.wK_spec (t : Tab) {a : ArrId} (h : a < t.wK) : a < tierOff ∧ a + tierOff < t.nw := by
  simp only [Tab.wK, tierOff] at h ⊢
  grind

/-- Tier `1`'s descriptor words are right after tier `0`'s. -/
theorem Tab.wpos_tier (t : Tab) {a : ArrId} (h : a < t.wK) (b : Nat) (hb : b ≤ 1) :
    t.wpos (a + tierOff * b) = t.wpos a + b := by
  simp only [Tab.wpos, Tab.wK, tierOff] at *
  rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl <;> grind

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

/-- The constant bytes of a byte source. -/
def BSrc.roms : BSrc → List (List UInt8)
  | .arr _ => []
  | .rom d => [d]

/-- The constant byte strings of an expression, a condition, a statement, a program. -/
def Expr.roms : Expr → List (List UInt8)
  | .bin _ a b | .cmpw _ a b => Expr.roms a ++ Expr.roms b
  | .ld8 _ i | .ld64 _ i => Expr.roms i
  | .ldc d i => d :: Expr.roms i
  | .ld64t _ t i => Expr.roms t ++ Expr.roms i
  | .len64t _ t => Expr.roms t
  | .ld8x8 s i => BSrc.roms s ++ Expr.roms i
  | _ => []

def WArr.roms : WArr → List (List UInt8)
  | .plain _ => []
  | .tier _ t => Expr.roms t

def Cond.roms : Cond → List (List UInt8)
  | .cmp _ a b => Expr.roms a ++ Expr.roms b
  | .and p q | .or p q => Cond.roms p ++ Cond.roms q
  | .not p => Cond.roms p

def Stmt.roms : Stmt → List (List UInt8)
  | .skip | .brk => []
  | .set _ e | .abort e => Expr.roms e
  | .st8 _ i e | .st64 _ i e => Expr.roms i ++ Expr.roms e
  | .seq s t => Stmt.roms s ++ Stmt.roms t
  | .ite c s t => Cond.roms c ++ Stmt.roms s ++ Stmt.roms t
  | .while c s => Cond.roms c ++ Stmt.roms s
  | .ret es => es.flatMap Expr.roms
  | .call _ _ args => args.flatMap Expr.roms
  | .gset _ e => Expr.roms e
  | .st64t _ t i e => Expr.roms t ++ Expr.roms i ++ Expr.roms e
  | .copy64 d di s si n => WArr.roms d ++ Expr.roms di ++ WArr.roms s ++ Expr.roms si ++ Expr.roms n
  | .copy8w d di s si n => WArr.roms d ++ Expr.roms di ++ BSrc.roms s ++ Expr.roms si ++ Expr.roms n
  | .scan8 _ s i e c => BSrc.roms s ++ Expr.roms i ++ Expr.roms e ++ [c]

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

/-! ## Names as numbers, and a search tree keyed by them

The kernel compares `String`s slowly (UTF-8 byte lists), `Nat` literals fast (GMP): code that the
kernel evaluates looks names up by `nameCode` in an `NTree` (`WFFast.lean`; the per-callee result
counts below). -/

/-- Bijective base-257 numeration of a byte list (digits `1..256`, least significant first). -/
def bytesCode : List UInt8 → Nat
  | [] => 0
  | b :: l => (b.toNat + 1) + 257 * bytesCode l

/-- A function name as a number. -/
def nameCode (s : String) : Nat := bytesCode s.toByteArray.data.toList

/-- Binary search tree: name code ↦ a number (the parameter count, the result count). -/
inductive NTree where
  | leaf
  | node (l : NTree) (k v : Nat) (r : NTree)
  deriving Repr, Inhabited

def NTree.find (k : Nat) : NTree → Option Nat
  | .leaf => none
  | .node l k' v r => if k < k' then find k l else if k = k' then some v else find k r

/-- Insert `k ↦ v`; `none` if `k` is there already. -/
def NTree.insert (k v : Nat) : NTree → Option NTree
  | .leaf => some (.node .leaf k v .leaf)
  | .node l k' v' r =>
    if k < k' then (insert k v l).map (.node · k' v' r)
    else if k = k' then none
    else (insert k v r).map (.node l k' v' ·)

/-- The most results a statement returns: a function sets only these (`Ctx.nr`); a caller that
reads more zeroes the rest itself. -/
def Stmt.nret : Stmt → Nat
  | .seq s t | .ite _ s t => max (Stmt.nret s) (Stmt.nret t)
  | .while _ s => Stmt.nret s
  | .ret es => es.length
  | _ => 0

/-- The result counts of a program's functions (`Stmt.nret` of the body) by `nameCode`; `none`
if a name occurs twice (built right to left, as `WFFast.lean`'s `progTree`). -/
def Prog.nrTree : Prog → Option NTree
  | [] => some .leaf
  | (f, fd) :: p => (Prog.nrTree p).bind (·.insert (nameCode f) (Stmt.nret fd.body))

/-- `Prog.nrTree`, or the empty tree (then every call site reads all `nres` results; `Prog.wf`
rules this case out). -/
def Prog.nrt (p : Prog) : NTree := (Prog.nrTree p).getD .leaf

/-- The results callee `f` sets: its entry in `t`, else all `tab.nres`. -/
def nrOf (t : NTree) (tab : Tab) (f : FnName) : Nat := (t.find (nameCode f)).getD tab.nres

/-- One more than the largest global variable an expression, a condition, a statement names. -/
def Expr.nglob : Expr → Nat
  | .bin _ a b | .cmpw _ a b => max (Expr.nglob a) (Expr.nglob b)
  | .ld8 _ i | .ld64 _ i | .ldc _ i => Expr.nglob i
  | .glob g => g.id + 1
  | .ld64t _ t i => max (Expr.nglob t) (Expr.nglob i)
  | .len64t _ t => Expr.nglob t
  | .ld8x8 _ i => Expr.nglob i
  | _ => 0

def WArr.nglob : WArr → Nat
  | .plain _ => 0
  | .tier _ t => Expr.nglob t

def Cond.nglob : Cond → Nat
  | .cmp _ a b => max (Expr.nglob a) (Expr.nglob b)
  | .and p q | .or p q => max (Cond.nglob p) (Cond.nglob q)
  | .not p => Cond.nglob p

def Stmt.nglob : Stmt → Nat
  | .skip | .brk => 0
  | .set _ e | .abort e => Expr.nglob e
  | .st8 _ i e | .st64 _ i e => max (Expr.nglob i) (Expr.nglob e)
  | .seq s t => max (Stmt.nglob s) (Stmt.nglob t)
  | .ite c s t => max (Cond.nglob c) (max (Stmt.nglob s) (Stmt.nglob t))
  | .while c s => max (Cond.nglob c) (Stmt.nglob s)
  | .ret es | .call _ _ es => es.foldl (fun acc e => max acc (Expr.nglob e)) 0
  | .gset g e => max (g.id + 1) (Expr.nglob e)
  | .st64t _ t i e => max (Expr.nglob t) (max (Expr.nglob i) (Expr.nglob e))
  | .copy64 d di s si n => max (WArr.nglob d) (max (Expr.nglob di) (max (WArr.nglob s)
      (max (Expr.nglob si) (Expr.nglob n))))
  | .copy8w d di _ si n => max (WArr.nglob d) (max (Expr.nglob di) (max (Expr.nglob si) (Expr.nglob n)))
  | .scan8 _ _ i e _ => max (Expr.nglob i) (Expr.nglob e)

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

/-! ## Temporaries

`compileE e t` evaluates `e` into `rax` and may write the temporaries `t, t+1, …, t + tempsE e - 1`. -/

/-- A right operand that needs no temporary: a variable, a global, an array length or a constant
(`simpleOp`, `loadInto`). -/
def Expr.isSimple : Expr → Bool
  | .var _ | .glob _ | .len8 _ | .len64 _ | .const _ => true
  | _ => false

def tempsE : Expr → Nat
  | .bin _ a b | .cmpw _ a b => if Expr.isSimple b then tempsE a else max (tempsE a) (1 + tempsE b)
  | .ld8 _ i | .ld64 _ i | .ldc _ i => tempsE i
  | .ld64t _ t i => if Expr.isSimple t then tempsE i else max (tempsE t) (1 + tempsE i)
  | .len64t _ t => tempsE t
  | .ld8x8 _ i => tempsE i
  | _ => 0

def tempsC : Cond → Nat
  | .cmp _ a b => if Expr.isSimple b then tempsE a else max (tempsE a) (1 + tempsE b)
  | .and p q | .or p q => max (tempsC p) (tempsC q)
  | .not p => tempsC p

def tempsArgs : Nat → List Expr → Nat
  | _, [] => 0
  | i, e :: es => max (max (i + 1) (i + tempsE e)) (tempsArgs (i + 1) es)

/-- The temporaries of `compileE` on each of `es`, from `0`. -/
def tempsEs : List Expr → Nat
  | [] => 0
  | e :: es => max (tempsE e) (tempsEs es)

/-- A bound on the temporaries of a statement (`tempsS`, which also knows which `return`s are
compiled without temporaries). -/
def tempsSB : Stmt → Nat
  | .skip | .brk => 0
  | .set _ e | .abort e => tempsE e
  | .ret es => max 1 (tempsArgs 0 es)
  | .st8 _ i e | .st64 _ i e => if Expr.isSimple e then tempsE i else max (tempsE i) (1 + tempsE e)
  | .seq s t => max (tempsSB s) (tempsSB t)
  | .ite c s t => max (tempsC c) (max (tempsSB s) (tempsSB t))
  | .while c s => max (tempsC c) (tempsSB s)
  | .call _ _ args => tempsArgs 0 args
  | .gset _ e => tempsE e
  | .st64t _ _ i e => if Expr.isSimple e then tempsE i else max (tempsE i) (1 + tempsE e)
  | .copy64 .. | .copy8w .. => 1
  | .scan8 .. => 0

/-- A bound on the number of words in the frame of `fd` (`Prog.wf` checks that it is small). -/
def frameWords (fd : FunDecl) : Nat := fd.nlocals + tempsSB fd.body

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
  deriving Repr

/-- The registers a leaf keeps locals in: neither the scratch registers `rax`/`rcx`/`rdx`, nor
`rsp`, `rbp` (the trampoline's), `r14` (fuel), `r15` (the table), nor the registers the harness
expects preserved (`rbx`, `r12`, `r13`; with them, 9 registers instead of 6 measured no faster:
docs/design/compproofD.md). -/
def allocRegs : List Reg64 := [.rdi, .r8, .r9, .r10, .r11, .rsi]

/-- The argument registers: a call with at most 6 arguments passes argument `i` in
`argRegs[i]`; more go through memory at `rsi`. -/
def argRegs : List Reg64 := allocRegs

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

/-! ### Simple operands (lane `compopt`, prototype A)

A right operand that is a variable, a global, an array length or a constant is not evaluated into
`rax` and spilled: it is used in place, as a memory operand or an immediate (`simpleOp`), or loaded
straight into `rcx`/`rdx` (`loadInto`). -/

/-- A constant that fits a sign-extended 32-bit immediate. -/
def fitsImm32 (w : Word) : Bool := -2147483648 ≤ w.toInt64.toInt && w.toInt64.toInt < 2147483648

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

/-- `cmp r, b` for a local `a` kept in register `r` and a simple `b`: no move into `rax`. -/
def cmpReg (ctx : Ctx) (a b : Expr) : Option Program :=
  match a with
  | .var x =>
    match ctx.alloc.lookup x, simpleOp ctx b with
    | some r, some o => some [i64 (.cmp (.reg (rr r)) o)]
    | _, _ => none
  | _ => none

/-- `r := r & 1`: from a tier word in `r`, the tier, which indexes the descriptor words (tier `1`
of array `a` is array `a + tierOff`, whose descriptor words are 8 bytes after `a`'s: `Tab.wpos`). -/
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

/-- An operand of a block that needs no code: a local, a global, an array length or an imm32
constant (`Stmt.wf` asks for this). -/
def Expr.isOpnd : Expr → Bool
  | .var _ | .glob _ | .len8 _ | .len64 _ => true
  | .const w => fitsImm32 w
  | _ => false

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
relative to tier `0`'s (`Tab.wpos`). -/
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
    match cmpReg ctx a b with
    | some code => code ++
      [movRI .rax 0, movRI .rdx 1, i64 (.cmovcc (cmpCC op) (rr .rax) (.reg (rr .rdx)))]
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

/-- The negation of a condition code. -/
def CondCode.neg : CondCode → CondCode
  | .o => .no | .no => .o | .c => .nc | .nc => .c | .z => .nz | .nz => .z | .be => .a | .a => .be
  | .s => .ns | .ns => .s | .p => .np | .np => .p | .l => .ge | .ge => .l | .le => .g | .g => .le

/-- Jump to `l` if `c` evaluates to `b`; fall through otherwise. -/
def compileC (ctx : Ctx) (path : Path) : Cond → Bool → Label → Nat → Program
  | .cmp op a b, pol, l, t =>
    match cmpReg ctx a b with
    | some code => code ++ [jccL (if pol then cmpCC op else CondCode.neg (cmpCC op)) l]
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

/-- `r := e` (`r` not `rax`): one instruction for a simple `e`, else through `rax`. -/
def valInto (ctx : Ctx) (r : Reg64) (e : Expr) : Program :=
  match loadInto ctx r e with
  | some code => code
  | none => compileE ctx e 0 ++ [movRR r .rax]

/-- Does `e` read register `r` (a local kept there)? -/
def Expr.readsReg (al : List (Var × Reg64)) (r : Reg64) : Expr → Bool
  | .var x => al.lookup x == some r
  | .bin _ a b | .cmpw _ a b => Expr.readsReg al r a || Expr.readsReg al r b
  | .ld8 _ i | .ld64 _ i | .ldc _ i => Expr.readsReg al r i
  | .ld64t _ t i => Expr.readsReg al r t || Expr.readsReg al r i
  | .len64t _ t => Expr.readsReg al r t
  | .ld8x8 _ i => Expr.readsReg al r i
  | _ => false

/-- Results `i, i + 1, …` (`i ≥ 1`) of a `return` straight into their registers. -/
def retRegs (ctx : Ctx) : Nat → List Expr → Program
  | _, [] => []
  | i, e :: es => valInto ctx (resReg i) e ++ retRegs ctx (i + 1) es

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
    | e0 :: rest => some (retRegs ctx 1 rest ++ compileE ctx e0 0 ++ zeroRes es.length (n - es.length))
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

/-- Arguments `es` into the registers `rs`. -/
def compileRegArgs (ctx : Ctx) : List Reg64 → List Expr → Program
  | r :: rs, e :: es => valInto ctx r e ++ compileRegArgs ctx rs es
  | _, _ => []

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
        some (compileRegArgs ctx argRegs args ++ burnFuel ++
          [i64 (.add (.reg (rr .rsp)) (oI (8 * F))), jmpL (fnL f)])
      else none
    | none => none
  | _, _ => none

def compileS (ctx : Ctx) (path : Path) : Stmt → Program
  | .skip => []
  | .set x e =>
    if ctx.treg == some x then compileE ctx e 0 ++ tregSet ++ [storeRax ctx x] else
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
    | none => compileS ctx (path.ch 1) s ++ compileS ctx (path.ch 2) t
  | .ite c (.abort (.const k)) .skip =>
    -- `if c abort k`: one conditional jump to an error exit (`ca_abort` with the code in `rbx`)
    if k = 0 then compileC ctx (path.ch 3) c true errorL 0
    else [movRI .rbx k] ++ compileC ctx (path.ch 3) c true abortL 0
  | .ite c s t =>
    compileC ctx (path.ch 3) c false (ctx.lbl path "E") 0 ++ compileS ctx (path.ch 4) s ++
      [jmpL (ctx.lbl path "X"), .label (ctx.lbl path "E")] ++ compileS ctx (path.ch 5) t ++
      [.label (ctx.lbl path "X")]
  | .while c s =>
    [.label (ctx.lbl path "H")] ++ compileC ctx (path.ch 3) c false (ctx.lbl path "X") 0 ++
      compileS { ctx with brk := ctx.lbl path "X" } (path.ch 6) s ++ burnFuel ++
      [jmpL (ctx.lbl path "H"), .label (ctx.lbl path "X")]
  | .brk => [jmpL ctx.brk]
  | .ret es =>
    match retDirect ctx es ctx.nr with
    | some code => code ++ [jmpL ctx.retL]
    | none => compileArgs ctx 0 es ++ loadRes ctx es.length 0 ctx.nr ++ [jmpL ctx.retL]
  | .call xs f args =>
    (if args.length ≤ argRegs.length then compileRegArgs ctx argRegs args
     else compileArgs ctx 0 args ++ [i64 (.lea (rr .rsi) (ctx.tmp 0))]) ++ burnFuel ++
      [i64 (.call (.rel (.sub (.label (fnL f)) .after_current_instruction))),
       ] ++ storeRes ctx.tab (xs.take (nrOf ctx.nrt ctx.tab f)) 0 ++ zeroVars (xs.drop (nrOf ctx.nrt ctx.tab f))
  | .abort (.const 0) => [jmpL errorL]
  | .abort e => compileE ctx e 0 ++ [movRR .rbx .rax, jmpL abortL]
  | .gset g e => compileE ctx e 0 ++ [movMR (mb .r15 (ctx.tab.globOff g)) .rax]
  | .st64t a t i e =>
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

/-- Zero `n` locals from `j` on. -/
def zeroLocals (ctx : Ctx) : Nat → Nat → Program
  | _, 0 => []
  | j, n + 1 =>
    (match ctx.alloc.lookup j with
     | some r => movRI r 0
     | none => i64 (.mov (.mem (mb .rsp (8 * j))) (oI 0))) :: zeroLocals ctx (j + 1) n

/-! ### Locals in registers (leaf functions) -/

/-- Does the statement call? -/
def Stmt.calls : Stmt → Bool
  | .seq s t | .ite _ s t => Stmt.calls s || Stmt.calls t
  | .while _ s => Stmt.calls s
  | .call .. => true
  | _ => false

def Expr.uses (w : Nat) (acc : Array Nat) : Expr → Array Nat
  | .var x => acc.modify x (· + w)
  | .bin _ a b | .cmpw _ a b => Expr.uses w (Expr.uses w acc a) b
  | .ld8 _ i | .ld64 _ i | .ldc _ i => Expr.uses w acc i
  | .ld64t _ t i => Expr.uses w (Expr.uses w acc t) i
  | .len64t _ t => Expr.uses w acc t
  | .ld8x8 _ i => Expr.uses w acc i
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
result registers first: fewer conflicts at a `return`). -/
def leafAlloc (fd : FunDecl) : List (Var × Reg64) :=
  if Stmt.calls fd.body || argRegs.length < fd.nparams then [] else
  let u := Stmt.uses 1 (Array.replicate fd.nlocals 0) fd.body
  -- parameters count as used
  let u := (List.range fd.nparams).foldl (fun a i => a.modify i (· + 1)) u
  let ranked := rankInsSort u ((List.range fd.nlocals).filter (fun x => u[x]! > 0))
  -- the tier local stays in its frame slot (its tier is in `rsi`)
  let chosen := (ranked.filter fun y => tregOf fd != some y).take allocRegs.length
  let ps := (chosen.filter (· < fd.nparams)).map fun i => (i, argRegs.getD i .rdi)
  let free := [Reg64.rsi, .r11, .r10, .r9, .r8, .rdi].filter fun r =>
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

/-- The context of the body of function `f`: a leaf keeps locals in registers (`leafAlloc`,
used when `allocOk`), but not its tier local (`tregOf`), whose tier is in `rsi`. -/
def fnCtx (tab : Tab) (t : NTree) (f : FnName) (fd : FunDecl) : Ctx :=
  let al := if !Stmt.calls fd.body && allocOk fd.nparams (leafAlloc fd) && tregFree (tregOf fd) (leafAlloc fd)
    then leafAlloc fd else []
  { tab, fn := f, nl := fd.nlocals, brk := lbl f 0 "Z", nr := Stmt.nret fd.body, nrt := t,
    leaf := !Stmt.calls fd.body, alloc := al, treg := tregOf fd,
    tailF := if Stmt.calls fd.body then some (fd.nlocals + tempsS al (Stmt.nret fd.body) fd.body) else none }

/-- A leaf that keeps every local in a register and needs no temporaries has no frame (and no
stack check). -/
def frameless (ctx : Ctx) (fd : FunDecl) : Bool :=
  ctx.leaf && (List.range fd.nlocals).all (fun x => (ctx.alloc.lookup x).isSome) &&
    tempsS ctx.alloc ctx.nr fd.body == 0

/-- `rsi := x & 1` on entry, for the tier local `x` (a parameter, in its argument register). -/
def tregEntry (ctx : Ctx) : Program :=
  match ctx.treg with
  | some x => [movRR .rsi (argRegs.getD x .rdi), i64 (.and (.reg (rr .rsi)) (.imm (.int64 (1 : Word).toInt64)))]
  | none => []

/-- A function's code between its prologue and its epilogue: parameters, zeroed locals, body,
results. -/
def fnBody0 (ctx : Ctx) (fd : FunDecl) : Program :=
  (if fd.nparams ≤ argRegs.length then storeParams ctx 0 (argRegs.take fd.nparams)
   else copyParams 0 fd.nparams) ++
  zeroLocals ctx fd.nparams (fd.nlocals - fd.nparams) ++
  compileS ctx 0 fd.body ++ [.label ctx.endL] ++ loadRes ctx 0 0 ctx.nr ++ [.label ctx.retL]

/-- A function's code between its prologue and its epilogue: the tier local's tier into `rsi`
(from its argument register, before the parameters are stored), then `fnBody0`. -/
def fnBody (ctx : Ctx) (fd : FunDecl) : Program := tregEntry ctx ++ fnBody0 ctx fd

/-- A function: stack check, frame, parameters, body, epilogue. On entry `rsp` points at the
return address, and the arguments are in `argRegs` (at most 6) or at `rsi`. It sets its first
`Stmt.nret fd.body` results; `t` holds every function's count (`Prog.nrt`), for the call sites. -/
def compileFn (tab : Tab) (t : NTree) (f : FnName) (fd : FunDecl) : Program :=
  let ctx := fnCtx tab t f fd
  let F := fd.nlocals + tempsS ctx.alloc ctx.nr fd.body
  if frameless ctx fd then [.label (fnL f)] ++ fnBody ctx fd ++ [i64 .ret]
  else
  [.label (fnL f),
   movRR .rax .rsp, i64 (.sub (.reg (rr .rax)) (oM (mb .r15 Tab.stackLimit))),
   i64 (.cmp (.reg (rr .rax)) (oI (8 * F + 8))), jccL .c exhaustedL,
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

/-- Every function of `p`, with the result counts `t`. -/
def compileFns (tab : Tab) (t : NTree) (p : Prog) : Program :=
  p.flatMap fun (f, fd) => compileFn tab t f fd

/-- The number of parameters of the entry function. -/
def entryNp (p : Prog) (entry : FnName) : Nat := ((p.lookup entry).map (·.nparams)).getD 0

/-- The whole program, with the result counts `t`: the trampoline, then every function. -/
def compileProgT (tab : Tab) (t : NTree) (p : Prog) (entry : FnName) : Program :=
  trampoline tab entry (nrOf t tab entry) (entryNp p entry) ++ compileFns tab t p

/-- The whole program: the trampoline, then every function. -/
def compileProg (tab : Tab) (p : Prog) (entry : FnName) : Program :=
  compileProgT tab (Prog.nrt p) p entry

end L.Compiler
