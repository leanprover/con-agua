module

public import Kraken.X64.Syntax

@[expose] public section

/-!
# The assembler-file parser (TRUSTED)

`parseAsmFile text` reads an assembler file as `as` (GNU binutils, x86-64, AT&T syntax) would, for
the small subset of the language that the checker's file `asm/checker.s` uses, and returns its
`.text` section as a Kraken `Program` (plus the data lines, which are not code). It is part of
the trusted base: the final theorems are about the `Program` it returns (`include_asm`,
`ConAgua/AsmFile/Include.lean`), and `as` assembles the same text. So every line is either read
exactly as `as` reads it, or rejected. Anything outside the subset is an error, never skipped.

The subset, one item per line (no leading or trailing blanks, no comments):
* `.text`, `.section .rodata`, `.section .note.GNU-stack,"",@progbits`: switch section. Once a
  non-text section was entered, `.text` is rejected (so the code is one contiguous run).
* `.globl NAME`: symbol visibility; no effect on the code.
* In `.text`: `NAME:` (a label) or an instruction (below).
* In `.rodata`: `NAME:`, `NAME: .quad INT`, `NAME: .byte INT, …, INT` (data; not code).
* In `.note.GNU-stack`: nothing.
* Empty lines.

Instructions (operation size 64 bits, except the byte source of `movzbq`; 64-bit addresses):
`movq addq subq andq orq xorq` (`SRC, DST`), `cmpq B, A`, `imulq B, A` (two operands),
`mulq X`, `shlq shrq sarq` (`$INT` or `%cl`, then `DST`), `lea MEM, %R`, `cmovCC X, %R`,
`movzbq MEM, %R`, `pushq X`, `popq X`, `jCC NAME`, `jmp NAME`, `call NAME`, `ret`.
Operands: `%R` (the sixteen 64-bit registers), `$INT`, `NAME` (branch targets only), and memory
`INT(%B)`, `(%B)`, `INT(%B,%I,S)`, `(%B,%I,S)` with `S ∈ {1, 2, 4, 8}`. `INT` is decimal with an
optional `-` and no leading zero (`as` reads `010` as octal), and must fit in 64 bits as a
signed number. `CC` is one of `as`'s spellings of the sixteen condition codes.

What the forms mean is Kraken's syntax as Kraken's own parser (`Kraken.X64.Parser.parse`) reads
them; in particular a branch to `NAME` is relative (`.rel (.sub (.label NAME)
.after_current_instruction)`), as `as` encodes it.
-/

namespace ConAgua.AsmFile

/-- A data line: the label and the values (`.quad`: one 8-byte value; `.byte`: bytes). -/
structure DataLine where
  name : String
  quad : Bool
  vals : List Int
  deriving Repr, BEq

/-- What a file holds: the code (the `.text` section) and the data lines. -/
structure AsmFile where
  text : Program
  data : List DataLine

abbrev P := Except String

/-- A symbol name: `[A-Za-z_.][A-Za-z0-9_.]*`. -/
def isName (s : String) : Bool :=
  match s.toList with
  | c :: cs => (c.isAlpha || c == '_' || c == '.') && cs.all fun c => c.isAlphanum || c == '_' || c == '.'
  | [] => false

def name (s : String) : P String :=
  if isName s then pure s else throw s!"bad name '{s}'"

/-- A decimal integer, optional `-`, no leading zero, in the signed 64-bit range. -/
def int (s : String) : P Int := do
  let (neg, ds) := if s.startsWith "-" then (true, (s.drop 1).toString) else (false, s)
  unless !ds.isEmpty && ds.all Char.isDigit do throw s!"bad integer '{s}'"
  if ds.length > 1 && ds.startsWith "0" then throw s!"integer with a leading zero '{s}'"
  let v : Int := if neg then -(ds.toNat! : Int) else ds.toNat!
  unless -(2 ^ 63 : Int) ≤ v && v < 2 ^ 63 do throw s!"integer out of range '{s}'"
  return v

def int64 (s : String) : P ConstExpr := do return .int64 (Int64.ofInt (← int s))

def reg64 : String → P Reg64
  | "%rax" => pure .rax | "%rbx" => pure .rbx | "%rcx" => pure .rcx | "%rdx" => pure .rdx
  | "%rsi" => pure .rsi | "%rdi" => pure .rdi | "%rsp" => pure .rsp | "%rbp" => pure .rbp
  | "%r8" => pure .r8 | "%r9" => pure .r9 | "%r10" => pure .r10 | "%r11" => pure .r11
  | "%r12" => pure .r12 | "%r13" => pure .r13 | "%r14" => pure .r14 | "%r15" => pure .r15
  | s => throw s!"bad register '{s}'"

def reg (s : String) : P (Reg .W64) := do return .low (← reg64 s) .W64

/-- A memory operand: `[INT](%B[,%I,S])`. -/
def mem (s : String) : P AddrExpr := do
  let some i := s.find? '(' |>.map (·.offset.byteIdx) | throw s!"bad memory operand '{s}'"
  let pre := (s.take i).toString
  let rest := (s.drop i).toString
  unless rest.startsWith "(" && rest.endsWith ")" do throw s!"bad memory operand '{s}'"
  let inner := ((rest.drop 1).dropEnd 1).toString
  let disp ← if pre.isEmpty then pure (.int64 0) else int64 pre
  match inner.splitOn "," with
  | [b] => return { base := some (.reg (← reg64 b)), idx := none, disp }
  | [b, x, sc] =>
    let scale ← match sc with
      | "1" => pure Width.W8 | "2" => pure .W16 | "4" => pure .W32 | "8" => pure .W64
      | _ => throw s!"bad scale '{sc}'"
    return { base := some (.reg (← reg64 b)), idx := some ⟨← reg64 x, scale⟩, disp }
  | _ => throw s!"bad memory operand '{s}'"

/-- A register or memory operand. -/
def rm (s : String) : P (RegOrMem .W64) :=
  if s.startsWith "%" then return .reg (← reg s) else return .mem (← mem s)

/-- A register, immediate or memory operand. -/
def opnd (s : String) : P (Operand .W64) :=
  if s.startsWith "$" then return .imm (← int64 (s.drop 1).toString) else return .regOrMem (← rm s)

def count (s : String) : P ShiftCountExpr :=
  if s == "%cl" then pure .cl
  else if s.startsWith "$" then return .imm8 (← int64 (s.drop 1).toString)
  else throw s!"bad shift count '{s}'"

/-- `as`'s spellings of the condition codes (the `CC` of `jCC`, `cmovCC`). -/
def cc : String → Option CondCode
  | "o" => some .o | "no" => some .no
  | "b" | "c" | "nae" => some .c | "ae" | "nc" | "nb" => some .nc
  | "e" | "z" => some .z | "ne" | "nz" => some .nz
  | "be" | "na" => some .be | "a" | "nbe" => some .a
  | "s" => some .s | "ns" => some .ns
  | "p" | "pe" => some .p | "np" | "po" => some .np
  | "l" | "nge" => some .l | "ge" | "nl" => some .ge
  | "le" | "ng" => some .le | "g" | "nle" => some .g
  | _ => none

/-- A branch target: a direct, relative branch to a symbol. -/
def target (s : String) : P ConstExpr := do
  return .sub (.label (← name s)) .after_current_instruction

def i64 (op : Operation .W64) : Instr := .regular .W64 .W64 op

/-- Two operands `A, B`, not both memory (`as` rejects that). -/
def two (args : List String) : P (String × String) := do
  match args with
  | [a, b] =>
    if !a.startsWith "%" && !a.startsWith "$" && !b.startsWith "%" then
      throw "two memory operands"
    return (a, b)
  | _ => throw s!"expected two operands, got {args.length}"

def one (args : List String) : P String := do
  match args with
  | [a] => return a
  | _ => throw s!"expected one operand, got {args.length}"

/-- An instruction line: the mnemonic, then the operands, separated by `", "`. -/
def instr (line : String) : P Instr := do
  let (mn, args) := match line.splitOn " " with
    | [m] => (m, [])
    | m :: _ => (m, ((line.drop (m.length + 1)).toString.splitOn ", "))
    | [] => ("", [])
  match mn with
  | "movq" => let (a, b) ← two args; return i64 (.mov (← rm b) (← opnd a))
  | "addq" => let (a, b) ← two args; return i64 (.add (← rm b) (← opnd a))
  | "subq" => let (a, b) ← two args; return i64 (.sub (← rm b) (← opnd a))
  | "andq" => let (a, b) ← two args; return i64 (.and (← rm b) (← opnd a))
  | "orq" => let (a, b) ← two args; return i64 (.or (← rm b) (← opnd a))
  | "xorq" => let (a, b) ← two args; return i64 (.xor (← rm b) (← opnd a))
  | "cmpq" => let (a, b) ← two args; return i64 (.cmp (← rm b) (← opnd a))
  | "imulq" => let (a, b) ← two args; return i64 (.imul none (.reg (← reg b)) (← opnd a))
  | "mulq" => return i64 (.mul (← rm (← one args)))
  | "shlq" => let (a, b) ← two args; return i64 (.shl (← rm b) (← count a))
  | "shrq" => let (a, b) ← two args; return i64 (.shr (← rm b) (← count a))
  | "sarq" => let (a, b) ← two args; return i64 (.sar (← rm b) (← count a))
  | "lea" => let (a, b) ← two args; return i64 (.lea (← reg b) (← mem a))
  | "movzbq" =>
    let (a, b) ← two args
    return i64 (@Operation.movzx .W64 .W8 (.reg (← reg b)) (.mem (← mem a)))
  | "pushq" => return i64 (.push (← opnd (← one args)))
  | "popq" => return i64 (.pop (← rm (← one args)))
  | "jmp" => return i64 (.jmp (.rel (← target (← one args))))
  | "call" => return i64 (.call (.rel (← target (← one args))))
  | "ret" => if args.isEmpty then return i64 .ret else throw "ret takes no operand"
  | _ =>
    if mn.startsWith "cmov" then
      let some k := cc (mn.drop 4).toString | throw s!"unknown instruction '{mn}'"
      let (a, b) ← two args
      return i64 (.cmovcc k (← reg b) (← rm a))
    else if mn.startsWith "j" then
      let some k := cc (mn.drop 1).toString | throw s!"unknown instruction '{mn}'"
      return i64 (.jcc k (← name (← one args)))
    else throw s!"unknown instruction '{mn}'"

inductive Section | text | rodata | note
  deriving BEq

/-- A data line `NAME: .quad INT`, `NAME: .byte INT, …` or `NAME:`. -/
def dataLine (line : String) : P DataLine := do
  match line.splitOn ": " with
  | [lab] =>
    unless lab.endsWith ":" do throw "expected a label"
    return { name := ← name (lab.dropEnd 1).toString, quad := false, vals := [] }
  | [lab, d] =>
    if d.startsWith ".quad " then
      return { name := ← name lab, quad := true, vals := [← int (d.drop 6).toString] }
    else if d.startsWith ".byte " then
      let vs ← ((d.drop 6).toString.splitOn ", ").mapM fun v => do
        let v ← int v
        unless 0 ≤ v && v < 256 do throw s!"byte out of range {v}"
        return v
      return { name := ← name lab, quad := false, vals := vs }
    else throw "expected .quad or .byte"
  | _ => throw "bad data line"

/-- Parse a file (see the module doc). The error names the line. -/
def parseAsmFile (text : String) : Except String AsmFile := do
  let mut sec := Section.text
  let mut code : Array Directive := #[]
  let mut data : Array DataLine := #[]
  let mut n := 0
  for line in text.splitOn "\n" do
    n := n + 1
    let r : P (Option Section × Option Directive × Option DataLine) := do
      if line.isEmpty then return (none, none, none)
      if line == ".text" then
        unless sec == .text do throw ".text after another section"
        return (some .text, none, none)
      if line == ".section .rodata" then return (some .rodata, none, none)
      if line == ".section .note.GNU-stack,\"\",@progbits" then return (some .note, none, none)
      if line.startsWith ".globl " then
        discard <| name (line.drop 7).toString
        return (none, none, none)
      match sec with
      | .text =>
        if line.endsWith ":" then return (none, some (.label (← name (line.dropEnd 1).toString)), none)
        return (none, some (.instr (← instr line)), none)
      | .rodata => return (none, none, some (← dataLine line))
      | .note => throw "content in .note.GNU-stack"
    match r with
    | .error e => throw s!"line {n}: {e}: {line}"
    | .ok (s, d, x) =>
      if let some s := s then sec := s
      if let some d := d then code := code.push d
      if let some x := x then data := data.push x
  return { text := code.toList, data := data.toList }

end ConAgua.AsmFile
