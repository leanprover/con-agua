module

public import ConAgua.Compiler.Compile
public import Kraken.X64.Semantics
public import Kraken.X64.PrintATT

@[expose] public section

/-!
# Running compiled L code

* `asmText` prints a compiled program as an assembler file (AT&T syntax, for `as`/`clang`) whose
  entry point is `ca_enter(T, fuel)`; `harness/run.c` is the matching C driver.
* `runKraken` runs a compiled program on Kraken's executable semantics (`Executable.eval`, with
  Kraken's fake layout), from the same initial state the C driver sets up, so that the compiled
  code can be tested against `L.run` with `#eval`/`#guard`.
-/

namespace L.Compiler

/-- The assembler file for `compileProg tab p entry`. The constant data `tab.rom` is emitted as
`ca_rom` (`ca_rom_len` bytes) in `.rodata`; the driver copies it into the table. -/
def asmText (tab : Tab) (p : Prog) (entry : FnName) : String :=
  ".text\n.globl " ++ enterL ++ "\n" ++ Kraken.X64.toATT (compileProg tab p entry) ++ "\n" ++
    ".section .rodata\n.globl ca_rom\n.globl ca_rom_len\nca_rom_len: .quad " ++ toString tab.rom.length ++
    "\nca_rom:" ++ (if tab.rom.isEmpty then "" else " .byte " ++ ", ".intercalate (tab.rom.map toString)) ++
    "\n.section .note.GNU-stack,\"\",@progbits\n"

/-- The outcome of a run of compiled code, as `ca_enter` returns it: on success, the `nres`
result registers. -/
inductive Outcome where
  | ok (rs : List Word)
  | exhausted
  | error
  deriving Repr, DecidableEq

/-- The first `n` result registers. -/
def resRegs (R : Reg64s) (n : Nat) : List Word :=
  (List.range n).map fun i => UInt64.ofBitVec (R.get64 (resReg i))

def Outcome.ofRegs (R : Reg64s) (n : Nat) : Outcome :=
  if R.rdx = 0 then .ok (resRegs R n) else if R.rdx = 1 then .exhausted else .error

/-- What `L.run` says, in the same shape (the first `n` results, `0` past the end; an
`outOfFuel` error is `exhausted`). -/
def Outcome.ofL (n : Nat) : Except Err (List Word × Mem) → Outcome
  | .ok (rs, _) => .ok ((List.range n).map fun i => rs.getD i 0)
  | .error .outOfFuel => .exhausted
  | .error _ => .error

def kStoreWord (m : DataMem) (a : Nat) (v : Word) : DataMem :=
  Mem.storeInt m (BitVec.ofNat 64 a) 8 v.toNat

def kStoreBytes (m : DataMem) (a : Nat) (bs : List UInt8) : DataMem :=
  Mem.storeBytes m (BitVec.ofNat 64 a) bs

def kWordBytes (v : Word) : List UInt8 :=
  (List.range 8).map fun i => (v >>> (8 * i).toUInt64).toUInt8

/-- Run `entry` of the compiled `p` on Kraken's semantics: the table at `0x10000`, the L stack
(`stackBytes` bytes) below `0x400000`, the arrays from `0x1000000` on, the trampoline's caller
stack at `0x8000`, returning to `0xdead0`. Returns `(rax, rdx)` at the return. -/
def runKraken (p : Prog) (entry : FnName) (args : List Word) (m : Mem) (fuel : Word)
    (stackBytes : Nat := 4096) : Except String Outcome := do
  let tab : Tab := Prog.tab p m.bytes.size m.words.size
  let T := 0x10000
  let stackTop := 0x400000
  let ra : Nat := 0xdead0
  let csp := 0x8000
  -- the arrays, one after the other
  let (bases8, next) := m.bytes.foldl (fun (acc, a) arr => (acc.push a, a + arr.size + 64)) (#[], 0x1000000)
  let (bases64, _) := m.words.foldl (fun (acc, a) arr => (acc.push a, a + 8 * arr.size + 64)) (#[], next)
  let mut d : DataMem := ∅
  -- the caller's stack: 64 bytes below and the return address
  d := kStoreBytes d (csp - 64) (List.replicate 64 0)
  d := kStoreWord d csp ra.toUInt64
  -- the L stack
  d := kStoreBytes d (stackTop - stackBytes) (List.replicate stackBytes 0)
  -- the table
  d := kStoreWord d (T + Tab.stackTop.toNat) stackTop.toUInt64
  d := kStoreWord d (T + Tab.stackLimit.toNat) (stackTop - stackBytes).toUInt64
  for a in [0:m.bytes.size] do
    d := kStoreWord d (T + (tab.base8 a).toNat) (bases8[a]!).toUInt64
    d := kStoreWord d (T + (tab.len8 a).toNat) (m.arr8 a).size.toUInt64
    d := kStoreBytes d bases8[a]! (m.arr8 a).toList
  for a in [0:m.words.size] do
    d := kStoreWord d (T + (tab.base64 a).toNat) (bases64[a]!).toUInt64
    d := kStoreWord d (T + (tab.len64 a).toNat) (m.arr64 a).size.toUInt64
    d := kStoreBytes d bases64[a]! ((m.arr64 a).toList.flatMap kWordBytes)
  d := kStoreBytes d (T + tab.romBase.toNat) tab.rom
  for (v, i) in args.zipIdx do
    d := kStoreWord d (T + tab.args.toNat + 8 * i) v
  let exe := Program.fakeLayout (compileProg tab p entry)
  let start := exe.labels.label enterL
  let s : MachineData := { dmem := d, regs := { rsp := csp.toUInt64, rdi := T.toUInt64, rsi := fuel } }
  let s' ← Executable.eval exe { data := s, pc := start } (fun st => st.pc = Int64.ofNat ra)
  return Outcome.ofRegs s'.data.regs tab.nres

end L.Compiler
