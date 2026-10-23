module

public import ConAgua.Compiler.Run

@[expose] public section

/-!
# The entry stub: `ca_start(in, in_len, pins, pins_len, base, base_len)` (lane `abi`)

The harness's whole job shrinks to: map a zero region, hand over the two input buffers, call once.
The stub, emitted before the trampoline, sets up inside the region everything the harness used to
lay out (`L.Compiler.Tab`), then tail-jumps into the trampoline `ca_enter(T, fuel)`:

* System V arguments: `rdi`/`rsi` = the input bytes (byte array `0`), `rdx`/`rcx` = the pin-data
  bytes (byte array `1`; ignored if the program has one byte array), `r8` = `base`, `r9` =
  `base_len`. Returns `rax`/`rdx` as `ca_enter` does.
* If `base_len < abiNeed`, it returns at once with `rdx = 1` (resources exhausted; never accept).
* The region is a static partition into `abiSlot`-byte slots (no allocator; the pages that are
  never touched never become real): slot `0` is the table (`T = base`), slot `1` the L stack
  (`abiStack` bytes at its bottom), then one slot per byte array `2, …, nb - 1` and per word array.
  Each array starts at its slot's start; its length is `abiSlot` bytes, resp. `abiWords` words.
* The constant data is written into the table by immediate stores (no `.rodata` read); the result
  area and the global variables are the region's zeros.
* The fuel is `2^62 - 1` (`checker_x64_accepts` takes any `N < 2^62`).

Nothing here is trusted: `sim_abiStub` (`ConAgua/Compiler/AbiSim.lean`) runs the stub on the
machine, `abiLayout_ok` and `abi_memRel` (`ConAgua/Final/Abi.lean`) show that it establishes
`Layout.Ok`/`MemRel` for the partition, and `checker_x64_accepts_abi` continues with
`checker_x64_accepts` at the trampoline. -/

namespace L.Compiler

/-- The slot size: `2^35` bytes (`2^32` words). -/
def abiSlot : Nat := 2 ^ 35
/-- The L stack: `2^30` bytes (the old harness's default `CA_STACK`). -/
def abiStack : Nat := 2 ^ 30
/-- The fuel the stub passes to the trampoline. -/
def abiFuel : Nat := 2 ^ 62 - 1

/-- Every word array gets its whole slot. -/
def abiWords : Nat := 2 ^ 32

/-- The slot of byte array `a ≥ 2`. -/
def abiSlot8 (a : Nat) : Nat := a
/-- The slot of word array `a`. -/
def abiSlot64 (tab : Tab) (a : Nat) : Nat := 2 + (tab.nb - 2) + a
/-- The region size the stub needs. -/
def abiNeed (tab : Tab) : Nat := abiSlot * (2 + (tab.nb - 2) + tab.nw)

/-! ## The stores

The stub's body writes the table's first words in order, word `i` at `[r8 + 8i]` (`storesCode`):
a register, an immediate (through `rax`), or `r8 + off` (an address in the region, through
`rax`). The table's layout (`Tab`) puts the stack top and limit, then the byte arrays' and the
word arrays' base/length pairs, then the constant data at consecutive words, so the stores are
one run from `T`. -/

inductive SVal where
  /-- the register `r` -/
  | reg (r : Reg64)
  /-- the word `w` -/
  | imm (w : Word)
  /-- `r8 + off` -/
  | addr (off : Nat)

/-- `[r8 + d] := v`. -/
def SVal.code (d : Nat) : SVal → Program
  | .reg r => [movMR (mb .r8 d) r]
  | .imm w => [movRI .rax w, movMR (mb .r8 d) .rax]
  | .addr off => [movRI .rax off.toUInt64, i64 (.add (.reg (rr .rax)) (oR .r8)), movMR (mb .r8 d) .rax]

/-- `[r8 + d] := v₀`, `[r8 + d + 8] := v₁`, …. -/
def storesCode (d : Nat) : List SVal → Program
  | [] => []
  | v :: vs => v.code d ++ storesCode (d + 8) vs

/-- The little-endian word of (at most) eight bytes, padded with zeros. -/
def romWord (bs : List UInt8) : Word := UInt64.ofBytes (bs ++ List.replicate (8 - bs.length) 0)

/-- The words of the constant data `bs` (the last one padded with zeros): structural, and `Nat`
arithmetic, so that the kernel evaluates it fast. -/
def romVals : List UInt8 → List SVal
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: bs =>
    .imm (romWord [b0, b1, b2, b3, b4, b5, b6, b7]) :: romVals bs
  | [] => []
  | bs => [.imm (romWord bs)]

/-- The table's words, in order: the stack top and limit, the input buffers (byte arrays `0`, `1`),
the other byte arrays, the word arrays, the constant data. -/
def abiVals (tab : Tab) : List SVal :=
  [.addr (abiSlot + abiStack), .addr abiSlot, .reg .rdi, .reg .rsi] ++
  (if 2 ≤ tab.nb then [.reg .rdx, .reg .rcx] else []) ++
  ((List.range tab.nb).drop 2).flatMap (fun a => [.addr (abiSlot * abiSlot8 a), .imm abiSlot.toUInt64]) ++
  (List.range tab.nw).flatMap (fun a => [.addr (abiSlot * abiSlot64 tab a), .imm abiWords.toUInt64]) ++
  romVals tab.rom

def abiDeclineL : Label := "ca_abi_decline"
def abiStartL : Label := "ca_start"

def abiHead (tab : Tab) : Program :=
  [.label abiStartL,
   movRI .rax (abiNeed tab).toUInt64, i64 (.cmp (.reg (rr .r9)) (oR .rax)), jccL .c abiDeclineL]

def abiTail : Program :=
  [movRR .rdi .r8, movRI .rsi abiFuel.toUInt64, jmpL enterL,
   .label abiDeclineL, movRI .rax 0, movRI .rdx 1, i64 .ret]

/-- The stub for the table `tab`. -/
def abiStub (tab : Tab) : Program :=
  abiHead tab ++ storesCode 0 (abiVals tab) ++ abiTail

/-- The stub's symbols for the harness: `ca_region_size` (the least `base_len`), `ca_slot` and
`ca_w0` (the offset of word array `0`; for diagnostics). -/
def abiSymbols (tab : Tab) : String :=
  s!".section .rodata\n.globl ca_region_size\n.globl ca_slot\n.globl ca_w0\nca_region_size: .quad {abiNeed tab}\nca_slot: .quad {abiSlot}\nca_w0: .quad {abiSlot * abiSlot64 tab 0}\n"

/-- The assembler file: the stub, then `code` (the trampoline and the functions), as `asmTextOf`. -/
def asmTextAbi (tab : Tab) (code : Program) : String :=
  ".text\n.globl " ++ abiStartL ++ "\n" ++ asmTextOf tab (abiStub tab ++ code) ++ abiSymbols tab

end L.Compiler
