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
  (List.range tab.nw).map (fun p => .addr (abiSlot * abiSlot64 tab (tab.wposInv p))) ++
  (List.range tab.nw).map (fun _ => .imm abiWords.toUInt64) ++
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

/-! ## The parallel mode's entries (lane parmode, docs/design/parmode.md)

More entries, emitted before `ca_start`. The checker's `check` reads the global `mode` (`0` in a
zero region: `ca_start` is the whole pipeline). `fz` lists the frozen arrays in header order, each
with the array that holds its image in place (`OUT` for the header, `CTL` for its seed, else
itself); `own` the worker's arrays.

* `ca_start_a(in, in_len, pins, pins_len, base, base_len)` (**entry 1**): `ca_start` with the mode
  word `1` (the stages, phase A, the frozen buffer, header and images, in the array `out`).
* `ca_check_b(buf, buf_len, lo, hi, region, region_len)` (**entry 2 over a buffer**, the threads):
  the table at `region`, the L stack in its second slot, the arrays `own` in the slots after it,
  frozen array `i` at `buf + 8 · buf[8 + 2i]` with length `buf[9 + 2i]`, every other array
  `(0, 0)`, the constant data as `ca_start`; `plo := lo`, `phi := hi`, the mode word `2`; then
  `ca_enter`. Declines (`rdx = 1`) if `region_len < workerNeed own`.
* `ca_check_seq(base, lo, hi)` (**entry 2 in place**, the sequential driver), on a region entry 1
  left: the table at `base` as `ca_start` lays it out, except that frozen array `i` is the prefix
  of its in-place array of length `buf[9 + 2i]` (`buf` the header in `out`'s slot) and the byte
  arrays are `(0, 0)`; `plo`, `phi`, the mode word `2`; then `ca_enter`.
* `ca_start_drv(in, in_len, pins, pins_len, base, base_len)` (**the sequential driver**): entry 1
  with the mode word `3` (the buffer's header only); if it returns `rdx = 0` and `rax = 2^63 + k`,
  `ca_check_seq(base, 0, k)`, whose result is the result. It needs no more memory than
  `ca_start`: entry 2 runs on phase A's region, its owned arrays where phase A left them, every
  frozen image in place. `rbx` (which the compiled code never writes) holds `base`. -/

def abiStartAL : Label := "ca_start_a"
def abiStartA0L : Label := "ca_start_a0"
def abiCheckBL : Label := "ca_check_b"
def abiCheckSL : Label := "ca_check_seq"
def abiDrvL : Label := "ca_start_drv"

/-- The worker region's size for the owned arrays `own`: the table, the stack, one slot each. -/
def workerNeed (own : List ArrId) : Nat := abiSlot * (2 + own.length)

/-- `ca_check_b`'s descriptor words for word array `a` (`rdi` the buffer, `rcx` the table). -/
def parDescB (tab : Tab) (fz : List (ArrId × ArrId)) (own : List ArrId) (a : ArrId) : Program :=
  match (fz.map (·.1)).idxOf? a with
  | some i =>
    [movRM .rax (mb .rdi (8 * (8 + 2 * i))), i64 (.shl (.reg (rr .rax)) (.imm8 (.int64 (Int64.ofInt 3)))),
     i64 (.add (.reg (rr .rax)) (oR .rdi)), movMR (mb .rcx (tab.base64 a)) .rax,
     movRM .rax (mb .rdi (8 * (9 + 2 * i))), movMR (mb .rcx (tab.len64 a)) .rax]
  | none =>
    match own.idxOf? a with
    | some k =>
      [movRI .rax (abiSlot * (2 + k)).toUInt64, i64 (.add (.reg (rr .rax)) (oR .rcx)),
       movMR (mb .rcx (tab.base64 a)) .rax, movRI .rax abiWords.toUInt64,
       movMR (mb .rcx (tab.len64 a)) .rax]
    | none => [movRI .rax 0, movMR (mb .rcx (tab.base64 a)) .rax, movMR (mb .rcx (tab.len64 a)) .rax]

/-- `ca_check_seq`'s descriptor words for word array `a` (`rdi` the table = the region, `rcx` the
header). -/
def parDescS (tab : Tab) (fz : List (ArrId × ArrId)) (a : ArrId) : Program :=
  match (fz.map (·.1)).idxOf? a with
  | some i =>
    [movRI .rax (abiSlot * abiSlot64 tab ((fz.map (·.2)).getD i 0)).toUInt64,
     i64 (.add (.reg (rr .rax)) (oR .rdi)), movMR (mb .rdi (tab.base64 a)) .rax,
     movRM .rax (mb .rcx (8 * (9 + 2 * i))), movMR (mb .rdi (tab.len64 a)) .rax]
  | none =>
    [movRI .rax (abiSlot * abiSlot64 tab a).toUInt64, i64 (.add (.reg (rr .rax)) (oR .rdi)),
     movMR (mb .rdi (tab.base64 a)) .rax, movRI .rax abiWords.toUInt64,
     movMR (mb .rdi (tab.len64 a)) .rax]

/-- `[r + d] := v₀`, `[r + d + 8] := v₁`, … for immediate words. -/
def immStores (r : Reg64) (d : Nat) : List SVal → Program
  | [] => []
  | .imm w :: vs => [movRI .rax w, movMR (mb r d) .rax] ++ immStores r (d + 8) vs
  | _ :: vs => immStores r (d + 8) vs

/-- The parallel mode's entries, for the globals `mode`, `plo`, `phi`, the buffer array `out`, the
frozen arrays `fz` and the owned arrays `own`. -/
def parStub (tab : Tab) (mode plo phi : GVar) (out : ArrId) (fz : List (ArrId × ArrId))
    (own : List ArrId) : Program :=
  -- entry 1, and the driver's entry 1
  [.label abiStartAL,
   movRI .rax (abiNeed tab).toUInt64, i64 (.cmp (.reg (rr .r9)) (oR .rax)), jccL .c abiStartL,
   movRI .rax 1, movMR (mb .r8 (tab.globOff mode)) .rax, jmpL abiStartL,
   .label abiStartA0L,
   movRI .rax (abiNeed tab).toUInt64, i64 (.cmp (.reg (rr .r9)) (oR .rax)), jccL .c abiStartL,
   movRI .rax 3, movMR (mb .r8 (tab.globOff mode)) .rax, jmpL abiStartL,
  -- entry 2 over a buffer
   .label abiCheckBL,
   movRI .rax (workerNeed own).toUInt64, i64 (.cmp (.reg (rr .r9)) (oR .rax)), jccL .c abiDeclineL,
   movRR .r9 .rcx, movRR .rcx .r8,
   movRI .rax (abiSlot + abiStack).toUInt64, i64 (.add (.reg (rr .rax)) (oR .rcx)),
   movMR (mb .rcx Tab.stackTop) .rax,
   movRI .rax abiSlot.toUInt64, i64 (.add (.reg (rr .rax)) (oR .rcx)),
   movMR (mb .rcx Tab.stackLimit) .rax,
   movRI .rax 0] ++
  ((List.range tab.nb).flatMap fun a => [movMR (mb .rcx (tab.base8 a)) .rax, movMR (mb .rcx (tab.len8 a)) .rax]) ++
  ((List.range tab.nw).flatMap fun p => parDescB tab fz own (tab.wposInv p)) ++
  immStores .rcx tab.romBase.toNat (romVals tab.rom) ++
  [movMR (mb .rcx (tab.globOff plo)) .rdx, movMR (mb .rcx (tab.globOff phi)) .r9,
   movRI .rax 2, movMR (mb .rcx (tab.globOff mode)) .rax,
   movRR .rdi .rcx, movRI .rsi abiFuel.toUInt64, jmpL enterL,
  -- entry 2 in place
   .label abiCheckSL,
   movRI .rcx (abiSlot * abiSlot64 tab out).toUInt64, i64 (.add (.reg (rr .rcx)) (oR .rdi)),
   movRI .rax (abiSlot + abiStack).toUInt64, i64 (.add (.reg (rr .rax)) (oR .rdi)),
   movMR (mb .rdi Tab.stackTop) .rax,
   movRI .rax abiSlot.toUInt64, i64 (.add (.reg (rr .rax)) (oR .rdi)),
   movMR (mb .rdi Tab.stackLimit) .rax,
   movRI .rax 0] ++
  ((List.range tab.nb).flatMap fun a => [movMR (mb .rdi (tab.base8 a)) .rax, movMR (mb .rdi (tab.len8 a)) .rax]) ++
  ((List.range tab.nw).flatMap fun p => parDescS tab fz (tab.wposInv p)) ++
  immStores .rdi tab.romBase.toNat (romVals tab.rom) ++
  [movMR (mb .rdi (tab.globOff plo)) .rsi, movMR (mb .rdi (tab.globOff phi)) .rdx,
   movRI .rax 2, movMR (mb .rdi (tab.globOff mode)) .rax,
   movRI .rsi abiFuel.toUInt64, jmpL enterL,
  -- the sequential driver
   .label abiDrvL,
   i64 (.push (oR .rbx)),
   movRI .rax (abiNeed tab).toUInt64, i64 (.cmp (.reg (rr .r9)) (oR .rax)), jccL .c "ca_drv_decline",
   movRR .rbx .r8,
   i64 (.call (.rel (.sub (.label abiStartA0L) .after_current_instruction))),
   i64 (.cmp (.reg (rr .rdx)) (oI 0)), jccL .nz "ca_drv_done",
   movRI .rcx 9223372036854775808, i64 (.cmp (.reg (rr .rax)) (oR .rcx)), jccL .c "ca_drv_done",
   i64 (.sub (.reg (rr .rax)) (oR .rcx)), movRR .rdx .rax, movRI .rsi 0, movRR .rdi .rbx,
   i64 (.call (.rel (.sub (.label abiCheckSL) .after_current_instruction))),
   jmpL "ca_drv_done",
   .label "ca_drv_decline", movRI .rax 0, movRI .rdx 1,
   .label "ca_drv_done", i64 (.pop (.reg (rr .rbx))), i64 .ret]

/-- The symbols of the parallel mode for the harness. -/
def parSymbols (tab : Tab) (out : ArrId) (own : List ArrId) : String :=
  s!".section .rodata\n.globl ca_out_off\n.globl ca_worker_size\nca_out_off: .quad {abiSlot * abiSlot64 tab out}\nca_worker_size: .quad {workerNeed own}\n"

/-- The assembler file with the parallel mode's entries (`parStub`) before the stub. -/
def asmTextAbiPar (tab : Tab) (mode plo phi : GVar) (out : ArrId) (fz : List (ArrId × ArrId))
    (own : List ArrId) (code : Program) : String :=
  ".text\n.globl " ++ abiStartL ++ "\n.globl " ++ abiStartAL ++ "\n.globl " ++ abiCheckBL ++ "\n.globl " ++
    abiCheckSL ++ "\n.globl " ++ abiDrvL ++ "\n" ++
    asmTextOf tab (parStub tab mode plo phi out fz own ++ abiStub tab ++ code) ++
    abiSymbols tab ++ parSymbols tab out own

end L.Compiler
