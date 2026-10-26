module

public import ConAgua.Compiler.Run

@[expose] public section

/-!
# The entry stubs (lane `abi`)

The harness's whole job shrinks to: map a zero region, hand over the two input buffers, call
`ca_start(in, in_len, pins, pins_len, base, base_len)` once. `ca_start` is the sequential driver
(`parStub`, below): it calls entry 1 and then entry 2 on the same region. Both go through the
setup stub `ca_setup` (`abiStub`, an internal label; the argument registers as `ca_start`'s),
emitted before the trampoline, which sets up inside the region everything the harness used to lay
out (`L.Compiler.Tab`), then tail-jumps into the trampoline `ca_enter(T, fuel)`:

* System V arguments: `rdi`/`rsi` = the input bytes (byte array `0`), `rdx`/`rcx` = the pin-data
  bytes (byte array `1`; ignored if the program has one byte array), `r8` = `base`, `r9` =
  `base_len`. Returns `rax`/`rdx` as `ca_enter` does.
* If `base_len < abiNeed`, or if `in_len` or `pins_len` is `2^63` or more (the top bit of `rsi`
  or `rcx` set: `cmp r, 0; jl`), it returns at once with `rdx = 1` (resources exhausted; never
  accept). So a run that gets past the stub has both buffers below `2^63` bytes, which the
  refinements assume (`InputsOK`).
* The region is a static partition into `abiSlot`-byte slots (no allocator; the pages that are
  never touched never become real): slot `0` is the table (`T = base`), slot `1` the L stack
  (`abiStack` bytes at its bottom), then one slot per byte array `2, …, nb - 1` and per word array.
  Each array starts at its slot's start; its length is `abiSlot` bytes, resp. `abiWords` words.
* The constant data is written into the table by immediate stores (no `.rodata` read); the result
  area and the global variables are the region's zeros.
* The fuel is `2^62 - 1` (`compile_correct` takes any `N < 2^62`).

Nothing here is trusted: `sim_abiStub` (`ConAgua/Compiler/AbiSim.lean`) runs the stub on the
machine, `abiLayout_ok` and `abi_memRel` (`ConAgua/Final/Abi.lean`) show that it establishes
`Layout.Ok`/`MemRel` for the partition, and `abi_harness` gives `compile_correct`'s premises at
the trampoline. -/

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
/-- The driver's save area (the caller's `r15` and its return address): the 16 bytes past
`ca_setup`'s region (`abiNeed`), which the driver needs in addition (`drvNeed`). Entry 1 is called
on the region without them (`r9 := abiNeed`), so it sees a zero region. -/
def drvSave (tab : Tab) : Nat := abiNeed tab
/-- The region size the driver needs. -/
def drvNeed (tab : Tab) : Nat := abiNeed tab + 16

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
def abiSetupL : Label := "ca_setup"
/-- The sequential driver (`parStub`), the entry the harness calls. -/
def abiStartL : Label := "ca_start"

def abiHead (tab : Tab) : Program :=
  [.label abiSetupL,
   movRI .rax (abiNeed tab).toUInt64, i64 (.cmp (.reg (rr .r9)) (oR .rax)), jccL .c abiDeclineL,
   i64 (.cmp (.reg (rr .rsi)) (oI 0)), jccL .l abiDeclineL,
   i64 (.cmp (.reg (rr .rcx)) (oI 0)), jccL .l abiDeclineL]

def abiTail : Program :=
  [movRR .rdi .r8, movRI .rsi abiFuel.toUInt64, jmpL enterL,
   .label abiDeclineL, movRI .rax 0, movRI .rdx 1, i64 .ret]

/-- The stub for the table `tab`. -/
def abiStub (tab : Tab) : Program :=
  abiHead tab ++ storesCode 0 (abiVals tab) ++ abiTail

/-- The stub's symbols for the harness: `ca_region_size` (the least `base_len`), `ca_slot` and
`ca_w0` (the offset of word array `0`; for diagnostics). `ca_region_size` is the sequential
driver's need (`drvNeed`, 16 bytes above `ca_setup`'s, which it covers). -/
def abiSymbols (tab : Tab) : String :=
  s!".section .rodata\n.globl ca_region_size\n.globl ca_slot\n.globl ca_w0\nca_region_size: .quad {drvNeed tab}\nca_slot: .quad {abiSlot}\nca_w0: .quad {abiSlot * abiSlot64 tab 0}\n"

/-- The assembler file of a program without the parallel mode's entries (the e2e tools): the
stub, labelled `ca_start` as well, then `code` (the trampoline and the functions), as
`asmTextOf`. -/
def asmTextAbi (tab : Tab) (code : Program) : String :=
  ".text\n.globl " ++ abiStartL ++ "\n" ++ asmTextOf tab (.label abiStartL :: abiStub tab ++ code) ++
    abiSymbols tab

/-! ## The parallel mode's entries (lane parmode, docs/design/parmode.md)

More entries, emitted before `ca_setup`. The checker's `check` reads the global `mode` (`0` in a
zero region, where `check` aborts: every entry writes the mode first). `fz` lists the frozen arrays in header order
(`hdrf` the header, `ctlf` the seed of `CTL`, `hw` the header's length), `own` the worker's
arrays.

* `ca_start_a(in, in_len, pins, pins_len, base, base_len)` (**entry 1**): `ca_setup` with the mode
  word `1` (the stages, phase A, the frozen buffer, header and images, in the array `out`).
* `ca_check_b(buf, buf_len, j, region, region_len)` (**entry 2 over a buffer**, the threads):
  the table at `region`, the L stack in its second slot, the arrays `own` in the slots after it,
  frozen array `i` at `buf + 8 · buf[8 + 2i]` with length `buf[9 + 2i]`, every other array
  `(0, 0)`, the constant data as `ca_setup`; `plo := j`, `phi := j + 1` (one pending group), the
  mode word `2`; then `ca_enter`. Declines (`rdx = 1`) if `region_len < workerNeed own`.
* `ca_check_seq` (**entry 2 in place**, the sequential driver; the region in `r8`, the range
  `lo`, `hi` in `rsi`, `rdx`), on a region entry 1 left: the table as `ca_setup` lays it out, except
  that `out`, the seed of `CTL` and the byte arrays get no memory and the header `hdrf` is the
  first `hw` words of `out`'s slot (`seqVals`: static words, as `abiStub`'s); `plo`, `phi`, the
  mode word `2`; then `ca_enter`. The frozen arrays are phase A's own, whole (only the threads
  read images cut to their extents).
* `ca_start(in, in_len, pins, pins_len, base, base_len)` (**the sequential driver**, what the
  harness calls): entry 1 with the mode word `3` (`ca_start_a0`: the buffer's header only); if it
  returns `rdx = 0` and `rax = 2^63 + k`, `ca_check_seq` on the same region for `[0, k)`, whose
  result is the result. It needs no more memory than `ca_setup`: entry 2 runs on phase A's region,
  on the arrays as phase A left them.
  It keeps its return address and the caller's `r15` past `ca_setup`'s region (`drvSave`; the
  driver's region is 16 bytes larger, `drvNeed`, the size `ca_region_size` names), pops its return
  address off the machine stack before each `call` and holds `base` in `r15` (which `ca_enter`
  restores); so each callee's machine stack is the caller's (the 32 bytes `AbiCall` names) and
  the driver touches no callee-saved register but `r15`. -/

def abiStartAL : Label := "ca_start_a"
def abiStartA0L : Label := "ca_start_a0"
def abiCheckBL : Label := "ca_check_b"
def abiCheckSL : Label := "ca_check_seq"
def abiDrvDoneL : Label := "ca_drv_done"
def abiDrvDeclineL : Label := "ca_drv_decline"


/-- The worker region's size for the owned arrays `own`: the table, the stack, one slot each. -/
def workerNeed (own : List ArrId) : Nat := abiSlot * (2 + own.length)

/-- `ca_check_b`'s descriptor words for word array `a` (`rdi` the buffer, `rcx` the table). -/
def parDescB (tab : Tab) (fz own : List ArrId) (a : ArrId) : Program :=
  match fz.idxOf? a with
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

/-- `ca_check_seq`'s table words, in `abiVals`' order: `ca_setup`'s layout of the region, except
that `out`, the seed `ctlf` and the byte arrays get no memory and the header `hdrf` is the first
`hw` words of `out`'s slot. Static values only (`storesCode`, as `abiStub`). -/
def seqVals (tab : Tab) (out hdrf ctlf : ArrId) (hw : Nat) : List SVal :=
  [.addr (abiSlot + abiStack), .addr abiSlot] ++
  (List.range tab.nb).flatMap (fun _ => [.imm 0, .imm 0]) ++
  (List.range tab.nw).map (fun p =>
    let a := tab.wposInv p
    if a = out ∨ a = ctlf then .imm 0
    else if a = hdrf then .addr (abiSlot * abiSlot64 tab out)
    else .addr (abiSlot * abiSlot64 tab a)) ++
  (List.range tab.nw).map (fun p =>
    let a := tab.wposInv p
    if a = out ∨ a = ctlf then .imm 0
    else if a = hdrf then .imm hw.toUInt64
    else .imm abiWords.toUInt64) ++
  romVals tab.rom

/-- `[r + d] := v₀`, `[r + d + 8] := v₁`, … for immediate words. -/
def immStores (r : Reg64) (d : Nat) : List SVal → Program
  | [] => []
  | .imm w :: vs => [movRI .rax w, movMR (mb r d) .rax] ++ immStores r (d + 8) vs
  | _ :: vs => immStores r (d + 8) vs

/-- The parallel mode's entries, for the globals `mode`, `plo`, `phi`, the buffer array `out`, the
frozen arrays `fz` and the owned arrays `own`. -/
def parStub (tab : Tab) (mode plo phi : GVar) (out hdrf ctlf : ArrId) (hw : Nat) (fz own : List ArrId) :
    Program :=
  -- entry 1, and the driver's entry 1
  [.label abiStartAL,
   movRI .rax (abiNeed tab).toUInt64, i64 (.cmp (.reg (rr .r9)) (oR .rax)), jccL .c abiSetupL,
   movRI .rax 1, movMR (mb .r8 (tab.globOff mode)) .rax, jmpL abiSetupL,
   .label abiStartA0L,
   movRI .rax (abiNeed tab).toUInt64, i64 (.cmp (.reg (rr .r9)) (oR .rax)), jccL .c abiSetupL,
   movRI .rax 3, movMR (mb .r8 (tab.globOff mode)) .rax, jmpL abiSetupL,
  -- entry 2 over a buffer
   .label abiCheckBL,
   movRI .rax (workerNeed own).toUInt64, i64 (.cmp (.reg (rr .r8)) (oR .rax)), jccL .c abiDeclineL,
   movRR .r9 .rdx, i64 (.add (.reg (rr .r9)) (oI 1)),
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
  -- entry 2 in place (the region in `r8`, the range in `rsi`, `rdx`)
   .label abiCheckSL] ++
  storesCode 0 (seqVals tab out hdrf ctlf hw) ++
  [movMR (mb .r8 (tab.globOff plo)) .rsi, movMR (mb .r8 (tab.globOff phi)) .rdx,
   movRI .rax 2, movMR (mb .r8 (tab.globOff mode)) .rax,
   movRR .rdi .r8, movRI .rsi abiFuel.toUInt64, jmpL enterL,
  -- the sequential driver (its return address and the caller's `r15` in the save area, the
  -- region in `r15`; each `call` puts its return address in the caller's slot)
   .label abiStartL,
   movRI .rax (drvNeed tab).toUInt64, i64 (.cmp (.reg (rr .r9)) (oR .rax)), jccL .c abiDrvDeclineL,
   movRI .rax (drvSave tab).toUInt64, i64 (.add (.reg (rr .rax)) (oR .r8)),
   movMR (mb .rax 0) .r15, i64 (.pop (.reg (rr .r11))), movMR (mb .rax 8) .r11, movRR .r15 .r8,
   movRI .r9 (abiNeed tab).toUInt64,
   i64 (.call (.rel (.sub (.label abiStartA0L) .after_current_instruction))),
   i64 (.cmp (.reg (rr .rdx)) (oI 0)), jccL .nz abiDrvDoneL,
   movRI .rcx 9223372036854775808, i64 (.cmp (.reg (rr .rax)) (oR .rcx)), jccL .c abiDrvDoneL,
   i64 (.sub (.reg (rr .rax)) (oR .rcx)), movRR .rdx .rax, movRI .rsi 0, movRR .r8 .r15,
   i64 (.call (.rel (.sub (.label abiCheckSL) .after_current_instruction))),
   .label abiDrvDoneL,
   movRR .rcx .rax, movRI .rax (drvSave tab).toUInt64, i64 (.add (.reg (rr .rax)) (oR .r15)),
   movRM .rsi (mb .rax 8), movRM .r15 (mb .rax 0), movRR .rax .rcx,
   i64 (.push (oR .rsi)), i64 .ret,
   .label abiDrvDeclineL, movRI .rax 0, movRI .rdx 1, i64 .ret]

/-- The symbols of the parallel mode for the harness. -/
def parSymbols (tab : Tab) (out : ArrId) (own : List ArrId) : String :=
  s!".section .rodata\n.globl ca_out_off\n.globl ca_worker_size\nca_out_off: .quad {abiSlot * abiSlot64 tab out}\nca_worker_size: .quad {workerNeed own}\n"

/-- The assembler file with the parallel mode's entries (`parStub`) before the stub. -/
def asmTextAbiPar (tab : Tab) (mode plo phi : GVar) (out hdrf ctlf : ArrId) (hw : Nat)
    (fz own : List ArrId) (code : Program) : String :=
  ".text\n.globl " ++ abiStartL ++ "\n.globl " ++ abiStartAL ++ "\n.globl " ++ abiCheckBL ++ "\n.globl " ++
    abiCheckSL ++ "\n" ++
    asmTextOf tab (parStub tab mode plo phi out hdrf ctlf hw fz own ++ abiStub tab ++ code) ++
    abiSymbols tab ++ parSymbols tab out own

end L.Compiler
