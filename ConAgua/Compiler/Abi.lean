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

* System V arguments: `rdi`/`rsi` = the input bytes (the byte array at descriptor position `0`),
  `rdx`/`rcx` = the pin-data bytes (position `1`; ignored if the program has one byte array), `r8` =
  `base`, `r9` = `base_len`. Returns `rax`/`rdx` as `ca_enter` does. Which arrays sit at positions
  `0` and `1` is the layout map's business: the final theorem's proof checks that they are the
  input's and the pin data's (`ConAgua/Final/Abi.lean`).
* If `base_len < abiNeed`, or if `in_len` or `pins_len` is `2^63` or more (the top bit of `rsi`
  or `rcx` set: `cmp r, 0; jl`), it returns at once with `rdx = 1` (resources exhausted; never
  accept). So a run that gets past the stub has both buffers below `2^63` bytes, which the
  refinements assume (`InputsOK`).
* The region is a static partition into `abiSlot`-byte slots (no allocator; the pages that are
  never touched never become real): slot `0` is the table (`T = base`), slot `1` the L stack
  (`abiStack` bytes at its bottom), then one slot per descriptor position past the two buffers, in
  position order (`Tab.slotOf`). Each array starts at its slot's start; its length is `abiSlot`
  bytes, resp. `abiWords` words. The table-relative array (`Tab.tbl64`) lies instead inside slot
  `0`, past the table, with its minimum length (`abiOff`, `abiSz`); it has the last position, which
  gets no slot (`Tab.nslot`).
* The constant data is written into the table by immediate stores (no `.rodata` read); the result
  area and the global variables are the region's zeros.
* The fuel is `abiFuelM = 2^62 - 1 - abiInl` (`compile_correct` takes any `N < 2^62`): the run of the
  inlined program it stands for is a run of the program with `abiFuel = 2^62 - 1` (`MainRef.lean`).

Nothing here is trusted: `sim_abiStub` (`ConAgua/Compiler/AbiSim.lean`) runs the stub on the
machine, `abiLayout_ok` and `abi_memRel` (`ConAgua/Final/Abi.lean`) show that it establishes
`Layout.Ok`/`MemRel` for the partition, and `abi_harness` gives `compile_correct`'s premises at
the trampoline. -/

namespace L.Compiler

/-- The slot size: `2^35` bytes (`2^32` words). -/
def abiSlot : Nat := 2 ^ 35
/-- The L stack: `2^30` bytes (the old harness's default `CA_STACK`). -/
def abiStack : Nat := 2 ^ 30
/-- The fuel of the L program's run that the final theorems speak of. -/
def abiFuel : Nat := 2 ^ 62 - 1
/-- The rounds of inlining before the code generator (`Compiler/Inline.lean`): a run of the inlined
program with fuel `n` is a run of the program with fuel `n + abiInl`. -/
def abiInl : Nat := 1
/-- The fuel the stub passes to the trampoline: `abiFuel - abiInl`, so that the run of the program
that the compiled (inlined) program's run stands for has fuel `abiFuel`. -/
def abiFuelM : Nat := abiFuel - abiInl

theorem abiFuelM_add : abiFuelM + abiInl = abiFuel := by decide

/-- Every word array gets its whole slot. -/
def abiWords : Nat := 2 ^ 32

/-- The caller's buffers: the byte positions `0` and `1` (if there are that many), which get the
input and the pin data and no slot. -/
def Tab.nbuf (tab : Tab) : Nat := min tab.nb 2

/-- The slot of descriptor position `p` (past the buffers): slot `0` is the table, slot `1` the L
stack, then one slot per position. -/
def Tab.slotOf (tab : Tab) (p : Nat) : Nat := p + 2 - tab.nbuf

/-- The number of slots: the table's, the stack's and one per position past the buffers, but none
for the table-relative array (`Tab.tbl`, at the last position: `abiTabOk`). -/
def Tab.nslot (tab : Tab) : Nat := tab.slotOf (tab.nb + tab.nw) - (if tab.tbl.isSome then 1 else 0)

/-- The slot of word array `a` (its tier 0). -/
def abiSlot64 (tab : Tab) (a : Nat) : Nat := tab.slotOf (tab.pos64 (TieredArray.t0 a))

/-- The length the stubs give word array `s` where they give it memory: the table-relative array
(`Tab.tbl64`) its minimum length, every other a whole slot. -/
def abiSz (tab : Tab) (s : TieredArray) : Nat :=
  match tab.tbl64 s with
  | some _ => tab.min64 s
  | none => abiWords

/-- Where `ca_setup` puts word position `p`'s array, from the region's start: the table-relative
array at its offset inside the table's slot, every other at its own slot. -/
def abiOff (tab : Tab) (p : Nat) : Nat :=
  match tab.tbl64 (tab.wAt p) with
  | some c => c
  | none => abiSlot * tab.slotOf p

/-- The region size the stub needs. -/
def abiNeed (tab : Tab) : Nat := abiSlot * tab.nslot
/-- The driver's save area (the caller's `r15` and its return address): the first 16 of the 64
bytes past `ca_setup`'s region (`abiNeed`), which the drivers need in addition (`drvNeed`; the
compared run's entry 1 `ca_start_ac` uses all 64, `cmpSave`). Entry 1 is called
on the region without them (`r9 := abiNeed`), so it sees a zero region. -/
def drvSave (tab : Tab) : Nat := abiNeed tab
/-- The region size the driver needs. -/
def drvNeed (tab : Tab) : Nat := abiNeed tab + 64

/-! ## The stores

The stub's body writes the table's first words in order, word `i` at `[r8 + 8i]` (`storesCode`):
a register, an immediate (through `rax`), or `r8 + off` (an address in the region, through
`rax`). The table's layout (`Tab`) puts the stack top and limit, then the bases, the lengths and
the 32-bit lengths of every position, then the constant data at consecutive words, so the stores
are one run from `T`. -/

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

/-- The base `ca_setup` gives position `p`: the input buffer, the pin-data buffer, a slot (bytes),
or `abiOff` (words). -/
def abiBase (tab : Tab) (p : Nat) : SVal :=
  if p < tab.nbuf then (if p = 0 then .reg .rdi else .reg .rdx)
  else if p < tab.nb then .addr (abiSlot * tab.slotOf p) else .addr (abiOff tab p)

/-- The length `ca_setup` gives position `p`: the buffers', a slot's bytes, `abiSz` words. -/
def abiLen (tab : Tab) (p : Nat) : SVal :=
  if p < tab.nbuf then (if p = 0 then .reg .rsi else .reg .rcx)
  else if p < tab.nb then .imm abiSlot.toUInt64 else .imm (abiSz tab (tab.wAt p)).toUInt64

/-- The length in 32-bit elements `ca_setup` gives position `p` (`Tab.dlen32`): twice `abiSz` at a
word position, `0` at a byte position. -/
def abiLen32 (tab : Tab) (p : Nat) : SVal :=
  if p < tab.nb then .imm 0 else .imm (2 * abiSz tab (tab.wAt p)).toUInt64

/-- The table's words, in order: the stack top and limit, the bases of the positions, their
lengths, their lengths in 32-bit elements, the constant data. -/
def abiVals (tab : Tab) : List SVal :=
  [.addr (abiSlot + abiStack), .addr abiSlot] ++
  (List.range (tab.nb + tab.nw)).map (abiBase tab) ++
  (List.range (tab.nb + tab.nw)).map (abiLen tab) ++
  (List.range (tab.nb + tab.nw)).map (abiLen32 tab) ++
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
  [movRR .rdi .r8, movRI .rsi abiFuelM.toUInt64, jmpL enterL,
   .label abiDeclineL, movRI .rax 0, movRI .rdx 1, i64 .ret]

/-- The stub for the table `tab`. -/
def abiStub (tab : Tab) : Program :=
  abiHead tab ++ storesCode 0 (abiVals tab) ++ abiTail

/-- The stub's symbols for the harness: `ca_region_size` (the least `base_len`), `ca_slot` and
`ca_w0` (the offset of the first word position's slot; the harness advises huge pages for the
slots from there). `ca_region_size` is the sequential driver's need (`drvNeed`, 64 bytes above
`ca_setup`'s, which it covers). -/
def abiSymbols (tab : Tab) : String :=
  s!".section .rodata\n.globl ca_region_size\n.globl ca_slot\n.globl ca_w0\nca_region_size: .quad {drvNeed tab}\nca_slot: .quad {abiSlot}\nca_w0: .quad {abiSlot * tab.slotOf tab.nb}\n"

/-- The table's counts for the harness and the tools: `ca_nw`, the slots from `ca_w0` on (the
word arrays' slots; `main.c` advises huge pages for them), `ca_nb` and `ca_npos`, the byte
positions and all positions (the descriptor columns, for the profiler). -/
def tabSymbols (tab : Tab) : String :=
  s!".section .rodata\n.globl ca_nw\n.globl ca_nb\n.globl ca_npos\nca_nw: .quad {tab.nslot - tab.slotOf tab.nb}\nca_nb: .quad {tab.nb}\nca_npos: .quad {tab.nb + tab.nw}\n"

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
  the table at `region`, the L stack in its second slot, the arrays `own` in the slots after it
  (`own[0]`, the table-relative array, inside the table's slot),
  frozen array `i` at `buf + 8 · buf[8 + 2i]` with length `buf[9 + 2i]`, every other array
  `(0, 0)`, the constant data as `ca_setup`; `plo := j`, `phi := j + 1` (one pending group), the
  mode word `2`; then `ca_enter`. Declines (`rdx = 1`) if a frozen array is shorter than its
  minimum length (`Tab.min64`, `bufMinStub`) or `region_len < workerNeed own`. A buffer with two
  phases (the compared run: `buf[5]`, the second phase's offset, nonzero) maps a job index
  `j ≥ buf[2]` to job `j - buf[2]` of the second phase's buffer at `buf + 8 · buf[5]`, on the
  region's second sub-region, from `workerNeed own` on (`cpProStub`; the harness's region is then
  at least `2 · workerNeed own` bytes, twice `ca_worker_size`).
* `ca_check_seq` (**entry 2 in place**, the sequential driver; the region in `r8`, the range
  `lo`, `hi` in `rsi`, `rdx`), on a region entry 1 left: the table as `ca_setup` lays it out, except
  that `out`, the seed of `CTL` and the byte arrays get no memory and the header `hdrf` is the
  first `hw` words of `out`'s slot (`seqVals`: static words, as `abiStub`'s); `plo`, `phi`, the
  mode word `2` (from `ca_check_seq_m`: the mode word in `r10`, the compared run's modes `8`, `9`);
  then `ca_enter`. The frozen arrays are phase A's own, whole (only the threads
  read images cut to their extents).
* `ca_start(in, in_len, pins, pins_len, base, base_len)` (**the sequential driver**, what the
  harness calls): entry 1 with the mode word `3` (`ca_start_a0`: the buffer's header only); if it
  returns `rdx = 0` and `rax = 2^63 + k`, `ca_check_seq` on the same region for `[0, k)`, whose
  result is the result. It needs no more memory than `ca_setup`: entry 2 runs on phase A's region,
  on the arrays as phase A left them.
  It keeps its return address and the caller's `r15` past `ca_setup`'s region (`drvSave`; the
  driver's region is 64 bytes larger, `drvNeed`, the size `ca_region_size` names), pops its return
  address off the machine stack before each `call` and holds `base` in `r15` (which `ca_enter`
  restores); so each callee's machine stack is the caller's (the 32 bytes `AbiCall` names) and
  the driver touches no callee-saved register but `r15`. -/

def abiStartAL : Label := "ca_start_a"
def abiStartA0L : Label := "ca_start_a0"
def abiCheckBL : Label := "ca_check_b"
/-- `ca_check_b` past its phase prologue (`cpProStub`), at its length tests. -/
def abiCheckB0L : Label := "ca_check_b_min"
/-- `ca_check_b` past its length tests (`bufMinStub`). -/
def abiCheckB1L : Label := "ca_check_b_go"
def abiCheckSL : Label := "ca_check_seq"
/-- `ca_check_seq` with the mode word in `r10` (the compared run's modes `8`, `9`). -/
def abiCheckSML : Label := "ca_check_seq_m"
/-- `ca_check_seq_m` past its table stores (the table already in place, the caller writes the
stack's top: a second run in place). -/
def abiCheckSGL : Label := "ca_check_seq_g"
def abiDrvDoneL : Label := "ca_drv_done"
def abiDrvDeclineL : Label := "ca_drv_decline"


/-- The worker region's size for the owned arrays `own`: the table (with `own[0]`, the
table-relative array, inside its slot), the stack, one slot each for `own[1]`, …. -/
def workerNeed (own : List TieredArray) : Nat := abiSlot * (2 + (own.length - 1))

/-- Where `ca_check_b` puts owned array `s`, number `k` of the owned list, from the worker region's
start: the table-relative array (`own[0]`) at its offset inside the table's slot, every other at
slot `1 + k` (`k ≥ 1`: `bufMinOk`). -/
def ownOff (tab : Tab) (s : TieredArray) (k : Nat) : Nat :=
  match tab.tbl64 s with
  | some c => c
  | none => abiSlot * (1 + k)

/-- `ca_check_b`'s descriptor words at position `p`, for the array `tab.wAt p` there (`rdi` the
buffer, `rcx` the table): a byte position gets no memory. -/
def parDescB (tab : Tab) (fz own : List TieredArray) (p : Nat) : Program :=
  if p < tab.nb then [movRI .rax 0, movMR (mb .rcx (tab.dbase p)) .rax, movMR (mb .rcx (tab.dlen p)) .rax,
    movMR (mb .rcx (tab.dlen32 p)) .rax] else
  match fz.idxOf? (tab.wAt p) with
  | some i =>
    [movRM .rax (mb .rdi (8 * (8 + 2 * i))), i64 (.shl (.reg (rr .rax)) (.imm8 (.int64 (Int64.ofInt 3)))),
     i64 (.add (.reg (rr .rax)) (oR .rdi)), movMR (mb .rcx (tab.dbase p)) .rax,
     movRM .rax (mb .rdi (8 * (9 + 2 * i))), movMR (mb .rcx (tab.dlen p)) .rax,
     i64 (.add (.reg (rr .rax)) (oR .rax)), movMR (mb .rcx (tab.dlen32 p)) .rax]
  | none =>
    match own.idxOf? (tab.wAt p) with
    | some k =>
      [movRI .rax (ownOff tab (tab.wAt p) k).toUInt64, i64 (.add (.reg (rr .rax)) (oR .rcx)),
       movMR (mb .rcx (tab.dbase p)) .rax, movRI .rax (abiSz tab (tab.wAt p)).toUInt64,
       movMR (mb .rcx (tab.dlen p)) .rax, movRI .rax (2 * abiSz tab (tab.wAt p)).toUInt64,
       movMR (mb .rcx (tab.dlen32 p)) .rax]
    | none => [movRI .rax 0, movMR (mb .rcx (tab.dbase p)) .rax, movMR (mb .rcx (tab.dlen p)) .rax,
      movMR (mb .rcx (tab.dlen32 p)) .rax]

/-- `ca_check_seq`'s base at position `p` (`seqVals`). -/
def seqBase (tab : Tab) (out hdrf ctlf : ArrId) (p : Nat) : SVal :=
  if p < tab.nb then .imm 0 else
  let a := tab.wAt p
  if a = ↑out ∨ a = ↑ctlf then .imm 0
  else if a = ↑hdrf then .addr (abiSlot * abiSlot64 tab out)
  else .addr (abiOff tab p)

/-- `ca_check_seq`'s length at position `p` (`seqVals`). -/
def seqLen (tab : Tab) (out hdrf ctlf : ArrId) (hw : Nat) (p : Nat) : SVal :=
  if p < tab.nb then .imm 0 else
  let a := tab.wAt p
  if a = ↑out ∨ a = ↑ctlf then .imm 0
  else if a = ↑hdrf then .imm hw.toUInt64
  else .imm (abiSz tab (tab.wAt p)).toUInt64

/-- `ca_check_seq`'s length in 32-bit elements at position `p`: twice `seqLen`'s. -/
def seqLen32 (tab : Tab) (out hdrf ctlf : ArrId) (hw : Nat) (p : Nat) : SVal :=
  if p < tab.nb then .imm 0 else
  let a := tab.wAt p
  if a = ↑out ∨ a = ↑ctlf then .imm 0
  else if a = ↑hdrf then .imm (2 * hw).toUInt64
  else .imm (2 * abiSz tab (tab.wAt p)).toUInt64

/-- `ca_check_seq`'s table words, in `abiVals`' order: `ca_setup`'s layout of the region, except
that `out`, the seed `ctlf` and the byte arrays get no memory and the header `hdrf` is the first
`hw` words of `out`'s slot. Static values only (`storesCode`, as `abiStub`). -/
def seqVals (tab : Tab) (out hdrf ctlf : ArrId) (hw : Nat) : List SVal :=
  [.addr (abiSlot + abiStack), .addr abiSlot] ++
  (List.range (tab.nb + tab.nw)).map (seqBase tab out hdrf ctlf) ++
  (List.range (tab.nb + tab.nw)).map (seqLen tab out hdrf ctlf hw) ++
  (List.range (tab.nb + tab.nw)).map (seqLen32 tab out hdrf ctlf hw) ++
  romVals tab.rom

/-- `[r + d] := v₀`, `[r + d + 8] := v₁`, … for immediate words. -/
def immStores (r : Reg64) (d : Nat) : List SVal → Program
  | [] => []
  | .imm w :: vs => [movRI .rax w, movMR (mb r d) .rax] ++ immStores r (d + 8) vs
  | _ :: vs => immStores r (d + 8) vs

/-- `ca_check_b`'s test of the frozen arrays' lengths against their minimum lengths (`Tab.min64`,
which the code generator relies on): for frozen array `fz[i]` with a minimum `k`,
`cmp [rdi + 8 (9 + 2i)], k; jb ca_abi_decline` (`rdi` the buffer, word `9 + 2i` entry `i`'s length).
Below the minimum the call declines (`rdx = 1`, never an accept). -/
def bufMinChk (tab : Tab) : Nat → List TieredArray → Program
  | _, [] => []
  | i, a :: l =>
    (if tab.min64 a = 0 then [] else
      [i64 (.cmp (.mem (mb .rdi (8 * (9 + 2 * i : Nat)))) (oI (tab.min64 a))), jccL .c abiDeclineL]) ++
    bufMinChk tab (i + 1) l

/-- **`ca_check_b`'s phase prologue** (a buffer with two phases, the compared run): with `rdi`
the buffer, `rdx` the job index `j`, `rcx`/`r8` the region: if `j ≥ buf[2]` (the first phase's job
count) and `buf[5] ≠ 0` (the second phase's offset, in words; `0` in a one-phase buffer), then
`j := j - buf[2]`, `buf := buf + 8 · buf[5]` (the second phase's self-contained buffer) and the
region's second sub-region, `[rcx + workerNeed, rcx + r8)` (declines below `2 · workerNeed`); else
nothing. The buffer length (`rsi`) stays: entry 2 never reads it. -/
def cpProStub (own : List TieredArray) : Program :=
  [movRM .rax (mb .rdi 16), i64 (.cmp (.reg (rr .rdx)) (oR .rax)), jccL .c abiCheckB0L,
   movRM .rax (mb .rdi 40), i64 (.cmp (.reg (rr .rax)) (oI 0)), jccL .z abiCheckB0L,
   movRI .rax (2 * workerNeed own).toUInt64, i64 (.cmp (.reg (rr .r8)) (oR .rax)), jccL .c abiDeclineL,
   movRR .rax .rdx, i64 (.sub (.reg (rr .rax)) (oM (mb .rdi 16))), movRR .rdx .rax,
   movRM .rax (mb .rdi 40), i64 (.shl (.reg (rr .rax)) (.imm8 (.int64 (Int64.ofInt 3)))),
   i64 (.add (.reg (rr .rax)) (oR .rdi)), movRR .rdi .rax,
   movRI .rax (workerNeed own).toUInt64, i64 (.add (.reg (rr .rax)) (oR .rcx)), movRR .rcx .rax,
   movRI .r9 (workerNeed own).toUInt64, movRR .rax .r8, i64 (.sub (.reg (rr .rax)) (oR .r9)),
   movRR .r8 .rax]

/-- `ca_check_b`'s entry: the phase prologue (`cpProStub`), the length tests (`bufMinChk`), then
the stub proper (`parStub0`). -/
def bufMinStub (tab : Tab) (fz own : List TieredArray) : Program :=
  [.label abiCheckBL] ++ cpProStub own ++ ([.label abiCheckB0L] ++ bufMinChk tab 0 fz ++ [jmpL abiCheckB1L])

/-- The parallel mode's entries, for the globals `mode`, `plo`, `phi`, the buffer array `out`, the
frozen arrays `fz` and the owned arrays `own` (`ca_check_b`'s length tests apart, `parStub`). -/
def parStub0 (tab : Tab) (mode plo phi : GVar) (out hdrf ctlf : ArrId) (hw : Nat) (fz own : List TieredArray) :
    Program :=
  -- entry 1, and the driver's entry 1
  [.label abiStartAL,
   movRI .rax (abiNeed tab).toUInt64, i64 (.cmp (.reg (rr .r9)) (oR .rax)), jccL .c abiSetupL,
   movRI .rax 1, movMR (mb .r8 (tab.globOff mode)) .rax, jmpL abiSetupL,
   .label abiStartA0L,
   movRI .rax (abiNeed tab).toUInt64, i64 (.cmp (.reg (rr .r9)) (oR .rax)), jccL .c abiSetupL,
   movRI .rax 3, movMR (mb .r8 (tab.globOff mode)) .rax, jmpL abiSetupL,
  -- entry 2 over a buffer, past its length tests
   .label abiCheckB1L,
   movRI .rax (workerNeed own).toUInt64, i64 (.cmp (.reg (rr .r8)) (oR .rax)), jccL .c abiDeclineL,
   movRR .r9 .rdx, i64 (.add (.reg (rr .r9)) (oI 1)),
   movRI .rax (abiSlot + abiStack).toUInt64, i64 (.add (.reg (rr .rax)) (oR .rcx)),
   movMR (mb .rcx Tab.stackTop) .rax,
   movRI .rax abiSlot.toUInt64, i64 (.add (.reg (rr .rax)) (oR .rcx)),
   movMR (mb .rcx Tab.stackLimit) .rax] ++
  ((List.range (tab.nb + tab.nw)).flatMap fun p => parDescB tab fz own p) ++
  immStores .rcx tab.romBase.toNat (romVals tab.rom) ++
  [movMR (mb .rcx (tab.globOff plo)) .rdx, movMR (mb .rcx (tab.globOff phi)) .r9,
   movRI .rax 2, movMR (mb .rcx (tab.globOff mode)) .rax,
   movRR .rdi .rcx, movRI .rsi abiFuelM.toUInt64, jmpL enterL,
  -- entry 2 in place (the region in `r8`, the range in `rsi`, `rdx`; from `ca_check_seq_m`, the
  -- mode word in `r10`; from `ca_check_seq_g`, past the table's stores)
   .label abiCheckSL, movRI .r10 2, .label abiCheckSML] ++
  storesCode 0 (seqVals tab out hdrf ctlf hw) ++
  [.label abiCheckSGL,
   movMR (mb .r8 (tab.globOff plo)) .rsi, movMR (mb .r8 (tab.globOff phi)) .rdx,
   movMR (mb .r8 (tab.globOff mode)) .r10,
   movRR .rdi .r8, movRI .rsi abiFuelM.toUInt64, jmpL enterL,
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

/-- The parallel mode's entries (`parStub0`), then `ca_check_b`'s length tests (`bufMinStub`). -/
def parStub (tab : Tab) (mode plo phi : GVar) (out hdrf ctlf : ArrId) (hw : Nat) (fz own : List TieredArray) :
    Program :=
  parStub0 tab mode plo phi out hdrf ctlf hw fz own ++ bufMinStub tab fz own

/-- The symbols of the parallel mode for the harness. -/
def parSymbols (tab : Tab) (out : ArrId) (own : List TieredArray) : String :=
  s!".section .rodata\n.globl ca_out_off\n.globl ca_worker_size\nca_out_off: .quad {abiSlot * abiSlot64 tab out}\nca_worker_size: .quad {workerNeed own}\n"

/-- The assembler file with the parallel mode's entries (`parStub`) before the stub. -/
def asmTextAbiPar (tab : Tab) (mode plo phi : GVar) (out hdrf ctlf : ArrId) (hw : Nat)
    (fz own : List TieredArray) (code : Program) : String :=
  ".text\n.globl " ++ abiStartL ++ "\n.globl " ++ abiStartAL ++ "\n.globl " ++ abiCheckBL ++ "\n.globl " ++
    abiCheckSL ++ "\n" ++
    asmTextOf tab (parStub tab mode plo phi out hdrf ctlf hw fz own ++ abiStub tab ++ code) ++
    abiSymbols tab ++ parSymbols tab out own

end L.Compiler
