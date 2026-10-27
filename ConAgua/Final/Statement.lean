import ConAgua.Compiler.Rel

/-!
# The final theorem's vocabulary: the verdict, the loaded memory, the calls

The final theorems (`ConAgua/Final/EndToEnd.lean`: `checkerFile_accepts`,
`checkerFile_accepts_regs`, `checkerFile_model_exists`, `checkerFile_no_False`) are
about the committed file `asm/checker.s`, called at `ca_start(in, in_len, pins, pins_len, base,
base_len)` as the harness calls it (`AbiCall`, `ConAgua/Final/Abi.lean`): if the machine returns
`rdx = 0` and `rax = ACCEPT`, the twin (con-ron's arena checker) accepts `[b]` (`TwinAccepts`,
`ConAgua/Final/Twin.lean`); in con-leche's terms, con-leche's own parser reads `b`, con-leche's
pure fold accepts the parsed records (prepared with some prelude, at some pin list), the accepted
environment has a model in every set theory, and a file declaring a theorem of type `False` is
never accepted.

`ca_start` is the sequential driver (`parStub`, `ConAgua/Compiler/Abi.lean`). It checks the
region size (`drvNeed`: the setup stub's region plus 16 bytes), keeps its return address and the
caller's `r15` in those 16 bytes past the setup stub's region (`drvSave`) and holds `base` in
`r15`. Then it calls entry 1 (`ca_start_a0`: the mode word `3`, then the setup stub `ca_setup`,
which lays out the table, the L stack and the arrays in the region and enters the trampoline
`ca_enter`; `check` runs the stages and phase A and writes the frozen buffer's header) and, if
that returns `rdx = 0` and `rax = 2^63 + k`, entry 2 in place (`ca_check_seq`: the table over
phase A's own arrays, the mode word `2`, the range `[0, k)`; `check` runs phase B over every
pending group), and returns entry 2's result; it restores `r15` and returns to the caller. Each
entry is one L run of `check` (`compile_correct`); the machine-level driver is `drv_outcome`
(`ConAgua/Final/DrvAbi.lean`), the L-level composition `drv_twinAccepts`
(`ConAgua/Checker/ParDriverTwin.lean`), and `checkerFile_drv_accepts_regs`
(`ConAgua/Final/DrvFinal.lean`) puts them together for the file.

The callee-saved registers: the trampoline `ca_enter`, through which every entry runs, saves
`rbp`, `r14` (and the table address) on the machine stack and `r15`, `rbx`, `r12`, `r13` in the 32
bytes past the table, and restores them on every exit; the driver also writes `r15` (restored
from its save area). `RegsRestored` states that `rsp`, `rbp`, `r14`, `r15`, `rbx`, `r12`, `r13`
are as at the call. Nothing about the registers the compiled code uses is assumed.

This file holds what the statements share: `ACCEPT`, the loaded memory `loadMem`, `HarnessCall`
(how the stub calls `ca_enter`: `compile_correct`'s premises) and `RegsRestored`.

## What is trusted (see `OVERVIEW.md` §2.3)

* Kraken's x64 semantics (`Ev`, `MachineData`), the assembler and the loader: the code of the
  committed file sits at `k0` (`hcode : Code checkerFile k0`), where `checkerFile` is the code of
  `checker.s` as the trusted parser reads it (`include_asm`, `ConAgua/AsmFile/Parse.lean`,
  `Include.lean`, `Term.lean`) and the kernel checked `checkerFile_eq : checkerFile = checkerStub
  ++ compileProg checkerTab checkerProg "check"` and `checkerStub_eq` (the parallel mode's entries,
  the driver among them, and the setup stub); so neither the Lean compiler and runtime that
  computed the code nor the printer that wrote the file is trusted. What reads the file is:
  `include_asm` runs the **compiled** Lean code of `parseAsmFile`, of `programTerm`/`labelExpr`
  (which evaluate `lbl`/`fnL` natively) and of Kraken's derived `ToExpr Directive` instance, and
  the kernel checks the term they produce. Mitigations: the parser's print-back check, and
  Kraken's own parser reads the file the same way (`ConAgua/AsmFile/CrossCheck.lean`, in
  `scripts/asm_file.py`); the assembler encodes what the file says (`scripts/check-asm.sh`),
  except branch and call targets, which `check_asm.py` does not compare: label and branch-target
  resolution by the assembler and linker is trusted (DESIGN.md, "Kernel-checked compiler output";
  docs/design/asmfile.md);
* the harness (`main.c`): it reads the input file whole into a buffer (read until EOF: `b` is
  whatever the buffer holds), passes the pin data `pins.bin` built into the binary (C23 `#embed`)
  as the second buffer, maps one zero region (`MAP_NORESERVE`) of `ca_region_size` bytes (`drvNeed`), calls
  `ca_start` once as `AbiCall` states (`ConAgua/Final/Abi.lean`: the buffers hold `b` and `pb`;
  the region is zero, mapped, in the address space, apart from both buffers and from the machine
  stack; the buffers are apart from each other; the return address is on the machine stack), and
  reads the verdict as `rdx = 0 ∧ rax = ACCEPT`, nothing else (that its callee-saved registers
  survive the call is proved: `checkerFile_accepts_regs`). The layout (the table, the L stack,
  the arrays, the constant data) is not trusted: the setup stub builds it and the proof checks it
  (`abi_memRel`, `abiLayout_ok`). The threaded mode (`--jobs=N`, N > 1) is not covered;
* buffer to stream: the file's bytes are `b`, read whole (the analogue of con-ron's `hreads`);
* `System.Platform.numBits = 64`;
* for the model and no-`False` corollaries, a model `[ConLeche.SetTheory V]` (ZF⁻ with an ω-chain
  of Grothendieck universes, `vendor/con-leche/ConLeche/SetTheory/Core.lean`): it cannot be built
  inside Lean, so these are relative to ZFC plus ω inaccessible cardinals.

Not trusted: the capacities (the setup stub gives every word array `2^32` words; the refinements
hold at every capacity, and `check` aborts on sizes it cannot work with), the fuel (`2^62 - 1`
per entry; the refinements hold at every fuel below `2^62`), **the pin-data bytes `pb`** the
harness passes as byte array `1` (`pins.bin`, built into the binary: the startup data and
con-leche's `Nat`-operation pin variants, serialised by `romgen pins.bin 3`, DESIGN.md "The pin
data as an input"): the theorems hold at every `pb`; `check`
decodes them at run time, interns the pin list they decode to, and aborts (declines) on bytes
that do not decode; `TwinAccepts` holds at that pin list and con-leche's theorems at every one.
Nor the ROM contents of the program (the prelude bytes: the prelude's records are checked as part
of the stream).
-/

namespace ConAgua.Final

open L L.Compiler

/-- The verdict word `check` returns first for accept. Not `0`, `1` or `2`, so that a status word
or an unset register is never read as accept. -/
def ACCEPT : Word := 0x4143_4345_5054

/-- The memory the loader sets up: the input bytes in byte array `0`, the pin data in byte array
`1`, the other byte arrays of sizes `s8` and the word arrays of sizes `s64`, all zero. -/
def loadMem (b pb : ByteArray) (s8 s64 : List Nat) : Mem :=
  { bytes := (b.data :: pb.data :: s8.map (Array.replicate · 0)).toArray
    words := (s64.map (Array.replicate · 0)).toArray }

/-- **How `ca_enter` is called** (`compile_correct`'s premises about the machine state, with no
entry arguments; the setup stub establishes them, `abi_harness`): the table address in `rdi`, the
fuel in `rsi`, room for the L stack, the stack top in the table, the return address on the machine
stack, 32 bytes of machine stack that are mapped and apart from L's regions, and the 32 bytes past
the table (the trampoline's save area), mapped and apart from the stack, the arrays and that window. -/
structure HarnessCall (G : L.Compiler.Layout) (N : Nat) (dm : MachineData) (ra : Word) : Prop where
  hT : dm.regs.rdi.toNat = G.T
  hN : dm.regs.rsi.toNat = N
  hroom : G.lo + 8 ≤ G.hi
  htop : L.Compiler.rdW dm.dmem (A G.T) = some (UInt64.ofNat G.hi)
  hra : L.Compiler.rdW dm.dmem (A dm.regs.rsp.toNat) = some ra
  hcs : ∀ x, dm.regs.rsp.toNat - 24 ≤ x → x < dm.regs.rsp.toNat + 8 →
    (dm.dmem.get? (A x)).isSome ∧ ¬ G.InStack x ∧ ¬ G.InArr x ∧ ¬ G.InTab x
  hcs24 : 24 ≤ dm.regs.rsp.toNat
  hcs8 : dm.regs.rsp.toNat + 8 < 2 ^ 64
  /-- the trampoline's save area, the 32 bytes past the table: mapped, apart from the L stack, the
  arrays and the 32 bytes of machine stack -/
  hsv : ∀ x, G.tabEnd ≤ x → x < G.tabEnd + 32 → (dm.dmem.get? (A x)).isSome ∧ ¬ G.InStack x ∧
    ¬ G.InArr x ∧ (x < dm.regs.rsp.toNat - 24 ∨ dm.regs.rsp.toNat + 8 ≤ x)
  hsv64 : G.tabEnd + 32 < 2 ^ 64

/-- **The caller's registers are intact on return**, relative to the registers `r0` at the call:
`rsp` is past the return address and the other callee-saved registers of System V, `rbp`,
`r14`, `r15`, `rbx`, `r12`, `r13`, hold their values from the call. The trampoline `ca_enter`
saves and restores them (`rbp`, `r14` on the machine stack, the others past the table), so this
holds whatever registers the compiled code uses. Together with the verdict in `rdx`/`rax` this is
all the harness relies on after the call. -/
def RegsRestored (r0 r : Reg64s) : Prop :=
  r.rsp.toNat = r0.rsp.toNat + 8 ∧ r.rbp = r0.rbp ∧ r.r14 = r0.r14 ∧ r.r15 = r0.r15 ∧
    r.rbx = r0.rbx ∧ r.r12 = r0.r12 ∧ r.r13 = r0.r13

end ConAgua.Final
