import ConAgua.Compiler.Main
import ConAgua.Final.Twin

/-!
# The final theorem: the x64 checker's accept means consistency

`checker_x64_accepts`: run the compiled checker from `ca_enter` on a machine whose input region
holds the bytes `b` (and whose pin-data region holds any bytes `pb`); if it returns `rdx = 0` and
`rax = ACCEPT`, the twin (con-ron's arena checker) accepts `[b]` (`TwinAccepts`). The corollaries
`x64_model_exists` and `x64_no_False` put that in con-leche's terms: con-leche's own parser reads
`b`, con-leche's pure fold accepts the parsed records (prepared with some prelude, at some pin
list), the accepted environment has a model in every set theory; and a file declaring a theorem of
type `False` is never accepted.

These start at the trampoline `ca_enter(T, fuel)`, with the layout (`G`, `MemRel`, `HarnessCall`)
as premises. The final theorems start one step earlier, at the entry stub `ca_start(in, in_len,
pins, pins_len, base, base_len)` (lane `abi`): the stub sets the layout up itself in a zero region
the caller passes (`checker_x64_accepts_abi`, `ConAgua/Final/Abi.lean`, built on
`checker_x64_accepts`), and `ConAgua/Checker/AsmFinal.lean` states them for the committed file
(`checkerFile_accepts`, `checkerFile_model_exists`, `checkerFile_no_False`).

The chain is `compile_correct` (x64 ⊑ L), then `PipelineRefines` (L ⊑ twin: the per-function
refinements, composed), then Theorem 1 and con-leche (`ConAgua/Final/Twin.lean`). Here
`PipelineRefines` is a hypothesis of the theorems, not an axiom and not a `sorry`; it is a property
of the program `p`, and the theorems hold for every `p` that has it. For the checker it is proved
(`pipelineRefines_checker loopStage_checker`), and `ConAgua/Final/Remaining.lean` states the final
theorems with it discharged (`checkerFile_accepts_remaining`, `checkerFile_accepts_regs`,
`checkerFile_model_exists_closed`, `checkerFile_no_False_closed`). The `_regs` variants
(`checker_x64_accepts_regs`) also keep `compile_correct`'s register conjunct: on return the
caller's `rsp`, `rbp`, `r14`, `r15` are intact (`RegsRestored`).

## What is trusted (see `docs/ROADMAP.md` §3, "Trusted base")

* Kraken's x64 semantics (`Ev`, `MachineData`), the assembler and the loader: the assembly of
  `compileProg G.tab p "check"` sits at `k0` (`hcode`). For the checker itself the code hypothesis
  is over the committed file: `ConAgua/Checker/AsmFinal.lean` restates these theorems with
  `hcode : Code checkerFile k0`, where `checkerFile` is the code of `asm/checker.s` as the trusted
  parser reads it (`include_asm`, `ConAgua/AsmFile/Parse.lean`, `Include.lean`, `Term.lean`) and
  the kernel checked `checkerFile_eq : checkerFile = checkerStub ++ compileProg checkerTab
  checkerProg "check"` and `checkerStub_eq : checkerStub = abiStub checkerTab`; so neither the
  Lean compiler and runtime that computed the code nor the printer that wrote the file is
  trusted. What reads the file is: `include_asm` runs the **compiled** Lean code of
  `parseAsmFile`, of `programTerm`/`labelExpr` (which evaluate `lbl`/`fnL` natively) and of
  Kraken's derived `ToExpr Directive` instance, and the kernel checks the term they produce.
  Mitigations: the parser's print-back check, and Kraken's own parser reads the file the same way
  (`ConAgua/AsmFile/CrossCheck.lean`, in `scripts/asm_file.py`); the assembler encodes what the
  file says (`harness/check-asm.sh`), except branch and call targets, which `check_asm.py` does
  not compare: label and branch-target resolution by the assembler and linker is trusted
  (DESIGN.md, "Kernel-checked compiler output"; docs/design/asmfile.md);
* the harness (`harness/main.c`, ~100 lines; **only** `main.c`: `harness/e2e.c`, which calls
  `ca_enter` with its own layout, is not covered by any theorem): it reads the input and the
  pin-data files whole into two buffers (read until EOF; a regular file that changes while it is
  read is an error), maps one zero region (`MAP_NORESERVE`) of `ca_region_size` bytes, calls `ca_start` once as
  `AbiCall` states (`ConAgua/Final/Abi.lean`: the buffers hold `b` and `pb`; the region is zero,
  mapped, in the address space, apart from both buffers and from the machine stack; the buffers are
  apart from each other; the return address is on the machine stack), and reads the verdict as
  `rdx = 0 ∧ rax = ACCEPT`, nothing else (that its callee-saved registers survive the call is
  proved: `checkerFile_accepts_regs`; `rbx`/`r12`/`r13` do not occur in the file). The layout (the table, the L stack, the arrays, the
  constant data) is not trusted: the stub builds it and the proof checks it (`abi_memRel`,
  `abiLayout_ok`). For the theorems here, from `ca_enter`, the layout is a premise (`hG`, `hmem`,
  `HarnessCall`);
* buffer to stream: the file's bytes are `b`, read whole (the analogue of con-ron's `hreads`);
* `System.Platform.numBits = 64`;
* for the model and no-`False` corollaries, a model `[ConLeche.SetTheory V]` (ZF⁻ with an ω-chain
  of Grothendieck universes, `vendor/con-leche/ConLeche/SetTheory/Core.lean`): it cannot be built
  inside Lean, so these are relative to ZFC plus ω inaccessible cardinals.

Not trusted: the capacities (here any `s8`, `s64`; from the stub, `2^32` words per word array:
`PipelineRefines` holds at all of them, `check` aborts on sizes it cannot work with), the fuel
(here any `N < 2^62`; from the stub, `2^62 - 1`), **the
pin-data bytes `pb`** the harness loads into byte array `1` (con-leche's `Nat`-operation pin
variants, serialised by `lake exe romgen`, DESIGN.md "The pin data as an input"): `PipelineRefines`
holds at every `pb`; `check` decodes them at run time, interns the pin list they decode to, and
aborts (declines) on bytes that do not decode; `TwinAccepts` holds at that pin list and
con-leche's theorems at every one. Nor the ROM contents of `p` (the prelude bytes: the prelude's
records are checked as part of the stream).
-/

namespace ConAgua.Final

open L L.Compiler

universe w

/-- The verdict word `check` returns first for accept. Not `0`, `1` or `2`, so that a status word
or an unset register is never read as accept. -/
def ACCEPT : Word := 0x4143_4345_5054

/-- The memory the loader sets up: the input bytes in byte array `0`, the pin data in byte array
`1`, the other byte arrays of sizes `s8` and the word arrays of sizes `s64`, all zero. -/
def loadMem (b pb : ByteArray) (s8 s64 : List Nat) : Mem :=
  { bytes := (b.data :: pb.data :: s8.map (Array.replicate · 0)).toArray
    words := (s64.map (Array.replicate · 0)).toArray }

/-- **The named hypothesis: L refines the twin's pipeline.** Every run of `check` (no arguments)
from the loaded memory that returns `ACCEPT` first comes from an accepting twin pipeline on the
same bytes. For every input size below `2^63`, **every pin-data buffer `pb`** (below `2^63`
bytes), every capacity choice (word arrays below `2^64` words, so that `len64` reads a size
exactly; on the machine they fit in the address space, `Layout.Ok.end64`) and every L fuel below
`2^62`.

Its proof for `checkerProg` (`pipelineRefines_checker`) is the per-function refinements, composed: from `ArenaR (loadMem b pb s8 s64)
(AState.init EStore.empty)` (`arenaR_init`, grown to every field, and the input buffer), each stage
of `check` refines its twin stage (`internReservedPins`, `builtinPreludeE`, `parseChunks [b]`,
`preparePrelude`, `internAllPins`, `installFold`, `checkPendingList` from `AState.worker`) in the
`natAddLit_refinesA` shape (`internAllPins` at the pin list `pb` decodes to), at every twin fuel `F ≥ n` for the knot fuels, with L counters for the
twin's counted fuels (`docs/ROADMAP.md` §3 (b)). Partial: nothing is claimed about a run that
aborts, runs out of fuel, or returns anything but `ACCEPT`. -/
def PipelineRefines (p : Prog) : Prop :=
  ∀ (b pb : ByteArray) (s8 s64 : List Nat) (N : Nat) (rs : List Word) (m' : Mem),
    System.Platform.numBits = 64 → b.size < 2 ^ 63 → pb.size < 2 ^ 63 → (∀ n ∈ s64, n < 2 ^ 64) →
    N < 2 ^ 62 →
    L.run p N "check" [] (loadMem b pb s8 s64) = .ok (rs, m') →
    rs.headD 0 = ACCEPT → TwinAccepts [b]

/-- **How the harness calls `ca_enter`** (`compile_correct`'s premises about the machine state, with
no entry arguments): the table address in `rdi`, the fuel in `rsi`, room for the L stack, the stack
top in the table, the return address on the machine stack, and 32 bytes of machine stack that are
mapped and apart from L's regions. -/
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

/-- **The caller's registers are intact on return**, relative to the registers `r0` at the call:
`rsp` is past the return address and `rbp`, `r14`, `r15` hold their values from the call. These
are the callee-saved registers (SysV) the code writes; `rbx`, `r12` and `r13` do not occur in
`asm/checker.s` (not a theorem). Together with the verdict in `rdx`/`rax` this is all the harness
relies on after the call. -/
def RegsRestored (r0 r : Reg64s) : Prop :=
  r.rsp.toNat = r0.rsp.toNat + 8 ∧ r.rbp = r0.rbp ∧ r.r14 = r0.r14 ∧ r.r15 = r0.r15

/-- **`checker_x64_accepts` with the registers**: in addition, the caller's callee-saved
registers are intact on return (`RegsRestored`, from `compile_correct`). -/
theorem checker_x64_accepts_regs [Host] (p : Prog) (hP : PipelineRefines p)
    (G : L.Compiler.Layout) (hG : G.Ok) (hwf : Prog.wf G.tab p = true) (hnres : 1 ≤ G.tab.nres)
    (k0 : Nat) (hcode : Code (compileProg G.tab p "check") k0)
    (fd : FunDecl) (hentry : p.lookup "check" = some fd) (hnp : fd.nparams = 0)
    (hnargs : G.nargs = 0)
    (b pb : ByteArray) (h64 : System.Platform.numBits = 64) (hb : b.size < 2 ^ 63)
    (hpb : pb.size < 2 ^ 63)
    (s8 s64 : List Nat) (N : Nat) (hN62 : N < 2 ^ 62) (dm : MachineData) (ra : Word)
    (hmem : MemRel G (loadMem b pb s8 s64) dm.dmem) (hc : HarnessCall G N dm ra) :
    Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ RegsRestored dm.regs st.data.regs ∧
        (st.data.regs.rdx = 0 → st.data.regs.rax = ACCEPT → TwinAccepts [b]))
      dm (label enterL) := by
  have hargs : ([] : List Word).length = fd.nparams := hnp.symm
  refine eventually_weaken _ _ _ _ ?_
    (compile_correct p "check" G hG hwf k0 hcode fd hentry [] hargs hnargs
      (loadMem b pb s8 s64) N dm ra hc.hT hc.hN hmem hc.hroom hc.htop (fun i h => absurd h (by simp))
      hc.hra hc.hcs hc.hcs24 hc.hcs8)
  intro st ⟨hpc, hsp, hbp, h14, h15, hout⟩
  refine ⟨hpc, ⟨hsp, hbp, h14, h15⟩, fun hrdx hacc => ?_⟩
  rcases hout with h1 | hout
  · rw [hrdx] at h1; exact absurd h1 (by decide)
  rcases hrun : L.run p N "check" [] (loadMem b pb s8 s64) with e | ⟨rs, m'⟩
  · rw [hrun] at hout
    rcases e with _ | _ | _ | _ <;> simp_all [OutcomeRel]
  · rw [hrun] at hout
    obtain ⟨-, hres, -⟩ := hout
    have hrax : st.data.regs.rax = rs.headD 0 := by
      have := hres.1 0 (by omega) (by simp [maxRes])
      simp only [rres] at this
      rwa [show rs.getD 0 0 = rs.headD 0 by cases rs <;> rfl] at this
    have hs64 : ∀ n ∈ s64, n < 2 ^ 64 := by
      intro n hn
      obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hn
      have hnw : a < G.tab.nw := by
        rw [← hmem.nw]; simpa [loadMem] using ha
      have hsz := hmem.size64 a hnw
      have he := hG.end64 a hnw
      have : ((loadMem b pb s8 s64).arr64 a).size = s64[a] := by
        simp [loadMem, Mem.arr64, ha]
      omega
    exact hP b pb s8 s64 N rs m' h64 hb hpb hs64 hN62 hrun (hrax ▸ hacc)

/-- **The final theorem.** A Kraken host holds the compiled checker `p` (any program with
`PipelineRefines`); the loader put the input bytes `b`, any pin-data bytes `pb` and zeroed arrays
of any sizes in the layout `G`; the harness calls `ca_enter` with fuel `N < 2^62`. Then the machine returns to the caller, and
if it reports `rdx = 0` with `rax = ACCEPT`, the twin's pipeline accepts `[b]`. -/
theorem checker_x64_accepts [Host] (p : Prog) (hP : PipelineRefines p)
    (G : L.Compiler.Layout) (hG : G.Ok) (hwf : Prog.wf G.tab p = true) (hnres : 1 ≤ G.tab.nres)
    (k0 : Nat) (hcode : Code (compileProg G.tab p "check") k0)
    (fd : FunDecl) (hentry : p.lookup "check" = some fd) (hnp : fd.nparams = 0)
    (hnargs : G.nargs = 0)
    (b pb : ByteArray) (h64 : System.Platform.numBits = 64) (hb : b.size < 2 ^ 63)
    (hpb : pb.size < 2 ^ 63)
    (s8 s64 : List Nat) (N : Nat) (hN62 : N < 2 ^ 62) (dm : MachineData) (ra : Word)
    (hmem : MemRel G (loadMem b pb s8 s64) dm.dmem) (hc : HarnessCall G N dm ra) :
    Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧
        (st.data.regs.rdx = 0 → st.data.regs.rax = ACCEPT → TwinAccepts [b]))
      dm (label enterL) :=
  eventually_weaken _ _ _ _ (fun _ ⟨hpc, _, h⟩ => ⟨hpc, h⟩)
    (checker_x64_accepts_regs p hP G hG hwf hnres k0 hcode fd hentry hnp hnargs b pb h64 hb hpb s8 s64
      N hN62 dm ra hmem hc)

/-- **Corollary: an accepted file has a model.** Under `checker_x64_accepts`'s premises, if the
machine reports accept, con-leche's parser reads `b` into records `rc`, con-leche's pure fold
accepts them (prepared with some prelude, at some pin list) with an environment `env`, and `env`
has a model in the set theory `V`.

**Relative to set theory.** The theorem assumes `[ConLeche.SetTheory V]`: a model of ZF⁻ with an
ω-chain of Grothendieck universes (`vendor/con-leche/ConLeche/SetTheory/Core.lean`). No instance
can be built inside Lean (a model of a theory of Lean's own strength would prove Lean consistent),
so the result is relative to ZFC plus ω inaccessible cardinals (the strength con-leche cites for
Lean itself): it gives its conclusion only given such a model. -/
theorem x64_model_exists (V : Type w) [ConLeche.SetTheory V] [Host] (p : Prog)
    (hP : PipelineRefines p)
    (G : L.Compiler.Layout) (hG : G.Ok) (hwf : Prog.wf G.tab p = true) (hnres : 1 ≤ G.tab.nres)
    (k0 : Nat) (hcode : Code (compileProg G.tab p "check") k0)
    (fd : FunDecl) (hentry : p.lookup "check" = some fd) (hnp : fd.nparams = 0)
    (hnargs : G.nargs = 0)
    (b pb : ByteArray) (h64 : System.Platform.numBits = 64) (hb : b.size < 2 ^ 63)
    (hpb : pb.size < 2 ^ 63)
    (s8 s64 : List Nat) (N : Nat) (hN62 : N < 2 ^ 62) (dm : MachineData) (ra : Word)
    (hmem : MemRel G (loadMem b pb s8 s64) dm.dmem) (hc : HarnessCall G N dm ra) :
    Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧
        (st.data.regs.rdx = 0 → st.data.regs.rax = ACCEPT →
          ∃ (pins : List ConLeche.NatOpPinSet) (preC : ConLeche.Frontend.PreludeIx)
            (rc : ConLeche.Frontend.ParseResultD) (F : Nat) (env : ConLeche.Env),
            ConLeche.Frontend.parseChunks [b] = .ok rc ∧
            ConLeche.checkDeclsPure .verified (ConLeche.fueledOps .verified F) pins
              (ConLeche.Frontend.preparePrelude preC rc.decls).toList = .ok env ∧
            Nonempty (ConLeche.Model V env)))
      dm (label enterL) :=
  eventually_weaken _ _ _ _
    (fun _ ⟨hpc, h⟩ => ⟨hpc, fun hrdx hacc => twinAccepts_model V (h hrdx hacc)⟩)
    (checker_x64_accepts p hP G hG hwf hnres k0 hcode fd hentry hnp hnargs b pb h64 hb hpb s8 s64
      N hN62 dm ra hmem hc)

/-- **Corollary: no `False`.** Under `checker_x64_accepts`'s premises, if `b` declares a theorem of
type `False` (in `jsonWithTheoremFalse`'s shape), the machine returns and does not report accept.

**Relative to set theory.** The theorem assumes `[ConLeche.SetTheory V]`: a model of ZF⁻ with an
ω-chain of Grothendieck universes (`vendor/con-leche/ConLeche/SetTheory/Core.lean`). No instance
can be built inside Lean (a model of a theory of Lean's own strength would prove Lean consistent),
so the result is relative to ZFC plus ω inaccessible cardinals (the strength con-leche cites for
Lean itself): it gives its conclusion only given such a model. -/
theorem x64_no_False (V : Type w) [ConLeche.SetTheory V] [Host] (p : Prog)
    (hP : PipelineRefines p)
    (G : L.Compiler.Layout) (hG : G.Ok) (hwf : Prog.wf G.tab p = true) (hnres : 1 ≤ G.tab.nres)
    (k0 : Nat) (hcode : Code (compileProg G.tab p "check") k0)
    (fd : FunDecl) (hentry : p.lookup "check" = some fd) (hnp : fd.nparams = 0)
    (hnargs : G.nargs = 0)
    (b pb : ByteArray) (hfalse : ConLeche.jsonWithTheoremFalse [b])
    (h64 : System.Platform.numBits = 64) (hb : b.size < 2 ^ 63) (hpb : pb.size < 2 ^ 63)
    (s8 s64 : List Nat) (N : Nat) (hN62 : N < 2 ^ 62) (dm : MachineData) (ra : Word)
    (hmem : MemRel G (loadMem b pb s8 s64) dm.dmem) (hc : HarnessCall G N dm ra) :
    Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧
        ¬ (st.data.regs.rdx = 0 ∧ st.data.regs.rax = ACCEPT))
      dm (label enterL) :=
  eventually_weaken _ _ _ _
    (fun _ ⟨hpc, h⟩ => ⟨hpc, fun ⟨hrdx, hacc⟩ => twinAccepts_no_False V hfalse (h hrdx hacc)⟩)
    (checker_x64_accepts p hP G hG hwf hnres k0 hcode fd hentry hnp hnargs b pb h64 hb hpb s8 s64
      N hN62 dm ra hmem hc)

/-! ## The hypothesis is satisfiable

`PipelineRefines` is not contradictory: a `check` that never accepts has it, so the theorems above are
not vacuous in `p`. (What they say about the real checker is the point of `PipelineRefines`'s
proof for `checkerProg`, `pipelineRefines_checker loopStage_checker`.) -/

/-- A `check` that always rejects. -/
def rejectProg : Prog := [("check", { nparams := 0, nlocals := 0, body := .ret [.const 0] })]

/-- It refines the twin, vacuously. -/
theorem pipelineRefines_reject : PipelineRefines rejectProg := by
  intro b pb s8 s64 N rs m' _ _ _ _ _ hrun hacc
  cases N with
  | zero =>
    simp [L.run, invoke, lookupFn, rejectProg, callFn, exec, StateT.run, throw, throwThe,
      MonadExceptOf.throw, Except.map] at hrun
    cases hrun
  | succ n =>
    simp [L.run, invoke, lookupFn, rejectProg, callFn, exec, step, evalArgs, evalE] at hrun
    obtain ⟨rfl, -⟩ := hrun
    simp [Sig.retVal, Sig.retOr] at hacc
    exact absurd hacc (by decide)

/-! The ledger: con-leche's three axioms. `PipelineRefines` is a hypothesis of the statements, not an
axiom of the environment, so it is not listed. -/

/-- info: 'ConAgua.Final.x64_model_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms x64_model_exists

/-- info: 'ConAgua.Final.x64_no_False' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms x64_no_False

end ConAgua.Final
