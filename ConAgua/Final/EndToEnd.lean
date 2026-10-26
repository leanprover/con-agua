import ConAgua.Final.DrvFinal
import ConAgua.Final.ThreadsFinal

/-!
# The end-to-end theorems

What is proved about the committed assembly file `checker.s`, in two modes of use.

**Sequential driver** (called at `ca_start`, as `AbiCall` states: input and pin buffers, a zero
region, the machine stack; and `numBits = 64`; the instance `Host`
and `Code checkerFile k0` say that the machine runs the file). The driver runs entry 1 (the
stages and phase A) and then entry 2 (phase B over every pending group) in place on the caller's
region.

* `checkerFile_accepts`: the machine returns to the return address `ra`, and if it reports
  `rdx = 0` with `rax = ACCEPT`, the twin's pipeline accepts the input (`TwinAccepts [b]`).
  This is the theorem the census reads.
* `checkerFile_accepts_regs`: the same, and the caller's callee-saved registers are intact on
  return (`RegsRestored`).
* `checkerFile_model_exists`: on accept, the input parses and its declarations check, and the
  resulting environment has a model in any set theory `V`.
* `checkerFile_no_False`: if the input declares a theorem of type `False`
  (`jsonWithTheoremFalse`), the machine does not report accept.

**Threaded harness** (`ThreadsRun`: the harness runs entry 1, hands the buffer it left to its
threads, and each thread calls `ca_check_b` per claimed group index on its own region; the
hypotheses are listed in `Final/ThreadsFinal.lean`).

* `checkerFile_threads_accept`: if every call reports accept and the threads claim every group
  index, the twin's pooled pipeline accepts the input (`TwinAcceptsPooled [b]`).
* `checkerFile_threads_regs`: every call (entry 1 and each `ca_check_b`) returns with the
  caller's callee-saved registers intact (`RegsRestored`).
* `checkerFile_threads_model`, `checkerFile_threads_no_False`: the model and no-`False`
  corollaries.

The model and no-`False` theorems take `[ConLeche.SetTheory V]`, a model of ZF⁻ with an
omega-chain of Grothendieck universes; no instance can be built inside Lean, so they are
relative to ZFC plus omega inaccessible cardinals. Every theorem here depends only on `propext`,
`Classical.choice` and `Quot.sound`, pinned with `#guard_msgs` at the end of the file.
-/

namespace ConAgua.Final

open L L.Compiler L.Checker L.Arena ConRon.Arena

universe w

/-- **`checkerFile_accepts` with the registers.** The machine returns to `ra` with the
caller's callee-saved registers intact (`RegsRestored`: `rsp` past the return address, `rbp`,
`r14`, `r15`, `rbx`, `r12`, `r13` as at the call; on every path, the driver's decline included),
and if it reports `rdx = 0` with `rax = ACCEPT`, the twin's pipeline accepts `[b]`. So the
harness, which reads only `rdx` and `rax` after the call, relies on nothing about the registers
the theorem does not state. -/
theorem checkerFile_accepts_regs [Host]
    (k0 : Nat) (hcode : Code checkerFile k0)
    (b pb : ByteArray) (h64 : System.Platform.numBits = 64)
    (dm : MachineData) (ra : Word) (hc : AbiCall b pb dm ra) :
    Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ RegsRestored dm.regs st.data.regs ∧
        (st.data.regs.rdx = 0 → st.data.regs.rax = ACCEPT → TwinAccepts [b]))
      dm (label abiStartL) :=
  checkerFile_drv_accepts_regs k0 hcode b pb h64 dm ra hc

/-- **The final theorem for the committed file `checker.s`** (called at the driver `ca_start`,
`AbiCall`), with no named hypothesis left beyond the call's own: if the machine reports `rdx = 0`
with `rax = ACCEPT`, the twin's pipeline accepts `[b]`. -/
theorem checkerFile_accepts [Host]
    (k0 : Nat) (hcode : Code checkerFile k0)
    (b pb : ByteArray) (h64 : System.Platform.numBits = 64)
    (dm : MachineData) (ra : Word) (hc : AbiCall b pb dm ra) :
    Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧
        (st.data.regs.rdx = 0 → st.data.regs.rax = ACCEPT → TwinAccepts [b]))
      dm (label abiStartL) :=
  eventually_weaken _ _ _ _ (fun _ ⟨hpc, _, h⟩ => ⟨hpc, h⟩)
    (checkerFile_accepts_regs k0 hcode b pb h64 dm ra hc)

/-- **An accepted file has a model** (`checker.s`, called at `ca_start`), with nothing left to
assume beyond the call.

**Relative to set theory.** The theorem assumes `[ConLeche.SetTheory V]`: a model of ZF⁻ with an
ω-chain of Grothendieck universes (`vendor/con-leche/ConLeche/SetTheory/Core.lean`). No instance
can be built inside Lean (a model of a theory of Lean's own strength would prove Lean consistent),
so the result is relative to ZFC plus ω inaccessible cardinals (the strength con-leche cites for
Lean itself): it gives its conclusion only given such a model. -/
theorem checkerFile_model_exists (V : Type w) [ConLeche.SetTheory V] [Host]
    (k0 : Nat) (hcode : Code checkerFile k0)
    (b pb : ByteArray) (h64 : System.Platform.numBits = 64)
    (dm : MachineData) (ra : Word) (hc : AbiCall b pb dm ra) :
    Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧
        (st.data.regs.rdx = 0 → st.data.regs.rax = ACCEPT →
          ∃ (pins : List ConLeche.NatOpPinSet) (preC : ConLeche.Frontend.PreludeIx)
            (rc : ConLeche.Frontend.ParseResultD) (F : Nat) (env : ConLeche.Env),
            ConLeche.Frontend.parseChunks [b] = .ok rc ∧
            ConLeche.checkDeclsPure .verified (ConLeche.fueledOps .verified F) pins
              (ConLeche.Frontend.preparePrelude preC rc.decls).toList = .ok env ∧
            Nonempty (ConLeche.Model V env)))
      dm (label abiStartL) :=
  eventually_weaken _ _ _ _
    (fun _ ⟨hpc, h⟩ => ⟨hpc, fun hrdx hacc => twinAccepts_model V (h hrdx hacc)⟩)
    (checkerFile_accepts k0 hcode b pb h64 dm ra hc)

/-- **No `False`** (`checker.s`, called at `ca_start`), with nothing left to assume beyond the
call: if `b` declares a theorem of type `False` (in `jsonWithTheoremFalse`'s shape), the machine
returns and does not report accept.

**Relative to set theory.** The theorem assumes `[ConLeche.SetTheory V]`: a model of ZF⁻ with an
ω-chain of Grothendieck universes (`vendor/con-leche/ConLeche/SetTheory/Core.lean`). No instance
can be built inside Lean (a model of a theory of Lean's own strength would prove Lean consistent),
so the result is relative to ZFC plus ω inaccessible cardinals (the strength con-leche cites for
Lean itself): it gives its conclusion only given such a model. -/
theorem checkerFile_no_False (V : Type w) [ConLeche.SetTheory V] [Host]
    (k0 : Nat) (hcode : Code checkerFile k0)
    (b pb : ByteArray) (hfalse : ConLeche.jsonWithTheoremFalse [b])
    (h64 : System.Platform.numBits = 64)
    (dm : MachineData) (ra : Word) (hc : AbiCall b pb dm ra) :
    Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧
        ¬ (st.data.regs.rdx = 0 ∧ st.data.regs.rax = ACCEPT))
      dm (label abiStartL) :=
  eventually_weaken _ _ _ _
    (fun _ ⟨hpc, h⟩ => ⟨hpc, fun ⟨hrdx, hacc⟩ => twinAccepts_no_False V hfalse (h hrdx hacc)⟩)
    (checkerFile_accepts k0 hcode b pb h64 dm ra hc)

/-- **Threaded accept**: if the harness runs as `ThreadsRun` says (entry 1, then `ca_check_b` per
claimed group index on each thread's own region, every call accepting, every index claimed), the
twin's pooled pipeline accepts `[b]`. -/
theorem checkerFile_threads_accept [Host] (k0 : Nat) (hcode : Code checkerFile k0)
    (b pb : ByteArray) (h64 : System.Platform.numBits = 64)
    (dm₀ : MachineData) (ra₀ : Word) (st₀ : MachineState) (B : Array Word) (ths : List ThreadM)
    (hR : ThreadsRun b pb dm₀ ra₀ st₀ B ths) : TwinAcceptsPooled [b] :=
  threadsRun_twinAcceptsPooled k0 hcode b pb h64 dm₀ ra₀ st₀ B ths hR

/-- **The threaded harness's registers**: if the harness runs as `ThreadsRun` says, entry 1 and
every `ca_check_b` call return with the caller's callee-saved registers intact. -/
theorem checkerFile_threads_regs [Host] (k0 : Nat) (hcode : Code checkerFile k0)
    (b pb : ByteArray) (h64 : System.Platform.numBits = 64)
    (dm₀ : MachineData) (ra₀ : Word) (st₀ : MachineState) (B : Array Word) (ths : List ThreadM)
    (hR : ThreadsRun b pb dm₀ ra₀ st₀ B ths) :
    RegsRestored dm₀.regs st₀.data.regs ∧ ∀ t ∈ ths, ∀ i < t.n, RegsRestored (t.dm i).regs (t.st i).data.regs :=
  (threadsRun_twinAcceptsPooled_regs k0 hcode b pb h64 dm₀ ra₀ st₀ B ths hR).2

/-- **An accepting threaded run has a model** (relative to set theory, as
`checkerFile_model_exists`). -/
theorem checkerFile_threads_model (V : Type w) [ConLeche.SetTheory V] [Host] (k0 : Nat) (hcode : Code checkerFile k0)
    (b pb : ByteArray) (h64 : System.Platform.numBits = 64)
    (dm₀ : MachineData) (ra₀ : Word) (st₀ : MachineState) (B : Array Word) (ths : List ThreadM)
    (hR : ThreadsRun b pb dm₀ ra₀ st₀ B ths) :
    ∃ (pins : List ConLeche.NatOpPinSet) (preC : ConLeche.Frontend.PreludeIx)
      (rc : ConLeche.Frontend.ParseResultD) (F : Nat) (env : ConLeche.Env),
      ConLeche.Frontend.parseChunks [b] = .ok rc ∧
      ConLeche.checkDeclsPure .verified (ConLeche.fueledOps .verified F) pins
        (ConLeche.Frontend.preparePrelude preC rc.decls).toList = .ok env ∧
      Nonempty (ConLeche.Model V env) :=
  twinAcceptsPooled_model V (checkerFile_threads_accept k0 hcode b pb h64 dm₀ ra₀ st₀ B ths hR)

/-- **No threaded run accepts a theorem of type `False`** (relative to set theory). -/
theorem checkerFile_threads_no_False (V : Type w) [ConLeche.SetTheory V] [Host] (k0 : Nat)
    (hcode : Code checkerFile k0) (b pb : ByteArray) (hfalse : ConLeche.jsonWithTheoremFalse [b])
    (h64 : System.Platform.numBits = 64)
    (dm₀ : MachineData) (ra₀ : Word) (st₀ : MachineState) (B : Array Word) (ths : List ThreadM) :
    ¬ ThreadsRun b pb dm₀ ra₀ st₀ B ths := fun hR =>
  twinAcceptsPooled_no_False V hfalse (checkerFile_threads_accept k0 hcode b pb h64 dm₀ ra₀ st₀ B ths hR)

/-- info: 'ConAgua.Final.checkerFile_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerFile_accepts
/-- info: 'ConAgua.Final.checkerFile_accepts_regs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerFile_accepts_regs
/-- info: 'ConAgua.Final.checkerFile_model_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerFile_model_exists
/-- info: 'ConAgua.Final.checkerFile_no_False' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerFile_no_False
/-- info: 'ConAgua.Final.checkerFile_threads_accept' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerFile_threads_accept
/-- info: 'ConAgua.Final.checkerFile_threads_regs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerFile_threads_regs
/-- info: 'ConAgua.Final.checkerFile_threads_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerFile_threads_model
/-- info: 'ConAgua.Final.checkerFile_threads_no_False' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerFile_threads_no_False

end ConAgua.Final
