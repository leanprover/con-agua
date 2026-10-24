import ConAgua.Checker.AsmFinal
import ConAgua.Checker.LoopStage
import ConAgua.Checker.IndArm

/-!
# The end-to-end theorems, closed

`checkerFile_accepts`, `checkerFile_model_exists` and `checkerFile_no_False`
(`Checker/AsmFinal.lean`) take `PipelineRefines checkerProg` as an argument. It is proved:
lane `pipeline`'s `pipelineRefines_checker` reduces it to `LoopStage checkerProg checkerRels`, and
`loopStage_checker` (`Checker/LoopStage.lean`, with the inductive arm `indArmSpec_checker`, lanes
`indproofs4`/`indstaget`) proves that. Here the final theorems are stated with nothing left to
assume beyond the call (`Host`, `Code checkerFile k0`, `numBits = 64`, the sizes, `AbiCall`; and
for the two corollaries a set-theory model `V`), and their axioms are pinned with `#guard_msgs`.
`checkerFile_accepts_remaining` is the theorem the census reads (`scripts/census.py`,
`ConAgua/Census/Main.lean`); `checkerFile_accepts_regs` adds that the caller's callee-saved
registers are intact on return. Audit: docs/design/audit.md, `ConAgua/Audit/Final.lean`.
-/

namespace ConAgua.Final

open L L.Compiler L.Checker L.Arena ConRon.Arena

universe w

/-- **The final theorem for the committed file `asm/checker.s`** (called through the entry stub
`ca_start`, `AbiCall`), with no named hypothesis left beyond the call's own: if the machine reports
`rdx = 0` with `rax = ACCEPT`, the twin's pipeline accepts `[b]`. -/
theorem checkerFile_accepts_remaining [Host]
    (k0 : Nat) (hcode : Code checkerFile k0)
    (b pb : ByteArray) (h64 : System.Platform.numBits = 64) (hb : b.size < 2 ^ 63)
    (hpb : pb.size < 2 ^ 63) (dm : MachineData) (ra : Word) (hc : AbiCall b pb dm ra) :
    Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧
        (st.data.regs.rdx = 0 → st.data.regs.rax = ACCEPT → TwinAccepts [b]))
      dm (label abiStartL) :=
  checkerFile_accepts (pipelineRefines_checker loopStage_checker) k0 hcode b pb h64 hb hpb
    dm ra hc

/-- **`checkerFile_accepts_remaining` with the registers.** The machine returns to `ra` with the
caller's callee-saved registers intact (`RegsRestored`: `rsp` past the return address, `rbp`,
`r14`, `r15` as at the call; on every path, the stub's decline included), and if it reports
`rdx = 0` with `rax = ACCEPT`, the twin's pipeline accepts `[b]`. So the harness, which reads only
`rdx` and `rax` after the call, relies on nothing about the registers the theorem does not state
(`rbx`, `r12`, `r13` do not occur in the file; not a theorem). -/
theorem checkerFile_accepts_regs [Host]
    (k0 : Nat) (hcode : Code checkerFile k0)
    (b pb : ByteArray) (h64 : System.Platform.numBits = 64) (hb : b.size < 2 ^ 63)
    (hpb : pb.size < 2 ^ 63) (dm : MachineData) (ra : Word) (hc : AbiCall b pb dm ra) :
    Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ RegsRestored dm.regs st.data.regs ∧
        (st.data.regs.rdx = 0 → st.data.regs.rax = ACCEPT → TwinAccepts [b]))
      dm (label abiStartL) :=
  checker_x64_accepts_abi_regs checkerProg (pipelineRefines_checker loopStage_checker) checkerTab
    checkerTab_abiOk checkerProg_wf (by decide) k0 (code_of_checkerFile_abi hcode)
    L.Checker.checkL checkerProg_lookup_check (by decide) b pb h64 hb hpb dm ra hc

/-- **An accepted file has a model**: `checkerFile_model_exists` with nothing left to assume beyond
the call.

**Relative to set theory.** The theorem assumes `[ConLeche.SetTheory V]`: a model of ZF⁻ with an
ω-chain of Grothendieck universes (`vendor/con-leche/ConLeche/SetTheory/Core.lean`). No instance
can be built inside Lean (a model of a theory of Lean's own strength would prove Lean consistent),
so the result is relative to ZFC plus ω inaccessible cardinals (the strength con-leche cites for
Lean itself): it gives its conclusion only given such a model. -/
theorem checkerFile_model_exists_closed (V : Type w) [ConLeche.SetTheory V] [Host]
    (k0 : Nat) (hcode : Code checkerFile k0)
    (b pb : ByteArray) (h64 : System.Platform.numBits = 64) (hb : b.size < 2 ^ 63)
    (hpb : pb.size < 2 ^ 63) (dm : MachineData) (ra : Word) (hc : AbiCall b pb dm ra) :
    Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧
        (st.data.regs.rdx = 0 → st.data.regs.rax = ACCEPT →
          ∃ (pins : List ConLeche.NatOpPinSet) (preC : ConLeche.Frontend.PreludeIx)
            (rc : ConLeche.Frontend.ParseResultD) (F : Nat) (env : ConLeche.Env),
            ConLeche.Frontend.parseChunks [b] = .ok rc ∧
            ConLeche.checkDeclsPure .verified (ConLeche.fueledOps .verified F) pins
              (ConLeche.Frontend.preparePrelude preC rc.decls).toList = .ok env ∧
            Nonempty (ConLeche.Model V env)))
      dm (label abiStartL) :=
  checkerFile_model_exists V (pipelineRefines_checker loopStage_checker) k0 hcode b pb h64 hb hpb
    dm ra hc

/-- **No `False`**: `checkerFile_no_False` with nothing left to assume beyond the call.

**Relative to set theory.** The theorem assumes `[ConLeche.SetTheory V]`: a model of ZF⁻ with an
ω-chain of Grothendieck universes (`vendor/con-leche/ConLeche/SetTheory/Core.lean`). No instance
can be built inside Lean (a model of a theory of Lean's own strength would prove Lean consistent),
so the result is relative to ZFC plus ω inaccessible cardinals (the strength con-leche cites for
Lean itself): it gives its conclusion only given such a model. -/
theorem checkerFile_no_False_closed (V : Type w) [ConLeche.SetTheory V] [Host]
    (k0 : Nat) (hcode : Code checkerFile k0)
    (b pb : ByteArray) (hfalse : ConLeche.jsonWithTheoremFalse [b])
    (h64 : System.Platform.numBits = 64) (hb : b.size < 2 ^ 63) (hpb : pb.size < 2 ^ 63)
    (dm : MachineData) (ra : Word) (hc : AbiCall b pb dm ra) :
    Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧
        ¬ (st.data.regs.rdx = 0 ∧ st.data.regs.rax = ACCEPT))
      dm (label abiStartL) :=
  checkerFile_no_False V (pipelineRefines_checker loopStage_checker) k0 hcode b pb hfalse h64 hb
    hpb dm ra hc

/-- info: 'ConAgua.Final.checkerFile_accepts_remaining' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerFile_accepts_remaining
/-- info: 'ConAgua.Final.checkerFile_accepts_regs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerFile_accepts_regs
/-- info: 'ConAgua.Final.checkerFile_model_exists_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerFile_model_exists_closed
/-- info: 'ConAgua.Final.checkerFile_no_False_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerFile_no_False_closed

end ConAgua.Final
