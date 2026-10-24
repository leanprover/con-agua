import ConAgua.Final.Remaining

/-!
# Audit (lane `audit`): the final theorems, closed

`checkerFile_model_exists` and `checkerFile_no_False` (`ConAgua/Checker/AsmFinal.lean`) still take
`PipelineRefines checkerProg` as an argument; `checkerFile_accepts_remaining` discharges it for
`checkerFile_accepts` only. Here the two corollaries are closed the same way
(`pipelineRefines_checker loopStage_checker`), and the axiom ledger of every final statement and
of the con-ron / con-leche theorems the chain uses is pinned with `#guard_msgs`.
Journal: docs/design/audit.md.
-/

namespace ConAgua.Final.Audit

open L L.Compiler L.Checker ConAgua.Final

universe w

/-- An accepted file has a model: `checkerFile_model_exists` with nothing left to assume beyond
the call (`Host`, `Code checkerFile k0`, `numBits = 64`, the sizes, `AbiCall`). -/
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

/-- No `False`: `checkerFile_no_False`, closed. -/
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

/-- info: 'ConAgua.Final.Audit.checkerFile_model_exists_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerFile_model_exists_closed
/-- info: 'ConAgua.Final.Audit.checkerFile_no_False_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerFile_no_False_closed
/-- info: 'ConAgua.Final.checkerFile_accepts_remaining' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerFile_accepts_remaining
/-- info: 'ConAgua.Final.checkerFile_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerFile_accepts
/-- info: 'L.Checker.loopStage_checker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms loopStage_checker
/-- info: 'L.Checker.pipelineRefines_checker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pipelineRefines_checker
/-- info: 'L.Checker.checkerFile_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerFile_eq
/-- info: 'ConAgua.Final.twinAccepts_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms twinAccepts_pure
/-- info: 'ConRon.Bridge.Arena.pooledAccepts_bridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ConRon.Bridge.Arena.pooledAccepts_bridge
/-- info: 'ConRon.Bridge.Inductives.indSpec_of_bridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ConRon.Bridge.Inductives.indSpec_of_bridge
/-- info: 'ConLeche.Model.checkDeclsPure_sound_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ConLeche.Model.checkDeclsPure_sound_of
/-- info: 'ConLeche.Frontend.parseChunks_jsonWithTheoremFalse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ConLeche.Frontend.parseChunks_jsonWithTheoremFalse

/-- `jsonWithTheoremFalse` is satisfiable (all strings empty, all ids `0`), so
`twinAccepts_no_False` says something: given a set-theory model, `TwinAccepts` is not trivially
true. -/
theorem jsonWithTheoremFalse_inhabited : ∃ b : ByteArray, ConLeche.jsonWithTheoremFalse [b] :=
  have h : ∀ x : ByteArray, ConLeche.Frontend.concatBytes [x] = x := fun x => by
    simp [ConLeche.Frontend.concatBytes]
  ⟨_, "", "", "", "", "", "", 0, 0, 0, 0, h _⟩

theorem twinAccepts_not_trivial (V : Type w) [ConLeche.SetTheory V] :
    ∃ b : ByteArray, ¬ TwinAccepts [b] :=
  let ⟨b, hb⟩ := jsonWithTheoremFalse_inhabited
  ⟨b, twinAccepts_no_False V hb⟩

end ConAgua.Final.Audit
