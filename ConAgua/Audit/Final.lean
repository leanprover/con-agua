import ConAgua.Final.Twin
import ConAgua.L.Syntax
import ConAgua.Compiler.Mem
import ConAgua.Checker.IndArmFns

/-!
# Audit (lane `audit`): axiom ledger of the final theorems and the chain

The end-to-end theorems (`checkerFile_accepts`, `checkerFile_accepts_regs`,
`checkerFile_model_exists`, `checkerFile_no_False`) live in
`ConAgua/Final/EndToEnd.lean`, with their own `#guard_msgs` axiom checks. Here the axiom ledger
of the other final statements and of the con-ron / con-leche theorems the chain uses is pinned
with `#guard_msgs`, and `TwinAccepts` is shown not to be trivially true.
Journal: docs/design/audit.md.
-/

namespace ConAgua.Final.Audit

open L L.Compiler L.Checker ConAgua.Final

universe w

/-- info: 'ConAgua.Final.checkerFile_drv_accepts_regs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerFile_drv_accepts_regs
/-- info: 'ConAgua.Final.drv_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms drv_outcome
/-- info: 'L.Checker.drv_twinAccepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms drv_twinAccepts
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
