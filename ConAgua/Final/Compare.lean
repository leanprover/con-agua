module

public import ConAgua.Final.CmpMain
public import ConAgua.Final.CmpChain
public import ConAgua.Final.CmpChainC
public import ConAgua.Final.CompareTwin
public import ConAgua.Final.ThreadsFinal
import ConAgua.Checker.AsmFinal
import ConAgua.Checker.ProgIRef
import ConAgua.Checker.AsmXOk
import ConAgua.Checker.ProgWf
import ConAgua.Final.DrvFinal
import all ConAgua.Checker.Entry

@[expose] public section

/-!
# The compared run's end-to-end theorems (lane compare)

What is proved about the committed assembly file `checker.s` when it is called at the compared
run's driver `ca_compare` (`CmpCall`: the challenge's and the solution's bytes, the pins, a zero
region, the machine stack; and `numBits = 64`).

* `checkerFile_compare_runs_regs`: the machine returns to the return address `ra` with the
  caller's callee-saved registers intact; `rdx = 0`, `rax = ACCEPT` means the L runs of the
  compared mode accepted (`CmpAccepts`), `rdx = 2` that one failed with the code in `rax`
  (`CmpErr`).
* `checkerFile_compare_accepts_regs`, `checkerFile_compare_accepts`: and an accept means the
  twin's compared run accepts (`TwinComparesAccepts bC bS`, `Final/CompareTwin.lean`).
* `checkerFile_compare_model`: on accept, con-leche's parser reads the challenge, and its
  prepared records, each hole the axiom of its statement (`ConLeche.Cached.sideRecord`), have a
  model in every set theory `V`. Nothing is concluded about the solution.
* `checkerFile_compare_no_False`: if the challenge declares a theorem of type `False`
  (`jsonWithTheoremFalse`), the machine does not report accept, whatever the solution.

The model and no-`False` corollaries take `[ConLeche.SetTheory V]` as the flat ones do
(`Final/EndToEnd.lean`). A reject or decline of the compared run claims nothing here.
-/

namespace ConAgua.Final

open L L.Compiler L.Checker L.Arena

/-- **The compared run's driver of `checker.s` on the machine, at the L level.** From
`ca_compare`, called as `CmpCall` says, the machine returns to `ra` with the callee-saved
registers restored, and its verdict is the L runs' (`CmpAccepts`, `CmpErr`). -/
theorem checkerFile_compare_runs_regs [Host] (k0 : Nat) (hcode : Code checkerFile k0)
    (bC bS pb : ByteArray) (h64 : System.Platform.numBits = 64)
    (sa : Word) (dm : MachineData) (ra : Word) (hc : CmpCall bC bS pb sa dm ra) :
    Ev (CmpPost dm ra
        (CmpAccepts checkerTab checkerProg MODE PLO PHI OUT HDRF CTLF hdrHw frozenIdsL parOwnedL bC bS pb)
        (CmpErr checkerTab checkerProg MODE PLO PHI OUT HDRF CTLF hdrHw frozenIdsL parOwnedL bC bS pb))
      dm (label abiCompareL) :=
  cmp_outcome_regs checkerProgI checkerProg checkerProgI_refines checkerTab checkerTab_abiOk checkerX_ok
    checkerTab_abiIO checkerProgI_wf (by decide) MODE PLO PHI OUT HDRF CTLF hdrHw frozenIdsL parOwnedL
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
    checker_seqParamsOk checker_bufMinOk parOwnedL_not_frozen (by decide +kernel)
    (fun a ha => List.all_eq_true.mp frozenIdsL_dom a ha) (by decide +kernel) k0
    (code_of_checkerFile_cmp hcode) L.Checker.checkL checkerProg_lookup_check (by decide)
    bC bS pb sa dm ra hc (checker_cmpGuard bC bS pb h64)

/-- info: 'ConAgua.Final.checkerFile_compare_runs_regs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerFile_compare_runs_regs

universe w

/-- **The compared run's final theorem, with the registers.** From `ca_compare`, called as
`CmpCall` says, the machine returns to `ra` with the caller's callee-saved registers intact, and if
it reports `rdx = 0` with `rax = ACCEPT`, the twin's compared run accepts the challenge `bC` with
the solution `bS`. -/
theorem checkerFile_compare_accepts_regs [Host] (k0 : Nat) (hcode : Code checkerFile k0)
    (bC bS pb : ByteArray) (h64 : System.Platform.numBits = 64)
    (sa : Word) (dm : MachineData) (ra : Word) (hc : CmpCall bC bS pb sa dm ra) :
    Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ RegsRestored dm.regs st.data.regs ∧
        (st.data.regs.rdx = 0 → st.data.regs.rax = ACCEPT → TwinComparesAccepts bC bS))
      dm (label abiCompareL) :=
  eventually_weaken _ _ _ _ (fun _ ⟨hpc, hr, h, _⟩ =>
      ⟨hpc, hr, fun h0 h1 => cmpAccepts_twin bC bS pb h64 (h h0 h1)⟩)
    (checkerFile_compare_runs_regs k0 hcode bC bS pb h64 sa dm ra hc)

/-- **The compared run's final theorem.** From `ca_compare`, called as `CmpCall` says, every run
returns to `ra`, and an accept (`rdx = 0`, `rax = ACCEPT`) means the twin's compared run accepts
the challenge `bC` with the solution `bS`. -/
theorem checkerFile_compare_accepts [Host] (k0 : Nat) (hcode : Code checkerFile k0)
    (bC bS pb : ByteArray) (h64 : System.Platform.numBits = 64)
    (sa : Word) (dm : MachineData) (ra : Word) (hc : CmpCall bC bS pb sa dm ra) :
    Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧
        (st.data.regs.rdx = 0 → st.data.regs.rax = ACCEPT → TwinComparesAccepts bC bS))
      dm (label abiCompareL) :=
  eventually_weaken _ _ _ _ (fun _ ⟨hpc, _, h⟩ => ⟨hpc, h⟩)
    (checkerFile_compare_accepts_regs k0 hcode bC bS pb h64 sa dm ra hc)

/-- **An accepted comparison's challenge has a model** (`checker.s`, called at `ca_compare`):
con-leche's parser reads the challenge, and its prepared records, each hole the axiom of its
statement, have a model in every set theory. Nothing is concluded about the solution.

**Relative to set theory**, as `checkerFile_model_exists` (`Final/EndToEnd.lean`). -/
theorem checkerFile_compare_model (V : Type w) [ConLeche.SetTheory V] [Host]
    (k0 : Nat) (hcode : Code checkerFile k0)
    (bC bS pb : ByteArray) (h64 : System.Platform.numBits = 64)
    (sa : Word) (dm : MachineData) (ra : Word) (hc : CmpCall bC bS pb sa dm ra) :
    Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧
        (st.data.regs.rdx = 0 → st.data.regs.rax = ACCEPT →
          ∃ (rcC : ConLeche.Frontend.ParseResultD) (preC : ConLeche.Frontend.PreludeIx),
            ConLeche.Frontend.parseChunks [bC] = .ok rcC ∧
            Nonempty (ConLeche.Model V (ConLeche.streamEnv
              ((ConLeche.Frontend.preparePrelude preC rcC.decls).toList.map
                ConLeche.Cached.sideRecord)))))
      dm (label abiCompareL) :=
  eventually_weaken _ _ _ _
    (fun _ ⟨hpc, h⟩ => ⟨hpc, fun h0 h1 => twinComparesAccepts_model V (h h0 h1)⟩)
    (checkerFile_compare_accepts k0 hcode bC bS pb h64 sa dm ra hc)

/-- **No `False` in an accepted comparison's challenge** (`checker.s`, called at `ca_compare`): if
the challenge declares a theorem of type `False` (in `jsonWithTheoremFalse`'s shape), the machine
returns and does not report accept, whatever the solution.

**Relative to set theory**, as `checkerFile_no_False` (`Final/EndToEnd.lean`). -/
theorem checkerFile_compare_no_False (V : Type w) [ConLeche.SetTheory V] [Host]
    (k0 : Nat) (hcode : Code checkerFile k0)
    (bC bS pb : ByteArray) (hfalse : ConLeche.jsonWithTheoremFalse [bC])
    (h64 : System.Platform.numBits = 64)
    (sa : Word) (dm : MachineData) (ra : Word) (hc : CmpCall bC bS pb sa dm ra) :
    Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧
        ¬ (st.data.regs.rdx = 0 ∧ st.data.regs.rax = ACCEPT))
      dm (label abiCompareL) :=
  eventually_weaken _ _ _ _
    (fun _ ⟨hpc, h⟩ => ⟨hpc, fun ⟨h0, h1⟩ => twinComparesAccepts_no_False V hfalse (h h0 h1)⟩)
    (checkerFile_compare_accepts k0 hcode bC bS pb h64 sa dm ra hc)

/-- info: 'ConAgua.Final.checkerFile_compare_accepts_regs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerFile_compare_accepts_regs

/-- info: 'ConAgua.Final.checkerFile_compare_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerFile_compare_accepts

/-- info: 'ConAgua.Final.checkerFile_compare_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerFile_compare_model

/-- info: 'ConAgua.Final.checkerFile_compare_no_False' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerFile_compare_no_False

end ConAgua.Final
