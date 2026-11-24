module

public import ConAgua.Final.CmpEntry1
public import ConAgua.Final.CmpSeqTwin
public import ConAgua.Final.CompareTwinSeq
import ConAgua.Checker.CmpSeqProg
import ConAgua.Checker.CmpCall

@[expose] public section

/-!
# The sequential compared run's final theorems (lane compare2)

`--compare` without `--jobs` (or with `N = 1`): the harness calls `ca_start_c` of `checker.s`
with the challenge's bytes as the input and the solution's on the stack (`AbiCall bC (some bS)`,
label `abiSeqL (some bS)`). Entry 1 freezes the store in place; the stub then runs, on a worker
region, the solution's jobs (mode `8`) and the challenge's (mode `9`) in place.

* `checkerFile_compare_accepts_regs`, `checkerFile_compare_accepts`: every run returns to the
  caller (with the callee-saved registers); an accept is `TwinComparesAccepts bC bS`, a reject
  or decline of class `1` or `2` is `TwinCompareVerdict bC bS` with that class.
* `checkerFile_compare_model`, `checkerFile_compare_no_False`: the challenge of an accepted
  comparison has a model, and one declaring a theorem of type `False` is not accepted.
-/

namespace ConAgua.Final

open L L.Compiler L.Checker L.Arena

universe w

/-- **The sequential compared run's final theorem, with the registers.** From `ca_start_c`
(`abiSeqL (some bS)`), called as `AbiCall bC (some bS)` says, the machine returns to `ra` with the
caller's callee-saved registers intact; if it reports `rdx = 0` with `rax = ACCEPT`, the twin's
sequential compared run accepts the challenge `bC` with the solution `bS`; if it reports
`rdx = 2` with a class `1` or `2`, the twin's run fails with that class. -/
theorem checkerFile_compare_accepts_regs [Host] (k0 : Nat) (hcode : Code checkerFile k0)
    (bC bS pb : ByteArray) (h64 : System.Platform.numBits = 64)
    (dm : MachineData) (ra : Word) (hc : AbiCall bC (some bS) pb dm ra) :
    Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ RegsRestored dm.regs st.data.regs ∧
        (st.data.regs.rdx = 0 → st.data.regs.rax = ACCEPT → TwinComparesAccepts bC bS) ∧
        (st.data.regs.rdx = 2 → st.data.regs.rax &&& 3 ≠ 0 →
          TwinCompareVerdict bC bS (st.data.regs.rax &&& 3)))
      dm (label (abiSeqL (some bS))) :=
  eventually_weaken _ _ _ _ (fun _ ⟨⟨hpc, hr, h, h2⟩, _⟩ =>
      ⟨hpc, hr, fun h0 h1 => cmpAccS_twin bC bS pb h64 checkerProg_cqSeq (h h0 h1),
        fun hd hk => cmpErrS_twin bC bS pb h64 checkerProg_cqSeq (h2 hd) hk⟩)
    (cmpSeq_regs k0 hcode bC bS pb (solAddr dm) dm ra hc.cmp)

/-- **The sequential compared run's final theorem.** From `ca_start_c`, called as
`AbiCall bC (some bS)` says, every run returns to `ra`; an accept (`rdx = 0`, `rax = ACCEPT`)
means the twin's sequential compared run accepts the challenge `bC` with the solution `bS`, a
reject or decline of class `1` or `2` that it fails with that class. -/
theorem checkerFile_compare_accepts [Host] (k0 : Nat) (hcode : Code checkerFile k0)
    (bC bS pb : ByteArray) (h64 : System.Platform.numBits = 64)
    (dm : MachineData) (ra : Word) (hc : AbiCall bC (some bS) pb dm ra) :
    Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧
        (st.data.regs.rdx = 0 → st.data.regs.rax = ACCEPT → TwinComparesAccepts bC bS) ∧
        (st.data.regs.rdx = 2 → st.data.regs.rax &&& 3 ≠ 0 →
          TwinCompareVerdict bC bS (st.data.regs.rax &&& 3)))
      dm (label (abiSeqL (some bS))) :=
  eventually_weaken _ _ _ _ (fun _ ⟨hpc, _, h⟩ => ⟨hpc, h⟩)
    (checkerFile_compare_accepts_regs k0 hcode bC bS pb h64 dm ra hc)

/-- **An accepted comparison's challenge has a model** (`checker.s`, called at `ca_start_c`):
con-leche's parser reads the challenge, and its prepared records, each hole the axiom of its
statement, have a model in every set theory. Nothing is concluded about the solution.

**Relative to set theory**, as `checkerFile_model_exists` (`Final/EndToEnd.lean`). -/
theorem checkerFile_compare_model (V : Type w) [ConLeche.SetTheory V] [Host]
    (k0 : Nat) (hcode : Code checkerFile k0)
    (bC bS pb : ByteArray) (h64 : System.Platform.numBits = 64)
    (dm : MachineData) (ra : Word) (hc : AbiCall bC (some bS) pb dm ra) :
    Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧
        (st.data.regs.rdx = 0 → st.data.regs.rax = ACCEPT →
          ∃ (rcC : ConLeche.Frontend.ParseResultD) (preC : ConLeche.Frontend.PreludeIx),
            ConLeche.Frontend.parseChunks [bC] = .ok rcC ∧
            Nonempty (ConLeche.Model V (ConLeche.streamEnv
              ((ConLeche.Frontend.preparePrelude preC rcC.decls).toList.map
                ConLeche.Cached.sideRecord)))))
      dm (label (abiSeqL (some bS))) :=
  eventually_weaken _ _ _ _
    (fun _ ⟨hpc, h, _⟩ => ⟨hpc, fun h0 h1 => twinComparesAccepts_model V (h h0 h1)⟩)
    (checkerFile_compare_accepts k0 hcode bC bS pb h64 dm ra hc)

/-- **No `False` in an accepted comparison's challenge** (`checker.s`, called at `ca_start_c`): if
the challenge declares a theorem of type `False` (in `jsonWithTheoremFalse`'s shape), no state the
machine reaches at the return address (`FirstReturn`) reports `rdx = 0` with `rax = ACCEPT`,
whatever the solution.

**Relative to set theory**, as `checkerFile_no_False` (`Final/EndToEnd.lean`). -/
theorem checkerFile_compare_no_False (V : Type w) [ConLeche.SetTheory V] [Host]
    (k0 : Nat) (hcode : Code checkerFile k0)
    (bC bS pb : ByteArray) (hfalse : ConLeche.jsonWithTheoremFalse [bC])
    (h64 : System.Platform.numBits = 64)
    (dm : MachineData) (ra : Word) (hc : AbiCall bC (some bS) pb dm ra)
    (st : MachineState) (hret : FirstReturn dm (label (abiSeqL (some bS))) ra st)
    (hrdx : st.data.regs.rdx = 0) (hacc : st.data.regs.rax = ACCEPT) : False :=
  twinComparesAccepts_no_False V hfalse
    ((hret _ (checkerFile_compare_accepts k0 hcode bC bS pb h64 dm ra hc) (fun _ h => h.1)).2.1 hrdx hacc)

/-- info: 'ConAgua.Final.checkerFile_compare_accepts_regs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerFile_compare_accepts_regs

end ConAgua.Final
