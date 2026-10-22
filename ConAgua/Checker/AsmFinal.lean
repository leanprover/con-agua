import ConAgua.Checker.Asm
import ConAgua.Final.Statement

/-!
# The final theorems, for the checker's code as a kernel-checked literal

`ConAgua/Final/Statement.lean` states the final theorems for any program `p` with
`PipelineRefines p`, about the host code `compileProg G.tab p "check"`: a term whose value, in
practice, came from running the compiler as compiled Lean code. Here they are restated for the
checker itself, `checkerProg`, with the code hypothesis over the literal `checkerAsm`
(`ConAgua/Checker/Asm.lean`): the host holds exactly the instructions of `checkerAsm`, whose
equality with `compileProg checkerTab checkerProg "check"` the kernel checked
(`checkerAsm_eq`). The harness prints `checkerAsm` (`ConAgua/Checker/AsmEmit.lean`), so neither the
Lean compiler nor its runtime is trusted to have computed the code; the printer, the assembler and
the loader still are (`harness/check-asm.sh` checks the printer and the assembler against each
other on every build of the printed file). DESIGN.md, "Kernel-checked compiler output".

The remaining hypotheses are those of `checker_x64_accepts`, with `G.tab = checkerTab` (the
loader's table is the one the code was compiled for); `Prog.wf`, the entry and the result count
are discharged here.
-/

namespace ConAgua.Final

open L L.Compiler L.Checker

universe w

theorem checkerProg_lookup_check : checkerProg.lookup "check" = some L.Checker.checkL := by
  decide +kernel

/-- `checker_x64_accepts` for the checker's code, `checkerAsm`. -/
theorem checkerAsm_accepts [Host] (hP : PipelineRefines checkerProg)
    (G : L.Compiler.Layout) (hG : G.Ok) (htab : G.tab = checkerTab)
    (k0 : Nat) (hcode : Code checkerAsm k0) (hnargs : G.nargs = 0)
    (b pb : ByteArray) (h64 : System.Platform.numBits = 64) (hb : b.size < 2 ^ 63)
    (hpb : pb.size < 2 ^ 63)
    (s8 s64 : List Nat) (N : Nat) (hN62 : N < 2 ^ 62) (dm : MachineData) (ra : Word)
    (hmem : MemRel G (loadMem b pb s8 s64) dm.dmem) (hc : HarnessCall G N dm ra) :
    Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧
        (st.data.regs.rdx = 0 → st.data.regs.rax = ACCEPT → TwinAccepts [b]))
      dm (label enterL) :=
  checker_x64_accepts checkerProg hP G hG (htab ▸ checkerProg_wf) (by rw [htab]; decide) k0
    (by rw [htab, checkerAsm_eq]; exact hcode) L.Checker.checkL checkerProg_lookup_check
    (by decide) hnargs b pb h64 hb hpb s8 s64 N hN62 dm ra hmem hc

/-- `x64_model_exists` for the checker's code, `checkerAsm`. -/
theorem checkerAsm_model_exists (V : Type w) [ConLeche.SetTheory V] [Host]
    (hP : PipelineRefines checkerProg)
    (G : L.Compiler.Layout) (hG : G.Ok) (htab : G.tab = checkerTab)
    (k0 : Nat) (hcode : Code checkerAsm k0) (hnargs : G.nargs = 0)
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
    (checkerAsm_accepts hP G hG htab k0 hcode hnargs b pb h64 hb hpb s8 s64 N hN62 dm ra hmem hc)

/-- `x64_no_False` for the checker's code, `checkerAsm`. -/
theorem checkerAsm_no_False (V : Type w) [ConLeche.SetTheory V] [Host]
    (hP : PipelineRefines checkerProg)
    (G : L.Compiler.Layout) (hG : G.Ok) (htab : G.tab = checkerTab)
    (k0 : Nat) (hcode : Code checkerAsm k0) (hnargs : G.nargs = 0)
    (b pb : ByteArray) (hfalse : ConLeche.jsonWithTheoremFalse [b])
    (h64 : System.Platform.numBits = 64) (hb : b.size < 2 ^ 63) (hpb : pb.size < 2 ^ 63)
    (s8 s64 : List Nat) (N : Nat) (hN62 : N < 2 ^ 62) (dm : MachineData) (ra : Word)
    (hmem : MemRel G (loadMem b pb s8 s64) dm.dmem) (hc : HarnessCall G N dm ra) :
    Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧
        ¬ (st.data.regs.rdx = 0 ∧ st.data.regs.rax = ACCEPT))
      dm (label enterL) :=
  eventually_weaken _ _ _ _
    (fun _ ⟨hpc, h⟩ => ⟨hpc, fun ⟨hrdx, hacc⟩ => twinAccepts_no_False V hfalse (h hrdx hacc)⟩)
    (checkerAsm_accepts hP G hG htab k0 hcode hnargs b pb h64 hb hpb s8 s64 N hN62 dm ra hmem hc)

/-- info: 'ConAgua.Final.checkerAsm_model_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerAsm_model_exists

/-- info: 'ConAgua.Final.checkerAsm_no_False' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerAsm_no_False

end ConAgua.Final
