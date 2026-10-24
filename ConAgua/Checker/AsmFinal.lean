import ConAgua.Checker.AsmFileEq
import ConAgua.Checker.ProgWf
import ConAgua.Final.Statement
import ConAgua.Final.Abi
import ConAgua.Checker.AsmStubEq

/-!
# The final theorems, for the committed assembler file `asm/checker.s`

`ConAgua/Final/Statement.lean` states the final theorems for any program `p` with
`PipelineRefines p`, about the host code `compileProg G.tab p "check"`. Here they are restated for
the checker itself, `checkerProg`, with the code hypothesis over `checkerFile`: the code of the
committed file `asm/checker.s` (the entry stub, the trampoline and the functions: exactly what
`harness/main.c` is assembled with), as the trusted parser reads it when
`ConAguaAsm/Checker.lean` is elaborated (`include_asm`). The kernel checked
`checkerFile_eq : checkerFile = checkerStub ++ compileProg checkerTab checkerProg "check"`
(`ConAgua/Checker/AsmFileEq.lean`), so neither the Lean compiler that computed the code nor the
printer that wrote the file is trusted; the parser, the assembler and the loader are
(`harness/check-asm.sh` checks the assembler against the file). DESIGN.md, "Kernel-checked
compiler output"; docs/design/asmfile.md.

`checkerAsm_accepts` is the same for the compiler's output (`Code checkerAsm k0`, the trampoline
and the functions); `checkerFile_accepts_enter` gets that code from the file's, after the stub,
and starts at the trampoline's entry (`HarnessCall`). The final theorems `checkerFile_accepts`,
`checkerFile_model_exists` and `checkerFile_no_False` start at the stub's entry `ca_start`
(`AbiCall`, lane `abi`): the file's stub is `abiStub checkerTab` (`checkerStub_eq`), which lays
out the table, the L stack and the arrays in the caller's zero region and enters the trampoline
(`checker_x64_accepts_abi`, `ConAgua/Final/Abi.lean`).

For `checkerFile_accepts_enter` the remaining hypotheses are those of `checker_x64_accepts`, with
`G.tab = checkerTab` (the loader's table is the one the code was compiled for); `Prog.wf`, the
entry and the result count are discharged here, and for the final theorems also the table's fit
for the stub (`checkerTab_abiOk`).
-/

namespace ConAgua.Final

open L L.Compiler L.Checker

universe w

set_option maxRecDepth 100000 in
theorem checkerProg_lookup_check : checkerProg.lookup "check" = some L.Checker.checkL := rfl

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

/-- The code of the file, after its stub, is the compiler's output. -/
theorem code_of_checkerFile [Host] {k0 : Nat} (hcode : Code checkerFile k0) :
    Code checkerAsm (k0 + checkerStub.length) := by
  rw [checkerFile_eq.lit] at hcode
  exact hcode.right

/-- `checker_x64_accepts` for the committed file `asm/checker.s`, from the trampoline's entry
(`HarnessCall`; the lemma `checkerFile_accepts` is built on, through the stub). -/
theorem checkerFile_accepts_enter [Host] (hP : PipelineRefines checkerProg)
    (G : L.Compiler.Layout) (hG : G.Ok) (htab : G.tab = checkerTab)
    (k0 : Nat) (hcode : Code checkerFile k0) (hnargs : G.nargs = 0)
    (b pb : ByteArray) (h64 : System.Platform.numBits = 64) (hb : b.size < 2 ^ 63)
    (hpb : pb.size < 2 ^ 63)
    (s8 s64 : List Nat) (N : Nat) (hN62 : N < 2 ^ 62) (dm : MachineData) (ra : Word)
    (hmem : MemRel G (loadMem b pb s8 s64) dm.dmem) (hc : HarnessCall G N dm ra) :
    Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧
        (st.data.regs.rdx = 0 → st.data.regs.rax = ACCEPT → TwinAccepts [b]))
      dm (label enterL) :=
  checkerAsm_accepts hP G hG htab _ (code_of_checkerFile hcode) hnargs b pb h64 hb hpb s8 s64 N
    hN62 dm ra hmem hc

/-! ## From the entry stub: the final theorems

The harness calls the stub `ca_start` (`AbiCall`: the two buffers and a zero region); the file's
stub is `abiStub checkerTab` (`checkerStub_eq`), which sets up the layout and enters the
trampoline (`checker_x64_accepts_abi`, `ConAgua/Final/Abi.lean`). -/

theorem checkerTab_abiOk : abiTabOk checkerTab = true := by decide

/-- The file's code: the stub, then the compiler's output. -/
theorem code_of_checkerFile_abi [Host] {k0 : Nat} (hcode : Code checkerFile k0) :
    Code (abiStub checkerTab ++ compileProg checkerTab checkerProg "check") k0 := by
  rw [checkerFile_eq, checkerStub_eq] at hcode
  exact hcode

/-- **The final theorem for the committed file `asm/checker.s`**: the harness calls `ca_start` as
`AbiCall` says; if the machine reports `rdx = 0` with `rax = ACCEPT`, the twin's pipeline accepts
`[b]`. -/
theorem checkerFile_accepts [Host] (hP : PipelineRefines checkerProg)
    (k0 : Nat) (hcode : Code checkerFile k0)
    (b pb : ByteArray) (h64 : System.Platform.numBits = 64) (hb : b.size < 2 ^ 63)
    (hpb : pb.size < 2 ^ 63) (dm : MachineData) (ra : Word) (hc : AbiCall b pb dm ra) :
    Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧
        (st.data.regs.rdx = 0 → st.data.regs.rax = ACCEPT → TwinAccepts [b]))
      dm (label abiStartL) :=
  checker_x64_accepts_abi checkerProg hP checkerTab checkerTab_abiOk checkerProg_wf (by decide) k0
    (code_of_checkerFile_abi hcode) L.Checker.checkL checkerProg_lookup_check (by decide)
    b pb h64 hb hpb dm ra hc

/-- **An accepted file has a model** (`asm/checker.s`, called through the stub).

**Relative to set theory.** The theorem assumes `[ConLeche.SetTheory V]`: a model of ZF⁻ with an
ω-chain of Grothendieck universes (`vendor/con-leche/ConLeche/SetTheory/Core.lean`). No instance
can be built inside Lean (a model of a theory of Lean's own strength would prove Lean consistent),
so the result is relative to ZFC plus ω inaccessible cardinals (the strength con-leche cites for
Lean itself): it gives its conclusion only given such a model. -/
theorem checkerFile_model_exists (V : Type w) [ConLeche.SetTheory V] [Host]
    (hP : PipelineRefines checkerProg) (k0 : Nat) (hcode : Code checkerFile k0)
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
  eventually_weaken _ _ _ _
    (fun _ ⟨hpc, h⟩ => ⟨hpc, fun hrdx hacc => twinAccepts_model V (h hrdx hacc)⟩)
    (checkerFile_accepts hP k0 hcode b pb h64 hb hpb dm ra hc)

/-- **No `False`** (`asm/checker.s`, called through the stub).

**Relative to set theory.** The theorem assumes `[ConLeche.SetTheory V]`: a model of ZF⁻ with an
ω-chain of Grothendieck universes (`vendor/con-leche/ConLeche/SetTheory/Core.lean`). No instance
can be built inside Lean (a model of a theory of Lean's own strength would prove Lean consistent),
so the result is relative to ZFC plus ω inaccessible cardinals (the strength con-leche cites for
Lean itself): it gives its conclusion only given such a model. -/
theorem checkerFile_no_False (V : Type w) [ConLeche.SetTheory V] [Host]
    (hP : PipelineRefines checkerProg) (k0 : Nat) (hcode : Code checkerFile k0)
    (b pb : ByteArray) (hfalse : ConLeche.jsonWithTheoremFalse [b])
    (h64 : System.Platform.numBits = 64) (hb : b.size < 2 ^ 63) (hpb : pb.size < 2 ^ 63)
    (dm : MachineData) (ra : Word) (hc : AbiCall b pb dm ra) :
    Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧
        ¬ (st.data.regs.rdx = 0 ∧ st.data.regs.rax = ACCEPT))
      dm (label abiStartL) :=
  eventually_weaken _ _ _ _
    (fun _ ⟨hpc, h⟩ => ⟨hpc, fun ⟨hrdx, hacc⟩ => twinAccepts_no_False V hfalse (h hrdx hacc)⟩)
    (checkerFile_accepts hP k0 hcode b pb h64 hb hpb dm ra hc)

/-- info: 'ConAgua.Final.checkerFile_model_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerFile_model_exists

/-- info: 'ConAgua.Final.checkerFile_no_False' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerFile_no_False

end ConAgua.Final
