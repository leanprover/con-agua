import ConAgua.Final.DrvFinal

/-!
# The end-to-end theorems, closed

The final theorems for the committed file `checker.s`, called at `ca_start` (`AbiCall`): the
sequential driver, which runs entry 1 (the stages and phase A, `check` in mode 3) and then entry 2
in place (phase B over every pending group, mode 2) on the caller's region. They come from
`checkerFile_drv_accepts_regs` (`Final/DrvFinal.lean`: the driver on the machine, `drv_outcome`,
composed with the L-level runs of both entries, `drv_twinAccepts`) and, for the corollaries, from
`twinAccepts_model`/`twinAccepts_no_False` (`Final/Twin.lean`). Nothing is left to assume beyond
the call (`Host`, `Code checkerFile k0`, `numBits = 64`, the sizes, `AbiCall`; and for the two
corollaries a set-theory model `V`), and their axioms are pinned with `#guard_msgs`.
`checkerFile_accepts_remaining` is the theorem the census reads (`scripts/census.py`,
`ConAgua/Census/Main.lean`); `checkerFile_accepts_regs` adds that the caller's callee-saved
registers are intact on return. Audit: docs/design/audit.md, `ConAgua/Audit/Final.lean`.
-/

namespace ConAgua.Final

open L L.Compiler L.Checker L.Arena ConRon.Arena

universe w

/-- **`checkerFile_accepts_remaining` with the registers.** The machine returns to `ra` with the
caller's callee-saved registers intact (`RegsRestored`: `rsp` past the return address, `rbp`,
`r14`, `r15` as at the call; on every path, the driver's decline included), and if it reports
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
  checkerFile_drv_accepts_regs k0 hcode b pb h64 hb hpb dm ra hc

/-- **The final theorem for the committed file `checker.s`** (called at the driver `ca_start`,
`AbiCall`), with no named hypothesis left beyond the call's own: if the machine reports `rdx = 0`
with `rax = ACCEPT`, the twin's pipeline accepts `[b]`. -/
theorem checkerFile_accepts_remaining [Host]
    (k0 : Nat) (hcode : Code checkerFile k0)
    (b pb : ByteArray) (h64 : System.Platform.numBits = 64) (hb : b.size < 2 ^ 63)
    (hpb : pb.size < 2 ^ 63) (dm : MachineData) (ra : Word) (hc : AbiCall b pb dm ra) :
    Ev (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧
        (st.data.regs.rdx = 0 → st.data.regs.rax = ACCEPT → TwinAccepts [b]))
      dm (label abiStartL) :=
  eventually_weaken _ _ _ _ (fun _ ⟨hpc, _, h⟩ => ⟨hpc, h⟩)
    (checkerFile_accepts_regs k0 hcode b pb h64 hb hpb dm ra hc)

/-- **An accepted file has a model** (`checker.s`, called at `ca_start`), with nothing left to
assume beyond the call.

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
  eventually_weaken _ _ _ _
    (fun _ ⟨hpc, h⟩ => ⟨hpc, fun hrdx hacc => twinAccepts_model V (h hrdx hacc)⟩)
    (checkerFile_accepts_remaining k0 hcode b pb h64 hb hpb dm ra hc)

/-- **No `False`** (`checker.s`, called at `ca_start`), with nothing left to assume beyond the
call: if `b` declares a theorem of type `False` (in `jsonWithTheoremFalse`'s shape), the machine
returns and does not report accept.

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
  eventually_weaken _ _ _ _
    (fun _ ⟨hpc, h⟩ => ⟨hpc, fun ⟨hrdx, hacc⟩ => twinAccepts_no_False V hfalse (h hrdx hacc)⟩)
    (checkerFile_accepts_remaining k0 hcode b pb h64 hb hpb dm ra hc)

/-- info: 'ConAgua.Final.checkerFile_accepts_remaining' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerFile_accepts_remaining
/-- info: 'ConAgua.Final.checkerFile_accepts_regs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerFile_accepts_regs
/-- info: 'ConAgua.Final.checkerFile_model_exists_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerFile_model_exists_closed
/-- info: 'ConAgua.Final.checkerFile_no_False_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkerFile_no_False_closed

end ConAgua.Final
