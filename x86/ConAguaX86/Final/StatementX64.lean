module

public import ConAguaX86.Compiler.Rel
meta import ConAgua.Final.Statement
meta import ConAguaX86.Compiler.Rel

@[expose] public section

/-!
# The x64 final theorem's vocabulary: `HarnessCall` and `RegsRestored`

Machine-level definitions split out from `ConAgua.Final.Statement`: `HarnessCall` (how the stub
calls `ca_enter`: `compile_correct`'s premises) and `RegsRestored`.
-/

namespace ConAgua.Final

open L L.Compiler

/-- **How `ca_enter` is called** (`compile_correct`'s premises about the machine state, with no
entry arguments; the setup stub establishes them, `abi_harness`): the table address in `rdi`, the
fuel in `rsi`, room for the L stack, the stack top in the table, the return address on the machine
stack, 32 bytes of machine stack that are mapped and apart from L's regions, and the 32 bytes past
the table (the trampoline's save area), mapped and apart from the stack, the arrays and that window. -/
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
  /-- the trampoline's save area, the 32 bytes past the table: mapped, apart from the L stack, the
  arrays and the 32 bytes of machine stack -/
  hsv : ∀ x, G.tabEnd ≤ x → x < G.tabEnd + 32 → (dm.dmem.get? (A x)).isSome ∧ ¬ G.InStack x ∧
    ¬ G.InArr x ∧ (x < dm.regs.rsp.toNat - 24 ∨ dm.regs.rsp.toNat + 8 ≤ x)
  hsv64 : G.tabEnd + 32 < 2 ^ 64

/-- **The caller's registers are intact on return**, relative to the registers `r0` at the call:
`rsp` is past the return address and the other callee-saved registers of System V, `rbp`,
`r14`, `r15`, `rbx`, `r12`, `r13`, hold their values from the call. The trampoline `ca_enter`
saves and restores them (`rbp`, `r14` on the machine stack, the others past the table), so this
holds whatever registers the compiled code uses. Together with the verdict in `rdx`/`rax` this is
all the harness relies on after the call. -/
def RegsRestored (r0 r : Reg64s) : Prop :=
  r.rsp.toNat = r0.rsp.toNat + 8 ∧ r.rbp = r0.rbp ∧ r.r14 = r0.r14 ∧ r.r15 = r0.r15 ∧
    r.rbx = r0.rbx ∧ r.r12 = r0.r12 ∧ r.r13 = r0.r13

end ConAgua.Final
