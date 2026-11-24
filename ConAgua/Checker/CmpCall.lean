module

public import ConAgua.Final.Abi
import Kraken.X64.Registers

@[expose] public section

/-!
# A compared run's call as the machine proofs take it (lane compare)

`CmpCall`: `AbiCall bC (some bS) pb dm ra` with the solution's address as a parameter;
`AbiCall.cmp` converts. Internal to the machine proofs of `ca_start_ac`, `ca_start_c`
(`Final/CmpMain.lean`, `Final/CmpA.lean`, `Final/CmpC.lean`, `Final/CmpEntry1.lean`); the final
theorems take `AbiCall`.
-/

namespace ConAgua.Final

open L L.Compiler

/-- **A compared run's call, with the solution's address as a parameter** (internal: the machine
proofs' form of `AbiCall bC (some bS) pb dm ra`, `AbiCall.cmp`): `ca_start`'s six arguments as `AbiArgs` says (the
challenge's bytes `bC` as the input, the pin data `pb`, a zero region), and on the machine stack
past the return address the solution's buffer `sa` and its length; the buffer holds `bS`, is in
the address space, apart from the region, from both other buffers and from the stack window. -/
structure CmpCall (bC bS pb : ByteArray) (sa : Word) (dm : MachineData) (ra : Word) : Prop
    extends AbiArgs bC pb dm ra where
  hsa : rdW dm.dmem (A (dm.regs.rsp.toNat + 8)) = some sa
  hsn : rdW dm.dmem (A (dm.regs.rsp.toNat + 16)) = some (UInt64.ofNat bS.size)
  hS : ∀ i (h : i < bS.size), dm.dmem.get? (A (sa.toNat + i)) = some bS[i]
  hSEnd : sa.toNat + bS.size < 2 ^ 64
  hSDisj : ∀ x, sa.toNat ≤ x → x < sa.toNat + bS.size →
    (x < dm.regs.r8.toNat ∨ dm.regs.r8.toNat + dm.regs.r9.toNat ≤ x) ∧
    ¬ (dm.regs.rdi.toNat ≤ x ∧ x < dm.regs.rdi.toNat + bC.size) ∧
    ¬ (dm.regs.rdx.toNat ≤ x ∧ x < dm.regs.rdx.toNat + pb.size) ∧
    (x < dm.regs.rsp.toNat - 24 ∨ dm.regs.rsp.toNat + 8 ≤ x)
  hsEnd : dm.regs.rsp.toNat + 24 < 2 ^ 64
  hsArgs : ∀ x, dm.regs.rsp.toNat + 8 ≤ x → x < dm.regs.rsp.toNat + 24 →
    x < dm.regs.r8.toNat ∨ dm.regs.r8.toNat + dm.regs.r9.toNat ≤ x

/-- **A compared run's call** (`AbiCall` with a solution) as the machine proofs take it, at the
solution's address `solAddr dm`. -/
theorem AbiCall.cmp {bC bS pb : ByteArray} {dm : MachineData} {ra : Word}
    (hc : AbiCall bC (some bS) pb dm ra) : CmpCall bC bS pb (solAddr dm) dm ra := by
  have h := hc.hsol bS rfl
  exact ⟨hc.toAbiArgs, h.hsa, h.hsn, h.hS, h.hSEnd, h.hSDisj, h.hsEnd, h.hsArgs⟩

end ConAgua.Final
