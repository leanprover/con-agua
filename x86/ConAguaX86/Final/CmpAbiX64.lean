module

public import ConAgua.Final.CmpAbi
public import ConAguaX86.Final.CmpStub
import Kraken.X64.Registers

@[expose] public section

/-!
# The compared run's driver `ca_compare` (x64 layout vocabulary)

`cmpBuf` and `CmpHiT` for the x64 machine-level theorems (`CmpMain.lean`, `CmpEntry1.lean`).
-/

namespace ConAgua.Final

open L L.Compiler L.Arena

/-- The frozen buffer mode `5` leaves: the first `OUT[1]` words of `out`. -/
def cmpBuf (out : ArrId) (m : Mem) : Array Word := (m.arr64 out).extract 0 ((m.arr64 out).getD 1 0).toNat

/-- **A return of `ca_start_ac` with `rdx = 0`, `rax ≥ 2^63`** (the jobs' count `kS + kC` in `rax`,
the memory `d`): the front, mode `7` returning `2^63 + kC`, `rax = 2^63 + kS + kC`, and the region at
`base` holds mode `7`'s final memory in the stub's layout (the solution's bytes at `sa` as the
input, the pin data at `pins`). -/
def CmpHiT (tab : Tab) (p : Prog) (mode : GVar) (bC bS pb : ByteArray) (base sa pins : Nat) (rax : Word)
    (d : DataMem) : Prop :=
  ∃ rs5 m5 rs7 m7, CmpFront45 tab p mode bC bS pb rs5 m5 ∧ cmpRun p (m5.setG mode 7) = .ok (rs7, m7) ∧
    2 ^ 63 ≤ (rs7.getD 0 0).toNat ∧
    rax = 9223372036854775808 + ((rs5.getD 0 0 - 9223372036854775808) + (rs7.getD 0 0 - 9223372036854775808)) ∧
    MemRel (abiLayout tab base sa bS.size pins pb.size) m7 d

end ConAgua.Final
