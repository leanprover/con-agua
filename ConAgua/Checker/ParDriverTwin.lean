module

public import ConAgua.Checker.ParDriverL
import ConAgua.Checker.CheckARun
import ConAgua.Checker.IndArm
import ConAgua.Checker.LoopProg
import ConAgua.Checker.LoopStage
import ConAgua.Checker.TwinShapeQuot
public import ConAgua.Checker.PresizeStage
public import ConAgua.Final.Twin

@[expose] public section

/-!
# The sequential driver's two runs give `TwinAccepts` (lane parmode)

docs/design/parmode.md, "Redesign". `drv_twinAccepts`: entry 1 (`check` with the mode word `3`,
from the loaded memory) returning `2^63 + k`, then entry 2 in place (`check` with the mode word `2`
on a memory `w` that keeps entry 1's final word arrays phase B's loop names, the range `[0, k)`, an
empty seed, the view in the header) returning `ACCEPT`: the twin's pipeline accepts. Entry 1 is
`checkA_run` (phase A ends in `PhaseBStart`, the memory is the buffer's `parCompactMem`, with the
header only), entry 2 `runMode2_agree` (phase B on the worker, through non-interference), and the
two are `SeqAccepts`, i.e. `TwinAccepts` (`Final/Twin.lean`).
-/

open ConRon.Arena ConAgua.Final

namespace L.Checker

open L L.Arena L.Rom

/-- **The driver's two runs accept ⇒ the twin accepts.** -/
theorem drv_twinAccepts (b pb : ByteArray) (sz : TieredArray → Nat) (hin : InputsOK b pb sz)
    (N₁ : Nat) (hN₁ : N₁ < 2 ^ 62) (rs₁ : List Word) (m₁ : Mem)
    (h₁ : L.run checkerProg N₁ "check" [] (loadMemM b pb sz 3) = .ok (rs₁, m₁))
    (hge : 9223372036854775808 ≤ (rs₁.headD 0).toNat)
    (N₂ : Nat) (hN₂ : N₂ ≤ 2 ^ 62) (w : Mem) (rs₂ : List Word) (m₂ : Mem)
    (hw : ∀ a, phaseBS a = true → w.arr64 a = m₁.arr64 a) (hmode : w.glob MODE = 2)
    (hlo : w.glob PLO = 0) (hhi : w.glob PHI = rs₁.headD 0 - 9223372036854775808)
    (hctlf : (w.arr64 CTLF).size = 0) (hv : rd64 w HDRF 3 = rd64 m₁ OUT 3)
    (h₂ : L.run checkerProg N₂ "check" [] w = .ok (rs₂, m₂)) (hacc : rs₂.headD 0 = ACCEPT) :
    TwinAccepts [b] := by
  sorry

end L.Checker
