module

import ConAgua.Arena.WhnfM2CRefine5
public import ConAgua.Arena.WhnfM2CRefine2

@[expose] public section
/-!
# `major_to_ctor`'s verdict claims

No verdict site of its own: the claims are the `infer_io`, `whnf` and `defeq` slots'
(`KnotUpToE`) and `proof_irrel`'s (`ProofIrrelWE`), through its pieces' unified refinements
(`mtc_ref` and below, `Arena/WhnfM2CRefine*.lean`): `majorToCtorE_of` (`MajorToCtorE`) is
`mtc_ref`'s error half.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

section top
variable (p : Prog) (hp : M2CProg' p) (hc : IotaCallees p) (hpi : ProofIrrelOKM p)
  (hE : ErecKeptKnot p) (hcc : ProjCallees p) (hnv : closedNV p L.Checker.nvFns = true)
  (hPI : ProofIrrelWE p)
include hp hc hpi hE hcc hnv hPI

/-- **`MajorToCtorE`**: `major_to_ctor`'s verdicts are `m2c_head`'s (`mtc_ref`'s error half). -/
theorem majorToCtorE_of : MajorToCtorE p := by
  sorry

end top

end L.Arena
