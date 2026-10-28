import ConAgua.Arena.WhnfM2CRefine5
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
theorem majorToCtorE_of : MajorToCtorE p :=
  fun n hk hkE F hnF s₀ a₀ dn vis fe MM eb mode d rec ro rc major rules hn62 hS hm4 hebm hmaj hr =>
    RefE.coreSpecE (mtcE_spec p hp.toM2CProg hp.majorToCtor (n + 1) s₀ mode vis d rec ro rc major) hnv
      ⟨hkE, hPI⟩ (mtc_ref p hp hc hpi hE hcc n F hk hnF hn62 dn vis fe eb mode d rec ro rc major hm4
        hebm hmaj rules s₀.mem a₀ MM hS hr)

end top

end L.Arena
