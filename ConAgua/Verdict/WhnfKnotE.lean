module

import ConAgua.Verdict.WhnfM2CE
import ConAgua.Verdict.WhnfPrepE
import ConAgua.Verdict.WhnfIotaRecE
import ConAgua.Verdict.WhnfIotaE
import ConAgua.Verdict.WhnfSlotE
import ConAgua.Verdict.WhnfPirrE
import ConAgua.Arena.StrLitKeep
import ConAgua.Arena.WhnfM2CRefine5
public import ConAgua.Arena.DefEqKnot
public import ConAgua.Arena.WhnfCoreAppLoop
public import ConAgua.Arena.WhnfIotaRecRefine2

@[expose] public section

/-!
# The `whnf` family's part of the error knot (lane `verdicts-b`, helper `k2`)

`whnfSlotsE_of`: the `whnf_core` and `whnf` slots' error halves one level up, under the ok knot's
program hypotheses (`KnotAllProg`) and the verdict closure (`closedNV`); `defeq_list`, the one
callee outside the family the slot bodies reach, by its refinement (`defeqList_ref`). Every function of the slot bodies' call tree is proved: `whnf_core`/`_loop`/`_step`
(`WhnfSlotE`), `whnf`/`_loop`/`_step` (`WhnfSlotE`), the `reduce_nat` family (`WhnfNatE`), the `proj`
arm (`stepProj_ref`, `Arena/WhnfCoreProj`), the `app` arm and `whnf_app` (`capp_ref`,
`Arena/WhnfCoreStep`), the ι family (`WhnfIotaE`, `WhnfIotaRecE`, `WhnfPrepE`), `major_to_ctor` (`WhnfM2CE`), `proof_irrel`
(`WhnfPirrE`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

section knot
variable {p : Prog} (hq : KnotAllProg p) (hnv : closedNV p L.Checker.nvFns = true)

include hq hnv in
theorem KnotAllProg.prepareMajorE : PrepareMajorE p :=
  prepareMajorE_of p hq.m2c.toIotaProg4 (KnotAllProg.iotaC hq) (KnotAllProg.whnfC hq) supKeep_of
    (majorToCtor_refines' p hq.m2c (KnotAllProg.iotaC hq) (KnotAllProg.proofIrrel hq)
      (ErecPKept.of_closed hq.hcl) (KnotAllProg.projC hq) hq.prop (KnotAllProg.instLP hq))
    (ErecKeptKnot.of_closed hq.hcl) hnv
    (majorToCtorE_of p hq.m2c (KnotAllProg.iotaC hq) (KnotAllProg.proofIrrel hq)
      (ErecPKept.of_closed hq.hcl) (KnotAllProg.projC hq) hq.prop (KnotAllProg.instLP hq) hnv
      (proofIrrelE_of p hq.m2c.toIotaProg4 (LvlDen.of_den coreDen_of) hnv))

include hq hnv in
theorem KnotAllProg.iotaRecFireE : IotaRecFireE p :=
  iotaRecFireE_of p hq.iotaRec (KnotAllProg.iotaC hq) (KnotAllProg.whnfC hq)
    (ErecKeptInst.of_closed hq.hcl) (ErecKeptRec.of_closed hq.hcl) (ErecKeptKnot.of_closed hq.hcl) hnv

include hq hnv in
theorem KnotAllProg.iotaRecAtE : IotaRecAtE p :=
  iotaRecAtE_of p hq.iotaRec (KnotAllProg.iotaC hq) (KnotAllProg.whnfC hq) supKeep_of
    (majorToCtor_refines' p hq.m2c (KnotAllProg.iotaC hq) (KnotAllProg.proofIrrel hq)
      (ErecPKept.of_closed hq.hcl) (KnotAllProg.projC hq) hq.prop (KnotAllProg.instLP hq))
    (ErecKeptInst.of_closed hq.hcl) (ErecKeptRec.of_closed hq.hcl) (ErecKeptKnot.of_closed hq.hcl) hnv
    (KnotAllProg.prepareMajorE hq hnv) (KnotAllProg.iotaRecFireE hq hnv)

include hq hnv in
/-- **The `whnf_core` and `whnf` slots' error halves one level up** (`KnotStepE`'s `whnf`
family part). -/
theorem whnfSlotsE_of (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) :
    WhnfCoreSlotE p (n + 1) ∧ WhnfSlotE p (n + 1) :=
  whnfSlotsE_step hq hnv (KnotAllProg.iotaRecAtE hq hnv) n hk hkE

end knot

end L.Arena
