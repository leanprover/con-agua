import ConAgua.Verdict.WhnfNatE
import ConAgua.Verdict.WhnfProjE
import ConAgua.Verdict.WhnfCertsE
import ConAgua.Verdict.WhnfIdxE
import ConAgua.Verdict.WhnfPirrE

/-!
# The `whnf` family's part of the error knot (lane `verdicts-b`, helper `k2`)

`whnfSlotsE_of`: the `whnf_core` and `whnf` slots' error halves one level up, under the ok knot's
program hypotheses (`KnotAllProg`), the verdict closure (`closedNV`), and the error claim of the one
callee outside the family the slot bodies reach (`WhnfCalleesE`: `defeq_list`, the `defeq`
family's). Every function of the slot bodies' call tree is proved: `whnf_core`/`_loop`/`_step`
(`WhnfSlotE`), `whnf`/`_loop`/`_step` (`WhnfSlotE`), the `reduce_nat` family (`WhnfNatE`), the `proj`
arm (`WhnfProjE`), the `app` arm and `whnf_app` (`WhnfAppE`), the ι family (`WhnfIotaE`,
`WhnfIotaRecE`, `WhnfPrepE`, `WhnfCertsE`, `WhnfIdxE`), `major_to_ctor` (`WhnfM2CE`), `proof_irrel`
(`WhnfPirrE`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- The error claims the slot bodies take as hypotheses: `defeq_list`'s (the `defeq` family's). -/
structure WhnfCalleesE (p : Prog) : Prop where
  defeqList : DefeqListE p

section knot
variable {p : Prog} (hq : KnotAllProg p) (hnv : closedNV p L.Checker.nvFns = true)
  (hE : WhnfCalleesE p)

include hq hnv in
theorem KnotAllProg.prepareMajorE : PrepareMajorE p :=
  prepareMajorE_of p hq.m2c.toIotaProg4 (KnotAllProg.iotaC hq) (KnotAllProg.whnfC hq) supKeep_of
    (majorToCtor_refines' p hq.m2c (KnotAllProg.iotaC hq) (KnotAllProg.proofIrrel hq)
      (ErecKeptKnot.of_closed hq.hcl) (KnotAllProg.projC hq))
    (ErecKeptKnot.of_closed hq.hcl) hnv
    (majorToCtorE_of p hq.m2c (KnotAllProg.iotaC hq) (KnotAllProg.proofIrrel hq)
      (ErecKeptKnot.of_closed hq.hcl) (KnotAllProg.projC hq) hnv
      (proofIrrelE_of p hq.m2c.toIotaProg4 (LvlDen.of_den coreDen_of) hnv))

include hq hnv hE in
theorem KnotAllProg.iotaRecFireE : IotaRecFireE p :=
  iotaRecFireE_of p hq.iotaRec (KnotAllProg.iotaC hq) (KnotAllProg.whnfC hq)
    (ErecKeptInst.of_closed hq.hcl) (ErecKeptRec.of_closed hq.hcl) (ErecKeptKnot.of_closed hq.hcl) hnv
    (iotaRecCmpE_of p hq.iotaRec (KnotAllProg.iotaC hq) (KnotAllProg.whnfC hq)
      (ErecKeptInst.of_closed hq.hcl) (ErecKeptRec.of_closed hq.hcl) hnv hE.defeqList)
    (iotaCertsFullE_of p hq.iotaRec.toIotaProg4 (KnotAllProg.whnfC hq).instList hnv)
    (iotaIndexOkE_of p hq.iotaRec.toIotaProg' (KnotAllProg.iotaC hq).inst1 hnv hE.defeqList)

include hq hnv hE in
theorem KnotAllProg.iotaRecAtE : IotaRecAtE p :=
  iotaRecAtE_of p hq.iotaRec hnv
    (iotaRecMajorE_of p hq.iotaRec (KnotAllProg.iotaC hq) (KnotAllProg.whnfC hq) supKeep_of
      (majorToCtor_refines' p hq.m2c (KnotAllProg.iotaC hq) (KnotAllProg.proofIrrel hq)
        (ErecKeptKnot.of_closed hq.hcl) (KnotAllProg.projC hq))
      (ErecKeptKnot.of_closed hq.hcl) hnv (KnotAllProg.prepareMajorE hq hnv)
      (KnotAllProg.iotaRecFireE hq hnv hE))

include hq hnv hE in
/-- **The `whnf_core` and `whnf` slots' error halves one level up** (`KnotStepE`'s `whnf`
family part). -/
theorem whnfSlotsE_of (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) :
    WhnfCoreSlotE p (n + 1) ∧ WhnfSlotE p (n + 1) :=
  whnfSlotsE_step hq hnv
    (coreAppE_of p hq.core hnv (KnotAllProg.iotaRecAtE hq hnv hE) (KnotAllProg.iota hq))
    (stepProjE_of p hq.core (KnotAllProg.whnfC hq) supKeep_of hnv)
    (reduceNatE_of p hq.delta hnv) n hk hkE

end knot

end L.Arena
