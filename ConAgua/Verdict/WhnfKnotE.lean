import ConAgua.Verdict.WhnfNatE
import ConAgua.Verdict.WhnfProjE
import ConAgua.Verdict.WhnfIotaRecE
import ConAgua.Verdict.WhnfPrepE

/-!
# The `whnf` family's part of the error knot (lane `verdicts-b`, helper `k2`)

`whnfSlotsE_of`: the `whnf_core` and `whnf` slots' error halves one level up, under the ok knot's
program hypotheses (`KnotAllProg`), the verdict closure (`closedNV`), and the error claims of the
callees not yet proved (`WhnfCalleesE`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- The error claims the slot bodies still take as hypotheses. -/
structure WhnfCalleesE (p : Prog) : Prop where
  majorToCtor : MajorToCtorE p
  iotaRecCmp : IotaRecCmpE p
  iotaCertsFull : IotaCertsFullE p
  iotaIndexOk : IotaIndexOkE p

section knot
variable {p : Prog} (hq : KnotAllProg p) (hnv : closedNV p L.Checker.nvFns = true)
  (hE : WhnfCalleesE p)

include hq hnv hE in
theorem KnotAllProg.prepareMajorE : PrepareMajorE p :=
  prepareMajorE_of p hq.m2c.toIotaProg4 (KnotAllProg.iotaC hq) (KnotAllProg.whnfC hq) supKeep_of
    (majorToCtor_refines' p hq.m2c (KnotAllProg.iotaC hq) (KnotAllProg.proofIrrel hq)
      (ErecKeptKnot.of_closed hq.hcl) (KnotAllProg.projC hq))
    (ErecKeptKnot.of_closed hq.hcl) hnv hE.majorToCtor

include hq hnv hE in
theorem KnotAllProg.iotaRecFireE : IotaRecFireE p :=
  iotaRecFireE_of p hq.iotaRec (KnotAllProg.iotaC hq) (KnotAllProg.whnfC hq)
    (ErecKeptInst.of_closed hq.hcl) (ErecKeptRec.of_closed hq.hcl) (ErecKeptKnot.of_closed hq.hcl) hnv
    hE.iotaRecCmp hE.iotaCertsFull hE.iotaIndexOk

include hq hnv hE in
theorem KnotAllProg.iotaRecAtE : IotaRecAtE p :=
  iotaRecAtE_of p hq.iotaRec hnv
    (iotaRecMajorE_of p hq.iotaRec (KnotAllProg.iotaC hq) (KnotAllProg.whnfC hq) supKeep_of
      (majorToCtor_refines' p hq.m2c (KnotAllProg.iotaC hq) (KnotAllProg.proofIrrel hq)
        (ErecKeptKnot.of_closed hq.hcl) (KnotAllProg.projC hq))
      (ErecKeptKnot.of_closed hq.hcl) hnv (KnotAllProg.prepareMajorE hq hnv hE)
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
