import ConAgua.Verdict.DefEqSpineE
import ConAgua.Verdict.DefEqLamsE
import ConAgua.Verdict.DefEqPeelE

/-!
# The `defeq` slot's error half one level up, assembled (lane `verdicts-b`, helper `k3`)

`defeq_body`'s callees' error claims (`DefeqBodyCalleesE`) from this family's proofs
(`DefEq*E.lean`) and the whnf family's error claims, taken as hypotheses in their ok
refinements' shapes (`DefeqWhnfE`). `KnotAllProg.defeqSlotE_all`: the `defeq` field of the error
knot's step (`KnotStepE`), `∀ n, KnotUpTo p n → KnotUpToE p n → DefeqSlotE p (n + 1)`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- **The whnf family's error claims this family uses** (hypotheses; each in its ok
refinement's shape: `boolTrueShortcut_refines`, `propIrrel_refines`, `ReduceProjCoreH`,
`setCert_refines`, `suCert_refines`, `ProofIrrelOK`, `etaCert_refines`, `deltaQuick_refines`,
`tryUnfoldProjApp_refines`, `lazyNat_refines`). -/
structure DefeqWhnfE (p : Prog) : Prop where
  boolTrueShortcut : BoolTrueShortcutE p
  propIrrel : PropIrrelE p
  reduceProjCore : ReduceProjCoreE p
  setCert : SetCertE p
  suCert : SuCertE p
  proofIrrel : ProofIrrelE p
  etaCert : EtaCertE p
  deltaQuick : DeltaQuickE p
  tryUnfoldProjApp : TryUnfoldProjAppE p
  lazyNat : LazyNatE p

section all
variable {p : Prog} (hq : KnotAllProg p) (hw : DefeqWhnfE p) (hnv : closedNV p L.Checker.nvFns = true)

include hq hw hnv in
/-- `lazy_delta_step`'s error claim from the family's proofs. -/
theorem KnotAllProg.lazyDeltaStepE : LazyDeltaStepE p :=
  let lp := hq.body.lazy
  let lc := KnotAllProg.lazy hq
  let hlE := ldsLeft_refinesE p lp lc hw.deltaQuick hnv
  let hrE := ldsRight_refinesE p lp lc hw.deltaQuick hnv
  let hsE := ldsSame_refinesE p lp lc (defeqSpine_refinesE p lp.spine hnv)
    (ldsUnfold2_refinesE p lp lc hw.deltaQuick hnv) hnv
  lazyDeltaStep_refinesE p lp hw.deltaQuick hw.tryUnfoldProjApp hlE hrE
    (ldsBoth_refinesE p lp hlE hrE hsE hnv) hnv

include hq hnv in
/-- `quick_defeq`'s error claim. -/
theorem KnotAllProg.quickDefeqE : QuickDefeqE p :=
  let qp := hq.body.lazy.spine.quick
  let lc := KnotAllProg.lazy hq
  quickDefeq_refinesE p qp lc.store (defeqBinders_refinesE p qp.lams.peel lc.instList hnv)
    (defeqLams_refinesE p qp.lams lc.inst1 hnv) hnv

include hq hw hnv in
/-- `lazy_delta_reduction`'s error claim. -/
theorem KnotAllProg.lazyDeltaReductionE : LazyDeltaReductionE p :=
  let lp := hq.body.lazy
  let lc := KnotAllProg.lazy hq
  lazyDeltaReduction_refinesE p lp lc (lazyIter_refinesE p lp lc
    (defeqOffset_refinesE p lp.mid lc.natPred hnv) hw.lazyNat (KnotAllProg.lazyDeltaStepE hq hw hnv) hnv)

include hq hw hnv in
/-- `defeq_tail`'s error claim. -/
theorem KnotAllProg.defeqTailE : DefeqTailE p :=
  let sp := hq.body.stuck
  let sc := KnotAllProg.stuck hq
  let irrE := stuckIrrel_refinesE p sp hq.body.iota sc hw.setCert hw.suCert hw.proofIrrel
  defeqTail_refinesE p sp sc
    (projPair_refinesE p sp (ldpr_refinesE p sp sc (KnotAllProg.lazyDeltaStepE hq hw hnv)
      hw.reduceProjCore))
    (defeqStuck_refinesE p sp (stuckStrE_of p sp sc irrE hnv)
      (stuckAppE_of p sp sc (appCongE_of p sp (defeqLst_refinesE p hq.lst) hnv) irrE)
      (stuckRestE_of p sp sc irrE hw.etaCert hnv) hnv) hnv

include hq hw hnv in
/-- **`defeq_body`'s callees' error claims**, all of this family's proved. -/
theorem KnotAllProg.defeqBodyCalleesE : DefeqBodyCalleesE p :=
  ⟨hw.boolTrueShortcut, hw.propIrrel, KnotAllProg.quickDefeqE hq hnv,
    KnotAllProg.lazyDeltaReductionE hq hw hnv, KnotAllProg.defeqTailE hq hw hnv⟩

include hq hw hnv in
/-- **The `defeq` slot's error half one level up** (the `defeq` field of `KnotStepE`). -/
theorem KnotAllProg.defeqSlotE_all (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) :
    DefeqSlotE p (n + 1) :=
  KnotAllProg.defeqSlotE hq (KnotAllProg.defeqBodyCalleesE hq hw hnv) hnv n hk hkE

end all

end L.Arena
