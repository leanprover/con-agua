import ConAgua.Verdict.DefEqLoopsE
import ConAgua.Verdict.DefEqTailE

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
`ProofIrrelOK`). -/
structure DefeqWhnfE (p : Prog) : Prop where
  boolTrueShortcut : BoolTrueShortcutE p
  propIrrel : PropIrrelE p
  reduceProjCore : ReduceProjCoreE p
  proofIrrel : ProofIrrelWE p

section all
variable {p : Prog} (hq : KnotAllProg p) (hw : DefeqWhnfE p) (hnv : closedNV p L.Checker.nvFns = true)

include hq hnv in
/-- `lazy_delta_step`'s error claim (`lds_ref`'s error half). -/
theorem KnotAllProg.lazyDeltaStepE : LazyDeltaStepE p :=
  let lp := hq.body.lazy
  fun n hk hkE F hF hn s₀ a₀ dn vis fe M eb mode d a b hs ha hb hd =>
    RefE.coreSpecE (ldsE_spec p lp.step lp.both lp.mid.tupa lp.left lp.right lp.same lp.unfold2 lp.mid.dq
      lp.spine.sp lp.spine.sp2 lp.spine.cmp lp.spine.rev (n + 1) s₀ mode vis d a b) hnv ⟨hkE, hnv⟩
      (lds_ref p lp (KnotAllProg.lazy hq) n hk F hF hn s₀ a₀ dn vis fe M eb mode d a b hs ha hb hd)

include hq hnv in
/-- `quick_defeq`'s error claim. -/
theorem KnotAllProg.quickDefeqE : QuickDefeqE p :=
  let qp := hq.body.lazy.spine.quick
  let lc := KnotAllProg.lazy hq
  fun n hk hkE F s₀ a₀ dn vis fe M eb mode d x y hF hn hs hx hy hd =>
    RefE.coreSpecE (qdE_spec p qp.qd qp.qs qp.qf qp.ql qp.lams.peel.binders qp.lams.lams (n + 1) s₀
      mode vis d x y) hnv ⟨hkE, hnv⟩
      (qd_ref p qp lc.instList lc.inst1 lc.store n hk F s₀ a₀ dn vis fe M eb mode d x y (by omega)
        (by omega) hs hx hy hd)

include hq hnv in
/-- `lazy_delta_reduction`'s error claim (`lazyDeltaReduction_ref`'s error half). -/
theorem KnotAllProg.lazyDeltaReductionE : LazyDeltaReductionE p :=
  let lp := hq.body.lazy
  fun n hk hkE F hF hn s₀ a₀ dn vis fe M eb mode d a b hs ha hb hd =>
    RefE.coreSpecE (lazyDeltaReduction_specE p lp.red (n + 1) s₀ mode vis d a b) trivial
      ⟨⟨hkE, hnv⟩, reduceNatE_of p hq.delta hnv⟩
      (lazyDeltaReduction_ref p lp (KnotAllProg.lazy hq) n hk F hF hn s₀ a₀ dn vis fe M eb mode d a b hs
        ha hb hd)

include hq hw hnv in
/-- `defeq_tail`'s error claim. -/
theorem KnotAllProg.defeqTailE : DefeqTailE p :=
  defeqTail_refinesE p hq.body.stuck hq.body.iota (KnotAllProg.stuck hq) (KnotAllProg.lazyDeltaStepE hq hnv)
    hw.reduceProjCore hw.proofIrrel (defeqLst_refinesE p hq.lst) hnv

include hq hw hnv in
/-- **`defeq_body`'s callees' error claims**, all of this family's proved. -/
theorem KnotAllProg.defeqBodyCalleesE : DefeqBodyCalleesE p :=
  ⟨hw.boolTrueShortcut, hw.propIrrel, KnotAllProg.quickDefeqE hq hnv,
    KnotAllProg.lazyDeltaReductionE hq hnv, KnotAllProg.defeqTailE hq hw hnv⟩

include hq hw hnv in
/-- **The `defeq` slot's error half one level up** (the `defeq` field of `KnotStepE`). -/
theorem KnotAllProg.defeqSlotE_all (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) :
    DefeqSlotE p (n + 1) :=
  KnotAllProg.defeqSlotE hq (KnotAllProg.defeqBodyCalleesE hq hw hnv) hnv n hk hkE

end all

end L.Arena
