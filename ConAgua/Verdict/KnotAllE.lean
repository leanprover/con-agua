import ConAgua.Verdict.InferKnotE
import ConAgua.Verdict.WhnfKnotE
import ConAgua.Verdict.WhnfMidE
import ConAgua.Verdict.WhnfSetE
import ConAgua.Verdict.DefEqAllE
import ConAgua.Verdict.DefEqEagerE
import ConAgua.Verdict.DeclValE
import ConAgua.Checker.LoopProg
import ConAgua.Checker.NoVerdictClosed

/-!
# The error knot, assembled (lane `verdicts-b`, helper `ka`)

The three families' error halves of the knot's slots one level up, put together:

* the `infer`/`infer_io` slots (`inferSlots_stepE`, `InferKnotE.lean`), over `InferCalleesE`:
  the verdict closure, `infer_proj`'s claim (`inferProj_refinesE'`) and `defeq_arg`'s
  (`defeqArg_refinesE` over the `defeq` slot and `defeq_e`'s `defeqE_refinesE`);
* the `whnf_core`/`whnf` slots (`whnfSlotsE_of`, `WhnfKnotE.lean`), over `defeq_list`'s claim
  (`defeqList_refinesE`, `DefEqLoopsE.lean`);
* the `defeq` slot (`KnotAllProg.defeqSlotE_all`, `DefEqAllE.lean`), over the whnf family's ten
  claims (`DefeqWhnfE`), each from its `Whnf*E.lean` proof. The whnf family's local copies
  `ProofIrrelWE`, `DefeqLstWE`, `QuickDefeqWE` of the defeq family's `ProofIrrelE`, `DefeqLstE`,
  `QuickDefeqSpecE` are the same propositions (bridged by unfolding).

`KnotAllProg.knotStepE` is the error knot's step (`KnotStepE`), `KnotAllProg.knotE_all` the error
knot at every fuel (`knotE_upTo`). `KnotTopProg.coreStubsE`: the three `*_core` stage stubs'
error claims at `checkFuel` the declaration family takes (`CoreStubsE`). At the substituted
checker program: `checkerProg_knotE`, `checkerProg_coreStubsE`, and at the substituted program
of phase B and the fold (`Prog.subPB bs checkerProg`) `checkerProg_knotEPB`,
`checkerProg_coreStubsEPB`, with the verdict closure carried over (`closedNV_subPB`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

section knot
variable {p : Prog} (hq : KnotAllProg p) (hnv : closedNV p L.Checker.nvFns = true)

include hq hnv in
/-- `defeq_arg`'s error claim, from the error knot (`defeq`, and `defeq_e` one level up). -/
theorem KnotAllProg.defeqArgE : DefeqArgE p := by
  intro n hk hkE F s₀ a₀ dn vis fe M eb mode d a ta ty hF hn hs ha hta hty
  cases n with
  | zero => exact CoreSpecE.zero p _ _ _ s₀ a₀
  | succ k =>
    have hde : DefeqESlotE p k := by
      cases k with
      | zero => intro F s₀ a₀ _ _ _ _ _ _ _ _ _ _ _ _ _ _; exact CoreSpecE.zero p _ _ _ s₀ a₀
      | succ j => exact defeqE_refinesE p hq.infer.knot j (hkE j (by omega)).defeq
    exact defeqArg_refinesE p hq.infer.leaf hnv k (isEagerReduceH_of p hq.body.stuck.leaf)
      (hkE k (by omega)).defeq hde F s₀ a₀ dn vis fe M eb mode d a ta ty (by omega) (by omega) hs ha
      hta hty

include hq hnv in
/-- **The inference bodies' callees' error claims** (`InferCalleesE`). -/
theorem KnotAllProg.inferCE : InferCalleesE p :=
  ⟨hnv, inferProj_refinesE' p hq.proj
      ⟨coreDen_of, findProj_refines p hq.projp, projFound p hq.projp, erecKept_of hq.hcl, hq.instLP,
        erecKeptProj_of hq.hcl⟩
      ⟨hnv, hq.projp.tblix, hq.projp.tblrow, hq.projp.findTable⟩,
    KnotAllProg.defeqArgE hq hnv⟩

include hq in
/-- **The `whnf` slots' callee's error claim** (`WhnfCalleesE`: `defeq_list`'s). -/
theorem KnotAllProg.whnfCE : WhnfCalleesE p :=
  ⟨defeqList_refinesE p hq.iotaRec.toIotaProg'⟩

include hq hnv in
/-- `quick_defeq`'s error claim at every fuel from the two knots (`QuickDefeqWE`, the whnf
family's copy of `QuickDefeqSpecE`). -/
theorem KnotAllProg.quickDefeqWE (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) :
    QuickDefeqWE p n := by
  cases n with
  | zero => intro F s₀ a₀ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _; exact CoreSpecE.zero p _ _ _ s₀ a₀
  | succ k => exact KnotAllProg.quickDefeqE hq hnv k (hk.mono (by omega)) (hkE.mono (by omega))

include hq hnv in
/-- **The whnf family's ten error claims the `defeq` family takes** (`DefeqWhnfE`). -/
theorem KnotAllProg.defeqWhnfE : DefeqWhnfE p where
  boolTrueShortcut := fun n _ hkE F s₀ a₀ dn vis fe M eb mode d a hF hn hs ha =>
    boolTrueShortcut_refinesE p hq.body.lazy.mid hnv n hkE F s₀ a₀ dn vis fe M eb mode d a hF hn hs ha
  propIrrel := fun n hk hkE F s₀ a₀ dn vis fe M eb mode d a b hF hn hs ha hb =>
    propIrrel_refinesE p hq.body.stuck (KnotAllProg.stuck hq) hnv
      (proofIrrelE_of p hq.m2c.toIotaProg4 (LvlDen.of_den coreDen_of) hnv)
      n hk hkE F s₀ a₀ dn vis fe M eb mode d a b hF hn hs ha hb
  reduceProjCore := fun n hk hkE F hF hn s₀ a₀ dn vis fe MM eb mode d sn i c hs _ hc =>
    reduceProjCore_refinesE p hq.core (strLitSupported_core p hq.str) (strLitCtor_core p hq.str) hnv
      n hk hkE F hF hn s₀ a₀ dn vis fe MM eb mode d sn i c hs hc (supKeep_of fe)
  setCert := fun n hk hkE F s₀ a₀ dn vis fe M eb mode d a b hF hn hs ha hb =>
    setCert_refinesE p hq.body.stuck hq.body.iota (KnotAllProg.stuck hq) hnv
      (defeqLst_refinesE p hq.lst) n hk hkE F s₀ a₀ dn vis fe M eb mode d a b hF hn hs ha hb
  suCert := fun n hk hkE F s₀ a₀ dn vis fe M eb mode d a b hF hn hs ha hb =>
    suCert_refinesE p hq.body.stuck (KnotAllProg.stuck hq) hnv
      n hk hkE F s₀ a₀ dn vis fe M eb mode d a b hF hn hs ha hb
  proofIrrel := proofIrrelE_of p hq.m2c.toIotaProg4 (LvlDen.of_den coreDen_of) hnv
  etaCert := fun n hk hkE F s₀ a₀ dn vis fe M eb mode d ty1 body1 b hF hn hs hty hbody hb =>
    etaCert_refinesE p hq.body.stuck (KnotAllProg.stuck hq) hnv
      n hk hkE F s₀ a₀ dn vis fe M eb mode d ty1 body1 b hF hn hs hty hbody hb
  deltaQuick := fun n hk hkE F s₀ a₀ dn vis fe M eb mode d a b hF hn hs ha hb hd =>
    deltaQuick_refinesE p hq.body.lazy.mid n (KnotAllProg.quickDefeqWE hq hnv n hk hkE)
      F s₀ a₀ dn vis fe M eb mode d a b hF hn hs ha hb hd
  tryUnfoldProjApp := fun n _ hkE F s₀ a₀ dn vis fe M eb mode d e hF hn hs he =>
    tryUnfoldProjApp_refinesE p hq.body.lazy.mid hnv n hkE F s₀ a₀ dn vis fe M eb mode d e hF hn hs he
  lazyNat := fun n hk hkE F hF hn s₀ a₀ dn vis fe M eb mode d a b hs ha hb =>
    lazyNat_refinesE p hq.body.lazy (KnotAllProg.lazy hq) hq.delta hnv
      n hk hkE F hF hn s₀ a₀ dn vis fe M eb mode d a b hs ha hb

include hq hnv in
/-- **The error knot's step**: the five slots' error halves one level up from the knot and the
error knot up to `n`. -/
@[refines_part ConRon.Arena.coreKnot "the five slots (step, verdicts)"]
theorem KnotAllProg.knotStepE : KnotStepE p := fun n hk hkE =>
  have hW := whnfSlotsE_of hq hnv (KnotAllProg.whnfCE hq) n hk hkE
  have hI := inferSlots_stepE p hq.infer (KnotAllProg.inferC hq) (KnotAllProg.inferCE hq hnv) n hk hkE
  ⟨hW.1, hW.2, hI.1, hI.2,
    KnotAllProg.defeqSlotE_all hq (KnotAllProg.defeqWhnfE hq hnv) hnv n hk hkE⟩

include hq hnv in
/-- **The error knot at every L fuel.** -/
@[refines_part ConRon.Arena.coreKnot "every fuel (verdicts)"]
theorem KnotAllProg.knotE_all (n : Nat) : KnotOKE p n :=
  knotE_upTo (knotUpTo_all hq) (KnotAllProg.knotStepE hq hnv) n n (Nat.le_refl _)

end knot

/-- **The `*_core` stage stubs' error claims at `checkFuel`** (`CoreStubsE`, the declaration
family's hypothesis), from the error knot. -/
theorem KnotTopProg.coreStubsE {p : Prog} (hq : KnotTopProg p)
    (hnv : closedNV p L.Checker.nvFns = true) : CoreStubsE p where
  inferTypeCore := inferTypeCore_refinesE p hq.entry (KnotAllProg.knotE_all hq.knot hnv)
  ensureSortCore := ensureSortCore_refinesE p hq.entry hq.knot.infer.leaf (knot_all hq.knot)
    (KnotAllProg.knotE_all hq.knot hnv)
  isDefEqCore := L.Ind.isDefEqCore_stageE hq.entry fun n => (KnotAllProg.knotE_all hq.knot hnv n).defeq

end L.Arena

namespace L

/-- `subPB` keeps a body's `noV` (an abort's constant code stays constant; calls keep their
callee). -/
theorem Stmt.noV_subPB (bs : List UInt8) (fs : List FnName) :
    ∀ (s : Stmt), s.noV fs = true → (s.subPB bs).noV fs = true
  | .seq s t, h | .ite _ s t, h => by
    simp only [Stmt.noV, Stmt.subPB, Bool.and_eq_true] at h ⊢
    exact ⟨Stmt.noV_subPB bs fs s h.1, Stmt.noV_subPB bs fs t h.2⟩
  | .while _ s, h => by simp only [Stmt.noV, Stmt.subPB] at h ⊢; exact Stmt.noV_subPB bs fs s h
  | .call .., h => by simpa [Stmt.noV, Stmt.subPB] using h
  | .abort e, h => by
    cases e <;> simp_all [Stmt.noV, Stmt.subPB, Expr.cls0, Expr.subPB]
  | .skip, _ | .set .., _ | .st8 .., _ | .st64 .., _ | .brk, _ | .ret _, _ | .gset .., _
  | .st64t .., _ | .copy64 .., _ | .copy8w .., _ | .scan8 .., _ => rfl

/-- **The verdict closure carries over to the substituted program.** -/
theorem closedNV_subPB (bs : List UInt8) {p : Prog} {fs : List FnName}
    (h : closedNV p fs = true) : closedNV (Prog.subPB bs p) fs = true := by
  simp only [closedNV, List.all_eq_true] at h ⊢
  intro f hf
  have := h f hf
  rw [L.Rom.lookup_subPB]
  cases e : p.lookup f with
  | none => rfl
  | some fd =>
    simp only [e] at this
    exact Stmt.noV_subPB bs fs _ this

end L

namespace L.Checker

open L L.Rom L.Arena L.Ind L.Compiler

/-- The verdict closure at the substituted checker program. -/
theorem checkerProg_nvPB (bs : List UInt8) : closedNV (Prog.subPB bs checkerProg) nvFns = true :=
  closedNV_subPB bs checkerProg_nv

/-- `natFns` at `checkerProg` (as `checkerProg_natAgreePB`). -/
theorem checkerProg_natArm : ProgHas checkerProg natArmProg' := by prog_bundle []

theorem checkerProg_natAgree : ∀ f ∈ natFns, checkerProg.lookup f = natArmProg'.lookup f :=
  ProgHas.agreeNames checkerProg_natArm

theorem checkerProg_lvlText : ∀ f ∈ lvlFns, checkerProg.lookup f = cvgProg.lookup f :=
  fun f hf => checkerProg_cvgAgree f (lvlFns_cvg f hf).1 (lvlFns_cvg f hf).2

/-- **The knot's program and entry points at `checkerProg`.** -/
theorem checkerProg_knotTop : KnotTopProg checkerProg := by
  prog_bundle [checkerProg_coreErec, checkerProg_natAgree, checkerProg_lvlText, checkerProg_cvgAgree,
    checkerProg_ivAgree, checkerProg_armAgree, checkerProg_cvgIn, checkerProg_ivIn, checkerProg_armIn]

/-- **The knot's program and entry points at the substituted checker program** (no ROM facts
needed: the knot reads no pin data). -/
theorem checkerProg_knotTopPB (bs : List UInt8) : KnotTopProg (Prog.subPB bs checkerProg) := by
  prog_bundle [checkerProg_cvgAgreePB bs, checkerProg_ivAgreePB bs, checkerProg_armAgreePB bs,
    checkerProg_cvgIn.subPB bs, checkerProg_ivIn.subPB bs, checkerProg_armIn.subPB bs,
    closedW_subPB bs checkerProg_coreErec, checkerProg_natAgreePB bs, checkerProg_lvlTextPB bs]

/-- **The error knot at `checkerProg`**, every fuel. -/
theorem checkerProg_knotE (n : Nat) : KnotOKE checkerProg n :=
  KnotAllProg.knotE_all checkerProg_knotTop.knot checkerProg_nv n

/-- **The core stage stubs' error claims at `checkerProg`.** -/
theorem checkerProg_coreStubsE : CoreStubsE checkerProg :=
  KnotTopProg.coreStubsE checkerProg_knotTop checkerProg_nv

/-- **The error knot at the substituted checker program** (phase B, the fold), every fuel. -/
theorem checkerProg_knotEPB (bs : List UInt8) (n : Nat) : KnotOKE (Prog.subPB bs checkerProg) n :=
  KnotAllProg.knotE_all (checkerProg_knotTopPB bs).knot (checkerProg_nvPB bs) n

/-- **The core stage stubs' error claims at the substituted checker program.** -/
theorem checkerProg_coreStubsEPB (bs : List UInt8) : CoreStubsE (Prog.subPB bs checkerProg) :=
  KnotTopProg.coreStubsE (checkerProg_knotTopPB bs) (checkerProg_nvPB bs)

end L.Checker
