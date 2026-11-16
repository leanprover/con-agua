module

public import ConAgua.Arena.DefEqBody
import ConAgua.Arena.InferFieldSortNat
import ConAgua.Arena.PropReadRefine4
import ConAgua.Arena.InferProj2
import ConAgua.Arena.StrLitBase
import ConAgua.Arena.StrLitCtor
import ConAgua.Arena.WhnfIotaRecRefine3
import ConAgua.Arena.WalkCore
public import ConAgua.Arena.InstLPEntry
import ConAgua.Arena.WhnfM2CRefine5
import ConAgua.Arena.WhnfSlotRefine
import ConAgua.Arena.CoreNatOp
import ConAgua.Arena.WhnfDeltaRefine2
import ConAgua.Arena.WhnfProjRefine2
public import ConAgua.Arena.InferBodyDisp
public import ConAgua.Arena.InferProj
public import ConAgua.Arena.PropReadRefine3
public import ConAgua.Arena.StrLitBase
public import ConAgua.Arena.WalkLeaves
public import ConAgua.Arena.WalkScope
public import ConAgua.Arena.WhnfIotaRecRefine
public import ConAgua.Arena.WhnfProjRefine

@[expose] public section

/-!
# The knot tied (lane `defeq`)

1. **Proved specs into the hypothesis structures** (one wrapper each): `lazyDeltaStepH_of`
   (`LazyDeltaStepH` from `lazyDeltaStep_refines`), `defeqLstOK_of` (`DefeqLstOK` from
   `defeqLst_refines`), `isEagerReduceH_of` (`IsEagerReduceH` from `isEagerReduce_refines`),
   `reduceNat_of` (`LazyCallees.reduceNat` from lane `whnf`'s `reduceNat_refines'`),
   `proofIrrelOK_of` (`ProofIrrelOK` from lane `whnf`'s `proofIrrel_refines'` over `CoreDen`).
2. **The knot.** No assumption is left (the last, `KnotCallees.instLP`, is `KnotAllProg.instLP`,
   helper `whnf4-ilp`'s `instLP_refines`); `knot_step`: `KnotUpTo p n →
   KnotOK p (n + 1)` from the five slot steps; `knot_all`: `KnotOK p n` at every fuel (fuel `0`:
   every L call at fuel `0` fails, `CoreSpec.zeroLet`).
3. **Lane `whnf`'s bundles from real proofs** (helper `whnf4-knot`): `WhnfCallees`
   (`KnotAllProg.whnfC`), `ProjCallees` (`projC`), `IotaCallees` (`iotaC`) and `CoreCallees`
   (`coreC`, its `iota` field lane `whnf`'s `iotaRecAt_refines'`) are built from the walks, the
   string-literal and projection proofs and the `inst_lp` walk; none of them uses a
   slot step of this file. Lane `whnf`'s two slot steps then come from its primed proofs over these
   bundles: `whnfCoreSlot_step` (`KnotAllProg.whnfCoreStep`) and the `whnf` chain over
   `whnfStep_refines'` (`KnotAllProg.whnfStep`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

/-! ## Proved specs into the hypotheses -/

/-- `LazyDeltaStepH` (the stuck side's hypothesis) from `lazyDeltaStep_refines`. -/
theorem lazyDeltaStepH_of (p : Prog) (hp : LazyProg p) (hc : LazyCallees p) : LazyDeltaStepH p :=
  fun n hk F hF hn s₀ a₀ dn vis fe M eb mode d a b hs ha hb hd =>
    lazyDeltaStep_refines p hp hc n hk F hF hn s₀ a₀ dn vis fe M eb mode d a b hs ha hb hd

/-- `DefeqLstOK` from `defeqLst_refines` (lists through `Array.toList`). -/
theorem defeqLstOK_of (p : Prog) (hp : p.lookup "defeq_lst" = some defeqLstL) : DefeqLstOK p :=
  fun n hk F hF hn s₀ a₀ dn vis fe M eb mode d ao an bo bn xs ys hs hx hy hxt hyt =>
    defeqLst_refines p hp n hk F hF hn s₀ a₀ dn vis fe M eb mode d ao an bo bn hs xs.toList
      ys.toList (by simpa using hx) (by simpa using hy) hxt hyt

/-- `IsEagerReduceH` from `isEagerReduce_refines` (fuel `0` fails). -/
theorem isEagerReduceH_of (p : Prog) (hp : DefEqLeafProg p) : IsEagerReduceH p
  | 0, s₀, a₀, dn, vis, fe, M, eb, _, _, _ => CoreSpec.zeroLet p _ _ _ _ s₀ a₀ dn vis fe M eb _
  | n + 1, s₀, a₀, dn, vis, fe, M, eb, h, hS, hh =>
      isEagerReduce_refines p hp n s₀ a₀ dn vis fe M eb h hS hh

/-- `ProofIrrelOK` from lane `whnf`'s `proofIrrel_refines'` (the levels it compares read back:
`LvlDen.of_den`). -/
theorem proofIrrelOK_of (p : Prog) (hp : IotaProg4 p) (hden : CoreDen) : ProofIrrelOK p :=
  proofIrrel_refines' p hp (LvlDen.of_den hden)

/-- `LazyCallees.reduceNat` from lane `whnf`'s `reduceNat_refines'`. -/
theorem reduceNat_of (p : Prog) (hp : WhnfDeltaProg' p) (hno : NatOpResultOK p) :
    ∀ n, n ≤ 2 ^ 62 → ReduceNatSpec p n :=
  fun n hn F s₀ a₀ dn vis fe MM eb mode d e hF hs he hk =>
    reduceNat_refines' p hp hno n F s₀ a₀ dn vis fe MM eb mode d e hF hn hs he hk

/-! ## The knot -/

/-- What the knot needs of a program. -/
structure KnotAllProg (p : Prog) : Prop where
  body : DefeqBodyProg p
  infer : InferAllProg p
  delta : WhnfDeltaProg' p
  lst : p.lookup "defeq_lst" = some defeqLstL
  /-- The phase-4 walks at their names (`CoreWalks.lean`): `inst1`, `inst_list`, `abs_entry`,
  `ar_entry`, `has_fvar` under `CoreS` at exactly `coreWalkFuel`. -/
  walks : CoreWalkProg p
  natPred : NatPredProg p
  lvc : LvlCacheProg p
  prop : PropReadProg p
  proj : InferProjProg p
  str : StrLitProg p
  projp : ProjProg p
  /-- `caps_never_zero`, `rec_fire_levels` and their callees (`capsNeverZeroOK_of`,
  `recFireLevelsOK_of`). -/
  ls : LsProg p
  /-- The core's write set leaves `EREC` alone (lane `whnf3`'s `CoreErec.lean`). -/
  hcl : closedA p coreErecA coreErecC coreFns = true
  /-- Lane `whnf`'s `whnf_core` family, the ι side (`iota_rec_at`, `major_to_ctor`) and the two
  walks `wscoped_bfast`, `leaf_guard`. -/
  core : WhnfCoreProg p
  iotaRec : IotaRecProg' p
  m2c : M2CProg' p
  ws : WsProg p
  lg : LgProg p
  /-- The `instLP` walk and its entries (`InstLPEntry.lean`, helper `whnf4-ilp`). -/
  ilw : ILWEntryProg p

theorem reservedBasisNames_run {m : Mem} {a : AState} (hP : PinsFull m a.pins) :
    reservedBasisNames.run a = .ok (a.pins.reserved, a) := by
  simp only [reservedBasisNames, pinReserved, StateT.run_bind, StateT.run_get, pure_bind,
    L.Arena.pinsReady_true hP, ↓reduceIte]
  rfl

theorem reservedContainsT_run {m : Mem} {a : AState} (hP : PinsFull m a.pins) (n : NIdx) :
    (reservedContainsT n).run a = .ok (a.pins.reserved.contains n, a) := by
  simp only [reservedContainsT, StateT.run_bind, reservedBasisNames_run hP, except_ok_bind]
  rfl

/-- `LvlsEqCH` from lane `whnf`'s `lvlsEqC_refines` (fuel below two: no run). -/
theorem lvlsEqCH_of (p : Prog) (hp : LvlCacheProg p) : LvlsEqCH p := by
  intro n s₀ a₀ dn vis fe M eb us vs hS hu hv _ _
  rcases Nat.lt_or_ge n 2 with h | h
  · apply CoreSpec.of_call
    intro r m' hc
    rw [lvlsEqC_small p hp.cs n h] at hc; cases hc
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    exact lvlsEqC_refines p hp k s₀ a₀ dn vis fe M eb hS us vs hu hv

/-- `ConstLpsDen` (helper `defeq2-prop`) is `StoreDen.constLps`. -/
theorem constLpsDen_of (h : CoreDen) : ConstLpsDen :=
  fun dn m a vis fe M eb hS => (h dn m a vis fe M eb hS).constLps

set_option maxRecDepth 8192 in
/-- `ErecKept` (`find_proj`) from the core's write set (`CoreErec.lean`). -/
theorem erecKept_of {p : Prog} (hcl : closedA p coreErecA coreErecC coreFns = true) : ErecKept p :=
  fun _ _ _ _ _ _ hf h => callW_erec_closedT hcl (by subst hf; decide) h

/-- `BStkCap` is `CoreS.bstk` (lane `whnf2`'s landing 1). -/
theorem bstkCap_of : BStkCap := fun _ _ _ _ _ _ _ hS => hS.bstk

section knot
variable {p : Prog} (hq : KnotAllProg p)

include hq in
/-- `inst_lp` refines `instLPFast coreWalkFuel` (helper `whnf4-ilp`'s `instLP_refines`). -/
theorem KnotAllProg.instLP : InstLPOK p := instLP_refines p hq.ilw

include hq in
/-- Lane `whnf`'s `WhnfCallees` (four leaves, all proved). -/
theorem KnotAllProg.whnfC : WhnfCallees p :=
  ⟨hq.walks.instListOK, hq.instLP, strLitCtor_core p hq.str, strLitStored_core p hq.str⟩

include hq in
/-- `find_proj` and its record-pool facts. -/
theorem KnotAllProg.projC : ProjCallees p :=
  ⟨findProj_refines p hq.projp, erecKept_of hq.hcl, projFound p hq.projp⟩

include hq in
/-- Lane `whnf`'s `IotaCallees`: the walks, `find_proj`, `lit_to_ctor_if_nat` proved;
`rec_fire_levels` (`recFireLevelsOK_of`). -/
theorem KnotAllProg.iotaC : IotaCallees p :=
  ⟨hq.walks.iotaInst1OK, findProj_refines p hq.projp,
    recFireLevelsOK_of p hq.ls,
    wscoped_core hq.ws, hq.walks.lbbOK, leafGuard_core hq.lg,
    fun n s₀ a₀ dn vis fe MM eb h hS hh => litToCtorIfNat_refines p hq.delta n s₀ a₀ dn vis fe MM eb h hS hh⟩

include hq in
/-- `proof_irrel` (lane `whnf`'s `proofIrrel_refines'` over `CoreDen`). -/
theorem KnotAllProg.proofIrrel : ProofIrrelOK p := proofIrrelOK_of p hq.m2c.toIotaProg4 coreDen_of

include hq in
/-- `iota_rec_at` one level up (lane `whnf`'s `iotaRecAt_refines'`, with `major_to_ctor` from
`majorToCtor_refines'`: neither takes a slot step of this file). -/
theorem KnotAllProg.iota (n : Nat) (hk : KnotUpTo p n) : IotaRecAtOK p (n + 1) :=
  iotaRecAt_refines' p hq.iotaRec (KnotAllProg.iotaC hq) (KnotAllProg.whnfC hq) supKeep_of
    (majorToCtor_refines' p hq.m2c (KnotAllProg.iotaC hq) (KnotAllProg.proofIrrel hq) (ErecPKept.of_closed hq.hcl)
      (KnotAllProg.projC hq) hq.prop (instLP_refines p hq.ilw))
    (ErecKeptInst.of_closed hq.hcl) (ErecKeptRec.of_closed hq.hcl) (ErecKeptKnot.of_closed hq.hcl)
    n hk

include hq in
/-- Lane `whnf`'s `CoreCallees`. -/
theorem KnotAllProg.coreC : CoreCallees p :=
  { toProjCallees := KnotAllProg.projC hq, inst1 := hq.walks.inst1OK, iota := KnotAllProg.iota hq }

include hq in
/-- `reduce_proj_core` (lane `whnf`'s `reduceProjCore_refines'`). -/
theorem KnotAllProg.reduceProjCore : ReduceProjCoreH p :=
  fun n hk F hF hn s₀ a₀ dn vis fe MM eb mode d sn i c hs hsn hc' =>
    reduceProjCore_refines' p hq.core (strLitStored_core p hq.str) (strLitCtor_core p hq.str)
      (KnotAllProg.projC hq) hq.core.lsn (erecKept_of hq.hcl) n hk F hF hn s₀ a₀ dn vis fe MM eb
      mode d sn i c hs hsn hc' (supKeep_of fe)

include hq in
/-- `unfold_definition` (lane `whnf`'s `unfoldDefinition_refines'`, over `inst_lp`). -/
theorem KnotAllProg.unfold : UnfoldDefOK p :=
  fun n s₀ a₀ dn vis fe M eb e hS he =>
    unfoldDefinition_refines' p hq.delta n s₀ a₀ dn vis fe M eb e hS he hq.instLP

include hq in
/-- `const_ty_at` (lane `whnf`'s `constTyAt_refines'`, over `inst_lp`). -/
theorem KnotAllProg.constTy : ConstTyAtOK p := constTyAt_refines' p hq.body.iota hq.instLP

include hq in
/-- The knot's `whnfCore` slot one level up (lane `whnf`'s `whnfCoreSlot_step`). -/
theorem KnotAllProg.whnfCoreStep (n : Nat) (hk : KnotUpTo p n) : WhnfCoreSlot p (n + 1) :=
  whnfCoreSlot_step p hq.core (KnotAllProg.whnfC hq) (KnotAllProg.coreC hq) supKeep_of n hk

include hq in
/-- The knot's `whnf` slot one level up (`whnf_refines`, over `inst_lp`; `reduce_nat` through its
unified model). -/
theorem KnotAllProg.whnfStep (n : Nat) (hk : KnotUpTo p n) : WhnfSlot p (n + 1) :=
  whnf_refines p hq.delta hq.instLP (natOpResultOK_of_agree hq.delta.natAgree) n hk

include hq in
/-- `DefeqCallees`: the walks from `CoreWalks.lean`, the rest from `KnotCallees`. -/
theorem KnotAllProg.defeq : DefeqCallees p :=
  ⟨hasFvar_core hq.walks.abs hq.walks.hf,
    notProofFast_core hq.prop coreDen_of (constLpsDen_of coreDen_of) (findProj_refines p hq.projp) (erecKept_of hq.hcl) (projFound p hq.projp),
    isProofFast_core hq.prop coreDen_of (constLpsDen_of coreDen_of) (findProj_refines p hq.projp) (erecKept_of hq.hcl) (projFound p hq.projp),
    abs1_core hq.walks.abs hq.walks.ae, absRange_core hq.walks.ar hq.walks.are⟩

include hq in
theorem KnotAllProg.lazy : LazyCallees p :=
  ⟨hq.walks.instListOK, hq.walks.inst1OK, (KnotAllProg.defeq hq).hasFvar, natPredW_of p hq.natPred, KnotAllProg.unfold hq,
    reduceNat_of p hq.delta (natOpResultOK_of_agree hq.delta.natAgree), StoreDenotes.of_den coreDen_of⟩

include hq in
theorem KnotAllProg.stuck : StuckCallees p :=
  ⟨KnotAllProg.defeq hq, KnotAllProg.proofIrrel hq, hq.walks.inst1OK, defeqLstOK_of p hq.lst,
    lvlsEqCH_of p hq.lvc, coreDen_of, strLitStored_core p hq.str, strLitCtor_core p hq.str, supKeep_of,
    lazyDeltaStepH_of p hq.body.lazy (KnotAllProg.lazy hq), KnotAllProg.reduceProjCore hq,
    hq.instLP, hq.walks.instListOK, hq.lvc⟩

include hq in
/-- The literal callees: `nat_lit_stored`, `const_e` (lane `whnf`'s proofs), `str_lit_stored`. -/
theorem KnotAllProg.lit : InferLitCallees p :=
  ⟨fun n s₀ a₀ dn vis fe M eb hS => natLitStored_refines p hq.delta n s₀ a₀ dn vis fe M eb hS,
    strLitStored_core p hq.str,
    fun n s₀ a₀ dn vis fe M eb nm hS hnm => constE_refines p hq.delta n s₀ a₀ dn vis fe M eb nm hS hnm⟩

include hq in
/-- **`infer_proj`'s callees** (`proj_guard_rows`: `pgrOK_of`). -/
theorem KnotAllProg.projCallees : InferProjCallees p :=
  ⟨coreDen_of, findProj_refines p hq.projp, projFound p hq.projp, erecKept_of hq.hcl, hq.instLP,
    ErecPKept.of_closed hq.hcl, pgrOK_of p hq.proj (KnotAllProg.constTy hq), hq.walks.iotaInst1OK, hq.prop⟩

include hq in
theorem KnotAllProg.inferC : InferCallees p :=
  ⟨hq.walks.inst1OK, hq.walks.instListOK, (KnotAllProg.defeq hq).abstract1, (KnotAllProg.defeq hq).abstractRange,
    KnotAllProg.constTy hq, hq.lit, isEagerReduceH_of p hq.body.stuck.leaf, bstkCap_of,
    inferProj_refines p hq.proj hq.projp (KnotAllProg.projCallees hq)⟩

/-- **The knot at fuel `0`**: every L call at fuel `0` fails. -/
theorem knot_zero (p : Prog) : KnotOK p 0 where
  whnfCore := fun _ s₀ a₀ dn vis fe M eb _ _ _ _ _ _ _ _ =>
    CoreSpec.zeroLet p _ _ _ _ s₀ a₀ dn vis fe M eb _
  whnf := fun _ s₀ a₀ dn vis fe M eb _ _ _ _ _ _ _ => CoreSpec.zeroLet p _ _ _ _ s₀ a₀ dn vis fe M eb _
  infer := fun _ s₀ a₀ dn vis fe M eb _ _ _ _ _ _ _ => CoreSpec.zeroLet p _ _ _ _ s₀ a₀ dn vis fe M eb _
  inferIO := fun _ s₀ a₀ dn vis fe M eb _ _ _ _ _ _ _ =>
    CoreSpec.zeroLet p _ _ _ _ s₀ a₀ dn vis fe M eb _
  defeq := fun _ s₀ a₀ dn vis fe M eb _ _ _ _ _ _ _ _ _ =>
    CoreSpec.zeroLet p _ _ _ _ s₀ a₀ dn vis fe M eb _

include hq in
/-- **The knot one level up**: every slot at `n + 1` from the knot up to `n`. -/
@[refines_part ConRon.Arena.coreKnot "the five slots (step)"]
theorem knot_step (n : Nat) (hk : KnotUpTo p n) : KnotOK p (n + 1) :=
  ⟨KnotAllProg.whnfCoreStep hq n hk, KnotAllProg.whnfStep hq n hk, inferSlot_step p hq.infer (KnotAllProg.inferC hq) n hk,
    inferIOSlot_step p hq.infer (KnotAllProg.inferC hq) n hk,
    defeqSlot_step p hq.body ⟨KnotAllProg.stuck hq, KnotAllProg.lazy hq⟩ n hk⟩

include hq in
theorem knotUpTo_all (n : Nat) : KnotUpTo p n := by
  induction n with
  | zero => intro k hk; obtain rfl : k = 0 := by omega
            exact knot_zero p
  | succ n ih =>
    intro k hk
    by_cases h : k ≤ n
    · exact ih k h
    · obtain rfl : k = n + 1 := by omega
      exact knot_step hq n ih

include hq in
/-- **The knot at every L fuel.** -/
@[refines ConRon.Arena.coreKnot]
theorem knot_all (n : Nat) : KnotOK p n := knotUpTo_all hq n n (Nat.le_refl _)

end knot

end L.Arena
