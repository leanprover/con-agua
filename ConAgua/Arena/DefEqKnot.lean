import ConAgua.Arena.DefEqBody
import ConAgua.Arena.WhnfIotaRefine4
import ConAgua.Arena.WhnfDeltaRefine4
import ConAgua.Arena.WhnfCoreLoop
import ConAgua.Arena.CoreWalks
import ConAgua.Arena.WhnfM2CRefine
import ConAgua.Arena.InferFieldSort
import ConAgua.Arena.InferFieldSortNat
import ConAgua.Arena.WhnfIotaRecRefine
import ConAgua.Arena.PropReadRefine4
import ConAgua.Arena.InferProj2
import ConAgua.Arena.StrLitSup
import ConAgua.Arena.StrLitCtor
import ConAgua.Arena.StrLitKeep
import ConAgua.Arena.WhnfProjRefine3
import ConAgua.Arena.WhnfIotaRecRefine3
import ConAgua.Arena.WalkCore

/-!
# The knot tied (lane `defeq`)

1. **Proved specs into the hypothesis structures** (one wrapper each): `lazyDeltaStepH_of`
   (`LazyDeltaStepH` from `lazyDeltaStep_refines`), `defeqLstOK_of` (`DefeqLstOK` from
   `defeqLst_refines`), `isEagerReduceH_of` (`IsEagerReduceH` from `isEagerReduce_refines`),
   `reduceNat_of` (`LazyCallees.reduceNat` from lane `whnf`'s `reduceNat_refines'`),
   `proofIrrelOK_of` (`ProofIrrelOK` from lane `whnf`'s `proofIrrel_refines'` over `CoreDen`).
2. **The knot.** `KnotCallees p` gathers every assumption left; `knot_step`: `KnotUpTo p n →
   KnotOK p (n + 1)` from the five slot steps; `knot_all`: `KnotOK p n` at every fuel (fuel `0`:
   every L call at fuel `0` fails, `CoreSpec.zeroLet`).
3. **Lane `whnf`'s bundles from real proofs** (helper `whnf4-knot`): `WhnfCallees`
   (`KnotCallees.whnfC`), `ProjCallees` (`projC`), `IotaCallees` (`iotaC`) and `CoreCallees`
   (`coreC`, its `iota` field lane `whnf`'s `iotaRecAt_refines'`) are built from the walks, the
   string-literal and projection proofs and the remaining `KnotCallees` leaves; none of them uses a
   slot step of this file. Lane `whnf`'s two slot steps then come from its primed proofs over these
   bundles: `whnfCoreSlot_step` (`KnotCallees.whnfCoreStep`) and the `whnf` chain over
   `whnfStep_refines'` (`KnotCallees.whnfStep`).
4. **`fire_ok` from `CoreDen`** (helper `whnf4-leaves`): `KnotCallees.fireOk` is lane `whnf3`'s
   `fireOk_refines` with `ProjSortDen`/`FireDen` from `StoreDen` (`fireOk_core`).
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
  rc : p.lookup "reserved_contains_w" = some reservedContainsL
  fsz : FieldSortZeroProg p
  natPred : NatPredProg p
  lvc : LvlCacheProg p
  prop : PropReadProg p
  proj : InferProjProg p
  str : StrLitProg p
  projp : ProjProg p
  /-- `fire_ok` and its callees (`pin_word`, the level cache, `lvl_eq_c`'s text). -/
  fire : FireProg p
  /-- The core's write set leaves `EREC` alone (lane `whnf3`'s `CoreErec.lean`). -/
  hcl : closedA p coreErecA coreErecC coreFns = true
  /-- Lane `whnf`'s `whnf_core` family, the ι side (`iota_rec_at`, `major_to_ctor`) and the two
  walks `wscoped_bfast`, `leaf_guard`. -/
  core : WhnfCoreProg p
  iotaRec : IotaRecProg' p
  m2c : M2CProg' p
  ws : WsProg p
  lg : LgProg p

/-- **Every assumption the knot still makes**: leaf facts with no proof yet, plus `den` and
`instLP`. -/
structure KnotCallees (p : Prog) : Prop where
  /-- Stored levels read back under `CoreS` (`StoreDen.lean`; to become a field of `CoreS`). -/
  den : CoreDen
  /-- `inst_lp` (lane `whnf3`'s `instLPFast` walk). -/
  instLP : InstLPOK p
  /-- `caps_never_zero`, `rec_fire_levels` under `CoreS` (helper `whnf3-lp` proved them at
  `ArenaD`, on `StoreWF` and the readback caches, which `CoreS` does not carry: D23; the
  universe arguments must read back at the call, which `CoreAfter` cannot carry from the
  recursor head's view without the store's growth `Ext`; DESIGN.md, helper `whnf4-leaves`). -/
  capsNeverZero : CapsNeverZeroOK p
  recFireLevels : RecFireLevelsOK p
  /-- A level-list comparison that runs compares lists that read back (`WhnfIotaRecRefine.lean`;
  the second list is `rec_fire_levels`' interned result: `StoreWF` again). -/
  lvlsEqDen : LvlsEqDen p

/-- `reserved_contains_w` refines `reservedContainsT` under `CoreS` (lane `whnf2`'s
`callW_reservedContains`: memory unchanged, the pins' reserved list). -/
theorem reservedContainsOK_of (p : Prog) (hp : p.lookup "reserved_contains_w" = some reservedContainsL) :
    ReservedContainsOK p := by
  intro n s₀ a₀ dn vis fe M eb x hS hx
  apply CoreSpec.of_call
  intro r m' hc
  obtain ⟨rfl, l, hl, hcont, hres⟩ := callW_reservedContains p hp n s₀.mem a₀ hS.pins x hx r m' hc
  rw [reservedBasisNames_run hS.pins] at hl
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj hl)
  exact coreRef_pure hS (reservedContainsT_run hS.pins _) (by rw [hcont]; rfl) hres

/-- `LvlsEqCH` from lane `whnf`'s `lvlsEqC_refines` (fuel below two: no run). -/
theorem lvlsEqCH_of (p : Prog) (hp : LvlCacheProg p) : LvlsEqCH p := by
  intro n s₀ a₀ dn vis fe M eb us vs hS hu hv ⟨lu, hlu⟩ ⟨lv, hlv⟩
  rcases Nat.lt_or_ge n 2 with h | h
  · apply CoreSpec.of_call
    intro r m' hc
    rw [lvlsEqC_small p hp.cs n h] at hc; cases hc
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    exact lvlsEqC_refines p hp k s₀ a₀ dn vis fe M eb hS us vs hu hv lu lv hlu hlv

/-- `ConstLpsDen` (helper `defeq2-prop`) is `StoreDen.constLps`. -/
theorem constLpsDen_of (h : CoreDen) : ConstLpsDen :=
  fun dn m a vis fe M eb hS => (h dn m a vis fe M eb hS).constLps

set_option maxRecDepth 8192 in
/-- `ErecKept` (`find_proj`, `fire_ok`) from the core's write set (`CoreErec.lean`). -/
theorem erecKept_of {p : Prog} (hcl : closedA p coreErecA coreErecC coreFns = true) : ErecKept p :=
  fun _ _ _ _ _ _ hf h => callW_erec_closed hcl (by rcases hf with rfl | rfl <;> decide) h

set_option maxRecDepth 8192 in
/-- `ErecKeptProj` (`lvl_eq_c`, `field_sort_zero`) from the core's write set. -/
theorem erecKeptProj_of {p : Prog} (hcl : closedA p coreErecA coreErecC coreFns = true) :
    ErecKeptProj p :=
  fun _ _ _ _ _ _ hf h => callW_erec_closed hcl (by rcases hf with rfl | rfl <;> decide) h

/-- `BStkCap` is `CoreS.bstk` (lane `whnf2`'s landing 1). -/
theorem bstkCap_of : BStkCap := fun _ _ _ _ _ _ _ hS => hS.bstk

section knot
variable {p : Prog} (hq : KnotAllProg p) (hc : KnotCallees p)

include hq hc in
/-- Lane `whnf`'s `WhnfCallees` (four leaves, all proved). -/
theorem KnotCallees.whnfC : WhnfCallees p :=
  ⟨hq.walks.instListOK, hc.instLP, strLitCtor_core p hq.str, strLitSupported_core p hq.str⟩

include hq hc in
/-- `fire_ok` (lane `whnf3`'s `fireOk_refines` over `CoreDen`, helper `whnf4-leaves`). -/
theorem KnotCallees.fireOk : FireOkOK p := fireOk_core p hq.fire (fieldSortZero_core p hq.fsz) hc.den

include hq hc in
/-- `find_proj`, `fire_ok` and their record-pool facts. -/
theorem KnotCallees.projC : ProjCallees p :=
  ⟨findProj_refines p hq.projp, hc.fireOk hq, erecKept_of hq.hcl, projFound p hq.projp⟩

include hq hc in
/-- Lane `whnf`'s `IotaCallees`: the walks, `find_proj`, `lit_to_ctor_if_nat` proved; `fire_ok`,
`caps_never_zero`, `rec_fire_levels` from `KnotCallees`. -/
theorem KnotCallees.iotaC : IotaCallees p :=
  ⟨hq.walks.iotaInst1OK, findProj_refines p hq.projp, hc.fireOk hq, hc.capsNeverZero, hc.recFireLevels,
    wscoped_core hq.ws, hq.walks.lbbOK, leafGuard_core hq.lg,
    fun n s₀ a₀ dn vis fe MM eb h hS hh => litToCtorIfNat_refines p hq.delta n s₀ a₀ dn vis fe MM eb h hS hh⟩

include hq hc in
/-- `proof_irrel` (lane `whnf`'s `proofIrrel_refines'` over `CoreDen`). -/
theorem KnotCallees.proofIrrel : ProofIrrelOK p := proofIrrelOK_of p hq.m2c.toIotaProg4 hc.den

include hq hc in
/-- `iota_rec_at` one level up (lane `whnf`'s `iotaRecAt_refines'`, with `major_to_ctor` from
`majorToCtor_refines'`: neither takes a slot step of this file). -/
theorem KnotCallees.iota (n : Nat) (hk : KnotUpTo p n) : IotaRecAtOK p (n + 1) :=
  iotaRecAt_refines' p hq.iotaRec (hc.iotaC hq) (hc.whnfC hq) supKeep_of
    (majorToCtor_refines' p hq.m2c (hc.iotaC hq) (hc.proofIrrel hq) (ErecKeptKnot.of_closed hq.hcl)
      (hc.projC hq))
    (ErecKeptInst.of_closed hq.hcl) (ErecKeptRec.of_closed hq.hcl) (ErecKeptKnot.of_closed hq.hcl)
    hc.lvlsEqDen n hk

include hq hc in
/-- Lane `whnf`'s `CoreCallees`. -/
theorem KnotCallees.coreC : CoreCallees p :=
  { toProjCallees := hc.projC hq, inst1 := hq.walks.inst1OK, iota := hc.iota hq }

include hq hc in
/-- `reduce_proj_core` (lane `whnf`'s `reduceProjCore_refines'`). -/
theorem KnotCallees.reduceProjCore : ReduceProjCoreH p :=
  fun n hk F hF hn s₀ a₀ dn vis fe MM eb mode d sn i c hs hsn hc' =>
    reduceProjCore_refines' p hq.core (strLitSupported_core p hq.str) (strLitCtor_core p hq.str)
      (hc.projC hq) hq.core.lsn (erecKept_of hq.hcl) n hk F hF hn s₀ a₀ dn vis fe MM eb
      mode d sn i c hs hsn hc' (supKeep_of fe)

include hq hc in
/-- `unfold_definition` (lane `whnf`'s `unfoldDefinition_refines'`, over `inst_lp`). -/
theorem KnotCallees.unfold : UnfoldDefOK p :=
  fun n s₀ a₀ dn vis fe M eb e hS he =>
    unfoldDefinition_refines' p hq.delta n s₀ a₀ dn vis fe M eb e hS he hc.instLP

include hq hc in
/-- `const_ty_at` (lane `whnf`'s `constTyAt_refines'`, over `inst_lp`). -/
theorem KnotCallees.constTy : ConstTyAtOK p := constTyAt_refines' p hq.body.iota hc.instLP

include hq hc in
/-- The knot's `whnfCore` slot one level up (lane `whnf`'s `whnfCoreSlot_step`). -/
theorem KnotCallees.whnfCoreStep (n : Nat) (hk : KnotUpTo p n) : WhnfCoreSlot p (n + 1) :=
  whnfCoreSlot_step p hq.core (hc.whnfC hq) (hc.coreC hq) supKeep_of n hk

include hq hc in
/-- The knot's `whnf` slot one level up: lane `whnf`'s `whnf_refines`, `whnfLoop_refines` and
`whnfStep_refines'` (over `inst_lp`; `reduce_nat` is `reduceNat_refines`). -/
theorem KnotCallees.whnfStep (n : Nat) (hk : KnotUpTo p n) : WhnfSlot p (n + 1) := by
  intro F s₀ a₀ dn vis fe MM eb mode d e hF hn2 hs he
  have hws : WhnfStepUpTo p n := fun j hj F' s a dn' vis' fe' MM' eb' mode' d' e' hF' hs' he' hk' =>
    whnfStep_refines' p hq.delta hc.instLP j (fun k _ => reduceNat_refines p hq.delta k) F' s a dn'
      vis' fe' MM' eb' mode' d' e' hF' (by omega) hs' he' hk'
  exact whnf_refines p hq.delta.toWhnfDeltaProg n (by omega) hk
    (whnfLoop_refines p hq.delta.toWhnfDeltaProg n hws) F s₀ a₀ dn vis fe MM eb mode d e hF hn2 hs he

include hq hc in
/-- `DefeqCallees`: the walks from `CoreWalks.lean`, the rest from `KnotCallees`. -/
theorem KnotCallees.defeq : DefeqCallees p :=
  ⟨hasFvar_core hq.walks.abs hq.walks.hf,
    notProofFast_core hq.prop hc.den (constLpsDen_of hc.den) (findProj_refines p hq.projp) (erecKept_of hq.hcl) (projFound p hq.projp),
    isProofFast_core hq.prop hc.den (constLpsDen_of hc.den) (findProj_refines p hq.projp) (erecKept_of hq.hcl) (projFound p hq.projp),
    abs1_core hq.walks.abs hq.walks.ae, absRange_core hq.walks.ar hq.walks.are, fieldSortZero_core p hq.fsz⟩

include hq hc in
theorem KnotCallees.lazy : LazyCallees p :=
  ⟨hq.walks.instListOK, hq.walks.inst1OK, (hc.defeq hq).hasFvar, natPredW_of p hq.natPred, hc.unfold hq,
    reduceNat_of p hq.delta (natOpResultOK_of_agree hq.delta.natAgree), StoreDenotes.of_den hc.den⟩

include hq hc in
theorem KnotCallees.stuck : StuckCallees p :=
  ⟨hc.defeq hq, hc.proofIrrel hq, hq.walks.inst1OK, defeqLstOK_of p hq.lst,
    reservedContainsOK_of p hq.rc,
    towerSlotsAll_refines' p hq.body.iota (findProj_refines p hq.projp) (projFound p hq.projp),
    lvlsEqCH_of p hq.lvc, hc.den, strLitSupported_core p hq.str, strLitCtor_core p hq.str, supKeep_of,
    lazyDeltaStepH_of p hq.body.lazy (hc.lazy hq), hc.reduceProjCore hq⟩

include hq in
/-- The literal callees: `nat_lit_supported`, `const_e` (lane `whnf`'s proofs), `str_lit_supported`. -/
theorem KnotAllProg.lit : InferLitCallees p :=
  ⟨fun n s₀ a₀ dn vis fe M eb hS => natLitSupported_refines p hq.delta n s₀ a₀ dn vis fe M eb hS,
    strLitSupported_core p hq.str,
    fun n s₀ a₀ dn vis fe M eb nm hS hnm => constE_refines p hq.delta n s₀ a₀ dn vis fe M eb nm hS hnm⟩

include hq hc in
theorem KnotCallees.infer : InferCallees p :=
  ⟨hq.walks.inst1OK, hq.walks.instListOK, (hc.defeq hq).abstract1, (hc.defeq hq).abstractRange,
    hc.constTy hq, hq.lit, isEagerReduceH_of p hq.body.stuck.leaf, bstkCap_of,
    inferProj_refines p hq.proj ⟨hc.den, (findProj_refines p hq.projp), (projFound p hq.projp), erecKept_of hq.hcl, hc.instLP, erecKeptProj_of hq.hcl⟩⟩

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

include hq hc in
/-- **The knot one level up**: every slot at `n + 1` from the knot up to `n`. -/
@[refines_part ConRon.Arena.coreKnot "the five slots (step)"]
theorem knot_step (n : Nat) (hk : KnotUpTo p n) : KnotOK p (n + 1) :=
  ⟨hc.whnfCoreStep hq n hk, hc.whnfStep hq n hk, inferSlot_step p hq.infer (hc.infer hq) n hk,
    inferIOSlot_step p hq.infer (hc.infer hq) n hk,
    defeqSlot_step p hq.body ⟨hc.stuck hq, hc.lazy hq⟩ n hk⟩

include hq hc in
theorem knotUpTo_all (n : Nat) : KnotUpTo p n := by
  induction n with
  | zero => intro k hk; obtain rfl : k = 0 := by omega
            exact knot_zero p
  | succ n ih =>
    intro k hk
    by_cases h : k ≤ n
    · exact ih k h
    · obtain rfl : k = n + 1 := by omega
      exact knot_step hq hc n ih

include hq hc in
/-- **The knot at every L fuel.** -/
@[refines_part ConRon.Arena.coreKnot "the five slots"]
theorem knot_all (n : Nat) : KnotOK p n := knotUpTo_all hq hc n n (Nat.le_refl _)

end knot

end L.Arena
