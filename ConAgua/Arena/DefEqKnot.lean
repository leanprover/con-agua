import ConAgua.Arena.DefEqBody
import ConAgua.Arena.WhnfIotaRefine4
import ConAgua.Arena.WhnfDeltaRefine4
import ConAgua.Arena.WhnfCoreLoop
import ConAgua.Arena.CoreWalks
import ConAgua.Arena.WhnfM2CRefine

/-!
# The knot tied (lane `defeq`)

1. **Proved specs into the hypothesis structures** (one wrapper each): `lazyDeltaStepH_of`
   (`LazyDeltaStepH` from `lazyDeltaStep_refines`), `defeqLstOK_of` (`DefeqLstOK` from
   `defeqLst_refines`), `isEagerReduceH_of` (`IsEagerReduceH` from `isEagerReduce_refines`),
   `reduceNat_of` (`LazyCallees.reduceNat` from lane `whnf`'s `reduceNat_refines'`),
   `proofIrrelOK_of` (`ProofIrrelOK` from lane `whnf`'s `proofIrrel_refines`, which rests on
   `CoreS.lvl_den`, a `sorry` there: so `ProofIrrelOK` stays a field of `KnotCallees`).
2. **The knot.** `KnotCallees p` gathers every assumption left; `knot_step`: `KnotUpTo p n →
   KnotOK p (n + 1)` from the five slot steps; `knot_all`: `KnotOK p n` at every fuel (fuel `0`:
   every L call at fuel `0` fails, `CoreSpec.zeroLet`). `whnfCallees_of` discharges lane `whnf`'s
   `WhnfCallees.inferStep`/`inferIOStep`/`defeqStep` (the slot steps themselves, no induction).
3. Lane `whnf`'s two slot steps enter `KnotCallees` as fields: `whnfCoreSlot_step` and the `whnf`
   chain are proved over that lane's stub bundles instantiated inline (`whnfCallees_stub`,
   `coreCallees_stub`, `sorry`s), so `knotWhnfCore_twin`/`knotWhnf_twin` give the fields modulo
   those `sorry`s.
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

/-- `ProofIrrelOK` from lane `whnf`'s `proofIrrel_refines` (which uses `CoreS.lvl_den`, a
`sorry`). -/
theorem proofIrrelOK_of (p : Prog) (hp : IotaProg4 p) : ProofIrrelOK p := proofIrrel_refines p hp

/-- `LazyCallees.reduceNat` from lane `whnf`'s `reduceNat_refines'` and its two assumptions. -/
theorem reduceNat_of (p : Prog) (hp : WhnfDeltaProg' p) (hno : NatOpResultOK p)
    (hg : ∀ n, WhnfGrowsUpTo p n) : ∀ n, n ≤ 2 ^ 62 → ReduceNatSpec p n :=
  fun n hn F s₀ a₀ dn vis fe MM eb mode d e hF hs he hk =>
    reduceNat_refines' p hp hno n (hg n) F s₀ a₀ dn vis fe MM eb mode d e hF hn hs he hk

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

/-- **Every assumption the knot still makes.** -/
structure KnotCallees (p : Prog) : Prop where
  /-- Lane `whnf`'s slot steps (proved there over its inline stub bundles). -/
  whnfCoreStep : ∀ n, KnotUpTo p n → WhnfCoreSlot p (n + 1)
  whnfStep : ∀ n, KnotUpTo p n → WhnfSlot p (n + 1)
  /-- `DefeqCallees` without the walks (`KnotAllProg.walks`): the `PropRead` readers and
  `field_sort_zero`. -/
  notProofFast : NotProofFastOK p
  isProofFast : IsProofFastOK p
  fieldSortZero : FieldSortZeroOK p
  /-- Lane `whnf`'s `proofIrrel_refines` rests on `CoreS.lvl_den` (`proofIrrelOK_of`). -/
  proofIrrel : ProofIrrelOK p
  towerSlots : TowerSlotsAllOK p
  lvlsEqC : LvlsEqCH p
  strLitSupported : StrLitSupportedOK p
  strLitCtor : StrLitCtorOK p
  supKeep : ∀ fe, SupKeep fe
  /-- Lane `whnf`'s `reduceProjCore_refines'` takes all of `WhnfCallees`, which holds the slot
  steps this file proves. -/
  reduceProjCore : ReduceProjCoreH p
  /-- `natPred_refines` posts `ResH`, the hypothesis `ResW`. -/
  natPred : NatPredW p
  /-- Lane `whnf`'s `unfoldDefinition_refines'` takes all of `WhnfCallees` (it uses `instLP`). -/
  unfold : UnfoldDefOK p
  whnfGrows : ∀ n, WhnfGrowsUpTo p n
  store : StoreDenotes
  constTy : ConstTyAtOK p
  bstk : BStkCallees p
  proj : InferProjOK p

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

/-- `BStkCap` is `CoreS.bstk` (lane `whnf2`'s landing 1). -/
theorem bstkCap_of : BStkCap := fun _ _ _ _ _ _ _ hS => hS.bstk

section knot
variable {p : Prog} (hq : KnotAllProg p) (hc : KnotCallees p)

include hq hc in
/-- `DefeqCallees`: the walks from `CoreWalks.lean`, the rest from `KnotCallees`. -/
theorem KnotCallees.defeq : DefeqCallees p :=
  ⟨hasFvar_core hq.walks.abs hq.walks.hf, hc.notProofFast, hc.isProofFast,
    abs1_core hq.walks.abs hq.walks.ae, absRange_core hq.walks.ar hq.walks.are, hc.fieldSortZero⟩

include hq hc in
theorem KnotCallees.lazy : LazyCallees p :=
  ⟨hq.walks.instListOK, hq.walks.inst1OK, (hc.defeq hq).hasFvar, hc.natPred, hc.unfold,
    reduceNat_of p hq.delta (natOpResultOK_of_agree hq.delta.natAgree) hc.whnfGrows, hc.store⟩

include hq hc in
theorem KnotCallees.stuck : StuckCallees p :=
  ⟨hc.defeq hq, hc.proofIrrel, hq.walks.inst1OK, defeqLstOK_of p hq.lst,
    reservedContainsOK_of p hq.rc, hc.towerSlots,
    hc.lvlsEqC, hc.strLitSupported, hc.strLitCtor, hc.supKeep,
    lazyDeltaStepH_of p hq.body.lazy (hc.lazy hq), hc.reduceProjCore⟩

include hq hc in
/-- The literal callees: `nat_lit_supported`, `const_e` (lane `whnf`'s proofs), `str_lit_supported`. -/
theorem KnotCallees.lit : InferLitCallees p :=
  ⟨fun n s₀ a₀ dn vis fe M eb hS => natLitSupported_refines p hq.delta n s₀ a₀ dn vis fe M eb hS,
    hc.strLitSupported,
    fun n s₀ a₀ dn vis fe M eb nm hS hnm => constE_refines p hq.delta n s₀ a₀ dn vis fe M eb nm hS hnm⟩

include hq hc in
theorem KnotCallees.infer : InferCallees p :=
  ⟨hq.walks.inst1OK, hq.walks.instListOK, (hc.defeq hq).abstract1, (hc.defeq hq).abstractRange,
    hc.constTy, hc.lit hq, isEagerReduceH_of p hq.body.stuck.leaf, hc.bstk, bstkCap_of, hc.proj⟩

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
  ⟨hc.whnfCoreStep n hk, hc.whnfStep n hk, inferSlot_step p hq.infer (hc.infer hq) n hk,
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

include hq hc in
/-- Lane `whnf`'s `WhnfCallees` from `KnotCallees`: its `inferStep`/`inferIOStep`/`defeqStep` are
the slot steps (no induction); `instLP` is the one stub `KnotCallees` does not carry. -/
theorem whnfCallees_of (hil : InstLPOK p) : WhnfCallees p :=
  ⟨hq.walks.instListOK, hil, hc.strLitCtor, hc.strLitSupported,
    fun n hk => inferSlot_step p hq.infer (hc.infer hq) n hk,
    fun n hk => inferIOSlot_step p hq.infer (hc.infer hq) n hk,
    fun n hk => defeqSlot_step p hq.body ⟨hc.stuck hq, hc.lazy hq⟩ n hk⟩

end knot

/-! ## Lane `whnf`'s slot steps as `KnotCallees` fields (modulo that lane's stubs) -/

/-- `KnotCallees.whnfCoreStep` from lane `whnf`'s `whnfCoreSlot_step` (proved over
`whnfCallees_stub`/`coreCallees_stub`). -/
theorem knotWhnfCore_twin (p : Prog) (hp : WhnfCoreProg p) :
    ∀ n, KnotUpTo p n → WhnfCoreSlot p (n + 1) :=
  whnfCoreSlot_step p hp

/-- `KnotCallees.whnfStep` from lane `whnf`'s `whnf_refines`, `whnfLoop_refines` and
`whnfStep_refines` (the last over `whnfCallees_stub` and that lane's `reduce_nat` stubs). -/
theorem knotWhnf_twin (p : Prog) (hp : WhnfDeltaProg' p) :
    ∀ n, KnotUpTo p n → WhnfSlot p (n + 1) := by
  intro n hk F s₀ a₀ dn vis fe MM eb mode d e hF hn2 hs he
  have hws : WhnfStepUpTo p n := fun j hj F' s a dn' vis' fe' MM' eb' mode' d' e' hF' hs' he' hk' =>
    whnfStep_refines p hp j F' s a dn' vis' fe' MM' eb' mode' d' e' hF' (by omega) hs' he' hk'
  exact whnf_refines p hp.toWhnfDeltaProg n (by omega) hk
    (whnfLoop_refines p hp.toWhnfDeltaProg n hws) F s₀ a₀ dn vis fe MM eb mode d e hF hn2 hs he

end L.Arena
