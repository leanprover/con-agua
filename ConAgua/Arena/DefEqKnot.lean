import ConAgua.Arena.DefEqBody
import ConAgua.Arena.WhnfIotaRefine4
import ConAgua.Arena.WhnfDeltaRefine4
import ConAgua.Arena.WhnfCoreLoop

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

/-- **Every assumption the knot still makes.** -/
structure KnotCallees (p : Prog) : Prop where
  /-- Lane `whnf`'s slot steps (proved there over its inline stub bundles). -/
  whnfCoreStep : ∀ n, KnotUpTo p n → WhnfCoreSlot p (n + 1)
  whnfStep : ∀ n, KnotUpTo p n → WhnfSlot p (n + 1)
  /-- `has_fvar`, `not_proof_fast`, `is_proof_fast`, `abs_entry`, `ar_entry`, `field_sort_zero`. -/
  defeq : DefeqCallees p
  /-- Lane `whnf`'s `proofIrrel_refines` rests on `CoreS.lvl_den` (`proofIrrelOK_of`). -/
  proofIrrel : ProofIrrelOK p
  inst1 : Inst1OK p
  instList : InstListOK p
  reservedContains : ReservedContainsOK p
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
  natOpResult : NatOpResultOK p
  whnfGrows : ∀ n, WhnfGrowsUpTo p n
  store : StoreDenotes
  constTy : ConstTyAtOK p
  lit : InferLitCallees p
  bstk : BStkCallees p
  bcap : BStkCap
  proj : InferProjOK p

section knot
variable {p : Prog} (hq : KnotAllProg p) (hc : KnotCallees p)

include hq hc in
theorem KnotCallees.lazy : LazyCallees p :=
  ⟨hc.instList, hc.inst1, hc.defeq.hasFvar, hc.natPred, hc.unfold,
    reduceNat_of p hq.delta hc.natOpResult hc.whnfGrows, hc.store⟩

include hq hc in
theorem KnotCallees.stuck : StuckCallees p :=
  ⟨hc.defeq, hc.proofIrrel, hc.inst1, defeqLstOK_of p hq.lst, hc.reservedContains, hc.towerSlots,
    hc.lvlsEqC, hc.strLitSupported, hc.strLitCtor, hc.supKeep,
    lazyDeltaStepH_of p hq.body.lazy (hc.lazy hq), hc.reduceProjCore⟩

include hq hc in
theorem KnotCallees.infer : InferCallees p :=
  ⟨hc.inst1, hc.instList, hc.defeq.abstract1, hc.defeq.abstractRange, hc.constTy, hc.lit,
    isEagerReduceH_of p hq.body.stuck.leaf, hc.bstk, hc.bcap, hc.proj⟩

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
  ⟨hc.instList, hil, hc.strLitCtor, hc.strLitSupported,
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
