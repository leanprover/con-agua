module

public import ConAgua.Arena.CoreDen
public import ConAgua.Arena.DefEqLeaves
public import ConAgua.Arena.InferBodyLet
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
public import ConAgua.Verdict.WhnfModels7E
public import ConAgua.Arena.CoreLevels
public import ConAgua.Arena.IndIface

@[expose] public section

/-!
# The stuck and irrelevance side of `DefEq.lean`: `prop_irrel` (lane `defeq`, helper `defeq-top`)

The callW pattern (`InferBodyLet.lean`): a word model of each function with its callees through
their runs (`callW`), the L spec by `vcgen` + `simp_all`, the refinement from the callees'
specs, threaded through the twin's `do` blocks by `coreRef_bind`. Bodies at L fuel `n + 1`
assume `KnotUpTo p n` and refine the twin at `coreKnot (decMode mode) (decEager mode) fe id F`, `F ≥ n`.

Callees with no proof yet are hypotheses (`StuckCallees`): `not_proof_fast`/`is_proof_fast`
(`DefeqCallees`), `proof_irrel` (`ProofIrrelOK`, a `sorry` in `WhnfIota.lean`).

* `prop_irrel` refines `propIrrel` (`propIrrel_refines`): the slow arm is `proofIrrel` verbatim
  (`propIrrel_eq`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-- What the stuck side's specs need of a program. -/
structure StuckProg (p : Prog) : Prop where
  leaf : DefEqLeafProg p
  body : InferBodyProg p
  propIrrel : p.lookup "prop_irrel" = some propIrrelL
  etaCert : p.lookup "eta_cert" = some etaCertL
  etaCertBody : p.lookup "eta_cert_body" = some etaCertBodyL
  etaCertTy : p.lookup "eta_cert_ty" = some etaCertTyL
  etaCtorShape : p.lookup "eta_ctor_shape" = some etaCtorShapeL
  ers : p.lookup "er_slice_eq" = some erSliceEqL
  setTail : p.lookup "struct_eta_cert_tail" = some structEtaCertTailL
  setGo : p.lookup "struct_eta_cert_go" = some structEtaCertGoL
  setWtb : p.lookup "struct_eta_cert_wtb" = some structEtaCertWtbL
  setWith : p.lookup "struct_eta_cert_with" = some structEtaCertWithL
  setCert : p.lookup "struct_eta_cert" = some structEtaCertL
  suTail : p.lookup "struct_unit_tail" = some structUnitTailL
  suHead : p.lookup "struct_unit_head" = some structUnitHeadL
  sunit : p.lookup "struct_unit_cert" = some structUnitCertL
  stuckIrrel : p.lookup "stuck_irrel" = some stuckIrrelL
  stuckStr : p.lookup "stuck_str" = some stuckStrL
  stuckAppCong : p.lookup "stuck_app_cong" = some stuckAppCongL
  stuckApp : p.lookup "stuck_app" = some stuckAppL
  stuckRest : p.lookup "stuck_rest" = some stuckRestL
  defeqStuck : p.lookup "defeq_stuck" = some defeqStuckL
  eview : p.lookup "e_view" = some L.Ind.eView
  ldprExit : p.lookup "ldpr_exit" = some ldprExitL
  ldpr : p.lookup "lazy_delta_proj_reduction" = some lazyDeltaProjReductionL
  projPair : p.lookup "defeq_proj_pair" = some defeqProjPairL
  defeqTail : p.lookup "defeq_tail" = some defeqTailL

/-- `defeq_lst(mode, vis, d, ao, an, bo, bn)` refines the twin's `defEqList` on two stack slices
below the top (helper `defeq-mid` proves it; a hypothesis here). -/
def DefeqLstOK (p : Prog) : Prop :=
  ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
  ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d ao an bo bn : Word) (xs ys : Array EIdx),
    SlotPre s₀ a₀ dn vis fe M eb mode → SpineR s₀.mem ao an xs → SpineR s₀.mem bo bn ys →
    ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat → bo.toNat + bn.toNat ≤ (spTop s₀.mem).toNat →
    CoreSpec p (n + 1) "defeq_lst" [mode, vis, d, ao, an, bo, bn]
      (defEqList (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat xs.toList ys.toList) decBool s₀ a₀ dn
      vis fe M eb

/-- The twin's reserved-name test: `reservedBasisNames`, then `List.contains`. -/
def reservedContainsT (n : NIdx) : AM Bool := do
  let rs ← reservedBasisNames
  pure (rs.contains n)

/-- `reserved_contains(x)` (lane `whnf`'s `WhnfIota.lean`, no spec yet) refines
`reservedContainsT`. -/
def ReservedContainsOK (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb x : Word), CoreS dn s₀.mem a₀ vis fe M eb → HW x →
    CoreSpec p n "reserved_contains_w" [x] (reservedContainsT (decI x)) decBool s₀ a₀ dn vis fe M eb

/-- `lvls_eq_c(us, vs)` refines `lvlsEq?` at two level lists that read back (lane `whnf`'s
`lvlsEqC_refines`; `lvlsEqCH_of`, `DefEqKnot.lean`). The callers' lists are stored constants'
(`StoreDen.constLs`). -/
def LvlsEqCH (p : Prog) : Prop :=
  ∀ (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb us vs : Word), CoreS dn s₀.mem a₀ vis fe M eb → HW us → HW vs →
    (∃ lu, denoteLs a₀.store.lss (decI us) = some lu) →
    (∃ lv, denoteLs a₀.store.lss (decI vs) = some lv) →
    CoreSpec p n "lvls_eq_c" [us, vs] (lvlsEq? (decI us) (decI vs)) (fun r => decO (r.headD 0))
      s₀ a₀ dn vis fe M eb


/-- A `DeltaStepA` result: `(k, a, b)`, `0` `.cont a b`, `1` `.eq`, `2` `.diff`, else `.unknown`. -/
def decDSs (r : List Word) : DeltaStepA :=
  if r.headD 0 = 0 then .cont (decE (r.tail.headD 0)) (decE (r.tail.tail.headD 0))
  else if r.headD 0 = 1 then .eq
  else if r.headD 0 = 2 then .diff
  else .unknown

/-- The three result words are handle words. -/
def ResW3 (r : List Word) : Prop := HW (r.headD 0) ∧ HW (r.tail.headD 0) ∧ HW (r.tail.tail.headD 0)

/-- `lazy_delta_step` refines `lazyDeltaStep` at the knot (helper `defeq-mid`'s; a hypothesis). -/
def LazyDeltaStepH (p : Prog) : Prop :=
  ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
  ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d a b : Word), SlotPre s₀ a₀ dn vis fe M eb mode → HW a → HW b →
    d.toNat < 2 ^ 63 →
    CoreSpec p (n + 1) "lazy_delta_step" [mode, vis, d, a, b]
      (lazyDeltaStep (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE a) (decE b))
      decDSs s₀ a₀ dn vis fe M eb ResW3

/-- `reduce_proj_core` refines `reduceProjCore` (lane `whnf`'s `reduceProjCore_refines'`; plugged in
`DefEqKnot.lean`, `KnotCallees.reduceProjCore`). -/
def ReduceProjCoreH (p : Prog) : Prop :=
  ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
  ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d sn i c : Word), SlotPre s₀ a₀ dn vis fe MM eb mode → HW sn → HW c →
    CoreSpec p (n + 1) "reduce_proj_core" [mode, vis, d, sn, i, c]
      (reduceProjCore (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decI sn) i.toNat
        (decE c)) decOptR s₀ a₀ dn vis fe MM eb ResW

/-- `proof_irrel` refines `proofIrrel` (the shape of lane `whnf`'s `proofIrrel_refines`,
`WhnfIotaRefine4.lean`). -/
def ProofIrrelOK (p : Prog) : Prop :=
  ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
  ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d a b : Word), CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 →
    eb = (mode >>> 1) &&& 1 → HW a → HW b →
    CoreSpec p (n + 1) "proof_irrel" [mode, vis, d, a, b]
      (proofIrrel (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE a) (decE b)) decBool s₀ a₀ dn
      vis fe MM eb

/-- `proof_irrel`'s error claim at fuel `N + 1` (the premises of `ProofIrrelOK`). -/
def ProofIrrelWE (p : Prog) : Prop :=
  ∀ (n : Nat), KnotUpTo p n → KnotUpToE p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d a b : Word), CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 →
    eb = (mode >>> 1) &&& 1 → HW a → HW b →
    CoreSpecE p (n + 1) "proof_irrel" [mode, vis, d, a, b]
      (proofIrrel (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE a) (decE b)) s₀ a₀

/-- **What the error claims of `major_to_ctor`'s pieces and of `prop_irrel` assume** at L fuel
`N + 1`: the knot's slots' claims up to `N`, `proof_irrel`'s. -/
structure M2CCtxE (p : Prog) (N : Nat) : Prop where
  knot : KnotUpToE p N
  pirr : ProofIrrelWE p

theorem M2CCtxE.mono {p : Prog} {N N' : Nat} (h : M2CCtxE p N) (hN : N' ≤ N) : M2CCtxE p N' :=
  ⟨h.knot.mono hN, h.pirr⟩

/-- The callees the stuck side assumes. -/
structure StuckCallees (p : Prog) : Prop where
  defeq : DefeqCallees p
  proofIrrel : ProofIrrelOK p
  inst1 : Inst1OK p
  defeqLst : DefeqLstOK p
  reservedContains : ReservedContainsOK p
  towerSlots : TowerSlotsAllOK p
  lvlsEqC : LvlsEqCH p
  /-- Stored levels read back (`StoreDen.lean`). -/
  den : CoreDen
  strLitStored : StrLitStoredOK p
  strLitCtor : StrLitCtorOK p
  /-- `strLitStored` keeps every stored node's view (`supKeep_of`, `StrLitKeep.lean`). -/
  supKeep : ∀ fe, SupKeep fe
  lazyDeltaStep : LazyDeltaStepH p
  reduceProjCore : ReduceProjCoreH p

/-- `proof_irrel` at every L fuel up to `n + 1` from the knot up to `n`. -/
theorem proofIrrel_at (p : Prog) (hc : StuckCallees p) :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
      (MM : ModeMaps) (eb mode d a b : Word), CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 →
      eb = (mode >>> 1) &&& 1 → HW a → HW b →
      CoreSpec p n "proof_irrel" [mode, vis, d, a, b]
        (proofIrrel (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE a) (decE b)) decBool s₀ a₀
        dn vis fe MM eb
  | 0, _, _, _, _, s₀, a₀, dn, vis, fe, MM, eb, _, _, _, _, _, _, _, _, _ =>
      CoreSpec.zeroLet p _ _ _ _ s₀ a₀ dn vis fe MM eb _
  | n + 1, hk, F, hF, hn, s₀, a₀, dn, vis, fe, MM, eb, mode, d, a, b, hS, hm, heb, ha, hb =>
      hc.proofIrrel n (hk.mono (by omega)) F (by omega) (by omega) s₀ a₀ dn vis fe MM eb mode d a b
        hS hm heb ha hb

/-! ## `prop_irrel` -/

/-- **`propIrrel`, its slow arm folded into `proofIrrel`** (the twin's text is the same). -/
theorem propIrrel_eq (r : CoreFnsA) (fe : IFEnv) (d : Nat) (a b : EIdx) :
    propIrrel r fe d a b = (do
      let x ← notProofFast fe coreWalkFuel a
      let y ← notProofFast fe coreWalkFuel b
      if x || y then pure false
      else do
        let z ← isProofFast fe coreWalkFuel a
        let w ← isProofFast fe coreWalkFuel b
        if z && w then pure true else proofIrrel r fe d a b) := rfl

theorem decBool_eq_true {r : List Word} (h : r.headD 0 ≠ 0) : decBool r = true := by
  simp only [decBool, bne_iff_ne]; exact h

theorem decBool_eq_false {r : List Word} (h : r.headD 0 = 0) : decBool r = false := by
  simp only [decBool, bne_eq_false_iff_eq]; exact h

/-- **`prop_irrel` refines `propIrrel`, both outcomes**: the errors are `proof_irrel`'s. -/
theorem pi_ref (p : Prog) (hc : StuckCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) :
    RefE (M2CCtxE p n) (piE p (n + 1) s₀.mem mode vis d a b)
      (propIrrel (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE a) (decE b)) a₀
      (CorePost decBool dn s₀.mem vis fe M eb ResH) := by
  simp only [piE]
  rw [propIrrel_eq]
  refine RefE.bind_callW (fun _ => rfl) (hc.defeq.notProofFast n s₀ a₀ dn vis fe M eb a hs.rel ha)
    fun r₁ m₁ _ h₁ => RefE.after_core (w := id) h₁ fun M₁ hS₁ _ => ?_
  dsimp only [piE.k_not_proof_fast]
  refine RefE.bind_callW (fun _ => rfl) (hc.defeq.notProofFast n ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb b
      hS₁ hb)
    fun r₂ m₂ _ h₂ => RefE.after_core (w := id) h₂ fun M₂ hS₂ _ => ?_
  dsimp only [piE.k_not_proof_fast_2]
  by_cases h12 : r₁.headD 0 ≠ 0 ∨ r₂.headD 0 ≠ 0
  · rw [ite_eq_left h12]
    have hx : (decBool r₁ || decBool r₂) = true := by
      rcases h12 with h | h <;> simp [decBool_eq_true h]
    rw [hx]
    exact RefE.ret rfl (CorePost.ret hS₂ rfl hw0)
  rw [ite_eq_right h12]
  simp only [not_or, ne_eq, Decidable.not_not] at h12
  have hx : (decBool r₁ || decBool r₂) = false := by
    simp [decBool_eq_false h12.1, decBool_eq_false h12.2]
  rw [hx]
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine RefE.bind_callW (fun _ => rfl) (hc.defeq.isProofFast n ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb a
      hS₂ ha)
    fun r₃ m₃ _ h₃ => RefE.after_core (w := id) h₃ fun M₃ hS₃ _ => ?_
  dsimp only [piE.k_is_proof_fast]
  refine RefE.bind_callW (fun _ => rfl) (hc.defeq.isProofFast n ⟨m₃, Locals.init []⟩ _ dn vis fe M₃ eb b
      hS₃ hb)
    fun r₄ m₄ _ h₄ => RefE.after_core (w := id) h₄ fun M₄ hS₄ _ => ?_
  dsimp only [piE.k_is_proof_fast_2]
  by_cases h34 : r₃.headD 0 ≠ 0 ∧ r₄.headD 0 ≠ 0
  · rw [ite_eq_left h34]
    have hx : (decBool r₃ && decBool r₄) = true := by
      simp [decBool_eq_true h34.1, decBool_eq_true h34.2]
    rw [hx]
    exact RefE.ret rfl (CorePost.ret hS₄ rfl hw1)
  rw [ite_eq_right h34]
  have hx : (decBool r₃ && decBool r₄) = false := by
    by_cases h3 : r₃.headD 0 = 0
    · simp [decBool_eq_false h3]
    · have h4 : r₄.headD 0 = 0 := Classical.byContradiction fun h4 => h34 ⟨h3, h4⟩
      simp [decBool_eq_false h4]
  rw [hx]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [← bind_pure (proofIrrel _ _ _ _ _)]
  refine RefE.bind_callE (fun _ => rfl) (proofIrrel_at p hc n hk F hF hn ⟨m₄, Locals.init []⟩ _ dn vis fe
      M₄ eb
      mode d a b hS₄ hs.mode4 hs.eb_mode ha hb)
    (fun hG => CoreSpecE.of_runs fun _ c5 => by
      cases n with
      | zero =>
        obtain ⟨e', he', h0⟩ := callE_zero p "proof_irrel" [mode, vis, d, a, b] m₄
        rw [c5] at he'; cases he'; exact ErrClaim.of_cls0 h0
      | succ N =>
      exact CoreSpecE.of_callE (hG.pirr N (hk.mono (Nat.le_succ N)) (hG.knot.mono (Nat.le_succ N)) F
        (by omega) (by omega) ⟨m₄, Locals.init []⟩ _ dn vis fe M₄ eb mode d a b hS₄ hs.mode4 hs.eb_mode
        ha hb) c5)
    fun _ _ _ h => RefE.ret rfl ⟨h.after, rfl, h.resOk⟩

/-- **`prop_irrel` refines `propIrrel`** at the knot, from the head readers' specs and
`proof_irrel`'s (`pi_ref`'s ok half). -/
@[refines ConRon.Arena.propIrrel]
theorem propIrrel_refines (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) :
    CoreSpec p (n + 1) "prop_irrel" [mode, vis, d, a, b]
      (propIrrel (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE a) (decE b)) decBool
      s₀ a₀ dn vis fe M eb :=
  RefE.coreSpec (piE_spec p hq.propIrrel (n + 1) s₀ mode vis d a b)
    (pi_ref p hc n hk F s₀ a₀ dn vis fe M eb mode d a b hF hn hs ha hb)

end L.Arena
