import ConAgua.Arena.CoreDen
import ConAgua.Arena.DefEqLeaves
import ConAgua.Arena.InferBodyLet
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr

/-!
# The stuck and irrelevance side of `DefEq.lean`: `prop_irrel` (lane `defeq`, helper `defeq-top`)

The callW pattern (`InferBodyLet.lean`): a word model of each function with its callees through
their runs (`callW`), the L spec by `vcgen` + `simp_all`, the refinement from the callees'
specs, threaded through the twin's `do` blocks by `coreRef_bind`. Bodies at L fuel `n + 1`
assume `KnotUpTo p n` and refine the twin at `coreKnot (decMode mode) fe id F`, `F ≥ n`.

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
      (defEqList (coreKnot (decMode mode) fe id F) fe d.toNat xs.toList ys.toList) decBool s₀ a₀ dn
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
      (lazyDeltaStep (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b))
      decDSs s₀ a₀ dn vis fe M eb ResW3

/-- `reduce_proj_core` refines `reduceProjCore` (lane `whnf`'s `reduceProjCore_refines'`; plugged in
`DefEqKnot.lean`, `KnotCallees.reduceProjCore`). -/
def ReduceProjCoreH (p : Prog) : Prop :=
  ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
  ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d sn i c : Word), SlotPre s₀ a₀ dn vis fe MM eb mode → HW sn → HW c →
    CoreSpec p (n + 1) "reduce_proj_core" [mode, vis, d, sn, i, c]
      (reduceProjCore (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI sn) i.toNat
        (decE c)) decOptR s₀ a₀ dn vis fe MM eb ResW

/-- `proof_irrel` refines `proofIrrel` (the shape of lane `whnf`'s `proofIrrel_refines`,
`WhnfIotaRefine4.lean`). -/
def ProofIrrelOK (p : Prog) : Prop :=
  ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
  ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d a b : Word), CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 →
    eb = (mode >>> 1) &&& 1 → HW a → HW b →
    CoreSpec p (n + 1) "proof_irrel" [mode, vis, d, a, b]
      (proofIrrel (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) decBool s₀ a₀ dn
      vis fe MM eb

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
  strLitSupported : StrLitSupportedOK p
  strLitCtor : StrLitCtorOK p
  /-- `strLitSupported` keeps every stored node's view (`supKeep_of`, `StrLitKeep.lean`). -/
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
        (proofIrrel (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) decBool s₀ a₀
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

section piK
variable (p : Prog) (n : Nat) (mode vis d a b : Word)

/-- After `is_proof_fast(b)`: the yes arm, else `proof_irrel`. -/
def piK4 (ia : Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if ia ≠ 0 ∧ r.headD 0 ≠ 0 then some (1, m)
    else call1W p n "proof_irrel" [mode, vis, d, a, b] m

def piK3 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => piK4 p n mode vis d a b (r.headD 0) (callW p n "is_proof_fast" [vis, b] m)

def piK2 (na : Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if na ≠ 0 ∨ r.headD 0 ≠ 0 then some (0, m)
    else piK3 p n mode vis d a b (callW p n "is_proof_fast" [vis, a] m)

/-- **The model of `prop_irrel`** past `not_proof_fast(a)`'s run. -/
def piK1 (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) => piK2 p n mode vis d a b (r.headD 0) (callW p n "not_proof_fast" [vis, b] m)

variable (r : List Word) (m : Mem) (w : Word)

theorem piK4_yes (h : w ≠ 0 ∧ r.headD 0 ≠ 0) : piK4 p n mode vis d a b w (some (r, m)) = some (1, m) := by
  simp only [piK4, h, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
theorem piK4_no (h : ¬ (w ≠ 0 ∧ r.headD 0 ≠ 0)) :
    piK4 p n mode vis d a b w (some (r, m)) = call1W p n "proof_irrel" [mode, vis, d, a, b] m := by
  simp only [piK4, h, ↓reduceIte]
theorem piK4_no0 (h : w = 0) :
    piK4 p n mode vis d a b w (some (r, m)) = call1W p n "proof_irrel" [mode, vis, d, a, b] m :=
  piK4_no p n mode vis d a b r m w (fun h' => h'.1 h)
theorem piK4_no1 (h : r.headD 0 = 0) :
    piK4 p n mode vis d a b w (some (r, m)) = call1W p n "proof_irrel" [mode, vis, d, a, b] m :=
  piK4_no p n mode vis d a b r m w (fun h' => h'.2 h)
theorem piK3_some : piK3 p n mode vis d a b (some (r, m)) =
    piK4 p n mode vis d a b (r.headD 0) (callW p n "is_proof_fast" [vis, b] m) := rfl
theorem piK2_yes (h : w ≠ 0 ∨ r.headD 0 ≠ 0) : piK2 p n mode vis d a b w (some (r, m)) = some (0, m) := by
  simp only [piK2, h, ↓reduceIte]
theorem piK2_no (h : ¬ (w ≠ 0 ∨ r.headD 0 ≠ 0)) :
    piK2 p n mode vis d a b w (some (r, m)) = piK3 p n mode vis d a b (callW p n "is_proof_fast" [vis, a] m) := by
  simp only [piK2, h, ↓reduceIte]
theorem piK2_yes0 (h : w ≠ 0) : piK2 p n mode vis d a b w (some (r, m)) = some (0, m) :=
  piK2_yes p n mode vis d a b r m w (.inl h)
theorem piK2_yes1 (h : r.headD 0 ≠ 0) : piK2 p n mode vis d a b w (some (r, m)) = some (0, m) :=
  piK2_yes p n mode vis d a b r m w (.inr h)
theorem piK1_some : piK1 p n mode vis d a b (some (r, m)) =
    piK2 p n mode vis d a b (r.headD 0) (callW p n "not_proof_fast" [vis, b] m) := rfl

end piK

section pispec
variable (p : Prog) (hq : StuckProg p)

set_option maxRecDepth 8000 in
include hq in
theorem propIrrel_spec (n : Nat) (s₀ : St) (mode vis d a b : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "prop_irrel" [mode, vis, d, a, b]
    ⦃fun r s' => LocEq s' s₀ ∧ piK1 p n mode vis d a b
      (callW p n "not_proof_fast" [vis, a] s₀.mem) = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hq.propIrrel]
  simp only [callFn, propIrrelL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, callW_spec p n "not_proof_fast",
      callW_spec p n "is_proof_fast", callW_spec p n "proof_irrel"] <;>
    -- depth for the locals' chain through four calls
    finish (gen := 20) [piK1_some, piK2_yes0, piK2_yes1, piK2_no, piK3_some, piK4_yes, piK4_no0,
      piK4_no1, call1W_some]

end pispec

theorem decBool_eq_true {r : List Word} (h : r.headD 0 ≠ 0) : decBool r = true := by
  simp only [decBool, bne_iff_ne]; exact h

theorem decBool_eq_false {r : List Word} (h : r.headD 0 = 0) : decBool r = false := by
  simp only [decBool, bne_eq_false_iff_eq]; exact h

/-- **`prop_irrel` refines `propIrrel`** at the knot, from the head readers' specs and
`proof_irrel`'s. -/
@[refines ConRon.Arena.propIrrel]
theorem propIrrel_refines (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) :
    CoreSpec p (n + 1) "prop_irrel" [mode, vis, d, a, b]
      (propIrrel (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) decBool
      s₀ a₀ dn vis fe M eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (propIrrel_spec p hq n s₀ mode vis d a b)
  subst hs0
  refine ⟨hloc, ?_⟩
  rw [propIrrel_eq]
  obtain ⟨r₁, m₁, hc1, hW⟩ := callW_cases rfl hW
  rw [piK1_some] at hW
  obtain ⟨r₂, m₂, hc2, hW⟩ := callW_cases rfl hW
  have h₁ := CoreSpec.of_callW (hc.defeq.notProofFast n s a₀ dn vis fe M eb a hs.rel ha) hc1
  refine coreRef_bind h₁ (fun M₁ hS₁ => ?_)
  have h₂ := CoreSpec.of_callW
    (hc.defeq.notProofFast n ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb b hS₁ hb) hc2
  refine coreRef_bind h₂ (fun M₂ hS₂ => ?_)
  by_cases h12 : r₁.headD 0 ≠ 0 ∨ r₂.headD 0 ≠ 0
  · rw [piK2_yes (h := h12)] at hW
    obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    have hx : (decBool r₁ || decBool r₂) = true := by
      rcases h12 with h | h <;> simp [decBool_eq_true h]
    rw [hx]
    simp only [↓reduceIte]
    exact coreRef_pure hS₂ rfl (decBool_eq_false hr.symm).symm
      (by unfold ResH; rw [← hr]; exact hw0)
  rw [piK2_no (h := h12)] at hW
  simp only [not_or, ne_eq, Decidable.not_not] at h12
  have hx : (decBool r₁ || decBool r₂) = false := by
    simp [decBool_eq_false h12.1, decBool_eq_false h12.2]
  rw [hx]
  simp only [Bool.false_eq_true, ↓reduceIte]
  obtain ⟨r₃, m₃, hc3, hW⟩ := callW_cases rfl hW
  rw [piK3_some] at hW
  obtain ⟨r₄, m₄, hc4, hW⟩ := callW_cases rfl hW
  have h₃ := CoreSpec.of_callW
    (hc.defeq.isProofFast n ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb a hS₂ ha) hc3
  refine coreRef_bind h₃ (fun M₃ hS₃ => ?_)
  have h₄ := CoreSpec.of_callW
    (hc.defeq.isProofFast n ⟨m₃, Locals.init []⟩ _ dn vis fe M₃ eb b hS₃ hb) hc4
  refine coreRef_bind h₄ (fun M₄ hS₄ => ?_)
  by_cases h34 : r₃.headD 0 ≠ 0 ∧ r₄.headD 0 ≠ 0
  · rw [piK4_yes (h := h34)] at hW
    obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    have hx : (decBool r₃ && decBool r₄) = true := by
      simp [decBool_eq_true h34.1, decBool_eq_true h34.2]
    rw [hx]
    simp only [↓reduceIte]
    exact coreRef_pure hS₄ rfl (decBool_eq_true (by rw [← hr]; decide)).symm
      (by unfold ResH; rw [← hr]; exact hw1)
  rw [piK4_no (h := h34)] at hW
  have hx : (decBool r₃ && decBool r₄) = false := by
    by_cases h3 : r₃.headD 0 = 0
    · simp [decBool_eq_false h3]
    · have h4 : r₄.headD 0 = 0 := by
        exact Classical.byContradiction fun h4 => h34 ⟨h3, h4⟩
      simp [decBool_eq_false h4]
  rw [hx]
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact CoreSpec.of_call1W (s₀ := ⟨m₄, Locals.init []⟩)
    (proofIrrel_at p hc n hk F hF hn _ _ dn vis fe M₄ eb mode d a b hS₄ hs.mode4 hs.eb_mode ha hb)
    (fun r r' h => by simp only [decBool, h]) hW

end L.Arena
