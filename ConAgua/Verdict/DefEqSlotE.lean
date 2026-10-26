import ConAgua.Verdict.DefEqBaseE
import ConAgua.Arena.KnotEntry

/-!
# The knot's `defeq` slot: its error claim one level up (lane `verdicts-b`, helper `k3`)

`defeq(mode, vis, d, a, b)` (`Knot.lean`) probes the memo (`de_find`), runs `defeq_body` on a miss
and records the verdict (`de_put`). The memo's two calls are outside the verdict closure, so a
failure of class `1`/`2` is `defeq_body`'s, at a memo miss: the twin's slot runs `defeqBody` there
(`knot_defeq_missE`). `defeqSlotE_of`: `DefeqSlotE p (n + 1)` from `defeq_body`'s error spec
(`DefeqBodySpecE`, the error half of `DefeqBodySpec`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

l_model defeqSlot_specE (p : Prog) (hf : p.lookup "defeq" = some defeqSlotL)
  fns [hf ↦ defeqSlotE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  finish [tierW, idxW] errors

/-- **`defeq_body`'s error spec** (the error half of `DefeqBodySpec`): under the same hypotheses
and the error knot up to `n`. -/
def DefeqBodySpecE (p : Prog) (n : Nat) : Prop :=
  ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d x y : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe MM eb mode →
    HW x → HW y → KnotUpTo p n → KnotUpToE p n →
    CoreSpecE p n "defeq_body" [mode, vis, d, x, y]
      (defeqBody (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE x) (decE y)) s₀ a₀

/-- At a memo miss the twin's slot fails where its body does. -/
theorem knot_defeq_missE (mode : ConLeche.CheckMode) (fe : IFEnv) (F d : Nat) (x y : EIdx)
    (a : AState) (hm : a.caches.defeqC[(x, y)]? = none) {e : Err}
    (h : ErrClaim (defeqBody mode (coreKnot mode fe id F) fe d x y) a e) :
    ErrClaim ((coreKnot mode fe id (F + 1)).defeq d x y) a e := by
  refine ErrClaim.of_run_eq (fun ce hce => ?_) h
  simp [coreKnot, hm, StateT.run_bind, hce]
  rfl

/-- The memo's calls are outside the verdict closure. -/
theorem defeqSlotE_nv : ∀ f ∈ ["de_find", "de_put"], f ∈ L.Checker.nvFns := by
  decide +kernel

/-- **The knot's `defeq` slot's error claim one level up**, from `defeq_body`'s. -/
theorem defeqSlotE_of (p : Prog) (hp : KnotProg p) (hnv : closedNV p L.Checker.nvFns = true)
    (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) (hb : DefeqBodySpecE p n) :
    DefeqSlotE p (n + 1) := by
  intro F s₀ a₀ dn vis fe MM eb mode d x y hF hn2 hs hx hy
  obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
  refine CoreSpecE.of_runs fun er hc => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (defeqSlot_specE p hp.defeq (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d x y) hc (Err.code_ne_of_cls hk0)
  simp only [defeqSlotE] at hW
  have hS := hs.rel
  have hkey : y ||| (mode >>> 1 &&& 1) <<< 32 = genW y eb := by rw [hs.eb_mode]; rfl
  rw [hkey] at hW
  cases h1 : callE p n "de_find" [x, genW y eb] s₀.mem with
  | error e1 =>
    rw [h1, defeqSlotE.k_de_find.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (defeqSlotE_nv "de_find" (by simp)) h1
  | ok q =>
  obtain ⟨r₁, m₁⟩ := q
  obtain ⟨t₁, ht₁, rfl, hne, rfl⟩ := triple_of_callE (s₀ := ⟨s₀.mem, Locals.init []⟩)
    (memoFindG_spec deSch p _ hp.deFind n ⟨s₀.mem, Locals.init []⟩ x (genW y eb)) h1
  simp only at ht₁
  subst ht₁
  rw [h1] at hW
  have hf := hS.core.de.findD hS.core.eb1 x y hx hy hne
  by_cases h2 : (mfindG deSch s₀.mem x (genW y eb)).headD 0 ≠ 0
  · rw [defeqSlotE.k_de_find.arm1 _ _ _ _ _ _ _ _ _ _ h2] at hW; cases hW
  have h2' : (mfindG deSch s₀.mem x (genW y eb)).headD 0 = 0 := by simpa using h2
  rw [defeqSlotE.k_de_find.arm2 _ _ _ _ _ _ _ _ _ _ h2'] at hW
  have hmiss := hf.2 h2'
  cases h3 : callE p n "defeq_body" [mode, vis, d, x, y] s₀.mem with
  | error e3 =>
    rw [h3, defeqSlotE.k_defeq_body.none] at hW; cases hW
    exact knot_defeq_missE _ fe F' d.toNat _ _ a₀ hmiss
      (CoreSpecE.of_callE (hb F' s₀ a₀ dn vis fe MM eb mode d x y (by omega) (by omega) hs hx hy hk
        hkE) h3)
  | ok q =>
  obtain ⟨r₃, m₃⟩ := q
  rw [h3] at hW
  simp only [defeqSlotE.k_defeq_body] at hW
  cases h4 : callE p n "de_find" [x, genW y eb] m₃ with
  | error e4 =>
    rw [h4, defeqSlotE.k_de_find_2.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (defeqSlotE_nv "de_find" (by simp)) h4
  | ok q =>
  rw [h4] at hW
  simp only [defeqSlotE.k_de_find_2] at hW
  cases h5 : callE p n "de_put" _ _ with
  | error e5 =>
    rw [h5, defeqSlotE.k_de_put.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (defeqSlotE_nv "de_put" (by simp)) h5
  | ok q => rw [h5] at hW; simp only [defeqSlotE.k_de_put] at hW; cases hW

end L.Arena

/-! ## `defeq_body` -/

namespace L.Arena

l_model defeqBody_specE (p : Prog) (hf : p.lookup "defeq_body" = some defeqBodyL)
  fns [hf ↦ defeqBodyE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

/-- **`quick_defeq`'s error spec** (the error half of `QuickDefeqSpec`). -/
def QuickDefeqSpecE (p : Prog) (n : Nat) : Prop :=
  ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d x y : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe M eb mode →
    HW x → HW y → d.toNat < 2 ^ 63 →
    CoreSpecE p n "quick_defeq" [mode, vis, d, x, y]
      (quickDefEq (decMode mode) (coreKnot (decMode mode) fe id F) d.toNat (decE x) (decE y)) s₀ a₀

/-- `quick_defeq`'s error spec one level up from the two knots (`quickDefeq_refinesE`). -/
def QuickDefeqE (p : Prog) : Prop :=
  ∀ n, KnotUpTo p n → KnotUpToE p n → QuickDefeqSpecE p (n + 1)

/-- **`lazy_delta_reduction`'s error spec** (the error half of `lazyDeltaReduction_refines`). -/
def LazyDeltaReductionE (p : Prog) : Prop :=
  ∀ (n : Nat), KnotUpTo p n → KnotUpToE p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
  ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d a b : Word), SlotPre s₀ a₀ dn vis fe M eb mode → HW a → HW b →
    d.toNat < 2 ^ 63 →
    CoreSpecE p (n + 1) "lazy_delta_reduction" [mode, vis, d, a, b]
      (lazyDeltaReduction (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat defeqLoopFuel
        (decE a) (decE b)) s₀ a₀

/-- **`defeq_tail`'s error spec** (the error half of `defeqTail_refines`). -/
def DefeqTailE (p : Prog) : Prop :=
  ∀ (n : Nat), KnotUpTo p n → KnotUpToE p n → ∀ (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a1 b1 : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe M eb mode → HW a1 →
    HW b1 → d.toNat < 2 ^ 63 →
    CoreSpecE p (n + 1) "defeq_tail" [mode, vis, d, a1, b1]
      (defeqTailT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE a1) (decE b1)) s₀ a₀

/-- **`bool_true_shortcut`'s error spec** (whnf family; the error half of
`boolTrueShortcut_refines`). -/
def BoolTrueShortcutE (p : Prog) : Prop :=
  ∀ (n : Nat), KnotUpTo p n → KnotUpToE p n → ∀ (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a : Word),
    n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe M eb mode → HW a →
    CoreSpecE p (n + 1) "bool_true_shortcut" [mode, vis, d, a]
      (boolTrueShortcut (coreKnot (decMode mode) fe id F) d.toNat (decE a)) s₀ a₀

/-- **`prop_irrel`'s error spec** (whnf family; the error half of `propIrrel_refines`). -/
def PropIrrelE (p : Prog) : Prop :=
  ∀ (n : Nat), KnotUpTo p n → KnotUpToE p n → ∀ (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word),
    n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe M eb mode → HW a → HW b →
    CoreSpecE p (n + 1) "prop_irrel" [mode, vis, d, a, b]
      (propIrrel (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) s₀ a₀

/-- The callees `defeq_body`'s error refinement assumes: two of the whnf family's
(`bool_true_shortcut`, `prop_irrel`) and three of this family's. -/
structure DefeqBodyCalleesE (p : Prog) : Prop where
  boolTrueShortcut : BoolTrueShortcutE p
  propIrrel : PropIrrelE p
  quickDefeq : QuickDefeqE p
  lazyDeltaReduction : LazyDeltaReductionE p
  defeqTail : DefeqTailE p

theorem defeqBodyE_nv : ∀ f ∈ ["is_bool_true", "has_fvar"], f ∈ L.Checker.nvFns := by
  decide +kernel

/-- **`defeq_body`'s error claim**: `DefeqBodySpecE p n`, from the ok refinements of its callees
(`DefeqBodyCallees`), their error claims (`DefeqBodyCalleesE`) and the knots up to `n`. -/
theorem defeqBody_refinesE (p : Prog) (hq : DefeqBodyProg p) (hc : DefeqBodyCallees p)
    (hcE : DefeqBodyCalleesE p) (hnv : closedNV p L.Checker.nvFns = true) (n : Nat) :
    DefeqBodySpecE p n := by
  intro F s₀ a₀ dn vis fe M eb mode d x y hF hn hs hx hy hk hkE
  cases n with
  | zero => exact CoreSpecE.zero p _ _ _ s₀ a₀
  | succ n =>
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (defeqBody_specE p hq.body (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d x y) hc0 (Err.code_ne_of_cls hk0)
  have hS := hs.rel
  rw [defeqBody_eq, decE_beq hx hy]
  simp only [defeqBodyE] at hW
  by_cases hxy : x = y
  · rw [ite_eq_left hxy] at hW; cases hW
  rw [ite_eq_right hxy] at hW
  simp only [hxy, decide_false, Bool.false_eq_true, ↓reduceIte]
  by_cases hd0 : d >>> 63 ≠ 0
  · rw [ite_eq_left hd0] at hW; cases hW; exact ErrClaim.of_cls0 rfl
  rw [ite_eq_right hd0] at hW
  have hd := depth_lt_of_shr d (by simpa using hd0)
  cases h1 : callE p n "is_bool_true" [y] s₀.mem with
  | error e1 =>
    rw [h1, defeqBodyE.k_is_bool_true.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (defeqBodyE_nv "is_bool_true" (by simp)) h1
  | ok q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [h1] at hW
  simp only [defeqBodyE.k_is_bool_true] at hW
  obtain ⟨k, rfl⟩ := callE_succ h1
  have hk' : KnotUpTo p k := hk.mono (by omega)
  have hkE' : KnotUpToE p k := hkE.mono (by omega)
  have h₁ := CoreSpec.of_callW (isBoolTrue_refines p hq.stuck.leaf k ⟨s₀.mem, Locals.init []⟩ a₀
    dn vis fe M eb y hS hy) (callW_of_callE h1)
  refine ErrClaim.bind_core h₁ (fun M₁ hS₁ => ?_)
  cases h2 : callE p (k + 1) "has_fvar" [x] m₁ with
  | error e2 =>
    rw [h2, defeqBodyE.k_has_fvar.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (defeqBodyE_nv "has_fvar" (by simp)) h2
  | ok q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [h2] at hW
  simp only [defeqBodyE.k_has_fvar] at hW
  have h₂ := CoreSpec.of_callW
    (hc.stuck.defeq.hasFvar (k + 1) ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb x hS₁ hx) (callW_of_callE h2)
  refine ErrClaim.bind_core h₂ (fun M₂ hS₂ => ?_)
  have hSP : ∀ {m : Mem} {st : AState} {M : ModeMaps}, CoreS dn m st vis fe M eb →
      SlotPre ⟨m, Locals.init []⟩ st dn vis fe M eb mode := fun h => ⟨h, hs.mode4, hs.eb_mode⟩
  -- the rest past the shortcut, from any state related at `m₃`
  have rest : ∀ (sc : Word) (st : AState) (m₃ : Mem) (M₃ : ModeMaps),
      CoreS dn m₃ st vis fe M₃ eb → defeqBodyE.j1 p (k + 1) mode vis d x y sc m₃ = .error er →
      ErrClaim (if (sc != 0) = true then pure true else
        defeqBodyRestT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE x) (decE y))
        st er := by
    intro sc st m₃ M₃ hS₃ hW3
    unfold defeqBodyE.j1 at hW3
    by_cases hsc : sc ≠ 0
    · rw [ite_eq_left hsc] at hW3; cases hW3
    rw [ite_eq_right hsc] at hW3
    have hsc' : sc = 0 := by simpa using hsc
    simp only [hsc', bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    unfold defeqBodyRestT
    have hQ := quickUpTo hq.lazy hc.lazy hk (k + 1) (by omega)
    have hQE := hcE.quickDefeq k hk' hkE'
    cases h4 : callE p (k + 1) "quick_defeq" [mode, vis, d, x, y] m₃ with
    | error e4 =>
      rw [h4, defeqBodyE.k_quick_defeq.none] at hW3; cases hW3
      exact ErrClaim.bind_left (CoreSpecE.of_callE (s₀ := ⟨m₃, Locals.init []⟩)
        (hQE F ⟨m₃, Locals.init []⟩ st dn vis fe M₃ eb mode d x y (by omega) (by omega) (hSP hS₃) hx
          hy hd) h4)
    | ok q =>
    obtain ⟨r₄, m₄⟩ := q
    rw [h4] at hW3
    simp only [defeqBodyE.k_quick_defeq] at hW3
    have h₄ := CoreSpec.of_callW (hQ F ⟨m₃, Locals.init []⟩ st dn vis fe M₃ eb mode d x y
      (by omega) (by omega) (hSP hS₃) hx hy hd) (callW_of_callE h4)
    refine ErrClaim.bind_core h₄ (fun M₄ hS₄ => ?_)
    by_cases hq4 : r₄.headD 0 ≠ 0
    · rw [ite_eq_left hq4] at hW3; cases hW3
    rw [ite_eq_right hq4] at hW3
    simp only [decOB, ite_eq_left (show r₄.headD 0 = 0 by simpa using hq4)]
    cases h5 : callE p (k + 1) "prop_irrel" [mode, vis, d, x, y] m₄ with
    | error e5 =>
      rw [h5, defeqBodyE.k_prop_irrel.none] at hW3; cases hW3
      exact ErrClaim.bind_left (CoreSpecE.of_callE (s₀ := ⟨m₄, Locals.init []⟩)
        (hcE.propIrrel k hk' hkE' F ⟨m₄, Locals.init []⟩ _ dn vis fe M₄ eb mode d x y (by omega)
          (by omega) (hSP hS₄) hx hy) h5)
    | ok q =>
    obtain ⟨r₅, m₅⟩ := q
    rw [h5] at hW3
    simp only [defeqBodyE.k_prop_irrel] at hW3
    have h₅ := CoreSpec.of_callW (propIrrel_refines p hq.stuck hc.stuck k hk' F ⟨m₄, Locals.init []⟩
      _ dn vis fe M₄ eb mode d x y (by omega) (by omega) (hSP hS₄) hx hy) (callW_of_callE h5)
    refine ErrClaim.bind_core h₅ (fun M₅ hS₅ => ?_)
    by_cases hp5 : r₅.headD 0 ≠ 0
    · rw [ite_eq_left hp5] at hW3; cases hW3
    rw [ite_eq_right hp5] at hW3
    rw [decBool_false_of (by simpa using hp5)]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hK := hk (k + 1) (by omega)
    have hKE := hkE (k + 1) (by omega)
    cases h6 : callE p (k + 1) "whnf_core" [mode, 1, vis, d, x] m₅ with
    | error e6 =>
      rw [h6, defeqBodyE.k_whnf_core.none] at hW3; cases hW3
      have := CoreSpecE.of_callE (s₀ := ⟨m₅, Locals.init []⟩)
        (hKE.whnfCore F ⟨m₅, Locals.init []⟩ _ dn vis fe M₅ eb mode 1 d x (by omega) (by omega)
          (hSP hS₅) hx) h6
      rw [show ((1 : Word) != 0) = true from rfl] at this
      exact ErrClaim.bind_left this
    | ok q =>
    obtain ⟨r₆, m₆⟩ := q
    rw [h6] at hW3
    simp only [defeqBodyE.k_whnf_core] at hW3
    have h₆ := CoreSpec.of_callW (hK.whnfCore F ⟨m₅, Locals.init []⟩ _ dn vis fe M₅ eb mode 1 d x
      (by omega) (by omega) (hSP hS₅) hx) (callW_of_callE h6)
    rw [show ((1 : Word) != 0) = true from rfl] at h₆
    refine ErrClaim.bind_core h₆ (fun M₆ hS₆ => ?_)
    cases h7 : callE p (k + 1) "whnf_core" [mode, 1, vis, d, y] m₆ with
    | error e7 =>
      rw [h7, defeqBodyE.k_whnf_core_2.none] at hW3; cases hW3
      have := CoreSpecE.of_callE (s₀ := ⟨m₆, Locals.init []⟩)
        (hKE.whnfCore F ⟨m₆, Locals.init []⟩ _ dn vis fe M₆ eb mode 1 d y (by omega) (by omega)
          (hSP hS₆) hy) h7
      rw [show ((1 : Word) != 0) = true from rfl] at this
      exact ErrClaim.bind_left this
    | ok q =>
    obtain ⟨r₇, m₇⟩ := q
    rw [h7] at hW3
    simp only [defeqBodyE.k_whnf_core_2] at hW3
    have h₇ := CoreSpec.of_callW (hK.whnfCore F ⟨m₆, Locals.init []⟩ _ dn vis fe M₆ eb mode 1 d y
      (by omega) (by omega) (hSP hS₆) hy) (callW_of_callE h7)
    rw [show ((1 : Word) != 0) = true from rfl] at h₇
    refine ErrClaim.bind_core h₇ (fun M₇ hS₇ => ?_)
    cases h8 : callE p (k + 1) "quick_defeq" [mode, vis, d, r₆.headD 0, r₇.headD 0] m₇ with
    | error e8 =>
      rw [h8, defeqBodyE.k_quick_defeq_2.none] at hW3; cases hW3
      exact ErrClaim.bind_left (CoreSpecE.of_callE (s₀ := ⟨m₇, Locals.init []⟩)
        (hQE F ⟨m₇, Locals.init []⟩ _ dn vis fe M₇ eb mode d _ _ (by omega) (by omega) (hSP hS₇)
          h₆.2.2.2 h₇.2.2.2 hd) h8)
    | ok q =>
    obtain ⟨r₈, m₈⟩ := q
    rw [h8] at hW3
    simp only [defeqBodyE.k_quick_defeq_2] at hW3
    have h₈ := CoreSpec.of_callW (hQ F ⟨m₇, Locals.init []⟩ _ dn vis fe M₇ eb mode d _ _
      (by omega) (by omega) (hSP hS₇) h₆.2.2.2 h₇.2.2.2 hd) (callW_of_callE h8)
    refine ErrClaim.bind_core h₈ (fun M₈ hS₈ => ?_)
    by_cases hq8 : r₈.headD 0 ≠ 0
    · rw [ite_eq_left hq8] at hW3; cases hW3
    rw [ite_eq_right hq8] at hW3
    simp only [decOB, ite_eq_left (show r₈.headD 0 = 0 by simpa using hq8)]
    cases h9 : callE p (k + 1) "lazy_delta_reduction" [mode, vis, d, r₆.headD 0, r₇.headD 0] m₈ with
    | error e9 =>
      rw [h9, defeqBodyE.k_lazy_delta_reduction.none] at hW3; cases hW3
      exact ErrClaim.bind_left (CoreSpecE.of_callE (s₀ := ⟨m₈, Locals.init []⟩)
        (hcE.lazyDeltaReduction k hk' hkE' F (by omega) (by omega) ⟨m₈, Locals.init []⟩ _ dn vis fe
          M₈ eb mode d _ _ (hSP hS₈) h₆.2.2.2 h₇.2.2.2 hd) h9)
    | ok q =>
    obtain ⟨r₉, m₉⟩ := q
    rw [h9] at hW3
    simp only [defeqBodyE.k_lazy_delta_reduction] at hW3
    have h₉ := CoreSpec.of_callW (lazyDeltaReduction_refines p hq.lazy hc.lazy k hk' F (by omega)
      (by omega) ⟨m₈, Locals.init []⟩ _ dn vis fe M₈ eb mode d _ _ (hSP hS₈) h₆.2.2.2 h₇.2.2.2 hd)
      (callW_of_callE h9)
    refine ErrClaim.bind_core h₉ (fun M₉ hS₉ => ?_)
    obtain ⟨g0, g1, g2⟩ := h₉.2.2.2
    by_cases l0 : r₉.headD 0 = 0
    · rw [ite_eq_left l0] at hW3; cases hW3
    rw [ite_eq_right l0] at hW3
    by_cases l1 : r₉.headD 0 = 1
    · rw [ite_eq_left l1] at hW3; cases hW3
    rw [ite_eq_right l1] at hW3
    simp only [decLR, ite_eq_right l0, ite_eq_right l1]
    cases h10 : callE p (k + 1) "defeq_tail" [mode, vis, d, r₉.tail.headD 0, r₉.tail.tail.headD 0]
        m₉ with
    | error e10 =>
      rw [h10, defeqBodyE.k_defeq_tail.none] at hW3; cases hW3
      exact CoreSpecE.of_callE (s₀ := ⟨m₉, Locals.init []⟩)
        (hcE.defeqTail k hk' hkE' F _ _ dn vis fe M₉ eb mode d _ _ (by omega) (by omega) (hSP hS₉)
          g1 g2 hd) h10
    | ok q => rw [h10] at hW3; simp only [defeqBodyE.k_defeq_tail] at hW3; cases hW3
  by_cases hb : r₁.headD 0 ≠ 0 ∧ ((mode >>> 1) &&& 1 ≠ 0 ∨ r₂.headD 0 = 0)
  · rw [ite_eq_left hb.1, ite_eq_left hb.2] at hW
    have hcond : (decBool r₁ && ((decMode mode).eager || !decBool r₂)) = true := by
      rw [decMode_eager mode hs.mode4, decBool_true_of hb.1]
      rcases hb.2 with h | h
      · simp [h]
      · simp [decBool_false_of h]
    rw [hcond]
    simp only [↓reduceIte]
    cases h3 : callE p (k + 1) "bool_true_shortcut" [mode, vis, d, x] m₂ with
    | error e3 =>
      rw [h3, defeqBodyE.k_bool_true_shortcut.none] at hW; cases hW
      exact ErrClaim.bind_left (CoreSpecE.of_callE (s₀ := ⟨m₂, Locals.init []⟩)
        (hcE.boolTrueShortcut k hk' hkE' F ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode d x (by omega)
          (by omega) (hSP hS₂) hx) h3)
    | ok q =>
    obtain ⟨r₃, m₃⟩ := q
    rw [h3] at hW
    simp only [defeqBodyE.k_bool_true_shortcut] at hW
    have h₃ := CoreSpec.of_callW (boolTrueShortcut_refines p hq.lazy.mid k hk' F ⟨m₂, Locals.init []⟩
      _ dn vis fe M₂ eb mode d x (by omega) (by omega) (hSP hS₂) hx) (callW_of_callE h3)
    refine ErrClaim.bind_core h₃ (fun M₃ hS₃ => ?_)
    exact rest _ _ _ _ hS₃ hW
  have hW' : defeqBodyE.j1 p (k + 1) mode vis d x y 0 m₂ = .error er := by
    by_cases hb1 : r₁.headD 0 ≠ 0
    · have hb2 : ¬ ((mode >>> 1) &&& 1 ≠ 0 ∨ r₂.headD 0 = 0) := fun h => hb ⟨hb1, h⟩
      rw [ite_eq_left hb1, ite_eq_right hb2] at hW; exact hW
    · rw [ite_eq_right hb1] at hW; exact hW
  have hcond : (decBool r₁ && ((decMode mode).eager || !decBool r₂)) = false := by
    rw [decMode_eager mode hs.mode4]
    by_cases h1 : r₁.headD 0 = 0
    · simp [decBool_false_of h1]
    · have h2 : ¬ ((mode >>> 1) &&& 1 ≠ 0 ∨ r₂.headD 0 = 0) := fun h => hb ⟨h1, h⟩
      simp only [not_or, ne_eq, Decidable.not_not] at h2
      simp [h2.1, decBool_true_of h2.2]
  rw [hcond]
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine ErrClaim.bind_right (v := false) (a₁ := AM.st (pure false : AM Bool) _) rfl ?_
  exact rest 0 _ _ _ hS₂ hW'

end L.Arena

/-! ## The slot step; `is_def_eq_core` -/

namespace L.Arena

/-- **The `defeq` slot's error half one level up** (`KnotStepE`'s `defeq` field), from the ok
knot, the error knot up to `n`, and `defeq_body`'s callees. -/
theorem defeqSlotE_step (p : Prog) (hq : DefeqBodyProg p) (hc : DefeqBodyCallees p)
    (hcE : DefeqBodyCalleesE p) (hnv : closedNV p L.Checker.nvFns = true) (n : Nat)
    (hk : KnotUpTo p n) (hkE : KnotUpToE p n) : DefeqSlotE p (n + 1) :=
  defeqSlotE_of p hq.knot hnv n hk hkE (defeqBody_refinesE p hq hc hcE hnv n)

/-- The same over `KnotAllProg` (the ok knot's program). -/
theorem KnotAllProg.defeqSlotE {p : Prog} (hq : KnotAllProg p) (hcE : DefeqBodyCalleesE p)
    (hnv : closedNV p L.Checker.nvFns = true) (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) :
    DefeqSlotE p (n + 1) :=
  defeqSlotE_step p hq.body ⟨KnotAllProg.stuck hq, KnotAllProg.lazy hq⟩ hcE hnv n hk hkE

l_model isDefEqCore_specE (p : Prog) (hf : p.lookup "is_def_eq_core" = some isDefEqCoreL)
  fns [hf ↦ isDefEqCoreE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  finish [tierW, idxW] errors

/-- **`is_def_eq_core`'s error claim under `CoreS`** (the error half of `isDefEqCore_refines`), from
the `defeq` slot's. -/
theorem isDefEqCore_refinesE (p : Prog) (hp : KnotEntryProg p) (n : Nat) (hd : DefeqSlotE p n)
    (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (dep x y : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hS : CoreS dn s₀.mem a₀ vis fe M 0) (hx : HW x) (hy : HW y) :
    CoreSpecE p (n + 1) "is_def_eq_core" [vis, dep, x, y]
      (isDefEqCore .verified fe F dep.toNat (decE x) (decE y)) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (isDefEqCore_specE p hp.isDefEqCore (n + 1) ⟨s₀.mem, Locals.init []⟩
    vis dep x y) hc (Err.code_ne_of_cls hk0)
  simp only [isDefEqCoreE] at hW
  cases h1 : callE p n "defeq" [0, vis, dep, x, y] s₀.mem with
  | error e1 =>
    rw [h1, isDefEqCoreE.k_defeq.none] at hW; cases hW
    exact CoreSpecE.of_callE (hd F s₀ a₀ dn vis fe M 0 0 dep x y hF hn (slotPre_zero hS) hx hy) h1
  | ok q => rw [h1] at hW; simp only [isDefEqCoreE.k_defeq] at hW; cases hW

end L.Arena

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- **`is_def_eq_core`'s error claim under `StageT`** (`CoreStubsE.isDefEqCore`'s shape, the error
half of `isDefEqCore_simT`), from the `defeq` slot's error claim at every fuel. -/
theorem isDefEqCore_stageE {p : Prog} (hp : KnotEntryProg p) (hdE : ∀ n, DefeqSlotE p n) :
    ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {m : Mem} {a : AState}, StageT dn vis fe m a → ∀ (dep x y : Word), H x → H y →
    ∀ e, callE p n "is_def_eq_core" [vis, dep, x, y] m = .error e →
      ErrClaim (isDefEqCore V fe checkFuel dep.toNat (decI x) (decI y)) a e := by
  intro n hn dn vis fe m a hS dep x y hx hy e hc
  refine ErrClaim.of_callE_succ hc fun k hk hc' => ?_
  subst hk
  obtain ⟨M, hC⟩ := hS.core
  exact CoreSpecE.of_callE (s₀ := ⟨m, Locals.init []⟩)
    (isDefEqCore_refinesE p hp k (hdE k) checkFuel ⟨m, Locals.init []⟩ a dn vis fe M dep x y
      (stage_fuel hn) (by omega) hC (hw_of_h hx) (hw_of_h hy)) hc'

end L.Ind
