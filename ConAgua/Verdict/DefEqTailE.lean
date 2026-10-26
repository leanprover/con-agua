import ConAgua.Verdict.DefEqSlotE

/-!
# `defeq_tail`'s error claim and the stuck side's (lane `verdicts-b`, helper `k3`)

The error halves of `DefEqStuckTail.lean`, `DefEqStuckProj.lean`, `DefEqStuckDisp.lean`, … in the
shape of their ok refinements (`CoreSpecE` in place of `CoreSpec`, the error knot `KnotUpToE`
beside the ok knot). Each proof follows its ok proof's call chain over the generated error model
(`l_model … errors`): a callee's failure is its own claim (`ErrClaim.bind_left`), a callee's ok
run is its ok refinement's (`ErrClaim.bind_core`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.deprecated false

namespace L.Arena

/-! ## The callees' error specs -/

/-- **`defeq_proj_pair`'s error spec** (the error half of `projPair_refines`). -/
def ProjPairE (p : Prog) : Prop :=
  ∀ (n : Nat), KnotUpTo p n → KnotUpToE p n → ∀ (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word),
    n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe M eb mode → HW a → HW b → d.toNat < 2 ^ 63 →
    CoreSpecE p (n + 1) "defeq_proj_pair" [mode, vis, d, a, b]
      (defeqProjPair (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) s₀ a₀

/-- **`defeq_stuck`'s error spec** (the error half of `defeqStuck_refines`). -/
def DefeqStuckE (p : Prog) : Prop :=
  ∀ (n : Nat), KnotUpTo p n → KnotUpToE p n → ∀ (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word),
    n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe M eb mode → HW a → HW b →
    CoreSpecE p (n + 1) "defeq_stuck" [mode, vis, d, a, b]
      (defeqStuck (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) s₀ a₀

/-! ## `defeq_tail` -/

l_model defeqTail_specE (p : Prog) (hf : p.lookup "defeq_tail" = some defeqTailL)
  fns [hf ↦ defeqTailE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

theorem defeqTailE_nv : "head_is_proj" ∈ L.Checker.nvFns := by decide +kernel

/-- **`defeq_tail`'s error claim** (`DefeqTailE`), from `defeq_proj_pair`'s and `defeq_stuck`'s and
the two slots'. -/
theorem defeqTail_refinesE (p : Prog) (hq : StuckProg p) (hc : StuckCallees p)
    (hppE : ProjPairE p) (hdsE : DefeqStuckE p) (hnv : closedNV p L.Checker.nvFns = true) :
    DefeqTailE p := by
  intro n hk hkE F s₀ a₀ dn vis fe M eb mode d a1 b1 hF hn hs ha hb hd
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (defeqTail_specE p hq.defeqTail (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d a1 b1) hc0 (Err.code_ne_of_cls hk0)
  have hS := hs.rel
  have hK := hk n (Nat.le_refl _)
  have hKE := hkE n (Nat.le_refl _)
  simp only [defeqTailE] at hW
  -- `defeq_stuck` from any state related at `m`
  have hstk : ∀ (st : AState) (m : Mem) (M' : ModeMaps), CoreS dn m st vis fe M' eb →
      defeqTailE.k_defeq_stuck p (callE p n "defeq_stuck" [mode, vis, d, a1, b1] m) = .error er →
      ErrClaim (defeqStuck (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE a1)
        (decE b1)) st er := by
    intro st m M' hS' hW'
    cases h : callE p n "defeq_stuck" [mode, vis, d, a1, b1] m with
    | error e =>
      rw [h, defeqTailE.k_defeq_stuck.none] at hW'; cases hW'
      refine ErrClaim.of_callE_succ h fun j hj h' => ?_
      subst hj
      exact CoreSpecE.of_callE (s₀ := ⟨m, Locals.init []⟩)
        (hdsE j (hk.mono (by omega)) (hkE.mono (by omega)) F _ st dn vis fe M' eb mode d a1 b1
          (by omega) (by omega) ⟨hS', hs.mode4, hs.eb_mode⟩ ha hb) h'
    | ok q => rw [h] at hW'; simp only [defeqTailE.k_defeq_stuck] at hW'; cases hW'
  unfold defeqTailT
  cases h1 : callE p n "defeq_proj_pair" [mode, vis, d, a1, b1] s₀.mem with
  | error e1 =>
    rw [h1, defeqTailE.k_defeq_proj_pair.none] at hW; cases hW
    refine ErrClaim.bind_left (ErrClaim.of_callE_succ h1 fun j hj h' => ?_)
    subst hj
    exact CoreSpecE.of_callE (hppE j (hk.mono (by omega)) (hkE.mono (by omega)) F s₀ a₀ dn vis fe M
      eb mode d a1 b1 (by omega) (by omega) hs ha hb hd) h'
  | ok q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [h1] at hW
  simp only [defeqTailE.k_defeq_proj_pair] at hW
  have h₁ := CoreSpec.of_callW (projPair_at p hq hc n hk F s₀ a₀ dn vis fe M eb mode d a1 b1 hF hn
    hs ha hb hd) (callW_of_callE h1)
  refine ErrClaim.bind_core h₁ (fun M₁ hS₁ => ?_)
  by_cases h0 : r₁.headD 0 ≠ 0
  · rw [if_pos h0] at hW; cases hW
  rw [if_neg h0] at hW
  rw [decBool_false_of (by simpa using h0)]
  simp only [Bool.false_eq_true, ↓reduceIte]
  cases h2 : callE p n "head_is_proj" [a1] m₁ with
  | error e2 =>
    rw [h2, defeqTailE.k_head_is_proj.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv defeqTailE_nv h2
  | ok q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [h2] at hW
  simp only [defeqTailE.k_head_is_proj] at hW
  have h₂ := CoreSpec.of_callW (headIsProj_at p hq n ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb a1 hS₁ ha)
    (callW_of_callE h2)
  refine ErrClaim.bind_core h₂ (fun M₂ hS₂ => ?_)
  cases h3 : callE p n "head_is_proj" [b1] m₂ with
  | error e3 =>
    rw [h3, defeqTailE.k_head_is_proj_2.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv defeqTailE_nv h3
  | ok q =>
  obtain ⟨r₃, m₃⟩ := q
  rw [h3] at hW
  simp only [defeqTailE.k_head_is_proj_2] at hW
  have h₃ := CoreSpec.of_callW (headIsProj_at p hq n ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb b1 hS₂ hb)
    (callW_of_callE h3)
  refine ErrClaim.bind_core h₃ (fun M₃ hS₃ => ?_)
  have hpp : (!decBool r₂ && !decBool r₃) = decide (r₂.headD 0 = 0 ∧ r₃.headD 0 = 0) := by
    unfold decBool
    generalize r₂.headD 0 = u
    generalize r₃.headD 0 = v
    by_cases x : u = 0 <;> by_cases y : v = 0 <;> simp [x, y]
  rw [hpp]
  by_cases hp0 : r₂.headD 0 = 0 ∧ r₃.headD 0 = 0
  · rw [if_pos hp0] at hW
    simp only [hp0, and_self, decide_true, ↓reduceIte]
    exact hstk _ m₃ M₃ hS₃ hW
  rw [if_neg hp0] at hW
  simp only [hp0, decide_false, Bool.false_eq_true, ↓reduceIte]
  cases h4 : callE p n "whnf_core" [mode, 0, vis, d, a1] m₃ with
  | error e4 =>
    rw [h4, defeqTailE.k_whnf_core.none] at hW; cases hW
    exact ErrClaim.bind_left (CoreSpecE.of_callE (s₀ := ⟨m₃, Locals.init []⟩)
      (hKE.whnfCore F ⟨m₃, Locals.init []⟩ _ dn vis fe M₃ eb mode 0 d a1 hF hn
        ⟨hS₃, hs.mode4, hs.eb_mode⟩ ha) h4)
  | ok q =>
  obtain ⟨r₄, m₄⟩ := q
  rw [h4] at hW
  simp only [defeqTailE.k_whnf_core] at hW
  have h₄ := CoreSpec.of_callW (hK.whnfCore F ⟨m₃, Locals.init []⟩ _ dn vis fe M₃ eb mode 0 d a1 hF hn
    ⟨hS₃, hs.mode4, hs.eb_mode⟩ ha) (callW_of_callE h4)
  refine ErrClaim.bind_core h₄ (fun M₄ hS₄ => ?_)
  cases h5 : callE p n "whnf_core" [mode, 0, vis, d, b1] m₄ with
  | error e5 =>
    rw [h5, defeqTailE.k_whnf_core_2.none] at hW; cases hW
    exact ErrClaim.bind_left (CoreSpecE.of_callE (s₀ := ⟨m₄, Locals.init []⟩)
      (hKE.whnfCore F ⟨m₄, Locals.init []⟩ _ dn vis fe M₄ eb mode 0 d b1 hF hn
        ⟨hS₄, hs.mode4, hs.eb_mode⟩ hb) h5)
  | ok q =>
  obtain ⟨r₅, m₅⟩ := q
  rw [h5] at hW
  simp only [defeqTailE.k_whnf_core_2] at hW
  have h₅ := CoreSpec.of_callW (hK.whnfCore F ⟨m₄, Locals.init []⟩ _ dn vis fe M₄ eb mode 0 d b1 hF hn
    ⟨hS₄, hs.mode4, hs.eb_mode⟩ hb) (callW_of_callE h5)
  refine ErrClaim.bind_core h₅ (fun M₅ hS₅ => ?_)
  have heq : (decH r₄ == decE a1 && decH r₅ == decE b1) =
      decide (r₄.headD 0 = a1 ∧ r₅.headD 0 = b1) := by
    simp only [decH, decE_beq h₄.2.2.2 ha, decE_beq h₅.2.2.2 hb, Bool.decide_and]
  rw [heq]
  by_cases hm : r₄.headD 0 = a1 ∧ r₅.headD 0 = b1
  · rw [if_pos hm] at hW
    simp only [hm, and_self, decide_true, ↓reduceIte]
    exact hstk _ m₅ M₅ hS₅ hW
  rw [if_neg hm] at hW
  simp only [hm, decide_false, Bool.false_eq_true, ↓reduceIte]
  cases h6 : callE p n "defeq" [mode, vis, d, r₄.headD 0, r₅.headD 0] m₅ with
  | error e6 =>
    rw [h6, defeqTailE.k_defeq_stuck.none] at hW; cases hW
    exact CoreSpecE.of_callE (s₀ := ⟨m₅, Locals.init []⟩)
      (hKE.defeq F _ _ dn vis fe M₅ eb mode d (r₄.headD 0) (r₅.headD 0) hF hn
        ⟨hS₅, hs.mode4, hs.eb_mode⟩ h₄.2.2.2 h₅.2.2.2) h6
  | ok q => rw [h6] at hW; simp only [defeqTailE.k_defeq_stuck] at hW; cases hW

end L.Arena
