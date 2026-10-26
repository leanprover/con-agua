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

/-! ## `ldpr_exit`, the projection loop, `defeq_proj_pair` -/

namespace L.Arena

/-- **`reduce_proj_core`'s error spec** (whnf family; the error half of `ReduceProjCoreH`). -/
def ReduceProjCoreE (p : Prog) : Prop :=
  ∀ (n : Nat), KnotUpTo p n → KnotUpToE p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
  ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d sn i c : Word), SlotPre s₀ a₀ dn vis fe MM eb mode → HW sn → HW c →
    CoreSpecE p (n + 1) "reduce_proj_core" [mode, vis, d, sn, i, c]
      (reduceProjCore (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI sn) i.toNat
        (decE c)) s₀ a₀

/-- **`lazy_delta_step`'s error spec** (the error half of `LazyDeltaStepH`). -/
def LazyDeltaStepE (p : Prog) : Prop :=
  ∀ (n : Nat), KnotUpTo p n → KnotUpToE p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
  ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d a b : Word), SlotPre s₀ a₀ dn vis fe M eb mode → HW a → HW b →
    d.toNat < 2 ^ 63 →
    CoreSpecE p (n + 1) "lazy_delta_step" [mode, vis, d, a, b]
      (lazyDeltaStep (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) s₀ a₀

l_model ldprExit_specE (p : Prog) (hf : p.lookup "ldpr_exit" = some ldprExitL)
  fns [hf ↦ ldprExitE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

/-- **`ldpr_exit`'s error claim** (the error half of `ldprExit_refines`). -/
theorem ldprExit_refinesE (p : Prog) (hq : StuckProg p) (hc : StuckCallees p)
    (hrpE : ReduceProjCoreE p) (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) (F : Nat)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d sn i a b k : Word) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hsn : HW sn) (ha : HW a) (hb : HW b)
    (hk0 : k ≠ 0) :
    CoreSpecE p (n + 1) "ldpr_exit" [mode, vis, d, sn, i, a, b, k]
      (ldprExitT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI sn) i.toNat
        (decE a) (decE b) (decDSs [k])) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hkc : er.cls = 0
  · exact ErrClaim.of_cls0 hkc
  have hW := triple_of_callE_err (ldprExit_specE p hq.ldprExit (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d sn i a b k) hc0 (Err.code_ne_of_cls hkc)
  have hS := hs.rel
  have hKE := hkE n (Nat.le_refl _)
  have hdef : ∀ (st : AState) (m : Mem) (M' : ModeMaps) (x y : Word), CoreS dn m st vis fe M' eb →
      HW x → HW y → ldprExitE.k_defeq p (callE p n "defeq" [mode, vis, d, x, y] m) = .error er →
      ErrClaim ((coreKnot (decMode mode) fe id F).defeq d.toNat (decE x) (decE y)) st er := by
    intro st m M' x y hS' hx hy hW'
    cases h : callE p n "defeq" [mode, vis, d, x, y] m with
    | error e =>
      rw [h, ldprExitE.k_defeq.none] at hW'; cases hW'
      exact CoreSpecE.of_callE (s₀ := ⟨m, Locals.init []⟩)
        (hKE.defeq F _ st dn vis fe M' eb mode d x y hF hn ⟨hS', hs.mode4, hs.eb_mode⟩ hx hy) h
    | ok q => rw [h] at hW'; simp only [ldprExitE.k_defeq] at hW'; cases hW'
  simp only [ldprExitE] at hW
  by_cases h1 : k = 1
  · rw [if_pos h1] at hW; cases hW
  rw [if_neg h1] at hW
  have hst : decDSs [k] = (if k = 2 then .diff else .unknown) := by
    unfold decDSs; simp [hk0, h1]
  have hbody : ∀ st, (st = DeltaStepA.diff ∨ st = DeltaStepA.unknown) →
      ldprExitT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI sn) i.toNat
        (decE a) (decE b) st =
      (do match ← reduceProjCore (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat
            (decI sn) i.toNat (decE a) with
          | some x =>
            match ← reduceProjCore (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat
                (decI sn) i.toNat (decE b) with
            | some y => (coreKnot (decMode mode) fe id F).defeq d.toNat x y
            | none => (coreKnot (decMode mode) fe id F).defeq d.toNat (decE a) (decE b)
          | none => (coreKnot (decMode mode) fe id F).defeq d.toNat (decE a) (decE b)) := by
    rintro st (rfl | rfl) <;> rfl
  rw [hbody _ (by rw [hst]; split <;> simp)]
  cases h1 : callE p n "reduce_proj_core" [mode, vis, d, sn, i, a] s₀.mem with
  | error e1 =>
    rw [h1, ldprExitE.k_reduce_proj_core.none] at hW; cases hW
    refine ErrClaim.bind_left (ErrClaim.of_callE_succ h1 fun j hj h' => ?_)
    subst hj
    exact CoreSpecE.of_callE (hrpE j (hk.mono (by omega)) (hkE.mono (by omega)) F (by omega)
      (by omega) s₀ a₀ dn vis fe M eb mode d sn i a hs hsn ha) h'
  | ok q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [h1] at hW
  simp only [ldprExitE.k_reduce_proj_core] at hW
  obtain ⟨n', rfl⟩ := callE_succ h1
  have h₁ := CoreSpec.of_callW (hc.reduceProjCore n' (hk.mono (by omega)) F (by omega) (by omega) s₀
    a₀ dn vis fe M eb mode d sn i a hs hsn ha) (callW_of_callE h1)
  refine ErrClaim.bind_core h₁ (fun M₁ hS₁ => ?_)
  by_cases f1 : r₁.headD 0 ≠ 0
  · rw [if_pos f1] at hW
    rw [decOptR_someS f1]
    cases h2 : callE p (n' + 1) "reduce_proj_core" [mode, vis, d, sn, i, b] m₁ with
    | error e2 =>
      rw [h2, ldprExitE.k_reduce_proj_core_2.none] at hW; cases hW
      exact ErrClaim.bind_left (CoreSpecE.of_callE (s₀ := ⟨m₁, Locals.init []⟩)
        (hrpE n' (hk.mono (by omega)) (hkE.mono (by omega)) F (by omega) (by omega)
          ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode d sn i b ⟨hS₁, hs.mode4, hs.eb_mode⟩ hsn hb) h2)
    | ok q =>
    obtain ⟨r₂, m₂⟩ := q
    rw [h2] at hW
    simp only [ldprExitE.k_reduce_proj_core_2] at hW
    have h₂ := CoreSpec.of_callW (hc.reduceProjCore n' (hk.mono (by omega)) F (by omega) (by omega)
      ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode d sn i b ⟨hS₁, hs.mode4, hs.eb_mode⟩ hsn hb)
      (callW_of_callE h2)
    refine ErrClaim.bind_core h₂ (fun M₂ hS₂ => ?_)
    by_cases f2 : r₂.headD 0 ≠ 0
    · rw [if_pos f2] at hW
      rw [decOptR_someS f2]
      exact hdef _ m₂ M₂ _ _ hS₂ h₁.2.2.2.2 h₂.2.2.2.2 hW
    · rw [if_neg f2] at hW
      rw [decOptR_noneS (by simpa using f2)]
      exact hdef _ m₂ M₂ _ _ hS₂ ha hb hW
  · rw [if_neg f1] at hW
    rw [decOptR_noneS (by simpa using f1)]
    exact hdef _ m₁ M₁ _ _ hS₁ ha hb hW

end L.Arena

namespace L.Arena

l_model ldpr_specE (p : Prog) (hf : p.lookup "lazy_delta_proj_reduction" = some lazyDeltaProjReductionL)
  fns [hf ↦ ldprE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

theorem ldprE_loop1_zero (p : Prog) (m : Mem) (mode vis d sn i a b : Word) :
    ldprE.loop1 p 0 m mode vis d sn i a b = .error .outOfFuel := by
  unfold ldprE.loop1; rfl

/-- **The projection loop's error claim** at every twin loop fuel `K + 1 ≥ k` (the error half of
`ldprW_ok`). -/
theorem ldprLoop_okE (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) (hlsE : LazyDeltaStepE p)
    (hrpE : ReduceProjCoreE p) (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n)
    (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (mode d sn i : Word) (hmode : mode < 4) (hsn : HW sn) (hd : d.toNat < 2 ^ 63) :
    ∀ k, k ≤ n + 1 → ∀ K, k ≤ K + 1 → ∀ (m : Mem) (a : AState) (MM : ModeMaps) (eb x y : Word)
      (er : Err), CoreS dn m a vis fe MM eb → eb = (mode >>> 1) &&& 1 → HW x → HW y →
      ldprE.loop1 p k m mode vis d sn i x y = .error er →
      ErrClaim (lazyDeltaProjReduction (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat
        (decI sn) i.toNat K (decE x) (decE y)) a er := by
  intro k
  induction k with
  | zero =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ h
    rw [ldprE_loop1_zero] at h; cases h
    exact ErrClaim.of_cls0 Err.cls_outOfFuel
  | succ k ih =>
    intro hkn K hK m a MM eb x y er hS heb hx hy h
    rw [ldprE.loop1.arm1 _ _ _ _ _ _ _ _ _ _ rfl] at h
    cases hcl : callE p k "lazy_delta_step" [mode, vis, d, x, y] m with
    | error e =>
      rw [hcl, ldprE.k_lazy_delta_step.none] at h; cases h
      refine ErrClaim.of_callE_succ hcl fun j hj h' => ?_
      subst hj
      obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
      exact ErrClaim.bind_left (CoreSpecE.of_callE (s₀ := ⟨m, Locals.init []⟩)
        (hlsE j (hk.mono (by omega)) (hkE.mono (by omega)) F (by omega) (by omega)
          ⟨m, Locals.init []⟩ a dn vis fe MM eb mode d x y ⟨hS, hmode, heb⟩ hx hy hd) h')
    | ok q =>
    obtain ⟨r, m₁⟩ := q
    rw [hcl] at h
    obtain ⟨j, rfl⟩ := callE_succ hcl
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    have hstep := hc.lazyDeltaStep j (hk.mono (by omega)) F (by omega) (by omega)
      ⟨m, Locals.init []⟩ a dn vis fe MM eb mode d x y ⟨hS, hmode, heb⟩ hx hy hd
    obtain ⟨hok, hA, hres, hrw⟩ := CoreSpec.of_callW hstep (callW_of_callE hcl)
    have hsr := AM.run_of_ok _ _ hok
    rw [hres] at hsr
    obtain ⟨M', hS₁, -, -⟩ := hA
    by_cases h0 : r.headD 0 = 0
    · rw [ldprE.k_lazy_delta_step.arm2 _ _ _ _ _ _ _ _ _ _ _ h0] at h
      rw [decDS_zero h0] at hsr
      exact ErrClaim.congr_run (ldpr_cont_run (decMode mode) (coreKnot (decMode mode) fe id F) fe
        d.toNat (decI sn) i.toNat K' (decE x) (decE y) _ _ a _ hsr)
        (ih (by omega) K' (by omega) m₁ _ M' eb _ _ er hS₁ heb hrw.2.1 hrw.2.2 h)
    · rw [ldprE.k_lazy_delta_step.arm1 _ _ _ _ _ _ _ _ _ _ _ h0] at h
      have hds : decDSs r = decDSs [r.headD 0] := decDS_nz h0
      have hnc : ∀ a' b', decDSs r ≠ .cont a' b' := decDS_ne_cont h0
      have hrun := ldpr_exit_run (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI sn)
        i.toNat K' (decE x) (decE y) _ _ _ hnc hsr
      rw [hds] at hrun
      cases hx' : callE p (j + 1) "ldpr_exit" [mode, vis, d, sn, i, x, y, r.headD 0] m₁ with
      | error e =>
        rw [hx', ldprE.k_ldpr_exit.none] at h; cases h
        exact ErrClaim.congr_run hrun (CoreSpecE.of_callE (s₀ := ⟨m₁, Locals.init []⟩)
          (ldprExit_refinesE p hq hc hrpE j (hk.mono (by omega)) (hkE.mono (by omega)) F
            ⟨m₁, Locals.init []⟩ _ dn vis fe M' eb mode d sn i x y (r.headD 0) (by omega) (by omega)
            ⟨hS₁, hmode, heb⟩ hsn hx hy h0) hx')
      | ok q => rw [hx', ldprE.k_ldpr_exit.arm1] at h; cases h

/-- **`lazy_delta_proj_reduction`'s error spec** (the error half of `ldpr_refines`). -/
def LdprE (p : Prog) : Prop :=
  ∀ (n : Nat), KnotUpTo p n → KnotUpToE p n → ∀ (F K : Nat), n ≤ F → n ≤ K → n ≤ 2 ^ 62 →
  ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d sn i a b : Word), SlotPre s₀ a₀ dn vis fe M eb mode → HW sn → HW a →
    HW b → d.toNat < 2 ^ 63 →
    CoreSpecE p (n + 1) "lazy_delta_proj_reduction" [mode, vis, d, sn, i, a, b]
      (lazyDeltaProjReduction (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI sn)
        i.toNat K (decE a) (decE b)) s₀ a₀

/-- **`lazy_delta_proj_reduction`'s error claim** (`LdprE`). -/
theorem ldpr_refinesE (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) (hlsE : LazyDeltaStepE p)
    (hrpE : ReduceProjCoreE p) : LdprE p := by
  intro n hk hkE F K hF hK hn s₀ a₀ dn vis fe M eb mode d sn i a b hs hsn ha hb hd
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hkc : er.cls = 0
  · exact ErrClaim.of_cls0 hkc
  have hW := triple_of_callE_err (ldpr_specE p hq.ldpr (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d sn i a b) hc0 (Err.code_ne_of_cls hkc)
  rw [ldprE.arm1] at hW
  exact ldprLoop_okE p hq hc hlsE hrpE n hk hkE F hF hn dn vis fe mode d sn i hs.mode4 hsn hd
    (n + 1) (Nat.le_refl _) K (by omega) _ a₀ M eb a b er hs.rel hs.eb_mode ha hb hW

l_model defeqProjPair_specE (p : Prog) (hf : p.lookup "defeq_proj_pair" = some defeqProjPairL)
  fns [hf ↦ defeqProjPairE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

/-- **`defeq_proj_pair`'s error claim** (`ProjPairE`). -/
theorem projPair_refinesE (p : Prog) (hq : StuckProg p) (hldprE : LdprE p) : ProjPairE p := by
  intro n hk hkE F s₀ a₀ dn vis fe M eb mode d a b hF hn hs ha hb hd
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hkc : er.cls = 0
  · exact ErrClaim.of_cls0 hkc
  have hW := triple_of_callE_err (defeqProjPair_specE p hq.projPair (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d a b) hc0 (Err.code_ne_of_cls hkc)
  simp only [defeqProjPairE] at hW
  have hS := hs.rel
  have hR := hS.arena.1
  by_cases g1 : a >>> 28 ≠ 9
  · rw [if_pos g1] at hW; cases hW
  rw [if_neg g1] at hW
  by_cases g2 : b >>> 28 ≠ 9
  · rw [if_pos g2] at hW; cases hW
  rw [if_neg g2] at hW
  have g1' : a >>> 28 = 9 := by simpa using g1
  have g2' : b >>> 28 = 9 := by simpa using g2
  by_cases c1 : tierW a ≠ 0 ∧ rdW (s₀.mem.arr64 CTL) 1 = 0
  · rw [if_pos c1] at hW; cases hW; exact ErrClaim.of_cls0 rfl
  rw [if_neg c1] at hW
  by_cases c2 : tcnt s₀.mem PROJ (tierW a) ≤ idxW a
  · rw [if_pos c2] at hW; cases hW; exact ErrClaim.of_cls0 rfl
  rw [if_neg c2] at hW
  by_cases c3 : tierW b ≠ 0 ∧ rdW (s₀.mem.arr64 CTL) 1 = 0
  · rw [if_pos c3] at hW; cases hW; exact ErrClaim.of_cls0 rfl
  rw [if_neg c3] at hW
  by_cases c4 : tcnt s₀.mem PROJ (tierW b) ≤ idxW b
  · rw [if_pos c4] at hW; cases hW; exact ErrClaim.of_cls0 rfl
  rw [if_neg c4] at hW
  obtain ⟨hva, hx1, hx3⟩ := view_proj s₀.mem a₀ hR a ha ⟨c1, by simpa using c2⟩ g1'
  obtain ⟨hvb, hy1, hy3⟩ := view_proj s₀.mem a₀ hR b hb ⟨c3, by simpa using c4⟩ g2'
  have htag : ∀ h : Word, HW h → ((decE h).tag == ETag.proj) = decide (h >>> 28 = 9) :=
    fun h hh => tag_beq_w _ hh 9 (by decide) ETag.proj rfl 9 rfl
  have hboth : ((decE a).tag == ETag.proj && (decE b).tag == ETag.proj) = true := by
    rw [htag a ha, htag b hb]; simp [g1', g2']
  refine ErrClaim.congr_run (pp_both _ _ fe _ _ _ a₀ hboth _ _ _ _ _ _ hva hvb) ?_
  generalize tfld s₀.mem PROJ (tierW a) (idxW a) 0 = x1 at hW hx1
  generalize tfld s₀.mem PROJ (tierW b) (idxW b) 0 = y1 at hW hy1
  generalize tfld s₀.mem PROJ (tierW a) (idxW a) 1 = x2 at hW
  generalize tfld s₀.mem PROJ (tierW b) (idxW b) 1 = y2 at hW
  generalize tfld s₀.mem PROJ (tierW a) (idxW a) 2 = x3 at hW hx3
  generalize tfld s₀.mem PROJ (tierW b) (idxW b) 2 = y3 at hW hy3
  by_cases e1 : x1 ≠ y1
  · rw [if_pos e1] at hW; cases hW
  rw [if_neg e1] at hW
  by_cases e2 : x2 ≠ y2
  · rw [if_pos e2] at hW; cases hW
  rw [if_neg e2] at hW
  have e1' : x1 = y1 := by simpa using e1
  have e2' : x2 = y2 := by simpa using e2
  subst e1' e2'
  simp only [beq_self_eq_true, Bool.and_self, ↓reduceIte]
  cases h1 : callE p n "lazy_delta_proj_reduction" [mode, vis, d, x1, x2, x3, y3] s₀.mem with
  | error e =>
    rw [h1, defeqProjPairE.k_lazy_delta_proj_reduction.none] at hW; cases hW
    refine ErrClaim.of_callE_succ h1 fun j hj h' => ?_
    subst hj
    exact CoreSpecE.of_callE (hldprE j (hk.mono (by omega)) (hkE.mono (by omega)) F defeqLoopFuel
      (by omega) (by unfold defeqLoopFuel; omega) (by omega) s₀ a₀ dn vis fe M eb mode d x1 x2 x3 y3
      hs hx1 hx3 hy3 hd) h'
  | ok q => rw [h1] at hW; simp only [defeqProjPairE.k_lazy_delta_proj_reduction] at hW; cases hW

end L.Arena

/-! ## `stuck_irrel` -/

namespace L.Arena

/-- **`struct_eta_cert`'s error spec** (whnf family; the error half of `setCert_refines`). -/
def SetCertE (p : Prog) : Prop :=
  ∀ (n : Nat), KnotUpTo p n → KnotUpToE p n → ∀ (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word),
    n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe M eb mode → HW a → HW b →
    CoreSpecE p (n + 1) "struct_eta_cert" [mode, vis, d, a, b]
      (structEtaCert (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) s₀ a₀

/-- **`struct_unit_cert`'s error spec** (whnf family; the error half of `suCert_refines`). -/
def SuCertE (p : Prog) : Prop :=
  ∀ (n : Nat), KnotUpTo p n → KnotUpToE p n → ∀ (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word),
    n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe M eb mode → HW a → HW b →
    CoreSpecE p (n + 1) "struct_unit_cert" [mode, vis, d, a, b]
      (structUnitCert (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) s₀ a₀

/-- **`proof_irrel`'s error spec** (whnf family; the error half of `ProofIrrelOK`). -/
def ProofIrrelE (p : Prog) : Prop :=
  ∀ (n : Nat), KnotUpTo p n → KnotUpToE p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
  ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d a b : Word), CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 →
    eb = (mode >>> 1) &&& 1 → HW a → HW b →
    CoreSpecE p (n + 1) "proof_irrel" [mode, vis, d, a, b]
      (proofIrrel (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) s₀ a₀

/-- **`eta_cert`'s error spec** (whnf family; the error half of `etaCert_refines`). -/
def EtaCertE (p : Prog) : Prop :=
  ∀ (n : Nat), KnotUpTo p n → KnotUpToE p n → ∀ (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d ty1 body1 b : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe M eb mode →
    HW ty1 → HW body1 → HW b →
    CoreSpecE p (n + 1) "eta_cert" [mode, vis, d, ty1, body1, b]
      (etaCert (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE ty1) (decE body1)
        (decE b)) s₀ a₀

/-- **`stuck_irrel`'s error spec** (the error half of `stuckIrrel_refines`). -/
def StuckIrrelE (p : Prog) : Prop :=
  ∀ (n : Nat), KnotUpTo p n → KnotUpToE p n → ∀ (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word),
    n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe M eb mode → HW a → HW b →
    CoreSpecE p (n + 1) "stuck_irrel" [mode, vis, d, a, b]
      (stuckIrrel (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) s₀ a₀

l_model stuckIrrel_specE (p : Prog) (hf : p.lookup "stuck_irrel" = some stuckIrrelL)
  fns [hf ↦ stuckIrrelE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

/-- **`stuck_irrel`'s error claim** (`StuckIrrelE`). -/
theorem stuckIrrel_refinesE (p : Prog) (hq : StuckProg p) (hi : IotaProg' p) (hc : StuckCallees p)
    (hsetE : SetCertE p) (hsuE : SuCertE p) (hpiE : ProofIrrelE p) : StuckIrrelE p := by
  intro n hk hkE F s₀ a₀ dn vis fe M eb mode d a b hF hn hs ha hb
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hkc : er.cls = 0
  · exact ErrClaim.of_cls0 hkc
  have hW := triple_of_callE_err (stuckIrrel_specE p hq.stuckIrrel (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d a b) hc0 (Err.code_ne_of_cls hkc)
  simp only [stuckIrrelE] at hW
  unfold stuckIrrel
  cases h1 : callE p n "struct_eta_cert" [mode, vis, d, a, b] s₀.mem with
  | error e =>
    rw [h1, stuckIrrelE.k_struct_eta_cert.none] at hW; cases hW
    refine ErrClaim.bind_left (ErrClaim.of_callE_succ h1 fun j hj h' => ?_)
    subst hj
    exact CoreSpecE.of_callE (hsetE j (hk.mono (by omega)) (hkE.mono (by omega)) F s₀ a₀ dn vis fe M
      eb mode d a b (by omega) (by omega) hs ha hb) h'
  | ok q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [h1] at hW
  simp only [stuckIrrelE.k_struct_eta_cert] at hW
  have h₁ := CoreSpec.of_callW (setCert_at p hq hi hc n hk F s₀ a₀ dn vis fe M eb mode d a b hF hn hs
    ha hb) (callW_of_callE h1)
  refine ErrClaim.bind_core h₁ (fun M₁ hS₁ => ?_)
  by_cases g1 : r₁.headD 0 ≠ 0
  · rw [if_pos g1] at hW; cases hW
  rw [if_neg g1] at hW
  rw [decBool_false_of (by simpa using g1)]
  simp only [Bool.false_eq_true, ↓reduceIte]
  cases h2 : callE p n "struct_eta_cert" [mode, vis, d, b, a] m₁ with
  | error e =>
    rw [h2, stuckIrrelE.k_struct_eta_cert_2.none] at hW; cases hW
    refine ErrClaim.bind_left (ErrClaim.of_callE_succ h2 fun j hj h' => ?_)
    subst hj
    exact CoreSpecE.of_callE (s₀ := ⟨m₁, Locals.init []⟩) (hsetE j (hk.mono (by omega))
      (hkE.mono (by omega)) F _ _ dn vis fe M₁ eb mode d b a (by omega) (by omega)
      ⟨hS₁, hs.mode4, hs.eb_mode⟩ hb ha) h'
  | ok q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [h2] at hW
  simp only [stuckIrrelE.k_struct_eta_cert_2] at hW
  have h₂ := CoreSpec.of_callW (setCert_at p hq hi hc n hk F ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb
    mode d b a hF hn ⟨hS₁, hs.mode4, hs.eb_mode⟩ hb ha) (callW_of_callE h2)
  refine ErrClaim.bind_core h₂ (fun M₂ hS₂ => ?_)
  by_cases g2 : r₂.headD 0 ≠ 0
  · rw [if_pos g2] at hW; cases hW
  rw [if_neg g2] at hW
  rw [decBool_false_of (by simpa using g2)]
  simp only [Bool.false_eq_true, ↓reduceIte]
  cases h3 : callE p n "struct_unit_cert" [mode, vis, d, a, b] m₂ with
  | error e =>
    rw [h3, stuckIrrelE.k_struct_unit_cert.none] at hW; cases hW
    refine ErrClaim.bind_left (ErrClaim.of_callE_succ h3 fun j hj h' => ?_)
    subst hj
    exact CoreSpecE.of_callE (s₀ := ⟨m₂, Locals.init []⟩) (hsuE j (hk.mono (by omega))
      (hkE.mono (by omega)) F _ _ dn vis fe M₂ eb mode d a b (by omega) (by omega)
      ⟨hS₂, hs.mode4, hs.eb_mode⟩ ha hb) h'
  | ok q =>
  obtain ⟨r₃, m₃⟩ := q
  rw [h3] at hW
  simp only [stuckIrrelE.k_struct_unit_cert] at hW
  have h₃ := CoreSpec.of_callW (suCert_at p hq hc n hk F ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb
    mode d a b hF hn ⟨hS₂, hs.mode4, hs.eb_mode⟩ ha hb) (callW_of_callE h3)
  refine ErrClaim.bind_core h₃ (fun M₃ hS₃ => ?_)
  by_cases g3 : r₃.headD 0 ≠ 0
  · rw [if_pos g3] at hW; cases hW
  rw [if_neg g3] at hW
  rw [decBool_false_of (by simpa using g3)]
  simp only [Bool.false_eq_true, ↓reduceIte]
  cases h4 : callE p n "proof_irrel" [mode, vis, d, a, b] m₃ with
  | error e =>
    rw [h4, stuckIrrelE.k_proof_irrel.none] at hW; cases hW
    refine ErrClaim.of_callE_succ h4 fun j hj h' => ?_
    subst hj
    exact CoreSpecE.of_callE (s₀ := ⟨m₃, Locals.init []⟩) (hpiE j (hk.mono (by omega))
      (hkE.mono (by omega)) F (by omega) (by omega) _ _ dn vis fe M₃ eb mode d a b hS₃ hs.mode4
      hs.eb_mode ha hb) h'
  | ok q => rw [h4] at hW; simp only [stuckIrrelE.k_proof_irrel] at hW; cases hW

end L.Arena

/-! ## `stuck_rest`: the free-variable, constant and λ arms (a decline site) -/

namespace L.Arena

l_model stuckRest_specE (p : Prog) (hf : p.lookup "stuck_rest" = some stuckRestL)
  fns [hf ↦ stuckRestE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

theorem stuckRestE_nv : "lvls_eq_c" ∈ L.Checker.nvFns := by decide +kernel

/-- **`stuck_rest`'s error claim** (the error half of `stuckRest_refines`): the level comparison of
two constants of the same name declines when `lvls_eq_c` runs out of fuel (`none`, the twin's
`liftFueled`); every other failure is a callee's. -/
theorem stuckRest_refinesE (p : Prog) (hq : StuckProg p) (hc : StuckCallees p)
    (hirrE : StuckIrrelE p) (hetaE : EtaCertE p) (hnv : closedNV p L.Checker.nvFns = true)
    (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a b ga a1 a2 gb b1 b2 : Word) (va vb : ENodeView) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b)
    (hva : a₀.store.view (decE a) = some va) (hvb : a₀.store.view (decE b) = some vb)
    (hwa : ViewW ga a1 a2 va) (hwb : ViewW gb b1 b2 vb)
    (h1 : ¬ (ga = 8 ∧ gb = 4)) (h2 : ¬ (ga = 4 ∧ gb = 8)) (h3 : ¬ (ga = 4 ∧ gb = 4)) :
    CoreSpecE p (n + 1) "stuck_rest" [mode, vis, d, a, b, ga, a1, a2, gb, b1, b2]
      (defeqStuck (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b))
      s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hkc : er.cls = 0
  · exact ErrClaim.of_cls0 hkc
  have hW := triple_of_callE_err (stuckRest_specE p hq.stuckRest (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d a b ga a1 a2 gb b1 b2) hc0 (Err.code_ne_of_cls hkc)
  have hS := hs.rel
  have hirr : ∀ (st : AState) (m : Mem) (M' : ModeMaps), CoreS dn m st vis fe M' eb →
      stuckRestE.k_stuck_irrel p (callE p n "stuck_irrel" [mode, vis, d, a, b] m) = .error er →
      ErrClaim (stuckIrrel (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) st er := by
    intro st m M' hS' hW'
    cases h : callE p n "stuck_irrel" [mode, vis, d, a, b] m with
    | error e =>
      rw [h, stuckRestE.k_stuck_irrel.none] at hW'; cases hW'
      refine ErrClaim.of_callE_succ h fun j hj h' => ?_
      subst hj
      exact CoreSpecE.of_callE (s₀ := ⟨m, Locals.init []⟩) (hirrE j (hk.mono (by omega))
        (hkE.mono (by omega)) F _ st dn vis fe M' eb mode d a b (by omega) (by omega)
        ⟨hS', hs.mode4, hs.eb_mode⟩ ha hb) h'
    | ok q => rw [h] at hW'; simp only [stuckRestE.k_stuck_irrel] at hW'; cases hW'
  have hta := hwa.tag
  have htb := hwb.tag
  simp only [stuckRestE] at hW
  -- the free variables
  by_cases hf : ga = 1 ∧ gb = 1
  · rw [if_pos hf.1, if_pos hf.2] at hW
    obtain ⟨i, t, rfl⟩ := tagV_fvar (hta ▸ hf.1)
    obtain ⟨j, u, rfl⟩ := tagV_fvar (htb ▸ hf.2)
    refine ErrClaim.congr_run (ds_fvar _ _ fe _ _ _ a₀ i j t u hva hvb) ?_
    have hij : (i == j) = decide (a1 = b1) := by
      rw [← hwa.2, ← hwb.2]
      by_cases e : a1 = b1
      · simp [e]
      · have : a1.toNat ≠ b1.toNat := fun e' => e (UInt64.toNat_inj.mp e')
        simp [e, this]
    rw [hij]
    by_cases e : a1 = b1
    · rw [if_pos e] at hW; cases hW
    · rw [if_neg e] at hW
      simp only [e, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact hirr a₀ s₀.mem M hS hW
  have hW1 : stuckRestE.j1 p n mode vis d a b ga a1 a2 gb b1 b2 s₀.mem = .error er := by
    by_cases g : ga = 1
    · rw [if_pos g, if_neg (fun h => hf ⟨g, h⟩)] at hW; exact hW
    · rw [if_neg g] at hW; exact hW
  clear hW
  simp only [stuckRestE.j1] at hW1
  -- the constants
  by_cases hcn : ga = 3 ∧ gb = 3
  · rw [if_pos hcn.1, if_pos hcn.2] at hW1
    obtain ⟨nm, us, rfl⟩ := tagV_const (hta ▸ hcn.1)
    obtain ⟨nm', us', rfl⟩ := tagV_const (htb ▸ hcn.2)
    obtain ⟨-, hw1, hd1, hw2, hd2⟩ := hwa
    obtain ⟨-, hw1', hd1', hw2', hd2'⟩ := hwb
    refine ErrClaim.congr_run (ds_const _ _ fe _ _ _ a₀ nm nm' us us' hva hvb) ?_
    rw [← hd1, ← hd1', ← hd2, ← hd2']
    by_cases e : a1 = b1
    · rw [if_pos e] at hW1
      rw [if_pos (by rw [e])]
      cases hl : callE p n "lvls_eq_c" [a2, b2] s₀.mem with
      | error e1 =>
        rw [hl, stuckRestE.k_lvls_eq_c.none] at hW1; cases hW1
        exact ErrClaim.of_callE_nv hnv stuckRestE_nv hl
      | ok q =>
      obtain ⟨r₁, m₁⟩ := q
      rw [hl] at hW1
      simp only [stuckRestE.k_lvls_eq_c] at hW1
      have h₁ := CoreSpec.of_callW (hc.lvlsEqC n ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe M eb a2 b2 hS
        hw2 hw2' (by rw [hd2]; exact (hc.den _ _ _ _ _ _ _ hS).constLs _ _ _ hva)
        (by rw [hd2']; exact (hc.den _ _ _ _ _ _ _ hS).constLs _ _ _ hvb)) (callW_of_callE hl)
      refine ErrClaim.bind_core h₁ (fun M₁ hS₁ => ?_)
      by_cases z0 : r₁.headD 0 = 0
      · -- the decline: `lvls_eq_c` ran out of fuel, the twin's `liftFueled` fails
        rw [if_pos z0] at hW1; cases hW1
        have : decO (r₁.headD 0) = none := by unfold decO; rw [if_pos z0]
        rw [this]
        exact ErrClaim.bind_left (ErrClaim.fail _ _ rfl)
      rw [if_neg z0] at hW1
      by_cases z1 : r₁.headD 0 = 1
      · rw [if_neg (fun h => h z1)] at hW1
        have : decO (r₁.headD 0) = some false := by unfold decO; rw [if_neg z0, if_pos z1]
        rw [this]
        exact hirr _ m₁ M₁ hS₁ hW1
      · rw [if_pos z1] at hW1; cases hW1
    · rw [if_neg e] at hW1
      rw [if_neg (fun h => e (decI_inj hw1 hw1' h))]
      exact hirr a₀ s₀.mem M hS hW1
  have hW2 : stuckRestE.j2 p n mode vis d a b ga a1 a2 gb b1 b2 s₀.mem = .error er := by
    by_cases g : ga = 3
    · rw [if_pos g, if_neg (fun h => hcn ⟨g, h⟩)] at hW1; exact hW1
    · rw [if_neg g] at hW1; exact hW1
  clear hW1
  simp only [stuckRestE.j2] at hW2
  have hlam : ∀ (t bd : EIdx) (w1 w2 x : Word) (T : AM Bool),
      HW w1 → decE w1 = t → HW w2 → decE w2 = bd → HW x →
      T.run a₀ = (lamArmT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat
        (decE a) (decE b) t bd (decE x)).run a₀ →
      stuckRestE.k_eta_cert p n mode vis d a b (callE p n "eta_cert" [mode, vis, d, w1, w2, x] s₀.mem)
        = .error er →
      ErrClaim T a₀ er := by
    intro t bd w1 w2 x T hw1 hd1 hw2 hd2 hx hT hW
    refine ErrClaim.congr_run hT ?_
    unfold lamArmT
    cases he : callE p n "eta_cert" [mode, vis, d, w1, w2, x] s₀.mem with
    | error e =>
      rw [he, stuckRestE.k_eta_cert.none] at hW; cases hW
      refine ErrClaim.bind_left (ErrClaim.of_callE_succ he fun j hj h' => ?_)
      subst hj
      have := CoreSpecE.of_callE (hetaE j (hk.mono (by omega)) (hkE.mono (by omega)) F s₀ a₀ dn vis
        fe M eb mode d w1 w2 x (by omega) (by omega) hs hw1 hw2 hx) h'
      rw [hd1, hd2] at this
      exact this
    | ok q =>
    obtain ⟨r₁, m₁⟩ := q
    rw [he] at hW
    simp only [stuckRestE.k_eta_cert] at hW
    have h₁ := CoreSpec.of_callW (etaCert_at p hq hc n hk F s₀ a₀ dn vis fe M eb mode d w1 w2 x hF hn
      hs hw1 hw2 hx) (callW_of_callE he)
    rw [hd1, hd2] at h₁
    refine ErrClaim.bind_core h₁ (fun M₁ hS₁ => ?_)
    by_cases e0 : r₁.headD 0 ≠ 0
    · rw [if_pos e0] at hW; cases hW
    · rw [if_neg e0] at hW
      rw [decBool_false_of (by simpa using e0)]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact hirr _ m₁ M₁ hS₁ hW
  by_cases hl : ga = 5
  · rw [if_pos hl] at hW2
    obtain ⟨t, bd, rfl⟩ := tagV_lam (hta ▸ hl)
    obtain ⟨-, hw1, hd1, hw2, hd2⟩ := hwa
    exact hlam t bd a1 a2 b _ hw1 hd1 hw2 hd2 hb (ds_lamL _ _ fe _ _ _ a₀ t bd vb hva hvb) hW2
  rw [if_neg hl] at hW2
  by_cases hl' : gb = 5
  · rw [if_pos hl'] at hW2
    obtain ⟨t, bd, rfl⟩ := tagV_lam (htb ▸ hl')
    obtain ⟨-, hw1, hd1, hw2, hd2⟩ := hwb
    exact hlam t bd b1 b2 a _ hw1 hd1 hw2 hd2 ha
      (ds_lamR _ _ fe _ _ _ a₀ t bd va hva hvb (by rw [← hta]; exact hl)) hW2
  rw [if_neg hl'] at hW2
  refine ErrClaim.congr_run (ds_irrel _ _ fe _ _ _ a₀ va vb hva hvb (by rw [← hta, ← htb]; exact h1)
    (by rw [← hta, ← htb]; exact h2) (by rw [← hta, ← htb]; exact hf)
    (by rw [← hta, ← htb]; exact hcn) (by rw [← hta, ← htb]; exact h3) (by rw [← hta]; exact hl)
    (by rw [← htb]; exact hl')) ?_
  exact hirr a₀ s₀.mem M hS hW2

end L.Arena
