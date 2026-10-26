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
  · rw [ite_eq_left h0] at hW; cases hW
  rw [ite_eq_right h0] at hW
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
  · rw [ite_eq_left hp0] at hW
    simp only [hp0, and_self, decide_true, ↓reduceIte]
    exact hstk _ m₃ M₃ hS₃ hW
  rw [ite_eq_right hp0] at hW
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
  · rw [ite_eq_left hm] at hW
    simp only [hm, and_self, decide_true, ↓reduceIte]
    exact hstk _ m₅ M₅ hS₅ hW
  rw [ite_eq_right hm] at hW
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
  · rw [ite_eq_left h1] at hW; cases hW
  rw [ite_eq_right h1] at hW
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
  · rw [ite_eq_left f1] at hW
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
    · rw [ite_eq_left f2] at hW
      rw [decOptR_someS f2]
      exact hdef _ m₂ M₂ _ _ hS₂ h₁.2.2.2.2 h₂.2.2.2.2 hW
    · rw [ite_eq_right f2] at hW
      rw [decOptR_noneS (by simpa using f2)]
      exact hdef _ m₂ M₂ _ _ hS₂ ha hb hW
  · rw [ite_eq_right f1] at hW
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
  · rw [ite_eq_left g1] at hW; cases hW
  rw [ite_eq_right g1] at hW
  by_cases g2 : b >>> 28 ≠ 9
  · rw [ite_eq_left g2] at hW; cases hW
  rw [ite_eq_right g2] at hW
  have g1' : a >>> 28 = 9 := by simpa using g1
  have g2' : b >>> 28 = 9 := by simpa using g2
  by_cases c1 : tierW a ≠ 0 ∧ rdW (s₀.mem.arr64 CTL) 1 = 0
  · rw [ite_eq_left c1] at hW; cases hW; exact ErrClaim.of_cls0 rfl
  rw [ite_eq_right c1] at hW
  by_cases c2 : tcnt s₀.mem PROJ (tierW a) ≤ idxW a
  · rw [ite_eq_left c2] at hW; cases hW; exact ErrClaim.of_cls0 rfl
  rw [ite_eq_right c2] at hW
  by_cases c3 : tierW b ≠ 0 ∧ rdW (s₀.mem.arr64 CTL) 1 = 0
  · rw [ite_eq_left c3] at hW; cases hW; exact ErrClaim.of_cls0 rfl
  rw [ite_eq_right c3] at hW
  by_cases c4 : tcnt s₀.mem PROJ (tierW b) ≤ idxW b
  · rw [ite_eq_left c4] at hW; cases hW; exact ErrClaim.of_cls0 rfl
  rw [ite_eq_right c4] at hW
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
  · rw [ite_eq_left e1] at hW; cases hW
  rw [ite_eq_right e1] at hW
  by_cases e2 : x2 ≠ y2
  · rw [ite_eq_left e2] at hW; cases hW
  rw [ite_eq_right e2] at hW
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
  · rw [ite_eq_left g1] at hW; cases hW
  rw [ite_eq_right g1] at hW
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
  · rw [ite_eq_left g2] at hW; cases hW
  rw [ite_eq_right g2] at hW
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
  · rw [ite_eq_left g3] at hW; cases hW
  rw [ite_eq_right g3] at hW
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
  · rw [ite_eq_left hf.1, ite_eq_left hf.2] at hW
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
    · rw [ite_eq_left e] at hW; cases hW
    · rw [ite_eq_right e] at hW
      simp only [e, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact hirr a₀ s₀.mem M hS hW
  have hW1 : stuckRestE.j1 p n mode vis d a b ga a1 a2 gb b1 b2 s₀.mem = .error er := by
    by_cases g : ga = 1
    · rw [ite_eq_left g, ite_eq_right (fun h => hf ⟨g, h⟩)] at hW; exact hW
    · rw [ite_eq_right g] at hW; exact hW
  clear hW
  simp only [stuckRestE.j1] at hW1
  -- the constants
  by_cases hcn : ga = 3 ∧ gb = 3
  · rw [ite_eq_left hcn.1, ite_eq_left hcn.2] at hW1
    obtain ⟨nm, us, rfl⟩ := tagV_const (hta ▸ hcn.1)
    obtain ⟨nm', us', rfl⟩ := tagV_const (htb ▸ hcn.2)
    obtain ⟨-, hw1, hd1, hw2, hd2⟩ := hwa
    obtain ⟨-, hw1', hd1', hw2', hd2'⟩ := hwb
    refine ErrClaim.congr_run (ds_const _ _ fe _ _ _ a₀ nm nm' us us' hva hvb) ?_
    rw [← hd1, ← hd1', ← hd2, ← hd2']
    by_cases e : a1 = b1
    · rw [ite_eq_left e] at hW1
      rw [ite_eq_left (by rw [e])]
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
        rw [ite_eq_left z0] at hW1; cases hW1
        have : decO (r₁.headD 0) = none := by unfold decO; rw [ite_eq_left z0]
        rw [this]
        exact ErrClaim.bind_left (ErrClaim.fail _ _ rfl)
      rw [ite_eq_right z0] at hW1
      by_cases z1 : r₁.headD 0 = 1
      · rw [ite_eq_right (fun h => h z1)] at hW1
        have : decO (r₁.headD 0) = some false := by unfold decO; rw [ite_eq_right z0, ite_eq_left z1]
        rw [this]
        exact hirr _ m₁ M₁ hS₁ hW1
      · rw [ite_eq_left z1] at hW1; cases hW1
    · rw [ite_eq_right e] at hW1
      rw [ite_eq_right (fun h => e (decI_inj hw1 hw1' h))]
      exact hirr a₀ s₀.mem M hS hW1
  have hW2 : stuckRestE.j2 p n mode vis d a b ga a1 a2 gb b1 b2 s₀.mem = .error er := by
    by_cases g : ga = 3
    · rw [ite_eq_left g, ite_eq_right (fun h => hcn ⟨g, h⟩)] at hW1; exact hW1
    · rw [ite_eq_right g] at hW1; exact hW1
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
    · rw [ite_eq_left e0] at hW; cases hW
    · rw [ite_eq_right e0] at hW
      rw [decBool_false_of (by simpa using e0)]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact hirr _ m₁ M₁ hS₁ hW
  by_cases hl : ga = 5
  · rw [ite_eq_left hl] at hW2
    obtain ⟨t, bd, rfl⟩ := tagV_lam (hta ▸ hl)
    obtain ⟨-, hw1, hd1, hw2, hd2⟩ := hwa
    exact hlam t bd a1 a2 b _ hw1 hd1 hw2 hd2 hb (ds_lamL _ _ fe _ _ _ a₀ t bd vb hva hvb) hW2
  rw [ite_eq_right hl] at hW2
  by_cases hl' : gb = 5
  · rw [ite_eq_left hl'] at hW2
    obtain ⟨t, bd, rfl⟩ := tagV_lam (htb ▸ hl')
    obtain ⟨-, hw1, hd1, hw2, hd2⟩ := hwb
    exact hlam t bd b1 b2 a _ hw1 hd1 hw2 hd2 ha
      (ds_lamR _ _ fe _ _ _ a₀ t bd va hva hvb (by rw [← hta]; exact hl)) hW2
  rw [ite_eq_right hl'] at hW2
  refine ErrClaim.congr_run (ds_irrel _ _ fe _ _ _ a₀ va vb hva hvb (by rw [← hta, ← htb]; exact h1)
    (by rw [← hta, ← htb]; exact h2) (by rw [← hta, ← htb]; exact hf)
    (by rw [← hta, ← htb]; exact hcn) (by rw [← hta, ← htb]; exact h3) (by rw [← hta]; exact hl)
    (by rw [← htb]; exact hl')) ?_
  exact hirr a₀ s₀.mem M hS hW2

end L.Arena

/-! ## `stuck_str` -/

namespace L.Arena

l_model stuckStr_specE (p : Prog) (hf : p.lookup "stuck_str" = some stuckStrL)
  fns [hf ↦ stuckStrE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] heartbeats 1000000
  simp [] errors

/-- **`stuck_str`'s error claim** (the error half of `stuckStr_refines`). -/
theorem stuckStr_refinesE (p : Prog) (hq : StuckProg p) (hc : StuckCallees p)
    (hirrE : StuckIrrelE p) (hnv : closedNV p L.Checker.nvFns = true)
    (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a b side lt fo : Word) (l : ConLeche.Literal) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) (hlt : HW lt) (hfo : HW fo)
    (hg : lt >>> 28 = 8) (hl : a₀.store.view (decE lt) = some (.lit l)) :
    CoreSpecE p (n + 1) "stuck_str" [mode, vis, d, a, b, side, lt, fo]
      (stuckStrT (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b) (side != 0) l
        (decE fo)) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hkc : er.cls = 0
  · exact ErrClaim.of_cls0 hkc
  have hW := triple_of_callE_err (stuckStr_specE p hq.stuckStr (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d a b side lt fo) hc0 (Err.code_ne_of_cls hkc)
  have hS := hs.rel
  have hR := hS.arena.1
  have hKE := hkE n (Nat.le_refl _)
  have hirr : ∀ (st : AState) (m : Mem) (M' : ModeMaps), CoreS dn m st vis fe M' eb →
      stuckStrE.j1 p n mode vis d a b m = .error er →
      ErrClaim (stuckIrrel (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) st er := by
    intro st m M' hS' hW'
    unfold stuckStrE.j1 at hW'
    cases h : callE p n "stuck_irrel" [mode, vis, d, a, b] m with
    | error e =>
      rw [h, stuckStrE.k_stuck_irrel.none] at hW'; cases hW'
      refine ErrClaim.of_callE_succ h fun j hj h' => ?_
      subst hj
      exact CoreSpecE.of_callE (s₀ := ⟨m, Locals.init []⟩) (hirrE j (hk.mono (by omega))
        (hkE.mono (by omega)) F _ st dn vis fe M' eb mode d a b (by omega) (by omega)
        ⟨hS', hs.mode4, hs.eb_mode⟩ ha hb) h'
    | ok q => rw [h] at hW'; simp only [stuckStrE.k_stuck_irrel] at hW'; cases hW'
  have hdef : ∀ (st : AState) (m : Mem) (M' : ModeMaps) (x y : Word), CoreS dn m st vis fe M' eb →
      HW x → HW y → stuckStrE.k_defeq p (callE p n "defeq" [mode, vis, d, x, y] m) = .error er →
      ErrClaim ((coreKnot (decMode mode) fe id F).defeq d.toNat (decE x) (decE y)) st er := by
    intro st m M' x y hS' hx hy hW'
    cases h : callE p n "defeq" [mode, vis, d, x, y] m with
    | error e =>
      rw [h, stuckStrE.k_defeq.none] at hW'; cases hW'
      exact CoreSpecE.of_callE (s₀ := ⟨m, Locals.init []⟩)
        (hKE.defeq F _ st dn vis fe M' eb mode d x y hF hn ⟨hS', hs.mode4, hs.eb_mode⟩ hx hy) h
    | ok q => rw [h] at hW'; simp only [stuckStrE.k_defeq, stuckStrE.j2] at hW'; cases hW'
  simp only [stuckStrE] at hW
  by_cases h1 : tierW lt ≠ 0 ∧ rdW (s₀.mem.arr64 CTL) 1 = 0
  · rw [ite_eq_left h1] at hW; cases hW; exact ErrClaim.of_cls0 rfl
  rw [ite_eq_right h1] at hW
  by_cases h2 : tcnt s₀.mem LIT (tierW lt) ≤ idxW lt
  · rw [ite_eq_left h2] at hW; cases hW; exact ErrClaim.of_cls0 rfl
  rw [ite_eq_right h2] at hW
  obtain ⟨kn, hkv, hrec⟩ := view_lit_f s₀.mem a₀ hR lt hlt ⟨h1, by simpa using h2⟩ hg
  rw [hl] at hkv
  have hkl : kn.l = l := by cases hkv; rfl
  obtain ⟨kl⟩ := kn
  simp only at hkl
  subst hkl
  cases kl with
  | natVal N =>
    have h0 : tfld s₀.mem LIT (tierW lt) (idxW lt) 0 = 0 := hrec.1
    rw [ite_eq_right (fun h => absurd (h0 ▸ h.1) (by decide))] at hW
    exact hirr a₀ s₀.mem M hS hW
  | strVal st =>
    have h0 : tfld s₀.mem LIT (tierW lt) (idxW lt) 0 = 1 := hrec.1
    rcases (Classical.em (fo >>> 28 = 3)).symm with h3 | h3
    · rw [ite_eq_right (fun h => h3 h.2)] at hW
      unfold stuckStrT
      rw [tag_beq_const _ hfo]
      simp only [h3, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact hirr a₀ s₀.mem M hS hW
    rw [ite_eq_left ⟨h0, h3⟩] at hW
    by_cases h4 : tierW fo ≠ 0 ∧ rdW (s₀.mem.arr64 CTL) 1 = 0
    · rw [ite_eq_left h4] at hW; cases hW; exact ErrClaim.of_cls0 rfl
    rw [ite_eq_right h4] at hW
    by_cases h5 : tcnt s₀.mem CONST (tierW fo) ≤ idxW fo
    · rw [ite_eq_left h5] at hW; cases hW; exact ErrClaim.of_cls0 rfl
    rw [ite_eq_right h5] at hW
    obtain ⟨hv, hnw, huw⟩ := L.Ind.view_const_f s₀.mem a₀ hR fo hfo ⟨h4, by simpa using h5⟩ h3
    have hct : ((decE fo).tag == ETag.const) = true := by rw [tag_beq_const _ hfo]; simp [h3]
    generalize tfld s₀.mem CONST (tierW fo) (idxW fo) 0 = co at hnw hW hv
    generalize tfld s₀.mem CONST (tierW fo) (idxW fo) 1 = uo at huw hW hv
    -- the pins
    cases hp1 : callE p n "pin_word" [52] s₀.mem with
    | error e => rw [hp1, stuckStrE.k_pin_word.none] at hW; cases hW; exact ErrClaim.of_nv hnv (by simp [defeqNVList]) hp1
    | ok q =>
    obtain ⟨r₁, m₁⟩ := q
    rw [hp1] at hW
    simp only [stuckStrE.k_pin_word] at hW
    obtain ⟨t₁, ht₁, hm₁, -, hr₁⟩ := triple_of_callE (s₀ := ⟨s₀.mem, Locals.init []⟩)
      (pinWord_rd p hq.leaf.pinword n ⟨s₀.mem, Locals.init []⟩ 52) hp1
    have em₁ : m₁ = s₀.mem := by rw [← ht₁]; exact hm₁
    subst em₁
    cases hp2 : callE p n "pin_at" [6] s₀.mem with
    | error e => rw [hp2, stuckStrE.k_pin_at.none] at hW; cases hW; exact ErrClaim.of_nv hnv (by simp [defeqNVList]) hp2
    | ok q =>
    obtain ⟨r₂, m₂⟩ := q
    obtain ⟨t₂, ht₂, hm₂, -, -, hr₂⟩ := triple_of_callE (s₀ := ⟨s₀.mem, Locals.init []⟩)
      (pinAt_rd p hq.leaf.pinat n ⟨s₀.mem, Locals.init []⟩ 6) hp2
    have em₂ : m₂ = s₀.mem := by rw [← ht₂]; exact hm₂
    subst em₂
    rw [hp2] at hW
    simp only [stuckStrE.k_pin_at] at hW
    -- `str_lit_supported`
    refine ErrClaim.congr_run (stuckStrT_run _ fe _ _ _ _ st _ a₀ s₀.mem hS.pins _ _ hct hv) ?_
    cases hp3 : callE p n "str_lit_supported" [vis] s₀.mem with
    | error e =>
      rw [hp3, stuckStrE.k_str_lit_supported.none] at hW; cases hW
      exact ErrClaim.of_nv hnv (by simp [defeqNVList]) hp3
    | ok q =>
    obtain ⟨r₃, m₃⟩ := q
    rw [hp3] at hW
    simp only [stuckStrE.k_str_lit_supported] at hW
    have h₃ := CoreSpec.of_callW (hc.strLitSupported n ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe M eb hS)
      (callW_of_callE hp3)
    refine ErrClaim.bind_core h₃ (fun M₃ hS₃ => ?_)
    have hsl : HW (rdW (s₀.mem.arr64 PINS) (1 + 6)) := by
      have := hS.pins.names_lt 6 (by decide); rwa [pinW_rdW s₀.mem (1 + 6) (1 + 6) rfl] at this
    have hel : HW (rdW (s₀.mem.arr64 PINS) 52) := by
      have := hS.pins.lv_lt.1; rwa [pinW_rdW s₀.mem 52 52 rfl] at this
    simp only [pinW_rdW s₀.mem (1 + 6) (1 + 6) rfl, pinW_rdW s₀.mem 52 52 rfl, decI_eq_iff' hnw hsl,
      decI_eq_iff' huw hel]
    rw [hr₁, hr₂] at hW
    by_cases hcond : co = rdW (s₀.mem.arr64 PINS) (1 + 6) ∧ uo = rdW (s₀.mem.arr64 PINS) 52 ∧
        r₃.headD 0 ≠ 0
    · rw [ite_eq_left hcond] at hW
      obtain ⟨hc₁, hc₂, hc₃⟩ := hcond
      rw [ite_eq_left ⟨hc₁, hc₂, decBool_true_of hc₃⟩]
      cases hp4 : callE p n "str_lit_ctor" [lt] m₃ with
      | error e =>
        rw [hp4, stuckStrE.k_str_lit_ctor.none] at hW; cases hW
        exact ErrClaim.of_nv hnv (by simp [defeqNVList]) hp4
      | ok q =>
      obtain ⟨r₄, m₄⟩ := q
      rw [hp4] at hW
      simp only [stuckStrE.k_str_lit_ctor] at hW
      have hv₃ := hc.supKeep fe a₀ (decE lt) _ hl
      have h₄ := CoreSpec.of_callW (hc.strLitCtor n ⟨m₃, Locals.init []⟩ _ dn vis fe M₃ eb lt st hS₃
        hlt hv₃) (callW_of_callE hp4)
      refine ErrClaim.bind_core h₄ (fun M₄ hS₄ => ?_)
      by_cases hsd : side = 0
      · rw [ite_eq_left hsd] at hW
        simp only [hsd, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        exact hdef _ m₄ M₄ _ _ hS₄ h₄.2.2.2 hb hW
      · rw [ite_eq_right hsd] at hW
        have : (side != 0) = true := by simpa using hsd
        simp only [this, ↓reduceIte]
        exact hdef _ m₄ M₄ _ _ hS₄ ha h₄.2.2.2 hW
    · rw [ite_eq_right hcond] at hW
      rw [ite_eq_right (fun h => hcond ⟨h.1, h.2.1, fun e => by
              have := h.2.2; rw [decBool_false_of e] at this; cases this⟩)]
      exact hirr _ m₃ M₃ hS₃ hW

end L.Arena

/-! ## `stuck_app_cong`, `stuck_app` -/

namespace L.Arena

/-- **`defeq_lst`'s error spec** (the error half of `DefeqLstOK`). -/
def DefeqLstE (p : Prog) : Prop :=
  ∀ (n : Nat), KnotUpTo p n → KnotUpToE p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
  ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d ao an bo bn : Word) (xs ys : Array EIdx),
    SlotPre s₀ a₀ dn vis fe M eb mode → SpineR s₀.mem ao an xs → SpineR s₀.mem bo bn ys →
    ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat → bo.toNat + bn.toNat ≤ (spTop s₀.mem).toNat →
    CoreSpecE p (n + 1) "defeq_lst" [mode, vis, d, ao, an, bo, bn]
      (defEqList (coreKnot (decMode mode) fe id F) fe d.toNat xs.toList ys.toList) s₀ a₀

l_model stuckAppCong_specE (p : Prog) (hf : p.lookup "stuck_app_cong" = some stuckAppCongL)
  fns [hf ↦ stuckAppCongE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

/-- **`stuck_app_cong`'s error claim** (the error half of `appCong_refines`). -/
theorem appCong_refinesE (p : Prog) (hq : StuckProg p) (hlstE : DefeqLstE p)
    (hnv : closedNV p L.Checker.nvFns = true) (n : Nat)
    (hk : KnotUpTo p n) (hkE : KnotUpToE p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word)
    (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) :
    CoreSpecE p (n + 1) "stuck_app_cong" [mode, vis, d, a, b]
      (appCongT (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hkc : er.cls = 0
  · exact ErrClaim.of_cls0 hkc
  have hW := triple_of_callE_err (stuckAppCong_specE p hq.stuckAppCong (n + 1)
    ⟨s₀.mem, Locals.init []⟩ mode vis d a b) hc0 (Err.code_ne_of_cls hkc)
  have hS := hs.rel
  have hK := hk n (Nat.le_refl _)
  have hKE := hkE n (Nat.le_refl _)
  have hspn := hS.spn
  rw [stuckAppCongE.arm1] at hW
  generalize rdW (s₀.mem.arr64 CTL) 136 = top at hW
  cases h1 : callE p n "get_app_args" [a] s₀.mem with
  | error e => rw [h1, stuckAppCongE.k_get_app_args.none] at hW; cases hW; exact ErrClaim.of_nv hnv (by simp [defeqNVList]) h1
  | ok q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [h1, stuckAppCongE.k_get_app_args.arm1] at hW
  obtain ⟨hf1, hg1, hr10, htop1, aa, hargs1, hsp1⟩ :=
    getAppArgs_callW hq.leaf.core.spine hS ha (callW_of_callE h1)
  have hS₁ := hS.frame_stk hf1 (by simp) (by simp)
  cases h2 : callE p n "get_app_args" [b] m₁ with
  | error e => rw [h2, stuckAppCongE.k_get_app_args_2.none] at hW; cases hW; exact ErrClaim.of_nv hnv (by simp [defeqNVList]) h2
  | ok q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [h2] at hW
  obtain ⟨hf2, hg2, hr20, htop2, bb, hargs2, hsp2⟩ :=
    getAppArgs_callW hq.leaf.core.spine hS₁ hb (callW_of_callE h2)
  have hS₂ := hS₁.frame_stk hf2 (by simp) (by simp)
  have hla : aa.length = (r₁.tail.headD 0).toNat := by simpa using hsp1.size
  have hlb : bb.length = (r₂.tail.headD 0).toNat := by simpa using hsp2.size
  have hspn₁ : (m₁.arr64 SPN).size < 2 ^ 63 := hg1.size ▸ hspn
  have hspn₂ : (m₂.arr64 SPN).size < 2 ^ 63 := hg2.size ▸ hspn₁
  simp only [stuckAppCongE.k_get_app_args_2] at hW
  rcases (Classical.em (r₁.tail.headD 0 = r₂.tail.headD 0)).symm with heq | heq
  · rw [ite_eq_right heq] at hW; cases hW
  rw [ite_eq_left heq] at hW
  have heq' : aa.length = bb.length := by rw [hla, hlb, heq]
  cases h3 : callE p n "get_app_fn" [a] m₂ with
  | error e => rw [h3, stuckAppCongE.k_get_app_fn.none] at hW; cases hW; exact ErrClaim.of_nv hnv (by simp [defeqNVList]) h3
  | ok q =>
  obtain ⟨r₃, m₃⟩ := q
  rw [h3, stuckAppCongE.k_get_app_fn.arm1] at hW
  obtain ⟨rfl, hh3, hgaf3⟩ := getAppFn_callW hq.leaf hS₂.arena.1 ha (callW_of_callE h3)
  cases h4 : callE p n "get_app_fn" [b] m₃ with
  | error e => rw [h4, stuckAppCongE.k_get_app_fn_2.none] at hW; cases hW; exact ErrClaim.of_nv hnv (by simp [defeqNVList]) h4
  | ok q =>
  obtain ⟨r₄, m₄⟩ := q
  rw [h4, stuckAppCongE.k_get_app_fn_2.arm1] at hW
  obtain ⟨rfl, hh4, hgaf4⟩ := getAppFn_callW hq.leaf hS₂.arena.1 hb (callW_of_callE h4)
  refine ErrClaim.congr_run (appCongT_eq _ fe _ _ _ a₀ aa bb hargs1 hargs2 heq' _ _ hgaf3 hgaf4) ?_
  cases h5 : callE p n "defeq" [mode, vis, d, r₃.headD 0, r₄.headD 0] m₄ with
  | error e =>
    rw [h5, stuckAppCongE.k_defeq.none] at hW; cases hW
    exact ErrClaim.bind_left (CoreSpecE.of_callE (s₀ := ⟨m₄, Locals.init []⟩)
      (hKE.defeq F ⟨m₄, Locals.init []⟩ a₀ dn vis fe M eb mode d (r₃.headD 0) (r₄.headD 0) hF hn
        ⟨hS₂, hs.mode4, hs.eb_mode⟩ hh3 hh4) h5)
  | ok q =>
  obtain ⟨r₅, m₅⟩ := q
  rw [h5] at hW
  simp only [stuckAppCongE.k_defeq] at hW
  have h₅ := CoreSpec.of_callW (hK.defeq F ⟨m₄, Locals.init []⟩ a₀ dn vis fe M eb mode d (r₃.headD 0)
    (r₄.headD 0) hF hn ⟨hS₂, hs.mode4, hs.eb_mode⟩ hh3 hh4) (callW_of_callE h5)
  obtain ⟨_, _, _, hst₅⟩ := h₅.2.1
  refine ErrClaim.bind_core h₅ (fun M₅ hS₅ => ?_)
  by_cases h0 : r₅.headD 0 = 0
  · rw [ite_eq_right (fun h => h h0)] at hW; cases hW
  rw [ite_eq_left h0] at hW
  rw [decBool_true_of h0]
  simp only [↓reduceIte]
  cases h6 : callE p n "defeq_lst" [mode, vis, d, r₁.headD 0, r₁.tail.headD 0, r₂.headD 0,
      r₂.tail.headD 0] m₅ with
  | error e =>
    rw [h6, stuckAppCongE.k_defeq_lst.none] at hW; cases hW
    have hb1 := hsp1.bound
    have hb2 := hsp2.bound
    have e1 : (spTop m₁).toNat = (r₁.headD 0).toNat + (r₁.tail.headD 0).toNat := by
      rw [htop1, ← hr10, addW_toNat (by omega)]
    have e2 : (spTop m₄).toNat = (r₂.headD 0).toNat + (r₂.tail.headD 0).toNat := by
      rw [htop2, ← hr20, addW_toNat (by have := hg1.size; omega)]
    have hle12 : (spTop m₁).toNat ≤ (spTop m₄).toNat := UInt64.le_iff_toNat_le.mp hg2.1
    have h5top : spTop m₅ = spTop m₄ := hst₅.1
    have hA : SpineR m₅ (r₁.headD 0) (r₁.tail.headD 0) aa.toArray :=
      (hsp1.grew hg2 (by omega) hspn₁).keep hst₅.size hst₅.below (by omega) hspn₂
    have hB : SpineR m₅ (r₂.headD 0) (r₂.tail.headD 0) bb.toArray :=
      hsp2.keep hst₅.size hst₅.below (by omega) hspn₂
    refine ErrClaim.of_callE_succ h6 fun j hj h' => ?_
    subst hj
    have := CoreSpecE.of_callE (s₀ := ⟨m₅, Locals.init []⟩)
      (hlstE j (hk.mono (by omega)) (hkE.mono (by omega)) F (by omega) (by omega)
        ⟨m₅, Locals.init []⟩ _ dn vis fe M₅ eb mode d (r₁.headD 0) (r₁.tail.headD 0) (r₂.headD 0)
        (r₂.tail.headD 0) aa.toArray bb.toArray ⟨hS₅, hs.mode4, hs.eb_mode⟩ hA hB
        (by rw [h5top]; omega) (by rw [h5top]; omega)) h'
    simpa only [List.toList_toArray] using this
  | ok q => rw [h6, stuckAppCongE.k_defeq_lst.arm1] at hW; simp only [stuckAppCongE.j1] at hW; cases hW

/-- **`stuck_app_cong`'s error spec** (`appCong_refinesE`'s shape at one fuel below). -/
def AppCongE (p : Prog) : Prop :=
  ∀ (n : Nat), KnotUpTo p n → KnotUpToE p n → ∀ (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word),
    n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe M eb mode → HW a → HW b →
    CoreSpecE p (n + 1) "stuck_app_cong" [mode, vis, d, a, b]
      (appCongT (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) s₀ a₀

theorem appCongE_of (p : Prog) (hq : StuckProg p) (hlstE : DefeqLstE p)
    (hnv : closedNV p L.Checker.nvFns = true) : AppCongE p :=
  fun n hk hkE F s₀ a₀ dn vis fe M eb mode d a b hF hn hs ha hb =>
    appCong_refinesE p hq hlstE hnv n hk hkE F s₀ a₀ dn vis fe M eb mode d a b hF hn hs ha hb

l_model stuckApp_specE (p : Prog) (hf : p.lookup "stuck_app" = some stuckAppL)
  fns [hf ↦ stuckAppE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

/-- **`stuck_app`'s error claim** (the error half of `stuckApp_refines`). -/
theorem stuckApp_refinesE (p : Prog) (hq : StuckProg p) (hc : StuckCallees p)
    (hacE : AppCongE p) (hirrE : StuckIrrelE p) (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n)
    (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d a b : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) :
    CoreSpecE p (n + 1) "stuck_app" [mode, vis, d, a, b]
      (stuckAppT (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hkc : er.cls = 0
  · exact ErrClaim.of_cls0 hkc
  have hW := triple_of_callE_err (stuckApp_specE p hq.stuckApp (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d a b) hc0 (Err.code_ne_of_cls hkc)
  simp only [stuckAppE] at hW
  rw [stuckAppT_eq]
  cases h1 : callE p n "stuck_app_cong" [mode, vis, d, a, b] s₀.mem with
  | error e =>
    rw [h1, stuckAppE.k_stuck_app_cong.none] at hW; cases hW
    refine ErrClaim.bind_left (ErrClaim.of_callE_succ h1 fun j hj h' => ?_)
    subst hj
    exact CoreSpecE.of_callE (hacE j (hk.mono (by omega)) (hkE.mono (by omega)) F s₀ a₀ dn vis fe M
      eb mode d a b (by omega) (by omega) hs ha hb) h'
  | ok q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [h1] at hW
  simp only [stuckAppE.k_stuck_app_cong] at hW
  have h₁ := CoreSpec.of_callW (appCong_at p hq hc n hk F s₀ a₀ dn vis fe M eb mode d a b hF hn hs ha
    hb) (callW_of_callE h1)
  refine ErrClaim.bind_core h₁ (fun M₁ hS₁ => ?_)
  by_cases h0 : r₁.headD 0 ≠ 0
  · rw [ite_eq_left h0] at hW; cases hW
  rw [ite_eq_right h0] at hW
  rw [decBool_false_of (by simpa using h0)]
  simp only [Bool.false_eq_true, ↓reduceIte]
  cases h2 : callE p n "stuck_irrel" [mode, vis, d, a, b] m₁ with
  | error e =>
    rw [h2, stuckAppE.k_stuck_irrel.none] at hW; cases hW
    refine ErrClaim.of_callE_succ h2 fun j hj h' => ?_
    subst hj
    exact CoreSpecE.of_callE (s₀ := ⟨m₁, Locals.init []⟩) (hirrE j (hk.mono (by omega))
      (hkE.mono (by omega)) F _ _ dn vis fe M₁ eb mode d a b (by omega) (by omega)
      ⟨hS₁, hs.mode4, hs.eb_mode⟩ ha hb) h'
  | ok q => rw [h2] at hW; simp only [stuckAppE.k_stuck_irrel] at hW; cases hW

end L.Arena

/-! ## `defeq_stuck`: the dispatcher -/

namespace L.Arena

/-- **`stuck_str`'s error spec** (`stuckStr_refinesE`'s shape). -/
def StuckStrE (p : Prog) : Prop :=
  ∀ (n : Nat), KnotUpTo p n → KnotUpToE p n → ∀ (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a b side lt fo : Word) (l : ConLeche.Literal), n ≤ F → n ≤ 2 ^ 62 →
    SlotPre s₀ a₀ dn vis fe M eb mode → HW a → HW b → HW lt → HW fo → lt >>> 28 = 8 →
    a₀.store.view (decE lt) = some (.lit l) →
    CoreSpecE p (n + 1) "stuck_str" [mode, vis, d, a, b, side, lt, fo]
      (stuckStrT (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b) (side != 0) l
        (decE fo)) s₀ a₀

/-- **`stuck_app`'s error spec** (`stuckApp_refinesE`'s shape). -/
def StuckAppE (p : Prog) : Prop :=
  ∀ (n : Nat), KnotUpTo p n → KnotUpToE p n → ∀ (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word),
    n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe M eb mode → HW a → HW b →
    CoreSpecE p (n + 1) "stuck_app" [mode, vis, d, a, b]
      (stuckAppT (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) s₀ a₀

/-- **`stuck_rest`'s error spec** (`stuckRest_refinesE`'s shape). -/
def StuckRestE (p : Prog) : Prop :=
  ∀ (n : Nat), KnotUpTo p n → KnotUpToE p n → ∀ (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a b ga a1 a2 gb b1 b2 : Word) (va vb : ENodeView), n ≤ F → n ≤ 2 ^ 62 →
    SlotPre s₀ a₀ dn vis fe M eb mode → HW a → HW b →
    a₀.store.view (decE a) = some va → a₀.store.view (decE b) = some vb →
    ViewW ga a1 a2 va → ViewW gb b1 b2 vb →
    ¬ (ga = 8 ∧ gb = 4) → ¬ (ga = 4 ∧ gb = 8) → ¬ (ga = 4 ∧ gb = 4) →
    CoreSpecE p (n + 1) "stuck_rest" [mode, vis, d, a, b, ga, a1, a2, gb, b1, b2]
      (defeqStuck (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) s₀ a₀

theorem stuckStrE_of (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) (hirrE : StuckIrrelE p)
    (hnv : closedNV p L.Checker.nvFns = true) : StuckStrE p :=
  fun n hk hkE F s₀ a₀ dn vis fe M eb mode d a b side lt fo l hF hn hs ha hb hlt hfo hg hl =>
    stuckStr_refinesE p hq hc hirrE hnv n hk hkE F s₀ a₀ dn vis fe M eb mode d a b side lt fo l hF hn
      hs ha hb hlt hfo hg hl

theorem stuckAppE_of (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) (hacE : AppCongE p)
    (hirrE : StuckIrrelE p) : StuckAppE p :=
  fun n hk hkE F s₀ a₀ dn vis fe M eb mode d a b hF hn hs ha hb =>
    stuckApp_refinesE p hq hc hacE hirrE n hk hkE F s₀ a₀ dn vis fe M eb mode d a b hF hn hs ha hb

theorem stuckRestE_of (p : Prog) (hq : StuckProg p) (hc : StuckCallees p) (hirrE : StuckIrrelE p)
    (hetaE : EtaCertE p) (hnv : closedNV p L.Checker.nvFns = true) : StuckRestE p :=
  fun n hk hkE F s₀ a₀ dn vis fe M eb mode d a b ga a1 a2 gb b1 b2 va vb hF hn hs ha hb hva hvb hwa
      hwb h1 h2 h3 =>
    stuckRest_refinesE p hq hc hirrE hetaE hnv n hk hkE F s₀ a₀ dn vis fe M eb mode d a b ga a1 a2 gb
      b1 b2 va vb hF hn hs ha hb hva hvb hwa hwb h1 h2 h3

l_model defeqStuck_specE (p : Prog) (hf : p.lookup "defeq_stuck" = some defeqStuckL)
  fns [hf ↦ defeqStuckE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

/-- **`defeq_stuck`'s error claim** (`DefeqStuckE`, the error half of `defeqStuck_refines`). -/
theorem defeqStuck_refinesE (p : Prog) (hq : StuckProg p) (hstrE : StuckStrE p) (happE : StuckAppE p)
    (hrestE : StuckRestE p) (hnv : closedNV p L.Checker.nvFns = true) : DefeqStuckE p := by
  intro n hk hkE F s₀ a₀ dn vis fe M eb mode d a b hF hn hs ha hb
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hkc : er.cls = 0
  · exact ErrClaim.of_cls0 hkc
  have hW := triple_of_callE_err (defeqStuck_specE p hq.defeqStuck (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d a b) hc0 (Err.code_ne_of_cls hkc)
  have hS := hs.rel
  simp only [defeqStuckE] at hW
  cases hca : callE p n "e_view" [a] s₀.mem with
  | error e => rw [hca, defeqStuckE.k_e_view.none] at hW; cases hW; exact ErrClaim.of_nv hnv (by simp [defeqNVList]) hca
  | ok q =>
  obtain ⟨ra, m₁⟩ := q
  rw [hca] at hW
  simp only [defeqStuckE.k_e_view] at hW
  obtain ⟨t₁, ht₁, hts₁, hne₁, hra⟩ := triple_of_callE (L.Ind.eView_spec p hq.eview n s₀ a) hca
  have hm₁ : m₁ = s₀.mem := by rw [← ht₁, hts₁]
  subst hm₁
  cases hcb : callE p n "e_view" [b] s₀.mem with
  | error e => rw [hcb, defeqStuckE.k_e_view_2.none] at hW; cases hW; exact ErrClaim.of_nv hnv (by simp [defeqNVList]) hcb
  | ok q =>
  obtain ⟨rb, m₂⟩ := q
  rw [hcb] at hW
  simp only [defeqStuckE.k_e_view_2] at hW
  obtain ⟨t₂, ht₂, hts₂, hne₂, hrb⟩ := triple_of_callE
    (L.Ind.eView_spec p hq.eview n ⟨s₀.mem, Locals.init []⟩ b) hcb
  have hm₂ : m₂ = s₀.mem := by rw [← ht₂, hts₂]
  subst hm₂
  have hne₁' : L.Ind.eViewW s₀.mem a ≠ [] := hra ▸ hne₁
  have hne₂' : L.Ind.eViewW s₀.mem b ≠ [] := hrb ▸ hne₂
  have hhda := eViewW_head s₀.mem a hne₁'
  have hhdb := eViewW_head s₀.mem b hne₂'
  rw [← hra] at hhda
  rw [← hrb] at hhdb
  obtain ⟨va, hva, hvra⟩ := L.Ind.eViewW_ok s₀.mem a₀ hS.arena.1 a hne₁'
  obtain ⟨vb, hvb, hvrb⟩ := L.Ind.eViewW_ok s₀.mem a₀ hS.arena.1 b hne₂'
  rw [← hra] at hvra
  rw [← hrb] at hvrb
  have hta := viewR_tag hvra
  have htb := viewR_tag hvrb
  have hsl : SlotPre ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe M eb mode := ⟨hS, hs.mode4, hs.eb_mode⟩
  -- a call's failure, through the one continuation
  have fin : ∀ {T : AM Bool} {f : FnName} {vs : List Word},
      (∀ j, n = j + 1 → CoreSpecE p (j + 1) f vs T ⟨s₀.mem, Locals.init []⟩ a₀) →
      defeqStuckE.k_stuck_rest p (callE p n f vs s₀.mem) = .error er → ErrClaim T a₀ er := by
    intro T f vs hsp hW'
    cases h : callE p n f vs s₀.mem with
    | error e =>
      rw [h, defeqStuckE.k_stuck_rest.none] at hW'; cases hW'
      exact ErrClaim.of_callE_succ h fun j hj h' => CoreSpecE.of_callE (hsp j hj) (hj ▸ h')
    | ok q => rw [h] at hW'; simp only [defeqStuckE.k_stuck_rest] at hW'; cases hW'
  by_cases c1 : ra.headD 0 = 8 ∧ rb.headD 0 = 4
  · rw [ite_eq_left c1.1, ite_eq_left c1.2] at hW
    obtain ⟨l, rfl⟩ := tagV_lit (hta ▸ c1.1)
    obtain ⟨fo, x, rfl⟩ := tagV_app (htb ▸ c1.2)
    obtain ⟨-, hfw, hfo, -, -⟩ := hvrb
    rw [getD1] at hfw hfo
    refine ErrClaim.congr_run (ds_strL _ _ fe _ _ _ a₀ l fo x hva hvb) ?_
    refine fin (fun j hj => ?_) hW
    subst hj
    have h := hstrE j (hk.mono (by omega)) (hkE.mono (by omega)) F _ a₀ dn vis fe M eb mode d a b 0 a
      (rb.tail.headD 0) l (by omega) (by omega) hsl ha hb ha hfw (by rw [← hhda]; exact c1.1) hva
    rw [hfo] at h
    simpa using h
  have hW1 : defeqStuckE.j1 p n mode vis d a b (ra.headD 0) (ra.tail.headD 0) (ra.tail.tail.headD 0)
      (rb.headD 0) (rb.tail.headD 0) (rb.tail.tail.headD 0) s₀.mem = .error er := by
    by_cases g : ra.headD 0 = 8
    · rw [ite_eq_left g, ite_eq_right (fun h => c1 ⟨g, h⟩)] at hW; exact hW
    · rw [ite_eq_right g] at hW; exact hW
  clear hW
  simp only [defeqStuckE.j1] at hW1
  by_cases c2 : ra.headD 0 = 4 ∧ rb.headD 0 = 8
  · rw [ite_eq_left c2.1, ite_eq_left c2.2] at hW1
    obtain ⟨fo, x, rfl⟩ := tagV_app (hta ▸ c2.1)
    obtain ⟨l, rfl⟩ := tagV_lit (htb ▸ c2.2)
    obtain ⟨-, hfw, hfo, -, -⟩ := hvra
    rw [getD1] at hfw hfo
    refine ErrClaim.congr_run (ds_strR _ _ fe _ _ _ a₀ l fo x hva hvb) ?_
    refine fin (fun j hj => ?_) hW1
    subst hj
    have h := hstrE j (hk.mono (by omega)) (hkE.mono (by omega)) F _ a₀ dn vis fe M eb mode d a b 1 b
      (ra.tail.headD 0) l (by omega) (by omega) hsl ha hb hb hfw (by rw [← hhdb]; exact c2.2) hvb
    rw [hfo] at h
    simpa using h
  by_cases c3 : ra.headD 0 = 4 ∧ rb.headD 0 = 4
  · rw [ite_eq_left c3.1, ite_eq_right (fun h => c2 ⟨c3.1, h⟩), ite_eq_left c3.2] at hW1
    obtain ⟨f, x, rfl⟩ := tagV_app (hta ▸ c3.1)
    obtain ⟨g, y, rfl⟩ := tagV_app (htb ▸ c3.2)
    refine ErrClaim.congr_run (ds_app _ _ fe _ _ _ a₀ f x g y hva hvb) ?_
    refine fin (fun j hj => ?_) hW1
    subst hj
    exact happE j (hk.mono (by omega)) (hkE.mono (by omega)) F _ a₀ dn vis fe M eb mode d a b
      (by omega) (by omega) hsl ha hb
  have hW2 : defeqStuckE.j2 p n mode vis d a b (ra.headD 0) (ra.tail.headD 0) (ra.tail.tail.headD 0)
      (rb.headD 0) (rb.tail.headD 0) (rb.tail.tail.headD 0) s₀.mem = .error er := by
    by_cases g : ra.headD 0 = 4
    · rw [ite_eq_left g, ite_eq_right (fun h => c2 ⟨g, h⟩), ite_eq_right (fun h => c3 ⟨g, h⟩)] at hW1; exact hW1
    · rw [ite_eq_right g] at hW1; exact hW1
  unfold defeqStuckE.j2 at hW2
  refine fin (fun j hj => ?_) hW2
  subst hj
  exact hrestE j (hk.mono (by omega)) (hkE.mono (by omega)) F _ a₀ dn vis fe M eb mode d a b _ _ _ _ _
    _ va vb (by omega) (by omega) hsl ha hb hva hvb (viewW_of hvra) (viewW_of hvrb) c1 c2 c3

end L.Arena
