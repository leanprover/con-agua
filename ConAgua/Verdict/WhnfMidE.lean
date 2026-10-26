import ConAgua.Verdict.WhnfModels7E
import ConAgua.Verdict.WhnfNatE
import ConAgua.Arena.DefEqMidLazy2
import ConAgua.Arena.IndTwin

/-!
# The `whnf` family's `defeq` helpers: `whnf_top`, `bool_true_shortcut`, `try_unfold_proj_app`,
`delta_quick`, `lazy_nat` (lane `verdicts-b`, helper `k2`)

No verdict site of their own: their claims are the knot's slots' (`KnotUpToE`), `reduce_nat`'s
(`callE_reduceNat`) and `quick_defeq`'s (a callee of the `defeq` family: `QuickDefeqWE`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

theorem whnfMidE_nv : ∀ f ∈ ["is_bool_true", "head_is_proj"], f ∈ L.Checker.nvFns := by
  decide +kernel

/-! ## `whnf_top` -/

/-- **`whnf_top`'s verdicts** are the `whnf` slot's (the verified mode). -/
theorem whnfTop_refinesE (p : Prog) (hw : p.lookup "whnf_top" = some whnfTopL) (n : Nat)
    (hkE : KnotUpToE p n) (hn : n + 1 ≤ 2 ^ 62) (F : Nat) (hF : n ≤ F) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (dep e : Word)
    (hS : CoreS dn s₀.mem a₀ vis fe M 0) (he : HW e) :
    CoreSpecE p (n + 1) "whnf_top" [vis, dep, e] (whnf ConLeche.CheckMode.verified fe F dep.toNat (decE e)) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (wtopE_spec p hw (n + 1) ⟨s₀.mem, Locals.init []⟩ vis dep e) hc0
    (Err.code_ne_of_cls hk0)
  simp only [wtopE] at hW
  have hW' := err_of_k (by intro q e; simp [wtopE.k_whnf]) (fun _ => rfl) hW
  have := CoreSpecE.of_callE ((hkE n (Nat.le_refl _)).whnf F s₀ a₀ dn vis fe M 0 0 dep e hF (by omega)
    (slotPre_zero hS) he) hW'
  exact this

/-! ## `bool_true_shortcut`, `try_unfold_proj_app` -/

theorem bts_err (r : CoreFnsA) (depth : Nat) (a : EIdx) (s : AState) (ce : CheckError)
    (h : (r.whnf depth a).run s = .error ce) : (boolTrueShortcut r depth a).run s = .error ce := by
  simp only [boolTrueShortcut, StateT.run_bind, h]; rfl

section mid
variable (p : Prog) (hp : DefEqMidProg p) (hnv : closedNV p L.Checker.nvFns = true)
include hp hnv

/-- **`bool_true_shortcut`'s verdicts** are the `whnf` slot's. -/
theorem boolTrueShortcut_refinesE (n : Nat) (hkE : KnotUpToE p n)
    (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d a : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) :
    CoreSpecE p (n + 1) "bool_true_shortcut" [mode, vis, d, a]
      (boolTrueShortcut (coreKnot (decMode mode) fe id F) d.toNat (decE a)) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (btsE_spec p hp.bts (n + 1) ⟨s₀.mem, Locals.init []⟩ mode vis d a) hc0
    (Err.code_ne_of_cls hk0)
  simp only [btsE] at hW
  cases c1 : callE p n "whnf" [mode, vis, d, a] s₀.mem with
  | error e1 =>
    rw [c1, btsE.k_whnf.none] at hW; cases hW
    exact ErrClaim.of_run_err (fun ce h' => bts_err _ _ _ a₀ ce h')
      (CoreSpecE.of_callE ((hkE n (Nat.le_refl _)).whnf F s₀ a₀ dn vis fe M eb mode d a hF hn hs ha) c1)
  | ok q =>
  rw [c1] at hW
  simp only [btsE.k_whnf] at hW
  exact ErrClaim.of_callE_nv hnv (whnfMidE_nv "is_bool_true" (by simp))
    (err_of_k (by intro q e; simp [btsE.k_is_bool_true]) (fun _ => rfl) hW)

/-- **`try_unfold_proj_app`'s verdicts** are the `whnf_core` slot's. -/
theorem tryUnfoldProjApp_refinesE (n : Nat) (hkE : KnotUpToE p n)
    (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d e : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (he : HW e) :
    CoreSpecE p (n + 1) "try_unfold_proj_app" [mode, vis, d, e]
      (tryUnfoldProjApp (coreKnot (decMode mode) fe id F) d.toNat (decE e)) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (tupaE_spec p hp.tupa (n + 1) ⟨s₀.mem, Locals.init []⟩ mode vis d e)
    hc0 (Err.code_ne_of_cls hk0)
  simp only [tupaE] at hW
  cases c1 : callE p n "head_is_proj" [e] s₀.mem with
  | error e1 =>
    rw [c1, tupaE.k_head_is_proj.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (whnfMidE_nv "head_is_proj" (by simp)) c1
  | ok q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [c1] at hW
  simp only [tupaE.k_head_is_proj] at hW
  split at hW
  · cases hW
  rename_i h0
  have hW' := err_of_k (by intro q e; simp only [tupaE.k_whnf_core]; split <;> simp) (fun _ => rfl) hW
  obtain ⟨k, rfl⟩ := callW_succ (callW_of_callE c1)
  have h₁ := CoreSpec.of_callW (headIsProj_refines p hp.leaf k s₀ a₀ dn vis fe M eb e hs.rel he)
    (callW_of_callE c1)
  obtain ⟨hok1, ⟨M₁, hS₁, -, -⟩, hres1, -⟩ := h₁
  have hrun1 := AM.run_of_ok _ _ hok1
  rw [hres1, decBool_t h0] at hrun1
  have hf0 : ((0 : Word) != 0) = false := rfl
  have hE := CoreSpecE.of_callE (s₀ := ⟨m₁, Locals.init []⟩)
    ((hkE (k + 1) (Nat.le_refl _)).whnfCore F _ _ dn vis fe M₁ eb mode 0 d e hF hn
      ⟨hS₁, hs.mode4, hs.eb_mode⟩ he) hW'
  rw [hf0] at hE
  refine ErrClaim.of_run_err (fun ce h' => ?_) hE
  simp only [tryUnfoldProjApp, StateT.run_bind, hrun1, except_ok_bind, ↓reduceIte, h']; rfl

end mid

/-! ## `delta_quick` -/

/-- `quick_defeq`'s error claim at fuel `n` (the shape of `QuickDefeqSpec`). -/
def QuickDefeqWE (p : Prog) (n : Nat) : Prop :=
  ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d x y : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe M eb mode →
    HW x → HW y → d.toNat < 2 ^ 63 →
    CoreSpecE p n "quick_defeq" [mode, vis, d, x, y]
      (quickDefEq (decMode mode) (coreKnot (decMode mode) fe id F) d.toNat (decE x) (decE y)) s₀ a₀

/-- **`delta_quick`'s verdicts** are `quick_defeq`'s. -/
theorem deltaQuick_refinesE (p : Prog) (hp : DefEqMidProg p) (n : Nat) (hq : QuickDefeqWE p n)
    (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d a b : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) (hd : d.toNat < 2 ^ 63) :
    CoreSpecE p (n + 1) "delta_quick" [mode, vis, d, a, b]
      (deltaQuick (decMode mode) (coreKnot (decMode mode) fe id F) d.toNat (decE a) (decE b)) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (dqE_spec p hp.dq (n + 1) ⟨s₀.mem, Locals.init []⟩ mode vis d a b) hc0
    (Err.code_ne_of_cls hk0)
  simp only [dqE] at hW
  have hW' := err_of_k (by intro q e; simp only [dqE.k_quick_defeq]; split <;> (try split) <;> simp)
    (fun _ => rfl) hW
  refine ErrClaim.of_run_err (fun ce h' => ?_)
    (CoreSpecE.of_callE (hq F s₀ a₀ dn vis fe M eb mode d a b hF hn hs ha hb hd) hW')
  simp only [deltaQuick, StateT.run_bind, h']; rfl

/-! ## `lazy_nat` -/

section lazy
variable (p : Prog) (hp : LazyProg p) (hc : LazyCallees p) (hdp : WhnfDeltaProg' p)
  (hnv : closedNV p L.Checker.nvFns = true)
include hp hc hdp hnv

/-- **`lazy_nat`'s verdicts** are `reduce_nat`'s and the `defeq` slot's. -/
theorem lazyNat_refinesE (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) (F : Nat) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) :
    CoreSpecE p (n + 1) "lazy_nat" [mode, vis, d, a, b]
      (natT (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (lnE_spec p hp.nat (n + 1) ⟨s₀.mem, Locals.init []⟩ mode vis d a b)
    hc0 (Err.code_ne_of_cls hk0)
  simp only [lnE] at hW
  have hS := hs.rel
  cases c1 : callE p n "reduce_nat" [mode, vis, d, a] s₀.mem with
  | error e1 =>
    rw [c1, lnE.k_reduce_nat.none] at hW; cases hW
    refine ErrClaim.of_run_err (fun ce h' => ?_)
      (callE_reduceNat p hdp hnv n F hF hn hk hkE s₀ a₀ dn vis fe M eb mode d a hs ha _ c1)
    simp only [natT, StateT.run_bind, h']; rfl
  | ok q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [c1] at hW
  simp only [lnE.k_reduce_nat] at hW
  obtain ⟨hok1, ⟨M₁, hS₁, -, -⟩, hres1, hrw1⟩ := CoreSpec.of_callW
    (hc.reduceNat n hn F s₀ a₀ dn vis fe M eb mode d a hF hs ha hk) (callW_of_callE c1)
  have hrun1 := AM.run_of_ok _ _ hok1
  rw [hres1] at hrun1
  have hdq : ∀ (x y : Word) (m₂ : Mem) (M₂ : ModeMaps) (a₂ : AState), CoreS dn m₂ a₂ vis fe M₂ eb →
      HW x → HW y → lnE.k_defeq p (callE p n "defeq" [mode, vis, d, x, y] m₂) = .error er →
      ErrClaim ((coreKnot (decMode mode) fe id F).defeq d.toNat (decE x) (decE y)) a₂ er := by
    intro x y m₂ M₂ a₂ hS₂ hx hy h
    have h' := err_of_k (by intro q e; simp [lnE.k_defeq]) (fun _ => rfl) h
    exact CoreSpecE.of_callE (s₀ := ⟨m₂, Locals.init []⟩)
      ((hkE n (Nat.le_refl _)).defeq F _ _ dn vis fe M₂ eb mode d x y hF hn ⟨hS₂, hs.mode4, hs.eb_mode⟩
        hx hy) h'
  by_cases h1 : r₁.headD 0 ≠ 0
  · rw [ite_eq_left h1] at hW
    rw [decOptR_some h1] at hrun1
    refine ErrClaim.of_run_err (fun ce h' => ?_) (hdq _ _ _ _ _ hS₁ hrw1.2 hb hW)
    simp only [natT, StateT.run_bind, hrun1, except_ok_bind, h']; rfl
  rw [ite_eq_right h1] at hW
  have h1' : r₁.headD 0 = 0 := by simpa using h1
  rw [decOptR_none h1'] at hrun1
  cases c2 : callE p n "reduce_nat" [mode, vis, d, b] m₁ with
  | error e2 =>
    rw [c2, lnE.k_reduce_nat_2.none] at hW; cases hW
    refine ErrClaim.of_run_err (fun ce h' => ?_)
      (callE_reduceNat p hdp hnv n F hF hn hk hkE ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode d b
        ⟨hS₁, hs.mode4, hs.eb_mode⟩ hb _ c2)
    simp only [natT, StateT.run_bind, hrun1, except_ok_bind, h']; rfl
  | ok q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [c2] at hW
  simp only [lnE.k_reduce_nat_2] at hW
  obtain ⟨hok2, ⟨M₂, hS₂, -, -⟩, hres2, hrw2⟩ := CoreSpec.of_callW (s₀ := ⟨m₁, Locals.init []⟩)
    (hc.reduceNat n hn F ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode d b hF ⟨hS₁, hs.mode4, hs.eb_mode⟩ hb hk)
    (callW_of_callE c2)
  have hrun2 := AM.run_of_ok _ _ hok2
  rw [hres2] at hrun2
  by_cases h2 : r₂.headD 0 ≠ 0
  · rw [ite_eq_left h2] at hW
    rw [decOptR_some h2] at hrun2
    refine ErrClaim.of_run_err (fun ce h' => ?_) (hdq _ _ _ _ _ hS₂ ha hrw2.2 hW)
    simp only [natT, StateT.run_bind, hrun1, except_ok_bind, hrun2, h']; rfl
  rw [ite_eq_right h2] at hW; cases hW

end lazy

end L.Arena
