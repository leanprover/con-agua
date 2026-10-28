import ConAgua.Verdict.DefEqQuickE
import ConAgua.Arena.GrindAttr
import ConAgua.L.ModelGen

/-!
# `defeq_lams`' error claim (lane `verdicts-b`, helper `k3`)

The error halves of `DefEqMidLams.lean` and `defeq_lams_inner` (`DefEqMid.lean`): `lams_open` (a
failure is the domains' `defeq` slot call's), `defeq_lams_inner` (the `defeq` and `infer` slots'),
the telescope loop (`lams_ref`'s error half, `DefEqMidLams.lean`). `lams_inst`, `lam_pair`
are outside the verdict closure.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## `defeq_lams_inner` -/

l_model defeqLamsInner_specE (p : Prog) (hf : p.lookup "defeq_lams_inner" = some defeqLamsInnerL)
  fns [hf ↦ defeqLamsInnerE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

/-- **`defeq_lams_inner`'s error claim** (the error half of `defeqLamsInner_refines`). -/
theorem defeqLamsInner_refinesE (p : Prog) (hp : DefEqMidProg p) (n : Nat) (hk : KnotUpTo p n)
    (hkE : KnotUpToE p n) (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d b₁ b₂ : Word) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hd : d.toNat + 1 < 2 ^ 64) (h₁ : HW b₁) (h₂ : HW b₂) :
    CoreSpecE p (n + 1) "defeq_lams_inner" [mode, vis, d, b₁, b₂]
      (defeqLamsInner (decMode mode) (coreKnot (decMode mode) fe id F) d.toNat (decE b₁) (decE b₂))
      s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hkc : er.cls = 0
  · exact ErrClaim.of_cls0 hkc
  have hW := triple_of_callE_err (defeqLamsInner_specE p hp.lamsInner (n + 1)
    ⟨s₀.mem, Locals.init []⟩ mode vis d b₁ b₂) hc0 (Err.code_ne_of_cls hkc)
  have hd1 : (d + 1).toNat = d.toNat + 1 := by
    rw [UInt64.toNat_add]; simp only [UInt64.toNat_one]; omega
  have K := hk n (Nat.le_refl _)
  have KE := hkE n (Nat.le_refl _)
  have hS := hs.rel
  unfold defeqLamsInner
  simp only [defeqLamsInnerE] at hW
  cases hc1 : callE p n "defeq" [mode, vis, d + 1, b₁, b₂] s₀.mem with
  | error e =>
    rw [hc1, defeqLamsInnerE.k_defeq.none] at hW; cases hW
    have := CoreSpecE.of_callE (KE.defeq F s₀ a₀ dn vis fe M eb mode (d + 1) b₁ b₂ hF hn hs h₁ h₂) hc1
    rw [hd1] at this
    exact ErrClaim.bind_left this
  | ok q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [hc1] at hW
  simp only [defeqLamsInnerE.k_defeq] at hW
  have e₁ := CoreSpec.of_callW (K.defeq F s₀ a₀ dn vis fe M eb mode (d + 1) b₁ b₂ hF hn hs h₁ h₂)
    (callW_of_callE hc1)
  rw [hd1] at e₁
  refine ErrClaim.bind_core e₁ (fun M₁ hS₁ => ?_)
  by_cases h0 : r₁.headD 0 = 0
  · rw [ite_eq_left h0] at hW; cases hW
  rw [ite_eq_right h0] at hW
  rw [decBool_t h0]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, mode_verified mode hs.mode4,
    decide_eq_true_eq]
  by_cases hv : mode &&& 1 = 0
  · rw [ite_eq_left hv] at hW
    simp only [hv, ↓reduceIte]
    cases hc2 : callE p n "infer" [mode, vis, d + 1, b₁] m₁ with
    | error e =>
      rw [hc2, defeqLamsInnerE.k_infer.none] at hW; cases hW
      have := CoreSpecE.of_callE (s₀ := ⟨m₁, Locals.init []⟩)
        (KE.infer F _ _ dn vis fe M₁ eb mode (d + 1) b₁ hF hn ⟨hS₁, hs.mode4, hs.eb_mode⟩ h₁) hc2
      rw [hd1] at this
      exact ErrClaim.bind_left this
    | ok q =>
    obtain ⟨r₂, m₂⟩ := q
    rw [hc2] at hW
    simp only [defeqLamsInnerE.k_infer] at hW
    have e₂ := CoreSpec.of_callW (s₀ := ⟨m₁, Locals.init []⟩)
      (K.infer F _ _ dn vis fe M₁ eb mode (d + 1) b₁ hF hn ⟨hS₁, hs.mode4, hs.eb_mode⟩ h₁)
      (callW_of_callE hc2)
    rw [hd1] at e₂
    refine ErrClaim.bind_core e₂ (fun M₂ hS₂ => ?_)
    cases hc3 : callE p n "infer" [mode, vis, d + 1, b₂] m₂ with
    | error e =>
      rw [hc3, defeqLamsInnerE.k_infer_2.none] at hW; cases hW
      have := CoreSpecE.of_callE (s₀ := ⟨m₂, Locals.init []⟩)
        (KE.infer F _ _ dn vis fe M₂ eb mode (d + 1) b₂ hF hn ⟨hS₂, hs.mode4, hs.eb_mode⟩ h₂) hc3
      rw [hd1] at this
      exact ErrClaim.bind_left this
    | ok q =>
    obtain ⟨r₃, m₃⟩ := q
    rw [hc3] at hW
    simp only [defeqLamsInnerE.k_infer_2] at hW
    have e₃ := CoreSpec.of_callW (s₀ := ⟨m₂, Locals.init []⟩)
      (K.infer F _ _ dn vis fe M₂ eb mode (d + 1) b₂ hF hn ⟨hS₂, hs.mode4, hs.eb_mode⟩ h₂)
      (callW_of_callE hc3)
    rw [hd1] at e₃
    refine ErrClaim.bind_core e₃ (fun M₃ hS₃ => ?_)
    have h4 := tailE (defeqLamsInnerE.k_defeq_2.none p) (fun ⟨_, _⟩ => ⟨_, rfl⟩) hW
    have := CoreSpecE.of_callE (s₀ := ⟨m₃, Locals.init []⟩)
      (KE.defeq F _ _ dn vis fe M₃ eb mode (d + 1) _ _ hF hn ⟨hS₃, hs.mode4, hs.eb_mode⟩
        e₂.2.2.2 e₃.2.2.2) h4
    rw [hd1] at this
    exact this
  · rw [ite_eq_right hv] at hW; cases hW

/-! ## `lams_open` -/

l_model lamsOpen_specE (p : Prog) (hf : p.lookup "lams_open" = some lamsOpenL)
  fns [hf ↦ lamsOpenE tuple] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

/-- **`lams_open`'s error claim** (the error half of `lamsOpen_refines`). -/
theorem lamsOpen_refinesE (p : Prog) (hp : LamsProg p) (hnv : closedNV p L.Checker.nvFns = true)
    (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d ty₁ body₁ ty₂ body₂ : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode)
    (h₁ : HW ty₁) (h₂ : HW ty₂) :
    CoreSpecE p (n + 1) "lams_open" [mode, vis, d, ty₁, body₁, ty₂, body₂]
      (lamsOpenT (coreKnot (decMode mode) fe id F) d.toNat (decE ty₁) (decE body₁) (decE ty₂)
        (decE body₂)) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hkc : er.cls = 0
  · exact ErrClaim.of_cls0 hkc
  have hW := triple_of_callE_err (lamsOpen_specE p hp.open_ (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d ty₁ body₁ ty₂ body₂) hc0 (Err.code_ne_of_cls hkc)
  rw [lamsOpenE.arm1] at hW
  unfold lamsOpenT
  cases hc1 : callE p n "defeq" [mode, vis, d, ty₁, ty₂] s₀.mem with
  | error e =>
    rw [hc1, lamsOpenE.k_defeq.none] at hW; cases hW
    exact ErrClaim.bind_left (CoreSpecE.of_callE
      ((hkE n (Nat.le_refl _)).defeq F s₀ a₀ dn vis fe M eb mode d ty₁ ty₂ hF hn hs h₁ h₂) hc1)
  | ok q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [hc1] at hW
  have e₁ := CoreSpec.of_callW
    ((hk n (Nat.le_refl _)).defeq F s₀ a₀ dn vis fe M eb mode d ty₁ ty₂ hF hn hs h₁ h₂)
    (callW_of_callE hc1)
  refine ErrClaim.bind_core e₁ (fun M₁ hS₁ => ?_)
  by_cases h0 : r₁.headD 0 = 0
  · rw [lamsOpenE.k_defeq.arm1 (hc1 := h0)] at hW; cases hW
  rw [lamsOpenE.k_defeq.arm2 (hc1 := h0)] at hW
  have h3 := tailE (lamsOpenE.k_lams_inst.none p) (fun ⟨_, _⟩ => ⟨_, rfl⟩) hW
  exact ErrClaim.of_nv hnv (by simp [defeqNVList]) h3

/-! ## The telescope loop -/

/-- **`defeq_lams`' error claim** (`DefeqLamsE`, `defeqLams_ref`'s error half). -/
theorem defeqLams_refinesE (p : Prog) (hp : LamsProg p) (hi : Inst1OK p)
    (hnv : closedNV p L.Checker.nvFns = true) : DefeqLamsE p :=
  fun n hk hkE F hF hn s₀ a₀ dn vis fe M eb mode d ty₁ body₁ ty₂ body₂ hs h1 hb1 h2 hb2 hd =>
    RefE.coreSpecE (defeqLams_specE p hp.lams (n + 1) s₀ mode vis d ty₁ body₁ ty₂ body₂) trivial
      ⟨fun j hj F hF hn s₀ a₀ dn vis fe M eb mode d ty₁ body₁ ty₂ body₂ hs h₁ h₂ =>
        lamsOpen_refinesE p hp hnv j (hk.mono hj) (hkE.mono hj) F hF hn s₀ a₀ dn vis fe M eb mode d
          ty₁ body₁ ty₂ body₂ hs h₁ h₂,
       fun k args m _ h => callE_nv hnv (_root_.L.Checker.nv_mem (by decide +kernel)) k args m h,
       fun j hj F s₀ a₀ dn vis fe M eb mode d b₁ b₂ hF hn hs hd h₁ h₂ =>
        defeqLamsInner_refinesE p hp.mid j (hk.mono hj) (hkE.mono hj) F s₀ a₀ dn vis fe M eb mode d
          b₁ b₂ hF hn hs hd h₁ h₂⟩
      (defeqLams_ref p hp hi n hk F hF hn s₀ a₀ dn vis fe M eb mode d ty₁ body₁ ty₂ body₂ hs h1 hb1
        h2 hb2 hd)

end L.Arena
