import ConAgua.Verdict.DefEqSlotE

/-!
# `quick_defeq`'s error claim and its arms (lane `verdicts-b`, helper `k3`)

The error halves of `DefEqMidQuick.lean`. `quick_sort` has a decline site: `lvl_eq_c` answers `0`
(out of level fuel), the twin's `liftFueled "level comparison"` fails with `notImplemented`.
`quick_forall` and `quick_lam` pass on `defeq_binders`' and `defeq_lams`' failures
(`DefeqBindersE`, `DefeqLamsE`, `DefEqPeelE.lean`, `DefEqLamsE.lean`); `lit_eq` and `e_view` are
outside the verdict closure.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.deprecated false

namespace L.Arena

/-! ## The arms' error specs -/

/-- **`defeq_binders`' error spec** (the error half of `defeqBinders_refines`). -/
def DefeqBindersE (p : Prog) : Prop :=
  ∀ (n : Nat), KnotUpTo p n → KnotUpToE p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
  ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d ty1 body1 ty2 body2 : Word), SlotPre s₀ a₀ dn vis fe M eb mode →
    HW ty1 → HW body1 → HW ty2 → HW body2 → d.toNat + 1 + peelFuel < 2 ^ 64 →
    CoreSpecE p (n + 1) "defeq_binders" [mode, vis, d, ty1, body1, ty2, body2]
      (defeqBinders (coreKnot (decMode mode) fe id F) d.toNat (decE ty1) (decE body1) (decE ty2)
        (decE body2)) s₀ a₀

/-- **`defeq_lams`' error spec** (the error half of `defeqLams_refines`). -/
def DefeqLamsE (p : Prog) : Prop :=
  ∀ (n : Nat), KnotUpTo p n → KnotUpToE p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
  ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d ty₁ body₁ ty₂ body₂ : Word), SlotPre s₀ a₀ dn vis fe M eb mode →
    HW ty₁ → HW body₁ → HW ty₂ → HW body₂ → d.toNat < 2 ^ 63 →
    CoreSpecE p (n + 1) "defeq_lams" [mode, vis, d, ty₁, body₁, ty₂, body₂]
      (defeqLams (decMode mode) (coreKnot (decMode mode) fe id F) lamsFuel d.toNat (decE ty₁)
        (decE body₁) (decE ty₂) (decE body₂)) s₀ a₀

/-! ## `quick_sort`: a decline site -/

l_model quickSort_specE (p : Prog) (hf : p.lookup "quick_sort" = some quickSortL)
  fns [hf ↦ quickSortE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

/-- **`quick_sort`'s error claim** (the error half of `quickSort_refines`): `lvl_eq_c`'s `0` (out of
level fuel) declines, as the twin's `liftFueled "level comparison"`. -/
theorem quickSort_refinesE (p : Prog) (hp : QuickProg p) (hsd : StoreDenotes)
    (hnv : closedNV p L.Checker.nvFns = true) (n : Nat) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb : Word) (mode : ConLeche.CheckMode) (r : CoreFnsA) (depth : Nat) (a b : Word)
    (hS : CoreS dn s₀.mem a₀ vis fe M eb) (h2a : a >>> 28 = 2)
    (h2b : b >>> 28 = 2) :
    CoreSpecE p (n + 1) "quick_sort" [a, b] (quickPairT mode r depth (decE a) (decE b)) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hkc : er.cls = 0
  · exact ErrClaim.of_cls0 hkc
  have hW := triple_of_callE_err (quickSort_specE p hp.qs (n + 1) ⟨s₀.mem, Locals.init []⟩ a b) hc0
    (Err.code_ne_of_cls hkc)
  rw [quickSortE.arm1] at hW
  cases hc1 : callE p n "e_view" [a] s₀.mem with
  | error e =>
    rw [hc1, quickSortE.k_e_view.none] at hW; cases hW
    exact ErrClaim.of_nv hnv (by simp [defeqNVList]) hc1
  | ok q =>
  obtain ⟨ra, m₁⟩ := q
  rw [hc1, quickSortE.k_e_view.arm1] at hW
  obtain ⟨rfl, va, hva, hvra, hta⟩ := eView_callW_view (a := a₀) hp.lams.peel.eview hS.arena.1
    (callW_of_callE hc1)
  obtain ⟨rfl, hwa⟩ := viewR_sort hvra (hta.trans h2a)
  cases hc2 : callE p n "e_view" [b] s₀.mem with
  | error e =>
    rw [hc2, quickSortE.k_e_view_2.none] at hW; cases hW
    exact ErrClaim.of_nv hnv (by simp [defeqNVList]) hc2
  | ok q =>
  obtain ⟨rb, m₂⟩ := q
  rw [hc2, quickSortE.k_e_view_2.arm1] at hW
  obtain ⟨rfl, vb, hvb, hvrb, htb⟩ := eView_callW_view (a := a₀) hp.lams.peel.eview hS.arena.1
    (callW_of_callE hc2)
  obtain ⟨rfl, hwb⟩ := viewR_sort hvrb (htb.trans h2b)
  refine ErrClaim.congr_run (quickPairT_sort mode r depth _ _ a₀ _ _ hva hvb) ?_
  obtain ⟨lu, hdu⟩ := hsd.sort dn s₀.mem a₀ vis fe M eb hS _ _ hva
  obtain ⟨lv, hdv⟩ := hsd.sort dn s₀.mem a₀ vis fe M eb hS _ _ hvb
  cases hc3 : callE p n "lvl_eq_c" [ra.tail.headD 0, rb.tail.headD 0] s₀.mem with
  | error e =>
    rw [hc3, quickSortE.k_lvl_eq_c.none] at hW; cases hW
    exact ErrClaim.of_nv hnv (by simp [defeqNVList]) hc3
  | ok q =>
  obtain ⟨rz, m₃⟩ := q
  rw [hc3] at hW
  obtain ⟨n₁, rfl⟩ := callE_succ hc3
  cases n₁ with
  | zero => exact absurd (callW_of_callE hc3) (lvlEqC_one p hp.lv _ _ _ _ _)
  | succ n₂ =>
  have e₃ := CoreSpec.of_callW (s₀ := ⟨s₀.mem, Locals.init []⟩)
    (lvlEqC_refines p hp.lv n₂ ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe M eb hS _ _ hwa hwb lu lv hdu hdv)
    (callW_of_callE hc3)
  refine ErrClaim.bind_core e₃ (fun M₃ hS₃ => ?_)
  by_cases hz : rz.headD 0 = 0
  · -- the decline: `lvl_eq_c` ran out of fuel, the twin's `liftFueled` fails
    rw [quickSortE.k_lvl_eq_c.abort1 (hc1 := hz)] at hW; cases hW
    have : decO (rz.headD 0) = none := by unfold decO; rw [if_pos hz]
    rw [this]
    exact ErrClaim.bind_left (ErrClaim.fail _ _ rfl)
  · rw [quickSortE.k_lvl_eq_c.arm1 (hc1 := hz)] at hW; cases hW

end L.Arena
