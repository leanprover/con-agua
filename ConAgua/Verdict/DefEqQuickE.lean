import ConAgua.Verdict.DefEqSlotE
import ConAgua.Arena.GrindAttr
import ConAgua.L.ModelGen

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
    have : decO (rz.headD 0) = none := by unfold decO; rw [ite_eq_left hz]
    rw [this]
    exact ErrClaim.bind_left (ErrClaim.fail _ _ rfl)
  · rw [quickSortE.k_lvl_eq_c.arm1 (hc1 := hz)] at hW; cases hW

end L.Arena

/-! ## `quick_forall`, `quick_lam`, `quick_defeq` -/

namespace L.Arena

l_model quickForall_specE (p : Prog) (hf : p.lookup "quick_forall" = some quickForallL)
  fns [hf ↦ quickForallE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

l_model quickLam_specE (p : Prog) (hf : p.lookup "quick_lam" = some quickLamL)
  fns [hf ↦ quickLamE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

/-- **`quick_forall`'s error claim** (the error half of `quickForall_refines`). -/
theorem quickForall_refinesE (p : Prog) (hp : QuickProg p) (hbE : DefeqBindersE p)
    (hnv : closedNV p L.Checker.nvFns = true) (n : Nat)
    (hk : KnotUpTo p n) (hkE : KnotUpToE p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a b : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode)
    (h6a : a >>> 28 = 6) (h6b : b >>> 28 = 6) (hd : d.toNat < 2 ^ 63) :
    CoreSpecE p (n + 1) "quick_forall" [mode, vis, d, a, b]
      (quickPairT (decMode mode) (coreKnot (decMode mode) fe id F) d.toNat (decE a) (decE b)) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hkc : er.cls = 0
  · exact ErrClaim.of_cls0 hkc
  have hW := triple_of_callE_err (quickForall_specE p hp.qf (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d a b) hc0 (Err.code_ne_of_cls hkc)
  rw [quickForallE.arm1] at hW
  have hS := hs.rel
  cases hc1 : callE p n "e_view" [a] s₀.mem with
  | error e =>
    rw [hc1, quickForallE.k_e_view.none] at hW; cases hW
    exact ErrClaim.of_nv hnv (by simp [defeqNVList]) hc1
  | ok q =>
  obtain ⟨ra, m₁⟩ := q
  rw [hc1, quickForallE.k_e_view.arm1] at hW
  obtain ⟨rfl, va, hva, hvra, hta⟩ := eView_callW_view (a := a₀) hp.lams.peel.eview hS.arena.1
    (callW_of_callE hc1)
  obtain ⟨rfl, hwa1, hwa2⟩ := viewR_forall hvra (hta.trans h6a)
  cases hc2 : callE p n "e_view" [b] s₀.mem with
  | error e =>
    rw [hc2, quickForallE.k_e_view_2.none] at hW; cases hW
    exact ErrClaim.of_nv hnv (by simp [defeqNVList]) hc2
  | ok q =>
  obtain ⟨rb, m₂⟩ := q
  rw [hc2, quickForallE.k_e_view_2.arm1] at hW
  obtain ⟨rfl, vb, hvb, hvrb, htb⟩ := eView_callW_view (a := a₀) hp.lams.peel.eview hS.arena.1
    (callW_of_callE hc2)
  obtain ⟨rfl, hwb1, hwb2⟩ := viewR_forall hvrb (htb.trans h6b)
  refine ErrClaim.congr_run (quickPairT_forall _ _ _ _ _ a₀ _ _ _ _ hva hvb) (ErrClaim.bind_left ?_)
  have h3 := tailE (quickForallE.k_defeq_binders.none p) (fun ⟨_, _⟩ => ⟨_, rfl⟩) hW
  refine ErrClaim.of_callE_succ h3 fun k hk' h' => ?_
  subst hk'
  have hpf := peelFuel_lt
  exact CoreSpecE.of_callE (s₀ := ⟨s₀.mem, Locals.init []⟩)
    (hbE k (hk.mono (by omega)) (hkE.mono (by omega)) F (by omega) (by omega) _ a₀ dn vis fe M eb mode d
      _ _ _ _ ⟨hS, hs.mode4, hs.eb_mode⟩ hwa1 hwa2 hwb1 hwb2 (by omega)) h'

/-- **`quick_lam`'s error claim** (the error half of `quickLam_refines`). -/
theorem quickLam_refinesE (p : Prog) (hp : QuickProg p) (hlE : DefeqLamsE p)
    (hnv : closedNV p L.Checker.nvFns = true) (n : Nat)
    (hk : KnotUpTo p n) (hkE : KnotUpToE p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a b : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode)
    (h5a : a >>> 28 = 5) (h5b : b >>> 28 = 5) (hd : d.toNat < 2 ^ 63) :
    CoreSpecE p (n + 1) "quick_lam" [mode, vis, d, a, b]
      (quickPairT (decMode mode) (coreKnot (decMode mode) fe id F) d.toNat (decE a) (decE b)) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hkc : er.cls = 0
  · exact ErrClaim.of_cls0 hkc
  have hW := triple_of_callE_err (quickLam_specE p hp.ql (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d a b) hc0 (Err.code_ne_of_cls hkc)
  rw [quickLamE.arm1] at hW
  have hS := hs.rel
  cases hc1 : callE p n "e_view" [a] s₀.mem with
  | error e =>
    rw [hc1, quickLamE.k_e_view.none] at hW; cases hW
    exact ErrClaim.of_nv hnv (by simp [defeqNVList]) hc1
  | ok q =>
  obtain ⟨ra, m₁⟩ := q
  rw [hc1, quickLamE.k_e_view.arm1] at hW
  obtain ⟨rfl, va, hva, hvra, hta⟩ := eView_callW_view (a := a₀) hp.lams.peel.eview hS.arena.1
    (callW_of_callE hc1)
  obtain ⟨rfl, hwa1, hwa2⟩ := viewR_lam hvra (hta.trans h5a)
  cases hc2 : callE p n "e_view" [b] s₀.mem with
  | error e =>
    rw [hc2, quickLamE.k_e_view_2.none] at hW; cases hW
    exact ErrClaim.of_nv hnv (by simp [defeqNVList]) hc2
  | ok q =>
  obtain ⟨rb, m₂⟩ := q
  rw [hc2, quickLamE.k_e_view_2.arm1] at hW
  obtain ⟨rfl, vb, hvb, hvrb, htb⟩ := eView_callW_view (a := a₀) hp.lams.peel.eview hS.arena.1
    (callW_of_callE hc2)
  obtain ⟨rfl, hwb1, hwb2⟩ := viewR_lam hvrb (htb.trans h5b)
  refine ErrClaim.congr_run (quickPairT_lam _ _ _ _ _ a₀ _ _ _ _ hva hvb) (ErrClaim.bind_left ?_)
  have h3 := tailE (quickLamE.k_defeq_lams.none p) (fun ⟨_, _⟩ => ⟨_, rfl⟩) hW
  refine ErrClaim.of_callE_succ h3 fun k hk' h' => ?_
  subst hk'
  exact CoreSpecE.of_callE (s₀ := ⟨s₀.mem, Locals.init []⟩)
    (hlE k (hk.mono (by omega)) (hkE.mono (by omega)) F (by omega) (by omega) _ a₀ dn vis fe M eb mode d
      _ _ _ _ ⟨hS, hs.mode4, hs.eb_mode⟩ hwa1 hwa2 hwb1 hwb2 hd) h'

l_model quickDefeq_specE (p : Prog) (hf : p.lookup "quick_defeq" = some quickDefeqL)
  fns [hf ↦ quickDefeqE tuple] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] errors

/-- **`quick_defeq`'s error claim** (`QuickDefeqSpecE` one level up, the error half of
`quickDefeq_refines`). -/
theorem quickDefeq_refinesE (p : Prog) (hp : QuickProg p) (hsd : StoreDenotes)
    (hbE : DefeqBindersE p) (hlE : DefeqLamsE p) (hnv : closedNV p L.Checker.nvFns = true) :
    QuickDefeqE p := by
  intro n hk hkE F s₀ a₀ dn vis fe M eb mode d x y hF hn hs hx hy hd
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hkc : er.cls = 0
  · exact ErrClaim.of_cls0 hkc
  have hW := triple_of_callE_err (quickDefeq_specE p hp.qd (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d x y) hc0 (Err.code_ne_of_cls hkc)
  have hS := hs.rel
  simp only [quickDefeqE] at hW
  rw [quickDefEq_eq]
  by_cases he : x = y
  · rw [ite_eq_left he] at hW; cases hW
  rw [ite_eq_right he] at hW
  have hb : (decE x == decE y) = false := by rw [decE_beq_eq _ _ hx hy]; simp [he]
  simp only [hb, Bool.false_eq_true, ↓reduceIte, tag_bne x y hx hy, decide_eq_true_eq]
  by_cases hg : x >>> 28 ≠ y >>> 28
  · rw [ite_eq_left hg] at hW; cases hW
  have hg' : x >>> 28 = y >>> 28 := Classical.byContradiction hg
  rw [ite_eq_right hg] at hW
  rw [ite_eq_right hg]
  simp only [tag_beq_w x hx 2 (by decide) ETag.sort rfl 2 rfl,
    tag_beq_w x hx 8 (by decide) ETag.lit rfl 8 rfl, tag_beq_w x hx 6 (by decide) ETag.forallE rfl 6 rfl,
    tag_beq_w x hx 5 (by decide) ETag.lam rfl 5 rfl, Bool.or_eq_true, decide_eq_true_eq]
  -- an arm's failure, at fuel `n = k + 1`
  have arm : ∀ (f : FnName) (args : List Word),
      quickDefeqE.k_quick_sort p (callE p n f args s₀.mem) = .error er →
      ∀ (T : AM (Option Bool)), (∀ k, n = k + 1 → ∀ e, callE p (k + 1) f args s₀.mem = .error e →
        ErrClaim T a₀ e) → ErrClaim T a₀ er := by
    intro f args h T hT
    have h3 := tailE (quickDefeqE.k_quick_sort.none p) (fun ⟨_, _⟩ => ⟨_, rfl⟩) h
    exact ErrClaim.of_callE_succ h3 fun k hk' h' => hT k hk' er h'
  by_cases h2 : x >>> 28 = 2
  · rw [ite_eq_left h2] at hW
    simp only [h2, true_or, ↓reduceIte]
    exact arm _ _ hW _ fun k _ e he => CoreSpecE.of_callE (s₀ := ⟨s₀.mem, Locals.init []⟩)
      (quickSort_refinesE p hp hsd hnv k _ a₀ dn vis fe M eb _ _ _ x y hS h2 (hg' ▸ h2)) he
  rw [ite_eq_right h2] at hW
  by_cases h8 : x >>> 28 = 8
  · rw [ite_eq_left h8] at hW
    have h3 := tailE (quickDefeqE.k_quick_sort.none p) (fun ⟨_, _⟩ => ⟨_, rfl⟩) hW
    exact ErrClaim.of_nv hnv (by simp [defeqNVList]) h3
  rw [ite_eq_right h8] at hW
  by_cases h6 : x >>> 28 = 6
  · rw [ite_eq_left h6] at hW
    simp only [h6, true_or, or_true, ↓reduceIte]
    exact arm _ _ hW _ fun k hnk e he => CoreSpecE.of_callE (s₀ := ⟨s₀.mem, Locals.init []⟩)
      (quickForall_refinesE p hp hbE hnv k (hk.mono (by omega)) (hkE.mono (by omega)) F (by omega)
        (by omega) _ a₀ dn vis fe M eb mode d x y ⟨hS, hs.mode4, hs.eb_mode⟩ h6 (hg' ▸ h6) hd) he
  rw [ite_eq_right h6] at hW
  by_cases h5 : x >>> 28 = 5
  · rw [ite_eq_left h5] at hW
    simp only [h5, or_true, ↓reduceIte]
    exact arm _ _ hW _ fun k hnk e he => CoreSpecE.of_callE (s₀ := ⟨s₀.mem, Locals.init []⟩)
      (quickLam_refinesE p hp hlE hnv k (hk.mono (by omega)) (hkE.mono (by omega)) F (by omega)
        (by omega) _ a₀ dn vis fe M eb mode d x y ⟨hS, hs.mode4, hs.eb_mode⟩ h5 (hg' ▸ h5) hd) he
  rw [ite_eq_right h5] at hW; cases hW

end L.Arena
