import ConAgua.Arena.IndLibSpec
import ConAgua.Arena.View
import ConAgua.Arena.SortRefine
import ConAgua.Arena.ConstRefine

/-!
# `e_view` refines the twin's `view` (lane `induct`)

`e_view(h)` returns `(tag, x, y, z)` (IndIface). Its word model `eViewW` follows the L code; under
`ArenaR`, a returning run means the twin's `view (decE h)` succeeds without changing the state,
and the words decode the view (`ViewR`). Every inductive-stage function that matches on a view
goes through this.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- **The model of `e_view`**: the four result words, `[]` where the L code aborts. -/
def eViewW (m : Mem) (h : Word) : List Word :=
  let g := h >>> 28
  let t := tierW h
  let i := idxW h
  if 4294967295 < h then []
  else if t ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then []
  else if g = 0 then
    if tcnt m BVAR t ≤ i then [] else [0, tfld m BVAR t i 0, 0, 0]
  else if g = 1 then
    if tcnt m FVAR t ≤ i then []
    else [1, tfld m FVAR t i 0, tfld m FVAR t i 1, 0]
  else if g = 2 then
    if tcnt m SORT t ≤ i then [] else [2, tfld m SORT t i 0, 0, 0]
  else if g = 3 then
    if tcnt m CONST t ≤ i then []
    else [3, tfld m CONST t i 0, tfld m CONST t i 1, 0]
  else if g = 4 then
    if tcnt m APP t ≤ i then []
    else [4, tfld m APP t i 0, tfld m APP t i 1, 0]
  else if g = 5 then
    if tcnt m LAM t ≤ i then []
    else [5, tfld m LAM t i 0, tfld m LAM t i 1, 0]
  else if g = 6 then
    if tcnt m FORALL t ≤ i then []
    else [6, tfld m FORALL t i 0, tfld m FORALL t i 1, 0]
  else if g = 7 then
    if tcnt m LET t ≤ i then []
    else [7, tfld m LET t i 0, tfld m LET t i 1,
      tfld m LET t i 2]
  else if g = 8 then
    if tcnt m LIT t ≤ i then [] else [8, 0, 0, 0]
  else if g = 9 then
    if tcnt m PROJ t ≤ i then []
    else [9, tfld m PROJ t i 0, tfld m PROJ t i 1,
      tfld m PROJ t i 2]
  else []

theorem eView_spec (p : Prog) (hp : p.lookup "e_view" = some eView) (n : Nat) (s₀ : St) (h : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "e_view" [h]
    ⦃fun r s' => s' = s₀ ∧ r ≠ [] ∧ r = eViewW s₀.mem h; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, eView]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld,
        evalE_cnt, tcntM, evalE_tierE, evalE_idxE] <;>
      finish [eViewW, tierW, idxW]

end L.Ind

namespace L.Ind

open L.Arena

/-- **The view's words**: `r` (as `e_view` returns them) denote the view `v`. -/
def ViewR (r : List Word) : ENodeView → Prop
  | .bvar i => r.headD 0 = 0 ∧ (r.getD 1 0).toNat = i
  | .fvar i ty => r.headD 0 = 1 ∧ (r.getD 1 0).toNat = i ∧ (r.getD 2 0).toNat < 2 ^ 32 ∧
      decE (r.getD 2 0) = ty
  | .sort u => r.headD 0 = 2 ∧ (r.getD 1 0).toNat < 2 ^ 32 ∧ decI (r.getD 1 0) = u
  | .const n us => r.headD 0 = 3 ∧ (r.getD 1 0).toNat < 2 ^ 32 ∧ decI (r.getD 1 0) = n ∧
      (r.getD 2 0).toNat < 2 ^ 32 ∧ decI (r.getD 2 0) = us
  | .app f x => r.headD 0 = 4 ∧ (r.getD 1 0).toNat < 2 ^ 32 ∧ decE (r.getD 1 0) = f ∧
      (r.getD 2 0).toNat < 2 ^ 32 ∧ decE (r.getD 2 0) = x
  | .lam ty b => r.headD 0 = 5 ∧ (r.getD 1 0).toNat < 2 ^ 32 ∧ decE (r.getD 1 0) = ty ∧
      (r.getD 2 0).toNat < 2 ^ 32 ∧ decE (r.getD 2 0) = b
  | .forallE ty b => r.headD 0 = 6 ∧ (r.getD 1 0).toNat < 2 ^ 32 ∧ decE (r.getD 1 0) = ty ∧
      (r.getD 2 0).toNat < 2 ^ 32 ∧ decE (r.getD 2 0) = b
  | .letE t v b => r.headD 0 = 7 ∧ (r.getD 1 0).toNat < 2 ^ 32 ∧ decE (r.getD 1 0) = t ∧
      (r.getD 2 0).toNat < 2 ^ 32 ∧ decE (r.getD 2 0) = v ∧
      (r.getD 3 0).toNat < 2 ^ 32 ∧ decE (r.getD 3 0) = b
  | .lit _ => r.headD 0 = 8
  | .proj n i e => r.headD 0 = 9 ∧ (r.getD 1 0).toNat < 2 ^ 32 ∧ decI (r.getD 1 0) = n ∧
      (r.getD 2 0).toNat = i ∧ (r.getD 3 0).toNat < 2 ^ 32 ∧ decE (r.getD 3 0) = e

section ok
variable (m : Mem) (a : AState) (hR : ArenaR m a) (h : Word) (hh : h.toNat < 2 ^ 32)
include hR hh

theorem view_sort_f (hv : viewOK m h SORT) (hg : h >>> 28 = 2) :
    a.store.view (decE h) = some (.sort (decI (tfld m SORT (tierW h) (idxW h) 0))) ∧
    (tfld m SORT (tierW h) (idxW h) 0).toNat < 2 ^ 32 := by
  obtain ⟨k, hk, hu⟩ := node_of m a h sortCS SoRecRel (·.sorts) _ hR.sort hv.2
  simp only [SoRecRel] at hu
  rw [hu, decI_word]
  exact ⟨by rw [view_tier m a hR h hh hv.1, get_sort _ h hh hg, Tbl.node?, hk]; rfl, word_lt _⟩

theorem view_const_f (hv : viewOK m h CONST) (hg : h >>> 28 = 3) :
    a.store.view (decE h) = some (.const (decI (tfld m CONST (tierW h) (idxW h) 0))
      (decI (tfld m CONST (tierW h) (idxW h) 1))) ∧
    (tfld m CONST (tierW h) (idxW h) 0).toNat < 2 ^ 32 ∧
    (tfld m CONST (tierW h) (idxW h) 1).toNat < 2 ^ 32 := by
  obtain ⟨k, hk, hn, hu⟩ := node_of m a h constCS CeRecRel (·.consts) _ hR.const hv.2
  rw [hn, hu, decI_word, decI_word]
  exact ⟨by rw [view_tier m a hR h hh hv.1, get_const _ h hh hg, Tbl.node?, hk]; rfl, word_lt _,
    word_lt _⟩

end ok

/-- **`e_view`'s words denote the twin's view**, when it returns. -/
theorem eViewW_ok (m : Mem) (a : AState) (hR : ArenaR m a) (h : Word) (hne : eViewW m h ≠ []) :
    ∃ v, a.store.view (decE h) = some v ∧ ViewR (eViewW m h) v := by
  unfold eViewW at hne ⊢
  have hh : h.toNat < 2 ^ 32 := by
    by_cases c : (4294967295 : Word) < h
    · simp [c] at hne
    · have : ¬ (4294967295 : Nat) < h.toNat := c
      omega
  have h1 : ¬ (4294967295 : Word) < h := fun c => by
    have : (4294967295 : Nat) < h.toNat := c
    omega
  simp only [h1, ite_false] at hne ⊢
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · simp [hs] at hne
  simp only [hs, ite_false] at hne ⊢
  have vok : ∀ c, ¬ tcnt m c (tierW h) ≤ idxW h → viewOK m h c :=
    fun c hc => ⟨hs, by simpa using hc⟩
  by_cases g0 : h >>> 28 = 0
  · simp only [g0, ite_true] at hne ⊢
    by_cases c : tcnt m BVAR (tierW h) ≤ idxW h
    · simp [c] at hne
    simp only [c, ite_false]
    exact ⟨_, view_bvar m a hR h hh (vok BVAR c) g0, by simp [ViewR]⟩
  simp only [g0, ite_false] at hne ⊢
  by_cases g1 : h >>> 28 = 1
  · simp only [g1, ite_true] at hne ⊢
    by_cases c : tcnt m FVAR (tierW h) ≤ idxW h
    · simp [c] at hne
    simp only [c, ite_false]
    obtain ⟨e, hl⟩ := view_fvar_idx m a hR h hh (vok FVAR c) g1
    exact ⟨_, e, by simp [ViewR, hl]⟩
  simp only [g1, ite_false] at hne ⊢
  by_cases g2 : h >>> 28 = 2
  · simp only [g2, ite_true] at hne ⊢
    by_cases c : tcnt m SORT (tierW h) ≤ idxW h
    · simp [c] at hne
    simp only [c, ite_false]
    obtain ⟨e, hl⟩ := view_sort_f m a hR h hh (vok SORT c) g2
    exact ⟨_, e, by simp [ViewR, hl]⟩
  simp only [g2, ite_false] at hne ⊢
  by_cases g3 : h >>> 28 = 3
  · simp only [g3, ite_true] at hne ⊢
    by_cases c : tcnt m CONST (tierW h) ≤ idxW h
    · simp [c] at hne
    simp only [c, ite_false]
    obtain ⟨e, hl, hl2⟩ := view_const_f m a hR h hh (vok CONST c) g3
    exact ⟨_, e, by simp [ViewR, hl, hl2]⟩
  simp only [g3, ite_false] at hne ⊢
  by_cases g4 : h >>> 28 = 4
  · simp only [g4, ite_true] at hne ⊢
    by_cases c : tcnt m APP (tierW h) ≤ idxW h
    · simp [c] at hne
    simp only [c, ite_false]
    obtain ⟨e, hl, hl2⟩ := view_app m a hR h hh (vok APP c) g4
    exact ⟨_, e, by simp [ViewR, hl, hl2]⟩
  simp only [g4, ite_false] at hne ⊢
  by_cases g5 : h >>> 28 = 5
  · simp only [g5, ite_true] at hne ⊢
    by_cases c : tcnt m LAM (tierW h) ≤ idxW h
    · simp [c] at hne
    simp only [c, ite_false]
    obtain ⟨e, hl, hl2⟩ := view_lam m a hR h hh (vok LAM c) g5
    exact ⟨_, e, by simp [ViewR, hl, hl2]⟩
  simp only [g5, ite_false] at hne ⊢
  by_cases g6 : h >>> 28 = 6
  · simp only [g6, ite_true] at hne ⊢
    by_cases c : tcnt m FORALL (tierW h) ≤ idxW h
    · simp [c] at hne
    simp only [c, ite_false]
    obtain ⟨e, hl, hl2⟩ := view_forall m a hR h hh (vok FORALL c) g6
    exact ⟨_, e, by simp [ViewR, hl, hl2]⟩
  simp only [g6, ite_false] at hne ⊢
  by_cases g7 : h >>> 28 = 7
  · simp only [g7, ite_true] at hne ⊢
    by_cases c : tcnt m LET (tierW h) ≤ idxW h
    · simp [c] at hne
    simp only [c, ite_false]
    obtain ⟨e, hl, hl2, hl3⟩ := view_let m a hR h hh (vok LET c) g7
    exact ⟨_, e, by simp [ViewR, hl, hl2, hl3]⟩
  simp only [g7, ite_false] at hne ⊢
  by_cases g8 : h >>> 28 = 8
  · simp only [g8, ite_true] at hne ⊢
    by_cases c : tcnt m LIT (tierW h) ≤ idxW h
    · simp [c] at hne
    simp only [c, ite_false]
    obtain ⟨l, e⟩ := view_lit m a hR h hh (vok LIT c) g8
    exact ⟨_, e, by simp [ViewR]⟩
  simp only [g8, ite_false] at hne ⊢
  by_cases g9 : h >>> 28 = 9
  · simp only [g9, ite_true] at hne ⊢
    by_cases c : tcnt m PROJ (tierW h) ≤ idxW h
    · simp [c] at hne
    simp only [c, ite_false]
    obtain ⟨e, hl, hl2⟩ := view_proj m a hR h hh (vok PROJ c) g9
    exact ⟨_, e, by simp [ViewR, hl, hl2]⟩
  simp [g9] at hne

/-- **`e_view` refines `view`**: on a return the memory is unchanged, the twin's `view` succeeds
without changing the state, and the words denote its view. -/
@[refines ConRon.Arena.view]
theorem eView_refines (p : Prog) (hp : p.lookup "e_view" = some eView) (n : Nat) (s₀ : St)
    (a₀ : AState) (hR : ArenaR s₀.mem a₀) (h : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "e_view" [h]
    ⦃fun r s' => s' = s₀ ∧ AM.ok (view (decE h)) a₀ ∧ AM.st (view (decE h)) a₀ = a₀ ∧
      ViewR r (AM.res (view (decE h)) a₀); ⊤⦄ := by
  refine triple_post (eView_spec p hp n s₀ h) ?_
  rintro r s' ⟨rfl, hne, rfl⟩
  obtain ⟨v, hv, hr⟩ := eViewW_ok s'.mem a₀ hR h hne
  have := view_run (decE h) a₀ v hv
  simp only [AM.ok, AM.st, AM.res, this]
  refine ⟨?_, ?_, ?_, hr⟩ <;> trivial

end L.Ind
