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
  let C := m.arr64 CTL
  if 4294967295 < h then []
  else if t ≠ 0 ∧ rdW C 1 = 0 then []
  else if g = 0 then
    if rdW C (22 + t) ≤ i then [] else [0, rdW (m.arr64 BREC) (i * 2 + t), 0, 0]
  else if g = 1 then
    if rdW C (26 + t) ≤ i then []
    else [1, rdW (m.arr64 FVREC) (i * 4 + t * 2), rdW (m.arr64 FVREC) (i * 4 + t * 2 + 1), 0]
  else if g = 2 then
    if rdW C (16 + t) ≤ i then [] else [2, rdW (m.arr64 SOREC) (i * 2 + t), 0, 0]
  else if g = 3 then
    if rdW C (18 + t) ≤ i then []
    else [3, rdW (m.arr64 CREC) (i * 4 + t * 2), rdW (m.arr64 CREC) (i * 4 + t * 2 + 1), 0]
  else if g = 4 then
    if rdW C (4 + t) ≤ i then []
    else [4, rdW (m.arr64 AREC) (i * 4 + t * 2), rdW (m.arr64 AREC) (i * 4 + t * 2 + 1), 0]
  else if g = 5 then
    if rdW C (28 + t) ≤ i then []
    else [5, rdW (m.arr64 LAREC) (i * 4 + t * 2), rdW (m.arr64 LAREC) (i * 4 + t * 2 + 1), 0]
  else if g = 6 then
    if rdW C (30 + t) ≤ i then []
    else [6, rdW (m.arr64 FAREC) (i * 4 + t * 2), rdW (m.arr64 FAREC) (i * 4 + t * 2 + 1), 0]
  else if g = 7 then
    if rdW C (20 + t) ≤ i then []
    else [7, rdW (m.arr64 LEREC) (i * 6 + t * 3), rdW (m.arr64 LEREC) (i * 6 + t * 3 + 1),
      rdW (m.arr64 LEREC) (i * 6 + t * 3 + 2)]
  else if g = 8 then
    if rdW C (2 + t) ≤ i then [] else [8, 0, 0, 0]
  else if g = 9 then
    if rdW C (32 + t) ≤ i then []
    else [9, rdW (m.arr64 PJREC) (i * 6 + t * 3), rdW (m.arr64 PJREC) (i * 6 + t * 3 + 1),
      rdW (m.arr64 PJREC) (i * 6 + t * 3 + 2)]
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
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
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

theorem view_sort_f (hv : viewOK m h 16) (hg : h >>> 28 = 2) :
    a.store.view (decE h) = some (.sort (decI (rdW (m.arr64 SOREC) (idxW h * 2 + tierW h)))) ∧
    (rdW (m.arr64 SOREC) (idxW h * 2 + tierW h)).toNat < 2 ^ 32 := by
  obtain ⟨k, hk, hu⟩ := node_of m a h sortCS SoRecRel (·.sorts) _ hR.sort hv.2
  simp only [SoRecRel] at hu
  rw [hu, decI_word]
  exact ⟨by rw [view_tier m a hR h hh hv.1, get_sort _ h hh hg, Tbl.node?, hk]; rfl, word_lt _⟩

theorem view_const_f (hv : viewOK m h 18) (hg : h >>> 28 = 3) :
    a.store.view (decE h) = some (.const (decI (rdW (m.arr64 CREC) (idxW h * 4 + tierW h * 2)))
      (decI (rdW (m.arr64 CREC) (idxW h * 4 + tierW h * 2 + 1)))) ∧
    (rdW (m.arr64 CREC) (idxW h * 4 + tierW h * 2)).toNat < 2 ^ 32 ∧
    (rdW (m.arr64 CREC) (idxW h * 4 + tierW h * 2 + 1)).toNat < 2 ^ 32 := by
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
  simp only [h1, if_false] at hne ⊢
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · simp [hs] at hne
  simp only [hs, if_false] at hne ⊢
  have vok : ∀ c, ¬ rdW (m.arr64 CTL) (c + tierW h) ≤ idxW h → viewOK m h c :=
    fun c hc => ⟨hs, by simpa using hc⟩
  by_cases g0 : h >>> 28 = 0
  · simp only [g0, if_true] at hne ⊢
    by_cases c : rdW (m.arr64 CTL) (22 + tierW h) ≤ idxW h
    · simp [c] at hne
    simp only [c, if_false]
    exact ⟨_, view_bvar m a hR h hh (vok 22 c) g0, by simp [ViewR]⟩
  simp only [g0, if_false] at hne ⊢
  by_cases g1 : h >>> 28 = 1
  · simp only [g1, if_true] at hne ⊢
    by_cases c : rdW (m.arr64 CTL) (26 + tierW h) ≤ idxW h
    · simp [c] at hne
    simp only [c, if_false]
    obtain ⟨e, hl⟩ := view_fvar_idx m a hR h hh (vok 26 c) g1
    exact ⟨_, e, by simp [ViewR, hl]⟩
  simp only [g1, if_false] at hne ⊢
  by_cases g2 : h >>> 28 = 2
  · simp only [g2, if_true] at hne ⊢
    by_cases c : rdW (m.arr64 CTL) (16 + tierW h) ≤ idxW h
    · simp [c] at hne
    simp only [c, if_false]
    obtain ⟨e, hl⟩ := view_sort_f m a hR h hh (vok 16 c) g2
    exact ⟨_, e, by simp [ViewR, hl]⟩
  simp only [g2, if_false] at hne ⊢
  by_cases g3 : h >>> 28 = 3
  · simp only [g3, if_true] at hne ⊢
    by_cases c : rdW (m.arr64 CTL) (18 + tierW h) ≤ idxW h
    · simp [c] at hne
    simp only [c, if_false]
    obtain ⟨e, hl, hl2⟩ := view_const_f m a hR h hh (vok 18 c) g3
    exact ⟨_, e, by simp [ViewR, hl, hl2]⟩
  simp only [g3, if_false] at hne ⊢
  by_cases g4 : h >>> 28 = 4
  · simp only [g4, if_true] at hne ⊢
    by_cases c : rdW (m.arr64 CTL) (4 + tierW h) ≤ idxW h
    · simp [c] at hne
    simp only [c, if_false]
    obtain ⟨e, hl, hl2⟩ := view_app m a hR h hh (vok 4 c) g4
    exact ⟨_, e, by simp [ViewR, hl, hl2]⟩
  simp only [g4, if_false] at hne ⊢
  by_cases g5 : h >>> 28 = 5
  · simp only [g5, if_true] at hne ⊢
    by_cases c : rdW (m.arr64 CTL) (28 + tierW h) ≤ idxW h
    · simp [c] at hne
    simp only [c, if_false]
    obtain ⟨e, hl, hl2⟩ := view_lam m a hR h hh (vok 28 c) g5
    exact ⟨_, e, by simp [ViewR, hl, hl2]⟩
  simp only [g5, if_false] at hne ⊢
  by_cases g6 : h >>> 28 = 6
  · simp only [g6, if_true] at hne ⊢
    by_cases c : rdW (m.arr64 CTL) (30 + tierW h) ≤ idxW h
    · simp [c] at hne
    simp only [c, if_false]
    obtain ⟨e, hl, hl2⟩ := view_forall m a hR h hh (vok 30 c) g6
    exact ⟨_, e, by simp [ViewR, hl, hl2]⟩
  simp only [g6, if_false] at hne ⊢
  by_cases g7 : h >>> 28 = 7
  · simp only [g7, if_true] at hne ⊢
    by_cases c : rdW (m.arr64 CTL) (20 + tierW h) ≤ idxW h
    · simp [c] at hne
    simp only [c, if_false]
    obtain ⟨e, hl, hl2, hl3⟩ := view_let m a hR h hh (vok 20 c) g7
    exact ⟨_, e, by simp [ViewR, hl, hl2, hl3]⟩
  simp only [g7, if_false] at hne ⊢
  by_cases g8 : h >>> 28 = 8
  · simp only [g8, if_true] at hne ⊢
    by_cases c : rdW (m.arr64 CTL) (2 + tierW h) ≤ idxW h
    · simp [c] at hne
    simp only [c, if_false]
    obtain ⟨l, e⟩ := view_lit m a hR h hh (vok 2 c) g8
    exact ⟨_, e, by simp [ViewR]⟩
  simp only [g8, if_false] at hne ⊢
  by_cases g9 : h >>> 28 = 9
  · simp only [g9, if_true] at hne ⊢
    by_cases c : rdW (m.arr64 CTL) (32 + tierW h) ≤ idxW h
    · simp [c] at hne
    simp only [c, if_false]
    obtain ⟨e, hl, hl2⟩ := view_proj m a hR h hh (vok 32 c) g9
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
