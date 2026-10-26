import ConAgua.Verdict.InferSpineE

/-!
# Error refinements of the binder telescopes (lane `verdicts-b`, helper `k1`)

The verdict claims of `infer_lams_leaf`, `infer_pis_leaf` (the leaves: the residual body's type,
for `∀` its sort; the outward rebuilds call only functions outside the verdict closure, so their
errors claim nothing), `infer_lams`, `infer_pis` (the peel loops, by induction on the loop fuel
as `lamsFull_ref`/`pisFull_ref`: a domain whose type is no sort rejects), `infer_lam`,
`infer_forall`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace L.Arena

/-! ## The leaves -/

l_model inferLamsLeaf_specE (p : Prog) (hf : p.lookup "infer_lams_leaf" = some inferLamsLeafL)
  fns [hf ↦ inferLamsLeafE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  finish [tierW, idxW] heartbeats 400000 errors

l_model inferPisLeaf_specE (p : Prog) (hf : p.lookup "infer_pis_leaf" = some inferPisLeafL)
  fns [hf ↦ inferPisLeafE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  finish [tierW, idxW] heartbeats 400000 errors

/-- The λ leaf's outward rebuild (`ar_entry`, `mk_forall`) fails with class `0` only. -/
theorem lamsOutE_cls0 (p : Prog) (hnv : closedNV p L.Checker.nvFns = true) :
    ∀ k (m : Mem) (d lo cur n' : Word) (e : Err),
      inferLamsLeafE.loop1 p k m d lo cur n' = .error e → e.cls = 0 := by
  intro k
  induction k with
  | zero => intro m d lo cur n' e h; rw [inferLamsLeafE.loop1.eq_1] at h; cases h; rfl
  | succ k ih =>
    intro m d lo cur n' e h
    rw [inferLamsLeafE.loop1.eq_2] at h
    split at h
    · cases h1 : callE p k "ar_entry" [rdW (m.arr64 BSTK) (lo + (n' - 1)), d, n' - 1, 0] m with
      | error e1 =>
        rw [h1, inferLamsLeafE.k_ar_entry_2.eq_1] at h; cases h
        exact callE_nv hnv (inferArmsE_nv "ar_entry" (by simp)) _ _ _ h1
      | ok q =>
      obtain ⟨r₁, m₁⟩ := q
      rw [h1, inferLamsLeafE.k_ar_entry_2.eq_2] at h
      cases h2 : callE p k "mk_forall" [r₁.headD 0, cur] m₁ with
      | error e2 =>
        rw [h2, inferLamsLeafE.k_mk_forall.none] at h; cases h
        exact callE_nv hnv (inferArmsE_nv "mk_forall" (by simp)) _ _ _ h2
      | ok q =>
      obtain ⟨r₂, m₂⟩ := q
      rw [h2, inferLamsLeafE.k_mk_forall.eq_2] at h
      exact ih _ _ _ _ _ _ h
    · cases h

/-- The ∀ leaf's outward `imax` fold (`intern_imax`) fails with class `0` only. -/
theorem pisOutE_cls0 (p : Prog) (hnv : closedNV p L.Checker.nvFns = true) :
    ∀ k (m : Mem) (lo v n' : Word) (e : Err),
      inferPisLeafE.loop1 p k m lo v n' = .error e → e.cls = 0 := by
  intro k
  induction k with
  | zero => intro m lo v n' e h; rw [inferPisLeafE.loop1.eq_1] at h; cases h; rfl
  | succ k ih =>
    intro m lo v n' e h
    rw [inferPisLeafE.loop1.eq_2] at h
    split at h
    · cases h1 : callE p k "intern_imax" [rdW (m.arr64 BSTK) (lo + (n' - 1)), v] m with
      | error e1 =>
        rw [h1, inferPisLeafE.k_intern_imax.eq_1] at h; cases h
        exact callE_nv hnv (inferArmsE_nv "intern_imax" (by simp)) _ _ _ h1
      | ok q =>
      obtain ⟨r₁, m₁⟩ := q
      rw [h1, inferPisLeafE.k_intern_imax.eq_2] at h
      exact ih _ _ _ _ _ h
    · cases h

/-- **`infer_lams_leaf`'s verdicts**: the residual body's type (the `infer` slot at `d + k`); the
opening and the outward rebuild claim nothing. -/
theorem inferLamsLeaf_refinesE (p : Prog) (hq : BindProg p) (hil : InstListOK p)
    (hnv : closedNV p L.Checker.nvFns = true) (n : Nat)
    (hk : KnotUpTo p n) (hkE : KnotUpToE p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d t k fo lo : Word) (fvs : Array EIdx) (ws : Array Word)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ht : HW t) (hf : SpineR s₀.mem fo k fvs)
    (hftop : fo.toNat + k.toNat ≤ (spTop s₀.mem).toNat) (hB : BStkR s₀.mem lo k ws)
    (hdk : d.toNat + k.toNat < 2 ^ 64) :
    CoreSpecE p (n + 1) "infer_lams_leaf" [mode, vis, d, t, k, fo, lo]
      (inferLamsLeaf (coreKnot (decMode mode) fe id F) d.toNat (decE t) k.toNat fvs (ws.map decE))
      s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (inferLamsLeaf_specE p hq.lamsLeaf (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d t k fo lo) hc0 (Err.code_ne_of_cls hk0)
  rw [inferLamsLeafE.arm1] at hW
  have hS := hs.rel
  have hdk' : (d + k).toNat = d.toNat + k.toNat := addW _ _ hdk
  have h0 : (0 : Word).toNat = 0 := rfl
  have hT : inferLamsLeaf (coreKnot (decMode mode) fe id F) d.toNat (decE t) k.toNat fvs (ws.map decE) =
      (instantiateListFast coreWalkFuel (decE t) fvs (0 : Word).toNat >>= fun ob =>
        (coreKnot (decMode mode) fe id F).infer (d + k).toNat ob >>= fun bt =>
        abstractRangeFast coreWalkFuel bt d.toNat k.toNat (0 : Word).toNat >>= fun cur =>
        inferLamsOut d.toNat (ws.map decE) k.toNat cur) := by
    rw [hdk', h0, inferLamsLeaf, Array.size_map, hB.size]
  rw [hT]
  cases h1 : callE p n "inst_list" [t, fo, k, 0] s₀.mem with
  | error e1 =>
    rw [h1, inferLamsLeafE.k_inst_list.eq_1] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (inferArmsE_nv "inst_list" (by simp)) h1
  | ok q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [h1, inferLamsLeafE.k_inst_list.eq_2] at hW
  have h₁ := CoreSpec.of_callW (hil n s₀ a₀ dn vis fe M eb t fo k 0 fvs hS ht hf hftop) (callW_of_callE h1)
  obtain ⟨M₁, hS₁, -, -⟩ := h₁.2.1
  refine ErrClaim.bind_ref h₁ ?_
  cases h2 : callE p n "infer" [mode, vis, d + k, r₁.headD 0] m₁ with
  | error e2 =>
    rw [h2, inferLamsLeafE.k_infer.eq_1] at hW; cases hW
    exact ErrClaim.bind_left (CoreSpecE.of_callE (s₀ := ⟨m₁, Locals.init []⟩)
      ((hkE n (Nat.le_refl _)).infer F ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode (d + k) (r₁.headD 0)
        hF hn ⟨hS₁, hs.mode4, hs.eb_mode⟩ h₁.2.2.2) h2)
  | ok q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [h2, inferLamsLeafE.k_infer.eq_2] at hW
  cases h3 : callE p n "ar_entry" [r₂.headD 0, d, k, 0] m₂ with
  | error e3 =>
    rw [h3, inferLamsLeafE.k_ar_entry.eq_1] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (inferArmsE_nv "ar_entry" (by simp)) h3
  | ok q =>
  obtain ⟨r₃, m₃⟩ := q
  rw [h3, inferLamsLeafE.k_ar_entry.eq_2] at hW
  cases hL : inferLamsLeafE.loop1 p (n + 1) m₃ d lo (r₃.headD 0) k with
  | error e4 =>
    rw [hL, inferLamsLeafE.k_loop1.eq_1] at hW; cases hW
    exact ErrClaim.of_cls0 (lamsOutE_cls0 p hnv _ _ _ _ _ _ _ hL)
  | ok q => rw [hL, inferLamsLeafE.k_loop1.arm1] at hW; cases hW

/-- **`infer_pis_leaf`'s verdicts**: the residual codomain's type (the `infer` slot at `d + k`),
`ensure_sort`'s; the opening, the outward fold and the sort claim nothing. -/
theorem inferPisLeaf_refinesE (p : Prog) (hp : InferLeafProg p) (hq : BindProg p) (hil : InstListOK p)
    (hnv : closedNV p L.Checker.nvFns = true) (n : Nat)
    (hk : KnotUpTo p n) (hkE : KnotUpToE p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d t k fo lo : Word) (fvs : Array EIdx) (ws : Array Word)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ht : HW t) (hf : SpineR s₀.mem fo k fvs)
    (hftop : fo.toNat + k.toNat ≤ (spTop s₀.mem).toNat) (hB : BStkR s₀.mem lo k ws)
    (hdk : d.toNat + k.toNat < 2 ^ 64) :
    CoreSpecE p (n + 1) "infer_pis_leaf" [mode, vis, d, t, k, fo, lo]
      (inferPisLeaf (coreKnot (decMode mode) fe id F) fe d.toNat (decE t) k.toNat fvs (ws.map decI))
      s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (inferPisLeaf_specE p hq.pisLeaf (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d t k fo lo) hc0 (Err.code_ne_of_cls hk0)
  rw [inferPisLeafE.arm1] at hW
  have hS := hs.rel
  have hdk' : (d + k).toNat = d.toNat + k.toNat := addW _ _ hdk
  have h0 : (0 : Word).toNat = 0 := rfl
  have hT : inferPisLeaf (coreKnot (decMode mode) fe id F) fe d.toNat (decE t) k.toNat fvs (ws.map decI) =
      (instantiateListFast coreWalkFuel (decE t) fvs (0 : Word).toNat >>= fun ob =>
        (coreKnot (decMode mode) fe id F).infer (d + k).toNat ob >>= fun bt =>
        ensureSort (coreKnot (decMode mode) fe id F) fe (d + k).toNat bt >>= fun v =>
        inferPisOut (ws.map decI) k.toNat v >>= fun iv => internSortE iv) := by
    rw [hdk', h0, inferPisLeaf, Array.size_map, hB.size]
  rw [hT]
  cases h1 : callE p n "inst_list" [t, fo, k, 0] s₀.mem with
  | error e1 =>
    rw [h1, inferPisLeafE.k_inst_list.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (inferArmsE_nv "inst_list" (by simp)) h1
  | ok q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [h1, inferPisLeafE.k_inst_list.eq_2] at hW
  have h₁ := CoreSpec.of_callW (hil n s₀ a₀ dn vis fe M eb t fo k 0 fvs hS ht hf hftop) (callW_of_callE h1)
  obtain ⟨M₁, hS₁, -, -⟩ := h₁.2.1
  refine ErrClaim.bind_ref h₁ ?_
  cases h2 : callE p n "infer" [mode, vis, d + k, r₁.headD 0] m₁ with
  | error e2 =>
    rw [h2, inferPisLeafE.k_infer.none] at hW; cases hW
    exact ErrClaim.bind_left (CoreSpecE.of_callE (s₀ := ⟨m₁, Locals.init []⟩)
      ((hkE n (Nat.le_refl _)).infer F ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode (d + k) (r₁.headD 0)
        hF hn ⟨hS₁, hs.mode4, hs.eb_mode⟩ h₁.2.2.2) h2)
  | ok q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [h2, inferPisLeafE.k_infer.eq_2] at hW
  have h₂ := CoreSpec.of_callW ((hk n (Nat.le_refl _)).infer F ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb
    mode (d + k) (r₁.headD 0) hF hn ⟨hS₁, hs.mode4, hs.eb_mode⟩ h₁.2.2.2) (callW_of_callE h2)
  obtain ⟨M₂, hS₂, -, -⟩ := h₂.2.1
  refine ErrClaim.bind_ref h₂ ?_
  cases h3 : callE p n "ensure_sort" [mode, vis, d + k, r₂.headD 0] m₂ with
  | error e3 =>
    rw [h3, inferPisLeafE.k_ensure_sort.eq_1] at hW; cases hW
    exact ErrClaim.bind_left (CoreSpecE.of_callE (s₀ := ⟨m₂, Locals.init []⟩)
      (ensureSortSpecE_of_knot p hp n hk hkE F ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode (d + k)
        (r₂.headD 0) hF hn ⟨hS₂, hs.mode4, hs.eb_mode⟩ h₂.2.2.2) h3)
  | ok q =>
  obtain ⟨r₃, m₃⟩ := q
  rw [h3, inferPisLeafE.k_ensure_sort.arm1] at hW
  cases hL : inferPisLeafE.loop1 p (n + 1) m₃ lo (r₃.headD 0) k with
  | error e4 =>
    rw [hL, inferPisLeafE.k_loop1.none] at hW; cases hW
    exact ErrClaim.of_cls0 (pisOutE_cls0 p hnv _ _ _ _ _ _ hL)
  | ok q =>
  obtain ⟨v, m₄⟩ := q
  rw [hL, inferPisLeafE.k_loop1.arm1] at hW
  cases h5 : callE p n "intern_sort" [v] m₄ with
  | error e5 =>
    rw [h5, inferPisLeafE.k_intern_sort.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (inferArmsE_nv "intern_sort" (by simp)) h5
  | ok q => rw [h5, inferPisLeafE.k_intern_sort.eq_2] at hW; cases hW

end L.Arena
