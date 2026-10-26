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

/-! ## `infer_lams` -/

l_model inferLams_specE (p : Prog) (hf : p.lookup "infer_lams" = some inferLamsL)
  fns [hf ↦ inferLamsE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 simp [tierW, idxW] errors

/-- `CTL[137]` (the binder top) is a word of the control array (as `CoreS.ctl136`). -/
theorem CoreS.ctl137 {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {M : ModeMaps}
    {eb : Word} {m : Mem} {a : AState} (hS : CoreS dn m a vis fe M eb) :
    137 < (m.arr64 CTL).size := by
  obtain ⟨mp, h⟩ := hS.memos.2.2.2.2.1
  unfold MemoRG MemoRV at h
  have := h.1
  simp only [coreLsbSch] at this
  have e : (156 : Word).toNat = 156 := rfl
  omega

/-- The guards of a telescope step's pushes from the L code's length checks and `CoreS`. -/
theorem tPushOK_of {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {M : ModeMaps}
    {eb : Word} {m : Mem} {a : AState} {fo lo k : Word} (hS : CoreS dn m a vis fe M eb)
    (h1 : ¬ m.len64 SPN ≤ fo + k) (h2 : ¬ m.len64 BSTK ≤ lo + k) : tPushOK m fo lo k :=
  ⟨h1, h2, lt_of_not_len64_le hS.spn h1, lt_of_not_len64_le hS.bstk h2, hS.ctl137⟩

/-- `infer_lams_leaf`'s error claim at every L fuel up to `n + 1`. -/
theorem inferLamsLeaf_anyE (p : Prog) (hq : BindProg p) (hil : InstListOK p)
    (hnv : closedNV p L.Checker.nvFns = true) :
    ∀ n, KnotUpTo p n → KnotUpToE p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 → ∀ (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d t k fo lo : Word) (fvs : Array EIdx) (ws : Array Word),
    SlotPre s₀ a₀ dn vis fe M eb mode → HW t → SpineR s₀.mem fo k fvs →
    fo.toNat + k.toNat ≤ (spTop s₀.mem).toNat → BStkR s₀.mem lo k ws →
    d.toNat + k.toNat < 2 ^ 64 →
    CoreSpecE p n "infer_lams_leaf" [mode, vis, d, t, k, fo, lo]
      (inferLamsLeaf (coreKnot (decMode mode) fe id F) d.toNat (decE t) k.toNat fvs (ws.map decE)) s₀ a₀
  | 0, _, _, _, _, _, s₀, a₀, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ =>
      CoreSpecE.zero p _ _ _ s₀ a₀
  | n + 1, hk, hkE, F, hF, hn, s₀, a₀, dn, vis, fe, M, eb, mode, d, t, k, fo, lo, fvs, ws, hs, ht, hf,
      hftop, hB, hdk =>
      inferLamsLeaf_refinesE p hq hil hnv n (hk.mono (by omega)) (hkE.mono (by omega)) F (by omega)
        (by omega) s₀ a₀ dn vis fe M eb mode d t k fo lo fvs ws hs ht hf hftop hB hdk

/-- **The λ peel loop with its leaf claims `inferLams`' failure** (by induction on the loop fuel,
as `lamsFull_ref`): a domain's type (the `infer` slot), its `whnf` (the slot), a domain type that
is no sort (a reject), the leaf's. -/
theorem lamsFullE_ref (p : Prog) (hp : InferLeafProg p) (hq : BindProg p) (hb : InferBodyProg p)
    (hil : InstListOK p) (hnv : closedNV p L.Checker.nvFns = true) (hcap : BStkCap)
    (N : Nat) (hk : KnotUpTo p N) (hkE : KnotUpToE p N) (F : Nat) (hFN : N ≤ F) (hN : N ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (mode d fo lo eb : Word)
    (hmode : mode < 4) (heb : eb = (mode >>> 1) &&& 1) (m₀ : Mem) :
    ∀ j, j ≤ N + 1 → ∀ (m : Mem) (a : AState) (M : ModeMaps) (peel t k ty0 : Word) (fvs : Array EIdx)
      (ws : Array Word),
      CoreS dn m a vis fe M eb → HW t → SpineR m fo k fvs → spTop m = fo + k →
      BStkR m lo k ws → bTop m = lo + k → (∀ (i : Nat) (h : i < ws.size), HW ws[i]) →
      d.toNat + k.toNat + peel.toNat < 2 ^ 64 →
      (∀ j, j < fo → spW m j = spW m₀ j) → (m.arr64 SPN).size = (m₀.arr64 SPN).size →
      (∀ j, j < lo → rdW (m.arr64 BSTK) j = rdW (m₀.arr64 BSTK) j) →
      (m.arr64 BSTK).size = (m₀.arr64 BSTK).size → PoolGrew m₀ m →
      ∀ er, er.cls ≠ 0 →
      inferLamsE.k_loop1 p N mode vis d fo lo
        (inferLamsE.loop1 p j m mode vis d peel t k fo lo ty0) = .error er →
      ErrClaim (inferLams (coreKnot (decMode mode) fe id F) d.toNat peel.toNat (decE t) k.toNat fvs
        (ws.map decE)) a er := by
  intro j
  induction j with
  | zero =>
    intro _ m a M peel t k ty0 fvs ws _ _ _ _ _ _ _ _ _ _ _ _ _ er hk0 hF
    rw [inferLamsE.loop1.eq_1, inferLamsE.k_loop1.none] at hF; cases hF; exact absurd rfl hk0
  | succ j ih =>
    intro hjN m a M peel t k ty0 fvs ws hS ht hf htop hB hbt hws hdk hb0 hsz hbb0 hbsz0 hpg0 er hk0 hF
    rw [inferLamsE.loop1.eq_2] at hF
    have hspn := hS.spn
    have hcp := hcap _ _ _ _ _ _ _ hS
    have hfb := hf.bound
    have hBb := hB.bound
    have haddf : (fo + k).toNat = fo.toNat + k.toNat := addW _ _ (by omega)
    have haddl : (lo + k).toNat = lo.toNat + k.toNat := addW _ _ (by omega)
    have haddd : (d + k).toNat = d.toNat + k.toNat := addW _ _ (by omega)
    have hftop : fo.toNat + k.toNat ≤ (spTop m).toNat := by rw [htop, haddf]; exact Nat.le_refl _
    have hbtop : lo.toNat + k.toNat ≤ (bTop m).toNat := by rw [hbt, haddl]; exact Nat.le_refl _
    have h0 : (0 : Word).toNat = 0 := rfl
    by_cases hc : peel ≠ 0 ∧ t >>> 28 = 5
    · rw [if_pos hc] at hF
      obtain ⟨hp0, ht5⟩ := hc
      split at hF
      · rw [inferLamsE.k_loop1.none] at hF
        exact absurd hF (fun h => cls_abort0 hk0 (Except.error.inj h))
      rename_i hc1
      split at hF
      · rw [inferLamsE.k_loop1.none] at hF
        exact absurd hF (fun h => cls_abort0 hk0 (Except.error.inj h))
      rename_i hc2
      have hv : viewOK m t LAM := ⟨hc1, UInt64.not_le.mp hc2⟩
      obtain ⟨-, hty, hbody⟩ := view_lam m a hS.arena.1 t ht hv ht5
      have hvb := viewBind_lam m a hS.arena.1 t ht hv ht5
      obtain ⟨p', hp'⟩ : ∃ p', peel.toNat = p' + 1 :=
        ⟨peel.toNat - 1, by
          have : peel.toNat ≠ 0 := fun h' => hp0 (UInt64.toNat_inj.mp (by simpa using h')); omega⟩
      have hlam : ((decE t).tag != ETag.lam) = false := by
        rw [bne_eq_false_iff_eq, ← beq_iff_eq, decE_tag_lam t ht]; simp [ht5]
      rw [hp', inferLams]
      simp only [hlam, Bool.false_eq_true, ↓reduceIte]
      refine ErrClaim.bind_right (by rw [viewBind_run', hvb]) ?_
      dsimp only
      cases h1 : callE p j "inst_list" [tfld m LAM (tierW t) (idxW t) 0, fo, k, 0] m with
      | error e1 =>
        rw [h1, inferLamsE.k_inst_list.none, inferLamsE.k_loop1.none] at hF; cases hF
        exact ErrClaim.of_callE_nv hnv (inferArmsE_nv "inst_list" (by simp)) h1
      | ok q =>
      obtain ⟨r₁, m₁⟩ := q
      rw [h1, inferLamsE.k_inst_list.eq_2] at hF
      have h₁ := CoreSpec.of_callW (hil j ⟨m, Locals.init []⟩ a dn vis fe M eb _ fo k 0 fvs hS hty hf
        hftop) (callW_of_callE h1)
      rw [h0] at h₁
      obtain ⟨M₁, hS₁, hK₁, hSt₁⟩ := h₁.2.1
      have hrw1 := h₁.2.2.2
      refine ErrClaim.bind_ref h₁ ?_
      cases h2 : callE p j "infer" [mode, vis, d + k, r₁.headD 0] m₁ with
      | error e2 =>
        rw [h2, inferLamsE.k_infer.none, inferLamsE.k_loop1.none] at hF; cases hF
        have hc := CoreSpecE.of_callE (s₀ := ⟨m₁, Locals.init []⟩) ((hkE j (by omega)).infer F
          ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode (d + k) (r₁.headD 0) (by omega) (by omega)
          ⟨hS₁, hmode, heb⟩ hrw1) h2
        rw [haddd] at hc
        exact ErrClaim.bind_left hc
      | ok q =>
      obtain ⟨r₂, m₂⟩ := q
      rw [h2, inferLamsE.k_infer.eq_2] at hF
      have h₂ := CoreSpec.of_callW ((hk j (by omega)).infer F ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb
        mode (d + k) (r₁.headD 0) (by omega) (by omega) ⟨hS₁, hmode, heb⟩ hrw1) (callW_of_callE h2)
      rw [haddd] at h₂
      obtain ⟨M₂, hS₂, hK₂, hSt₂⟩ := h₂.2.1
      have hrw2 := h₂.2.2.2
      refine ErrClaim.bind_ref h₂ ?_
      cases h3 : callE p j "whnf" [mode, vis, d + k, r₂.headD 0] m₂ with
      | error e3 =>
        rw [h3, inferLamsE.k_whnf.none, inferLamsE.k_loop1.none] at hF; cases hF
        have hc := CoreSpecE.of_callE (s₀ := ⟨m₂, Locals.init []⟩) ((hkE j (by omega)).whnf F
          ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode (d + k) (r₂.headD 0) (by omega) (by omega)
          ⟨hS₂, hmode, heb⟩ hrw2) h3
        rw [haddd] at hc
        exact ErrClaim.bind_left hc
      | ok q =>
      obtain ⟨r₃, m₃⟩ := q
      rw [h3, inferLamsE.k_whnf.eq_2] at hF
      have h₃ := CoreSpec.of_callW ((hk j (by omega)).whnf F ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb
        mode (d + k) (r₂.headD 0) (by omega) (by omega) ⟨hS₂, hmode, heb⟩ hrw2) (callW_of_callE h3)
      rw [haddd] at h₃
      obtain ⟨M₃, hS₃, hK₃, hSt₃⟩ := h₃.2.1
      have hrw3 := h₃.2.2.2
      refine ErrClaim.bind_ref h₃ ?_
      by_cases g1 : r₃.headD 0 >>> 28 ≠ 2
      · rw [if_pos g1, inferLamsE.k_loop1.none] at hF; cases hF
        simp only [show decH r₃ = decE (r₃.headD 0) from rfl, tag_sort_ne _ hrw3 g1,
          Bool.false_eq_true, ↓reduceIte]
        exact ErrClaim.fail _ _ rfl
      rw [if_neg g1] at hF
      have g1' : r₃.headD 0 >>> 28 = 2 := by simpa using g1
      simp only [show decH r₃ = decE (r₃.headD 0) from rfl, tag_sort_beq _ hrw3 g1', ↓reduceIte,
        internFVarE]
      cases h4 : callE p j "intern_fvar" [d + k, r₁.headD 0] m₃ with
      | error e4 =>
        rw [h4, inferLamsE.k_intern_fvar.none, inferLamsE.k_loop1.none] at hF; cases hF
        exact ErrClaim.of_callE_nv hnv (inferArmsE_nv "intern_fvar" (by simp)) h4
      | ok q =>
      obtain ⟨r₄, m₄⟩ := q
      rw [h4, inferLamsE.k_intern_fvar.eq_2] at hF
      obtain ⟨s₄, hs₄, -, hfv⟩ := triple_of_callW (s₀ := ⟨m₃, Locals.init []⟩)
        (internFVar_spec p hb.fvf hb.fvp hb.fvi j _ (d + k) (r₁.headD 0)) (callW_of_callE h4)
      rw [hs₄] at hfv
      have h₄ := internFVar_core hS₃ (d + k) (r₁.headD 0) hrw1 r₄ hfv
      rw [haddd] at h₄
      obtain ⟨M₄, hS₄, hK₄, hSt₄⟩ := h₄.2.1
      have hrw4 := h₄.2.2.2
      have hB₄ : BKept m₃ m₄ := by
        exact BKept.of_frame ((fvinternW_frame (hI := hfv)))
          (by simp [fvarSch, FVREC, FVSLOT, FVLP, BSTK]) (by simp [fvarSch])
      refine ErrClaim.bind_ref h₄ ?_
      split at hF
      · rw [inferLamsE.k_loop1.none] at hF
        exact absurd hF (fun h => cls_abort0 hk0 (Except.error.inj h))
      rename_i g2a
      split at hF
      · rw [inferLamsE.k_loop1.none] at hF
        exact absurd hF (fun h => cls_abort0 hk0 (Except.error.inj h))
      rename_i g2b
      have g2 : tPushOK m₄ fo lo k := tPushOK_of hS₄ g2a g2b
      have hSt14 := hSt₁.trans (hSt₂.trans (hSt₃.trans hSt₄))
      have hBK := hSt₁.bstk.trans (hSt₂.bstk.trans (hSt₃.bstk.trans hB₄))
      have hf₄ : SpineR m₄ fo k fvs := hf.keep hSt14.size hSt14.below hftop hspn
      have hB4 : BStkR m₄ lo k ws := hB.keep hBK hbtop hcp
      have hb₄ : ∀ i, i < fo → spW m₄ i = spW m₀ i := fun i hi => by
        have hi' : i < spTop m := by
          rw [htop, UInt64.lt_iff_toNat_lt, haddf]; have := UInt64.lt_iff_toNat_lt.mp hi; omega
        exact (hSt14.below i hi').trans (hb0 i hi)
      have hbb₄ : ∀ i, i < lo → rdW (m₄.arr64 BSTK) i = rdW (m₀.arr64 BSTK) i := fun i hi => by
        have hi' : i < bTop m := by
          rw [hbt, UInt64.lt_iff_toNat_lt, haddl]; have := UInt64.lt_iff_toNat_lt.mp hi; omega
        exact (hBK.2.2 i hi').trans (hbb0 i hi)
      obtain ⟨hS', hf', htop', hB', hbt', hb', hsz', hbszT, hbbT, hpgT⟩ := tPush_step (m₀ := m₀) hS₄
        (by rw [hBK.2.1]; exact hcp) hf₄ hB4 hb₄ (hSt14.size.trans hsz) g2 hrw4
      have hws' : ∀ (i : Nat) (h : i < (ws.push (r₁.headD 0)).size), HW (ws.push (r₁.headD 0))[i] := by
        intro i hi
        rw [Array.getElem_push]
        split
        · exact hws i _
        · exact hrw1
      have hpeel1 : (peel - 1).toNat = peel.toNat - 1 := by
        rw [UInt64.toNat_sub_of_le]; · rfl
        rw [UInt64.le_iff_toNat_le]; simp
        have : peel.toNat ≠ 0 := fun h' => hp0 (UInt64.toNat_inj.mp (by simpa using h')); omega
      have hk1 : (k + 1).toNat = k.toNat + 1 := addW _ _ (by simp; omega)
      have hih := ih (by omega) _ _ M₄ (peel - 1) _ (k + 1) _ _ _ hS' hbody hf' htop' hB' hbt' hws'
        (by rw [hk1, hpeel1]; omega) hb' hsz' (fun i hi => (hbbT i hi).trans (hbb₄ i hi))
        (hbszT.trans (hBK.2.1.trans hbsz0)) ((hpg0.trans hSt14.pool).trans hpgT) er hk0 hF
      rw [hk1, hpeel1, hp', Nat.add_sub_cancel, Array.map_push] at hih
      exact hih
    · rw [if_neg hc, inferLamsE.k_loop1.eq_2] at hF
      cases hL : callE p N "infer_lams_leaf" [mode, vis, d, t, k, fo, lo] m with
      | error e1 =>
        rw [hL, inferLamsE.k_infer_lams_leaf.none] at hF; cases hF
        have hc' := CoreSpecE.of_callE (s₀ := ⟨m, Locals.init []⟩) (inferLamsLeaf_anyE p hq hil hnv N hk
          hkE F hFN hN ⟨m, Locals.init []⟩ a dn vis fe M eb mode d t k fo lo fvs ws ⟨hS, hmode, heb⟩ ht
          hf hftop hB (by omega)) hL
        refine ErrClaim.of_run_eq' (fun ce h => ?_) hc'
        by_cases hp0 : peel = 0
        · subst hp0; exact h
        · have ht5 : ¬ t >>> 28 = 5 := fun h => hc ⟨hp0, h⟩
          obtain ⟨p', hp'⟩ : ∃ p', peel.toNat = p' + 1 :=
            ⟨peel.toNat - 1, by
              have : peel.toNat ≠ 0 := fun h' => hp0 (UInt64.toNat_inj.mp (by simpa using h')); omega⟩
          have hlam : ((decE t).tag != ETag.lam) = true := by
            rw [bne_iff_ne, ne_eq, ← beq_iff_eq, decE_tag_lam t ht]; simp [ht5]
          rw [hp', inferLams]
          simp only [hlam, ↓reduceIte]
          exact h
      | ok q => rw [hL, inferLamsE.k_infer_lams_leaf.eq_2] at hF; cases hF

/-- **`infer_lams`' verdicts** from a telescope state (the error half of `inferLams_tel`). -/
theorem inferLams_telE (p : Prog) (hp : InferLeafProg p) (hq : BindProg p) (hb : InferBodyProg p)
    (hil : InstListOK p) (hnv : closedNV p L.Checker.nvFns = true) (hcap : BStkCap)
    (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d peel t k fo lo : Word) (fvs : Array EIdx) (ws : Array Word) (m₀ : Mem)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ht : HW t) (hf : SpineR s₀.mem fo k fvs)
    (htop : spTop s₀.mem = fo + k) (hB : BStkR s₀.mem lo k ws) (hbt : bTop s₀.mem = lo + k)
    (hws : ∀ (i : Nat) (h : i < ws.size), HW ws[i]) (hdk : d.toNat + k.toNat + peel.toNat < 2 ^ 64)
    (hb0 : ∀ j, j < fo → spW s₀.mem j = spW m₀ j) (hsz : (s₀.mem.arr64 SPN).size = (m₀.arr64 SPN).size)
    (hbb0 : ∀ j, j < lo → rdW (s₀.mem.arr64 BSTK) j = rdW (m₀.arr64 BSTK) j)
    (hbsz0 : (s₀.mem.arr64 BSTK).size = (m₀.arr64 BSTK).size) (hpg0 : PoolGrew m₀ s₀.mem) :
    CoreSpecE p (n + 1) "infer_lams" [mode, vis, d, peel, t, k, fo, lo]
      (inferLams (coreKnot (decMode mode) fe id F) d.toNat peel.toNat (decE t) k.toNat fvs
        (ws.map decE)) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (inferLams_specE p hq.lams (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d peel t k fo lo) hc0 (Err.code_ne_of_cls hk0)
  rw [inferLamsE.eq_2] at hW
  exact lamsFullE_ref p hp hq hb hil hnv hcap n hk hkE F hF hn dn vis fe mode d fo lo eb hs.mode4
    hs.eb_mode m₀ (n + 1) (Nat.le_refl _) s₀.mem a₀ M peel t k 0 fvs ws hs.rel ht hf htop hB hbt hws hdk
    hb0 hsz hbb0 hbsz0 hpg0 er hk0 hW

/-! ## `infer_pis` -/

l_model inferPis_specE (p : Prog) (hf : p.lookup "infer_pis" = some inferPisL)
  fns [hf ↦ inferPisE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 simp [tierW, idxW] errors

/-- `infer_pis_leaf`'s error claim at every L fuel up to `n + 1`. -/
theorem inferPisLeaf_anyE (p : Prog) (hp : InferLeafProg p) (hq : BindProg p) (hil : InstListOK p)
    (hnv : closedNV p L.Checker.nvFns = true) :
    ∀ n, KnotUpTo p n → KnotUpToE p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 → ∀ (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d t k fo lo : Word) (fvs : Array EIdx) (ws : Array Word),
    SlotPre s₀ a₀ dn vis fe M eb mode → HW t → SpineR s₀.mem fo k fvs →
    fo.toNat + k.toNat ≤ (spTop s₀.mem).toNat → BStkR s₀.mem lo k ws →
    d.toNat + k.toNat < 2 ^ 64 →
    CoreSpecE p n "infer_pis_leaf" [mode, vis, d, t, k, fo, lo]
      (inferPisLeaf (coreKnot (decMode mode) fe id F) fe d.toNat (decE t) k.toNat fvs (ws.map decI))
      s₀ a₀
  | 0, _, _, _, _, _, s₀, a₀, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ =>
      CoreSpecE.zero p _ _ _ s₀ a₀
  | n + 1, hk, hkE, F, hF, hn, s₀, a₀, dn, vis, fe, M, eb, mode, d, t, k, fo, lo, fvs, ws, hs, ht, hf,
      hftop, hB, hdk =>
      inferPisLeaf_refinesE p hp hq hil hnv n (hk.mono (by omega)) (hkE.mono (by omega)) F (by omega)
        (by omega) s₀ a₀ dn vis fe M eb mode d t k fo lo fvs ws hs ht hf hftop hB hdk

/-- **The ∀ peel loop with its leaf claims `inferPis`' failure** (by induction on the loop fuel,
as `pisFull_ref`). -/
theorem pisFullE_ref (p : Prog) (hp : InferLeafProg p) (hq : BindProg p) (hb : InferBodyProg p)
    (hil : InstListOK p) (hnv : closedNV p L.Checker.nvFns = true) (hcap : BStkCap)
    (N : Nat) (hk : KnotUpTo p N) (hkE : KnotUpToE p N) (F : Nat) (hFN : N ≤ F) (hN : N ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (mode d fo lo eb : Word)
    (hmode : mode < 4) (heb : eb = (mode >>> 1) &&& 1) (m₀ : Mem) :
    ∀ j, j ≤ N + 1 → ∀ (m : Mem) (a : AState) (M : ModeMaps) (peel t k ty0 u0 : Word)
      (fvs : Array EIdx) (ws : Array Word),
      CoreS dn m a vis fe M eb → HW t → SpineR m fo k fvs → spTop m = fo + k →
      BStkR m lo k ws → bTop m = lo + k →
      d.toNat + k.toNat + peel.toNat < 2 ^ 64 →
      (∀ j, j < fo → spW m j = spW m₀ j) → (m.arr64 SPN).size = (m₀.arr64 SPN).size →
      (∀ j, j < lo → rdW (m.arr64 BSTK) j = rdW (m₀.arr64 BSTK) j) →
      (m.arr64 BSTK).size = (m₀.arr64 BSTK).size → PoolGrew m₀ m →
      ∀ er, er.cls ≠ 0 →
      inferPisE.k_loop1 p N mode vis d fo lo
        (inferPisE.loop1 p j m mode vis d peel t k fo lo ty0 u0) = .error er →
      ErrClaim (inferPis (coreKnot (decMode mode) fe id F) fe d.toNat peel.toNat (decE t) k.toNat fvs
        (ws.map decI)) a er := by
  intro j
  induction j with
  | zero =>
    intro _ m a M peel t k ty0 u0 fvs ws _ _ _ _ _ _ _ _ _ _ _ _ er hk0 hF
    rw [inferPisE.loop1.eq_1, inferPisE.k_loop1.none] at hF; cases hF; exact absurd rfl hk0
  | succ j ih =>
    intro hjN m a M peel t k ty0 u0 fvs ws hS ht hf htop hB hbt hdk hb0 hsz hbb0 hbsz0 hpg0 er hk0 hF
    rw [inferPisE.loop1.eq_2] at hF
    have hspn := hS.spn
    have hcp := hcap _ _ _ _ _ _ _ hS
    have hfb := hf.bound
    have hBb := hB.bound
    have haddf : (fo + k).toNat = fo.toNat + k.toNat := addW _ _ (by omega)
    have haddl : (lo + k).toNat = lo.toNat + k.toNat := addW _ _ (by omega)
    have haddd : (d + k).toNat = d.toNat + k.toNat := addW _ _ (by omega)
    have hftop : fo.toNat + k.toNat ≤ (spTop m).toNat := by rw [htop, haddf]; exact Nat.le_refl _
    have hbtop : lo.toNat + k.toNat ≤ (bTop m).toNat := by rw [hbt, haddl]; exact Nat.le_refl _
    have h0 : (0 : Word).toNat = 0 := rfl
    by_cases hc : peel ≠ 0 ∧ t >>> 28 = 6
    · rw [if_pos hc] at hF
      obtain ⟨hp0, ht6⟩ := hc
      split at hF
      · rw [inferPisE.k_loop1.none] at hF
        exact absurd hF (fun h => cls_abort0 hk0 (Except.error.inj h))
      rename_i hc1
      split at hF
      · rw [inferPisE.k_loop1.none] at hF
        exact absurd hF (fun h => cls_abort0 hk0 (Except.error.inj h))
      rename_i hc2
      have hv : viewOK m t FORALL := ⟨hc1, UInt64.not_le.mp hc2⟩
      obtain ⟨-, hty, hbody⟩ := view_forall m a hS.arena.1 t ht hv ht6
      have hvb := viewBind_forall m a hS.arena.1 t ht hv ht6
      obtain ⟨p', hp'⟩ : ∃ p', peel.toNat = p' + 1 :=
        ⟨peel.toNat - 1, by
          have : peel.toNat ≠ 0 := fun h' => hp0 (UInt64.toNat_inj.mp (by simpa using h')); omega⟩
      have hlam : ((decE t).tag != ETag.forallE) = false := by
        rw [bne_eq_false_iff_eq, ← beq_iff_eq, tag_fa_beq t ht]; simp [ht6]
      rw [hp', inferPis]
      simp only [hlam, Bool.false_eq_true, ↓reduceIte]
      refine ErrClaim.bind_right (by rw [viewBind_run', hvb]) ?_
      dsimp only
      cases h1 : callE p j "inst_list" [tfld m FORALL (tierW t) (idxW t) 0, fo, k, 0] m with
      | error e1 =>
        rw [h1, inferPisE.k_inst_list.none, inferPisE.k_loop1.none] at hF; cases hF
        exact ErrClaim.of_callE_nv hnv (inferArmsE_nv "inst_list" (by simp)) h1
      | ok q =>
      obtain ⟨r₁, m₁⟩ := q
      rw [h1, inferPisE.k_inst_list.eq_2] at hF
      have h₁ := CoreSpec.of_callW (hil j ⟨m, Locals.init []⟩ a dn vis fe M eb _ fo k 0 fvs hS hty hf
        hftop) (callW_of_callE h1)
      rw [h0] at h₁
      obtain ⟨M₁, hS₁, hK₁, hSt₁⟩ := h₁.2.1
      have hrw1 := h₁.2.2.2
      refine ErrClaim.bind_ref h₁ ?_
      cases h2 : callE p j "infer" [mode, vis, d + k, r₁.headD 0] m₁ with
      | error e2 =>
        rw [h2, inferPisE.k_infer.none, inferPisE.k_loop1.none] at hF; cases hF
        have hc := CoreSpecE.of_callE (s₀ := ⟨m₁, Locals.init []⟩) ((hkE j (by omega)).infer F
          ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode (d + k) (r₁.headD 0) (by omega) (by omega)
          ⟨hS₁, hmode, heb⟩ hrw1) h2
        rw [haddd] at hc
        exact ErrClaim.bind_left hc
      | ok q =>
      obtain ⟨r₂, m₂⟩ := q
      rw [h2, inferPisE.k_infer.eq_2] at hF
      have h₂ := CoreSpec.of_callW ((hk j (by omega)).infer F ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb
        mode (d + k) (r₁.headD 0) (by omega) (by omega) ⟨hS₁, hmode, heb⟩ hrw1) (callW_of_callE h2)
      rw [haddd] at h₂
      obtain ⟨M₂, hS₂, hK₂, hSt₂⟩ := h₂.2.1
      have hrw2 := h₂.2.2.2
      refine ErrClaim.bind_ref h₂ ?_
      cases h3 : callE p j "whnf" [mode, vis, d + k, r₂.headD 0] m₂ with
      | error e3 =>
        rw [h3, inferPisE.k_whnf.none, inferPisE.k_loop1.none] at hF; cases hF
        have hc := CoreSpecE.of_callE (s₀ := ⟨m₂, Locals.init []⟩) ((hkE j (by omega)).whnf F
          ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode (d + k) (r₂.headD 0) (by omega) (by omega)
          ⟨hS₂, hmode, heb⟩ hrw2) h3
        rw [haddd] at hc
        exact ErrClaim.bind_left hc
      | ok q =>
      obtain ⟨r₃, m₃⟩ := q
      rw [h3, inferPisE.k_whnf.eq_2] at hF
      have h₃ := CoreSpec.of_callW ((hk j (by omega)).whnf F ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb
        mode (d + k) (r₂.headD 0) (by omega) (by omega) ⟨hS₂, hmode, heb⟩ hrw2) (callW_of_callE h3)
      rw [haddd] at h₃
      obtain ⟨M₃, hS₃, hK₃, hSt₃⟩ := h₃.2.1
      have hrw3 := h₃.2.2.2
      refine ErrClaim.bind_ref h₃ ?_
      by_cases g1 : r₃.headD 0 >>> 28 ≠ 2
      · rw [if_pos g1, inferPisE.k_loop1.none] at hF; cases hF
        simp only [show decH r₃ = decE (r₃.headD 0) from rfl, tag_sort_ne _ hrw3 g1,
          Bool.false_eq_true, ↓reduceIte]
        exact ErrClaim.fail _ _ rfl
      rw [if_neg g1] at hF
      have g1' : r₃.headD 0 >>> 28 = 2 := by simpa using g1
      split at hF
      · rw [inferPisE.k_loop1.none] at hF
        exact absurd hF (fun h => cls_abort0 hk0 (Except.error.inj h))
      rename_i gs1
      split at hF
      · rw [inferPisE.k_loop1.none] at hF
        exact absurd hF (fun h => cls_abort0 hk0 (Except.error.inj h))
      rename_i gs2
      obtain ⟨hvs, hu⟩ := L.Ind.view_sort_f m₃ _ hS₃.arena.1 (r₃.headD 0) hrw3 ⟨gs1, UInt64.not_le.mp gs2⟩ g1'
      simp only [show decH r₃ = decE (r₃.headD 0) from rfl, tag_sort_beq _ hrw3 g1', ↓reduceIte]
      refine ErrClaim.bind_right (L.Ind.viewSort_run (L.Ind.viewSort_of_view _ _ _
        ((decE_tag_eq _ hrw3 2 (by decide)).mpr g1') hvs)) ?_
      dsimp only
      simp only [internFVarE]
      cases h4 : callE p j "intern_fvar" [d + k, r₁.headD 0] m₃ with
      | error e4 =>
        rw [h4, inferPisE.k_intern_fvar.none, inferPisE.k_loop1.none] at hF; cases hF
        exact ErrClaim.of_callE_nv hnv (inferArmsE_nv "intern_fvar" (by simp)) h4
      | ok q =>
      obtain ⟨r₄, m₄⟩ := q
      rw [h4, inferPisE.k_intern_fvar.eq_2] at hF
      obtain ⟨s₄, hs₄, -, hfv⟩ := triple_of_callW (s₀ := ⟨m₃, Locals.init []⟩)
        (internFVar_spec p hb.fvf hb.fvp hb.fvi j _ (d + k) (r₁.headD 0)) (callW_of_callE h4)
      rw [hs₄] at hfv
      have h₄ := internFVar_core hS₃ (d + k) (r₁.headD 0) hrw1 r₄ hfv
      rw [haddd] at h₄
      obtain ⟨M₄, hS₄, hK₄, hSt₄⟩ := h₄.2.1
      have hrw4 := h₄.2.2.2
      have hB₄ : BKept m₃ m₄ := by
        exact BKept.of_frame ((fvinternW_frame (hI := hfv)))
          (by simp [fvarSch, FVREC, FVSLOT, FVLP, BSTK]) (by simp [fvarSch])
      refine ErrClaim.bind_ref h₄ ?_
      split at hF
      · rw [inferPisE.k_loop1.none] at hF
        exact absurd hF (fun h => cls_abort0 hk0 (Except.error.inj h))
      rename_i g2a
      split at hF
      · rw [inferPisE.k_loop1.none] at hF
        exact absurd hF (fun h => cls_abort0 hk0 (Except.error.inj h))
      rename_i g2b
      have g2 : tPushOK m₄ fo lo k := tPushOK_of hS₄ g2a g2b
      have hSt14 := hSt₁.trans (hSt₂.trans (hSt₃.trans hSt₄))
      have hBK := hSt₁.bstk.trans (hSt₂.bstk.trans (hSt₃.bstk.trans hB₄))
      have hf₄ : SpineR m₄ fo k fvs := hf.keep hSt14.size hSt14.below hftop hspn
      have hB4 : BStkR m₄ lo k ws := hB.keep hBK hbtop hcp
      have hb₄ : ∀ i, i < fo → spW m₄ i = spW m₀ i := fun i hi => by
        have hi' : i < spTop m := by
          rw [htop, UInt64.lt_iff_toNat_lt, haddf]; have := UInt64.lt_iff_toNat_lt.mp hi; omega
        exact (hSt14.below i hi').trans (hb0 i hi)
      have hbb₄ : ∀ i, i < lo → rdW (m₄.arr64 BSTK) i = rdW (m₀.arr64 BSTK) i := fun i hi => by
        have hi' : i < bTop m := by
          rw [hbt, UInt64.lt_iff_toNat_lt, haddl]; have := UInt64.lt_iff_toNat_lt.mp hi; omega
        exact (hBK.2.2 i hi').trans (hbb0 i hi)
      obtain ⟨hS', hf', htop', hB', hbt', hb', hsz', hbszT, hbbT, hpgT⟩ := tPush_step (m₀ := m₀) hS₄
        (by rw [hBK.2.1]; exact hcp) hf₄ hB4 hb₄ (hSt14.size.trans hsz) g2 hrw4
      have hpeel1 : (peel - 1).toNat = peel.toNat - 1 := by
        rw [UInt64.toNat_sub_of_le]; · rfl
        rw [UInt64.le_iff_toNat_le]; simp
        have : peel.toNat ≠ 0 := fun h' => hp0 (UInt64.toNat_inj.mp (by simpa using h')); omega
      have hk1 : (k + 1).toNat = k.toNat + 1 := addW _ _ (by simp; omega)
      have hih := ih (by omega) _ _ M₄ (peel - 1) _ (k + 1) _ _ _ _ hS' hbody hf' htop' hB' hbt'
        (by rw [hk1, hpeel1]; omega) hb' hsz' (fun i hi => (hbbT i hi).trans (hbb₄ i hi))
        (hbszT.trans (hBK.2.1.trans hbsz0)) ((hpg0.trans hSt14.pool).trans hpgT) er hk0 hF
      rw [hk1, hpeel1, hp', Nat.add_sub_cancel, Array.map_push] at hih
      exact hih
    · rw [if_neg hc, inferPisE.k_loop1.eq_2] at hF
      cases hL : callE p N "infer_pis_leaf" [mode, vis, d, t, k, fo, lo] m with
      | error e1 =>
        rw [hL, inferPisE.k_infer_pis_leaf.none] at hF; cases hF
        have hc' := CoreSpecE.of_callE (s₀ := ⟨m, Locals.init []⟩) (inferPisLeaf_anyE p hp hq hil hnv N
          hk hkE F hFN hN ⟨m, Locals.init []⟩ a dn vis fe M eb mode d t k fo lo fvs ws ⟨hS, hmode, heb⟩
          ht hf hftop hB (by omega)) hL
        refine ErrClaim.of_run_eq' (fun ce h => ?_) hc'
        by_cases hp0 : peel = 0
        · subst hp0; exact h
        · have ht6 : ¬ t >>> 28 = 6 := fun h => hc ⟨hp0, h⟩
          obtain ⟨p', hp'⟩ : ∃ p', peel.toNat = p' + 1 :=
            ⟨peel.toNat - 1, by
              have : peel.toNat ≠ 0 := fun h' => hp0 (UInt64.toNat_inj.mp (by simpa using h')); omega⟩
          have hlam : ((decE t).tag != ETag.forallE) = true := by
            rw [bne_iff_ne, ne_eq, ← beq_iff_eq, tag_fa_beq t ht]; simp [ht6]
          rw [hp', inferPis]
          simp only [hlam, ↓reduceIte]
          exact h
      | ok q => rw [hL, inferPisE.k_infer_pis_leaf.eq_2] at hF; cases hF

/-- **`infer_pis`' verdicts** from a telescope state (the error half of `inferPis_tel`). -/
theorem inferPis_telE (p : Prog) (hp : InferLeafProg p) (hq : BindProg p) (hb : InferBodyProg p)
    (hil : InstListOK p) (hnv : closedNV p L.Checker.nvFns = true) (hcap : BStkCap)
    (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d peel t k fo lo : Word) (fvs : Array EIdx) (ws : Array Word) (m₀ : Mem)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ht : HW t) (hf : SpineR s₀.mem fo k fvs)
    (htop : spTop s₀.mem = fo + k) (hB : BStkR s₀.mem lo k ws) (hbt : bTop s₀.mem = lo + k)
    (hdk : d.toNat + k.toNat + peel.toNat < 2 ^ 64)
    (hb0 : ∀ j, j < fo → spW s₀.mem j = spW m₀ j) (hsz : (s₀.mem.arr64 SPN).size = (m₀.arr64 SPN).size)
    (hbb0 : ∀ j, j < lo → rdW (s₀.mem.arr64 BSTK) j = rdW (m₀.arr64 BSTK) j)
    (hbsz0 : (s₀.mem.arr64 BSTK).size = (m₀.arr64 BSTK).size) (hpg0 : PoolGrew m₀ s₀.mem) :
    CoreSpecE p (n + 1) "infer_pis" [mode, vis, d, peel, t, k, fo, lo]
      (inferPis (coreKnot (decMode mode) fe id F) fe d.toNat peel.toNat (decE t) k.toNat fvs
        (ws.map decI)) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (inferPis_specE p hq.pis (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d peel t k fo lo) hc0 (Err.code_ne_of_cls hk0)
  rw [inferPisE.eq_2] at hW
  exact pisFullE_ref p hp hq hb hil hnv hcap n hk hkE F hF hn dn vis fe mode d fo lo eb hs.mode4
    hs.eb_mode m₀ (n + 1) (Nat.le_refl _) s₀.mem a₀ M peel t k 0 0 fvs ws hs.rel ht hf htop hB hbt hdk
    hb0 hsz hbb0 hbsz0 hpg0 er hk0 hW

/-! ## `infer_lam`, `infer_forall` -/

l_model inferLam_specE (p : Prog) (hf : p.lookup "infer_lam" = some inferLamL)
  fns [hf ↦ inferLamE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 simp [tierW, idxW] errors

l_model inferForall_specE (p : Prog) (hf : p.lookup "infer_forall" = some inferForallL)
  fns [hf ↦ inferForallE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 simp [tierW, idxW] errors

theorem tPush_zero (m : Mem) (so lo fv x : Word) :
    (((m.set64 SPN so fv).set64 BSTK lo x).set64 CTL 136 (so + 1)).set64 CTL 137 (lo + 1) =
      tPush m so lo 0 fv x := by
  simp [tPush]

theorem callE_zero_cls {p : Prog} {f : FnName} {vs : List Word} {m : Mem} {e : Err}
    (h : callE p 0 f vs m = .error e) : e.cls = 0 := by
  obtain ⟨e', he', h0⟩ := callE_zero p f vs m
  rw [h] at he'; cases he'; exact h0

/-- **`infer_lam`'s verdicts**: the domain's type (the `infer` and `whnf` slots), a domain type
that is no sort rejects, the telescope's (`inferLams_telE`). -/
theorem inferLam_refinesE (p : Prog) (hp : InferLeafProg p) (hq : BindProg p) (hb : InferBodyProg p)
    (hil : InstListOK p) (hnv : closedNV p L.Checker.nvFns = true) (hcap : BStkCap)
    (n : Nat) (hk : KnotUpTo p n) (hkE : KnotUpToE p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d ty body : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hty : HW ty) (hbody : HW body) :
    CoreSpecE p (n + 1) "infer_lam" [mode, vis, d, ty, body]
      (inferLam (coreKnot (decMode mode) fe id F) d.toNat (decE ty) (decE body)) s₀ a₀ := by
  refine CoreSpecE.of_runs fun er hc0 => ?_
  by_cases hk0 : er.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hW := triple_of_callE_err (inferLam_specE p hq.lam (n + 1) ⟨s₀.mem, Locals.init []⟩
    mode vis d ty body) hc0 (Err.code_ne_of_cls hk0)
  rw [inferLamE.eq_2] at hW
  split at hW
  · exact absurd hW (fun h => cls_abort0 hk0 (Except.error.inj h))
  rename_i hd
  have hd63 : d.toNat < 2 ^ 63 := by
    have : d >>> 63 = 0 := by simpa using hd
    have h2 := congrArg UInt64.toNat this
    rw [UInt64.toNat_shiftRight] at h2
    simp [Nat.shiftRight_eq_div_pow] at h2
    have := d.toNat_lt
    omega
  have hS := hs.rel
  have hK := hk n (Nat.le_refl _)
  have hKE := hkE n (Nat.le_refl _)
  simp only [inferLam]
  cases h1 : callE p n "infer" [mode, vis, d, ty] s₀.mem with
  | error e1 =>
    rw [h1, inferLamE.k_infer.none] at hW; cases hW
    exact ErrClaim.bind_left (CoreSpecE.of_callE (hKE.infer F s₀ a₀ dn vis fe M eb mode d ty hF hn hs hty) h1)
  | ok q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [h1, inferLamE.k_infer.eq_2] at hW
  have h₁ := CoreSpec.of_callW (hK.infer F s₀ a₀ dn vis fe M eb mode d ty hF hn hs hty) (callW_of_callE h1)
  obtain ⟨M₁, hS₁, hK₁, hSt₁⟩ := h₁.2.1
  refine ErrClaim.bind_ref h₁ ?_
  cases h2 : callE p n "whnf" [mode, vis, d, r₁.headD 0] m₁ with
  | error e2 =>
    rw [h2, inferLamE.k_whnf.none] at hW; cases hW
    exact ErrClaim.bind_left (CoreSpecE.of_callE (s₀ := ⟨m₁, Locals.init []⟩) (hKE.whnf F _ _ dn vis fe
      M₁ eb mode d (r₁.headD 0) hF hn ⟨hS₁, hs.mode4, hs.eb_mode⟩ h₁.2.2.2) h2)
  | ok q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [h2, inferLamE.k_whnf.eq_2] at hW
  have h₂ := CoreSpec.of_callW (hK.whnf F ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode d (r₁.headD 0)
    hF hn ⟨hS₁, hs.mode4, hs.eb_mode⟩ h₁.2.2.2) (callW_of_callE h2)
  obtain ⟨M₂, hS₂, hK₂, hSt₂⟩ := h₂.2.1
  refine ErrClaim.bind_ref h₂ ?_
  by_cases g1 : r₂.headD 0 >>> 28 ≠ 2
  · rw [if_pos g1] at hW; cases hW
    simp only [show decH r₂ = decE (r₂.headD 0) from rfl, tag_sort_ne _ h₂.2.2.2 g1,
      Bool.false_eq_true, ↓reduceIte]
    exact ErrClaim.fail _ _ rfl
  rw [if_neg g1] at hW
  have g1' : r₂.headD 0 >>> 28 = 2 := by simpa using g1
  simp only [show decH r₂ = decE (r₂.headD 0) from rfl, tag_sort_beq _ h₂.2.2.2 g1', ↓reduceIte,
    internFVarE]
  cases h3 : callE p n "intern_fvar" [d, ty] m₂ with
  | error e3 =>
    rw [h3, inferLamE.k_intern_fvar.none] at hW; cases hW
    exact ErrClaim.of_callE_nv hnv (inferArmsE_nv "intern_fvar" (by simp)) h3
  | ok q =>
  obtain ⟨r₃, m₃⟩ := q
  rw [h3, inferLamE.k_intern_fvar.eq_2] at hW
  obtain ⟨s₃, hs₃, -, hfv⟩ := triple_of_callW (s₀ := ⟨m₂, Locals.init []⟩)
    (internFVar_spec p hb.fvf hb.fvp hb.fvi n _ d ty) (callW_of_callE h3)
  rw [hs₃] at hfv
  have h₃ := internFVar_core hS₂ d ty hty r₃ hfv
  obtain ⟨M₃, hS₃, hK₃, hSt₃⟩ := h₃.2.1
  have hrw3 := h₃.2.2.2
  refine ErrClaim.bind_ref h₃ ?_
  split at hW
  · exact absurd hW (fun h => cls_abort0 hk0 (Except.error.inj h))
  rename_i g2a
  split at hW
  · exact absurd hW (fun h => cls_abort0 hk0 (Except.error.inj h))
  rename_i g2b
  rw [tPush_zero] at hW
  obtain ⟨so, hso⟩ : ∃ so, so = rdW (m₃.arr64 CTL) 136 := ⟨_, rfl⟩
  obtain ⟨lo, hlo⟩ : ∃ lo, lo = rdW (m₃.arr64 CTL) 137 := ⟨_, rfl⟩
  rw [← hso, ← hlo] at hW; rw [← hso] at g2a; rw [← hlo] at g2b
  have g2 : tPushOK m₃ so lo 0 := tPushOK_of hS₃ (by simpa using g2a) (by simpa using g2b)
  have hcp := hcap _ _ _ _ _ _ _ hS₃
  have hsoS : so.toNat ≤ (m₃.arr64 SPN).size := by
    have := g2.2.2.1; simp at this; omega
  have hloS : lo.toNat ≤ (m₃.arr64 BSTK).size := by
    have := g2.2.2.2.1; simp at this; omega
  obtain ⟨hS', hf', htop', hB', hbt', hb', hsz', hbszT, hbbT, hpgT⟩ := tPush_step (m₀ := m₃)
    (fvs := #[]) (ws := #[]) hS₃ hcp (SpineR.empty _ _ hsoS) (BStkR.empty _ _ hloS) (fun _ _ => rfl) rfl
    g2 hrw3
  have e01 : (0 : Word) + 1 = 1 := rfl
  rw [e01] at hf' htop' hB' hbt'
  cases h4 : callE p n "infer_lams" [mode, vis, d, 16777216, body, 1, so, lo]
      (tPush m₃ so lo 0 (r₃.headD 0) ty) with
  | ok q => rw [h4, inferLamE.k_infer_lams.eq_2] at hW; cases hW
  | error e4 =>
  rw [h4, inferLamE.k_infer_lams.none] at hW; cases hW
  cases n with
  | zero => exact absurd (callE_zero_cls h4) hk0
  | succ n' =>
  have hc := CoreSpecE.of_callE (s₀ := ⟨tPush m₃ so lo 0 (r₃.headD 0) ty, Locals.init []⟩)
    (inferLams_telE p hp hq hb hil hnv hcap n' (hk.mono (by omega)) (hkE.mono (by omega)) F (by omega)
      (by omega) _ _ dn vis fe M₃ eb mode d 16777216 body 1 so lo _ _ m₃ ⟨hS', hs.mode4, hs.eb_mode⟩
      hbody hf' htop' hB' hbt' (by intro i hi; simp at hi; subst hi; simpa using hty) (by simp; omega)
      hb' hsz' hbbT hbszT hpgT) h4
  have hpf : (16777216 : Word).toNat = peelFuel := rfl
  have ha2 : ((#[] : Array Word).push ty).map decE = #[decE ty] := by simp
  rw [hpf, ha2] at hc
  exact hc

end L.Arena
