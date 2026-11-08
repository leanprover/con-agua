module

public import ConAgua.Arena.PropReadRefine
import ConAgua.Arena.DefEqStuckShape
import ConAgua.Arena.WhnfCoreRefine
import ConRon.Bridge.Grind

@[expose] public section

/-!
# The prop-ness readers: the identity-like wrappers and `peelPisW` (helper `defeq2-prop`)

`unwrap_step` (one δβ step of `unwrapIdDefs`), `unwrap_id_defs` and `peel_pis_w` (both recursive
in L, as in the twin: by induction on the L fuel). Every lemma is about a run (`callW … = some`),
so a caller applies it to its callee's run.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


namespace L.Arena

open ConLeche (Name Level PropWhen)

/-! ## Helpers -/

/-- A decoded definition record: its value is word `q + 5`. -/
theorem decCI_defnV {a b : Array Word} {dn : NIdx → Option ConLeche.Name} {q : Word}
    {ci : IConstantInfo} (h : decCI (aread a) q.toNat = some ci) (hab : ArrExt (aread a) (aread b))
    (hsz : b.size < 2 ^ 63) (h1 : rdW b q = 1) :
    ∃ cv hint, ci = .defnInfo cv (decE (rdW b (q + 5))) hint ∧ HW (rdW b (q + 5)) := by
  sorry

/-- A decoded record whose kind word is not `1` is not a definition. -/
theorem decCI_not_defn {a b : Array Word} {dn : NIdx → Option ConLeche.Name} {q : Word}
    {ci : IConstantInfo} (h : decCI (aread a) q.toNat = some ci) (hab : ArrExt (aread a) (aread b))
    (hsz : b.size < 2 ^ 63) (h1 : rdW b q ≠ 1) : ∀ cv v hint, ci ≠ .defnInfo cv v hint := by
  sorry

/-- A run of `env_find`: the memory unchanged, the twin's lookup decoded. -/
theorem pr_envFind {p : Prog} (hp : PropReadProg p) {n : Nat} {dn : NIdx → Option ConLeche.Name}
    {m m' : Mem} {vis : Word} {fe : IFEnv} (hE : EnvR m vis fe) {k : Word} (hk : HW k)
    {r : List Word} (hc : callW p n "env_find" [k, vis] m = some (r, m')) :
    m' = m ∧ fe.find? (decI k) = decFound dn m (r.headD 0) (r.tail.headD 0) ∧
      (r.headD 0 ≠ 0 → ∃ ci, decCI (erecP m) (r.tail.headD 0).toNat = some ci) := by
  sorry

/-- The head name of a `const` handle (the store's projection). -/
theorem pr_viewConstName (m : Mem) (a : AState) (hR : ArenaR m a) (h : Word) (hh : h.toNat < 2 ^ 32)
    (hv : viewOK m h CONST) (_hg : tagW h = 3) :
    a.store.viewConstName (decE h) = some (decI (tfld m CONST (tierW h) (idxW h) 0)) := by
  obtain ⟨k, hk, hn, hu⟩ := node_of m a h constCS CeRecRel (·.consts) _ hR.const hv.2
  have hfl := ConsR.flag hR.app
  have e : a.store.viewConstName (decE h) =
      ((if tierW h = 0 then a.store.pers else a.store.scr).consts.node? (idxW h).toNat).map
        (fun r => r.n) := by
    unfold EStore.viewConstName EStore.persGetConstName
    rw [decE_pers h hh]
    by_cases ht : tierW h = 0
    · simp [ht, ETables.getConstName, decE_idx h (narrow_of_cnt m h hR.const rfl hv.2)]
    · have hon : a.store.scratchOn = true := by
        rw [← hfl]; simp only [bne_iff_ne, ne_eq]; exact fun h1 => hv.1 ⟨ht, h1⟩
      simp [ht, hon, ETables.getConstName, decE_idx h (narrow_of_cnt m h hR.const rfl hv.2)]
  rw [e]; simp only [Tbl.node?, hk, Option.map_some]; rw [hn, decI_word]

/-- `getAppArgs` at the counter of a successful `app_count_at` is `getAppArgs` at any larger one. -/
theorem acaW_args {m : Mem} {a : AState} (hR : ArenaR m a) {e f c h : Word} (he : HW e)
    (hW : acaW m e f = some (c, h)) (F : Nat) (hF : f.toNat ≤ F) :
    (getAppArgs F (decE e)).run a = (getAppArgs f.toNat (decE e)).run a := by
  unfold acaW at hW
  rcases hL : gafLoopW m e f with _ | ⟨e', f'⟩ <;> rw [hL] at hW
  · cases hW
  by_cases hf0 : f' = 0
  · simp [hf0] at hW
  exact gafLoopW_args m a hR _ e f e' f' F (Nat.le_refl _) he hL hf0 hF

/-! ## `unwrap_step` -/

section uws
variable {p : Prog} (hp : PropReadProg p)
include hp

/-- **`unwrap_step` is one step of `unwrapIdDefs`**: `(0, _)` the twin answers `e` itself, `(1, e')`
it goes on at `e'`. -/
theorem uws_ok {n : Nat} {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb) {f e : Word}
    (hf : f.toNat ≤ coreWalkFuel) (he : HW e) {r : List Word}
    (hc : callW p n "unwrap_step" [vis, f, e] m = some (r, m')) :
    RdAfter dn m m' a a vis fe M eb ∧ (r.headD 0 ≠ 0 → HW (r.tail.headD 0)) ∧
      ∀ j : Nat, (unwrapIdDefs fe f.toNat (j + 1) (decE e)).run a =
        if r.headD 0 = 0 then .ok (decE e, a)
        else (unwrapIdDefs fe f.toNat j (decE (r.tail.headD 0))).run a := by
  sorry

end uws

/-! ## `unwrap_id_defs`, `peel_pis_w` -/

section uid
variable {p : Prog} (hp : PropReadProg p)
include hp

/-- **`unwrap_id_defs` refines `unwrapIdDefs`.** -/
@[refines ConRon.Arena.unwrapIdDefs]
theorem uid_ok : ∀ (n : Nat) {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState}
    {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word} (_hS : CoreS dn m a vis fe M eb)
    {f k e : Word} (_hf : f.toNat ≤ coreWalkFuel) (_he : HW e) {r : List Word}
    (_hc : callW p n "unwrap_id_defs" [vis, f, k, e] m = some (r, m')),
    (unwrapIdDefs fe f.toNat k.toNat (decE e)).run a = .ok (decE (r.headD 0), a) ∧
      RdAfter dn m m' a a vis fe M eb ∧ HW (r.headD 0) := by
  intro n
  induction n with
  | zero => intro dn m m' a vis fe M eb _hS f k e _hf _he r _hc; rw [callW_zero] at _hc; cases _hc
  | succ n ih =>
  intro dn m m' a vis fe M eb _hS f k e _hf _he r _hc
  obtain ⟨t, ht, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (unwrapIdDefs_spec p hp n ⟨m, Locals.init []⟩ vis f k e) _hc
  rw [ht] at hW
  generalize r.headD 0 = x at hW ⊢
  unfold uidW at hW
  by_cases hk : k = 0
  · subst hk
    simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl⟩ := hW
    exact ⟨by simp [unwrapIdDefs]; rfl, RdAfter.refl _hS, _he⟩
  simp only [hk, ↓reduceIte] at hW
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (pr_word_ne0 k hk)
  rcases hc1 : callW p n "unwrap_step" [vis, f, e] m with _ | ⟨r₁, m₁⟩ <;> rw [hc1] at hW
  · cases hW
  obtain ⟨hRd₁, hb₁, hrun₁⟩ := uws_ok hp _hS _hf _he hc1
  simp only [uidK] at hW
  by_cases h0 : r₁.headD 0 = 0
  · simp only [h0, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl⟩ := hW
    refine ⟨by rw [hj, hrun₁ j, ite_eq_left h0], hRd₁, _he⟩
  simp only [h0, ↓reduceIte] at hW
  rcases hc2 : callW p n "unwrap_id_defs" [vis, f, k - 1, r₁.tail.headD 0] m₁ with _ | ⟨r₂, m₂⟩
  · rw [call1W, hc2] at hW; cases hW
  rw [call1W_some _ _ _ _ _ _ _ hc2] at hW
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  obtain ⟨hrun₂, hRd₂, hb₂⟩ := ih hRd₁.rel _hf (hb₁ h0) hc2
  refine ⟨?_, hRd₁.trans hRd₂, hb₂⟩
  rw [hj, hrun₁ j]
  simp only [h0, ↓reduceIte]
  rw [show j = (k - 1).toNat by rw [pr_word_sub1 k hk]; omega]
  exact hrun₂

/-- **`peel_pis_w` refines `peelPisW`.** -/
@[refines ConRon.Arena.peelPisW]
theorem ppw_ok : ∀ (n : Nat) {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState}
    {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word} (_hS : CoreS dn m a vis fe M eb)
    {f k e : Word} (_hf : f.toNat ≤ coreWalkFuel) (_he : HW e) {r : List Word}
    (_hc : callW p n "peel_pis_w" [vis, f, k, e] m = some (r, m')),
    (ConRon.Arena.peelPisW fe f.toNat k.toNat (decE e)).run a =
        .ok (decOpt (r.headD 0) (r.tail.headD 0), a) ∧
      RdAfter dn m m' a a vis fe M eb ∧ (r.headD 0 ≠ 0 → HW (r.tail.headD 0)) := by
  intro n
  induction n with
  | zero => intro dn m m' a vis fe M eb _hS f k e _hf _he r _hc; rw [callW_zero] at _hc; cases _hc
  | succ n ih =>
  intro dn m m' a vis fe M eb _hS f k e _hf _he r _hc
  obtain ⟨t, ht, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (peelPisW_spec p hp n ⟨m, Locals.init []⟩ vis f k e) _hc
  rw [ht] at hW
  generalize r.headD 0 = x at hW ⊢
  generalize r.tail.headD 0 = y at hW ⊢
  -- the step at a `∀` node `u`, from memory `m₁`
  have step : ∀ {m₁ : Mem} (u : Word), RdAfter dn m m₁ a a vis fe M eb → HW u → tagW u = 6 →
      k ≠ 0 → ppwK2 p n vis f k u m₁ = some (x, y, m') →
      (do match ← viewBind (decE u) with
          | none => failDanglingE
          | some (_, b) => ConRon.Arena.peelPisW fe f.toNat (k.toNat - 1) b : AM (Option EIdx)).run a =
        .ok (decOpt x y, a) ∧ RdAfter dn m m' a a vis fe M eb ∧ (x ≠ 0 → HW y) := by
    intro m₁ u hRd hu h6 hk hK
    have hS₁ := hRd.rel
    unfold ppwK2 at hK
    by_cases hv1 : tierW u ≠ 0 ∧ rdW (m₁.arr64 CTL) 1 = 0
    · simp [hv1] at hK
    by_cases hv2 : tcnt m₁ FORALL (tierW u) ≤ idxW u
    · simp [hv1, hv2] at hK
    simp only [hv1, hv2, ↓reduceIte] at hK
    have hvo : idxW u < tcnt m₁ FORALL (tierW u) := UInt64.not_le.mp hv2
    have hvb := viewBind_forall m₁ a hS₁.arena.base u hu ⟨hv1, hvo⟩ h6
    have h1 := (view_forall m₁ a hS₁.arena.base u hu ⟨hv1, hvo⟩ h6).2.2
    rcases hc2 : callW p n "peel_pis_w" [vis, f, k - 1,
        tfld m₁ FORALL (tierW u) (idxW u) 1] m₁ with _ | ⟨r₂, m₂⟩
    · rw [hc2] at hK; cases hK
    rw [hc2] at hK
    simp only [t2W, Option.some.injEq, Prod.mk.injEq] at hK
    obtain ⟨rfl, rfl, rfl⟩ := hK
    obtain ⟨hrun₂, hRd₂, hb₂⟩ := ih hS₁ _hf h1 hc2
    refine ⟨?_, hRd.trans hRd₂, hb₂⟩
    rw [pr_word_sub1 k hk] at hrun₂
    simp only [StateT.run_bind, viewBind_run' _ a, hvb, except_ok_bind]
    exact hrun₂
  unfold ppwW at hW
  by_cases hk : k = 0
  · subst hk
    simp only [↓reduceIte] at hW
    rcases hc1 : callW p n "unwrap_id_defs" [vis, f, 4, e] m with _ | ⟨r₁, m₁⟩
    · rw [call1W, hc1] at hW; cases hW
    rw [call1W_some _ _ _ _ _ _ _ hc1] at hW
    simp only [ppwK0, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl, rfl⟩ := hW
    obtain ⟨hrun₁, hRd₁, hb₁⟩ := uid_ok hp n _hS _hf _he hc1
    simp only [show (4 : Word).toNat = 4 from rfl] at hrun₁
    refine ⟨?_, hRd₁, fun _ => hb₁⟩
    simp only [UInt64.toNat_zero, ConRon.Arena.peelPisW, StateT.run_bind, hrun₁, except_ok_bind]
    rfl
  simp only [hk, ↓reduceIte] at hW
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (pr_word_ne0 k hk)
  have hj' : j = k.toNat - 1 := by omega
  by_cases h6 : tagW e = 6
  · simp only [h6, ne_eq, not_true_eq_false, ↓reduceIte] at hW
    obtain ⟨hrun, hRd, hb⟩ := step e (RdAfter.refl _hS) _he h6 hk hW
    refine ⟨?_, hRd, hb⟩
    have ht : ((decE e).tag == ETag.forallE) = true := by
      rw [tag_beq_w e _he 6 (by decide) ETag.forallE rfl 6 rfl]; simp [h6]
    rw [hj, ConRon.Arena.peelPisW, hj']
    simp only [ht, ↓reduceIte]
    exact hrun
  simp only [h6, ne_eq, not_false_eq_true, ↓reduceIte] at hW
  have ht : ((decE e).tag == ETag.forallE) = false := by
    rw [tag_beq_w e _he 6 (by decide) ETag.forallE rfl 6 rfl]; simp [h6]
  rcases hc1 : callW p n "unwrap_id_defs" [vis, f, 4, e] m with _ | ⟨r₁, m₁⟩
  · rw [call1W, hc1] at hW; cases hW
  rw [call1W_some _ _ _ _ _ _ _ hc1] at hW
  obtain ⟨hrun₁, hRd₁, hb₁⟩ := uid_ok hp n _hS _hf _he hc1
  simp only [show (4 : Word).toNat = 4 from rfl] at hrun₁
  simp only [ppwK1] at hW
  generalize r₁.headD 0 = u at hW hrun₁ hb₁
  have hpre : (ConRon.Arena.peelPisW fe f.toNat k.toNat (decE e)).run a =
      (if (decE u).tag == ETag.forallE then
        (do match ← viewBind (decE u) with
          | none => failDanglingE
          | some (_, b) => ConRon.Arena.peelPisW fe f.toNat (k.toNat - 1) b : AM (Option EIdx))
       else pure none).run a := by
    rw [hj, ConRon.Arena.peelPisW, hj']
    simp only [ht, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
      hrun₁, except_ok_bind, Nat.succ_sub_one]
    rfl
  by_cases hu6 : tagW u = 6
  · simp only [hu6, ne_eq, not_true_eq_false, ↓reduceIte] at hW
    obtain ⟨hrun, hRd, hb⟩ := step u hRd₁ hb₁ hu6 hk hW
    have htu : ((decE u).tag == ETag.forallE) = true := by
      rw [tag_beq_w u hb₁ 6 (by decide) ETag.forallE rfl 6 rfl]; simp [hu6]
    refine ⟨?_, hRd, hb⟩
    rw [hpre]; simp only [htu, ↓reduceIte]; exact hrun
  simp only [hu6, ne_eq, not_false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨rfl, rfl, rfl⟩ := hW
  have htu : ((decE u).tag == ETag.forallE) = false := by
    rw [tag_beq_w u hb₁ 6 (by decide) ETag.forallE rfl 6 rfl]; simp [hu6]
  refine ⟨?_, hRd₁, fun h => absurd rfl h⟩
  rw [hpre]; simp only [htu, Bool.false_eq_true, ↓reduceIte]; rfl

end uid

end L.Arena
