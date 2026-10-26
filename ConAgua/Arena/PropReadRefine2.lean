import ConAgua.Arena.PropReadRefine
import ConAgua.Arena.InferLeaves
import ConAgua.Arena.DefEqStuckShape

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
    {ci : IConstantInfo} (h : decCI a dn q.toNat = some ci) (hab : ArrExt a b)
    (hsz : b.size < 2 ^ 63) (h1 : rdW b q = 1) :
    ∃ cv hint, ci = .defnInfo cv (decE (rdW b (q + 5))) hint ∧ HW (rdW b (q + 5)) := by
  cases hq : a[q.toNat]? with
  | none => simp [decCI, nat?, hq] at h
  | some w =>
  have hrd : rdW b q = w := by
    have := rdW_ext hab hsz (k := 0) (by decide) (by simpa using hq); simpa using this
  rw [hrd] at h1; subst h1
  simp only [decCI, nat?, hq, Option.map_some, Option.bind_eq_bind, Option.bind_some,
    show UInt64.toNat 1 = 1 from rfl, Option.bind_eq_some_iff] at h
  obtain ⟨cv, -, v, hv, hint, -, hc⟩ := h
  cases hc
  obtain ⟨w5, hw5, hl5, rfl⟩ := hd?_eq hv
  have h5 : rdW b (q + 5) = w5 := rdW_ext hab hsz (k := 5) (by decide) hw5
  exact ⟨cv, hint, by rw [h5, decE_eq], by rw [h5]; exact hl5⟩

/-- A decoded record whose kind word is not `1` is not a definition. -/
theorem decCI_not_defn {a b : Array Word} {dn : NIdx → Option ConLeche.Name} {q : Word}
    {ci : IConstantInfo} (h : decCI a dn q.toNat = some ci) (hab : ArrExt a b)
    (hsz : b.size < 2 ^ 63) (h1 : rdW b q ≠ 1) : ∀ cv v hint, ci ≠ .defnInfo cv v hint :=
  (decCI_defn h hab hsz).2 h1

/-- A run of `env_find`: the memory unchanged, the twin's lookup decoded. -/
theorem pr_envFind {p : Prog} (hp : PropReadProg p) {n : Nat} {dn : NIdx → Option ConLeche.Name}
    {m m' : Mem} {vis : Word} {fe : IFEnv} (hE : EnvR dn m vis fe) {k : Word} (hk : HW k)
    {r : List Word} (hc : callW p n "env_find" [k, vis] m = some (r, m')) :
    m' = m ∧ fe.find? (decI k) = decFound dn m (r.headD 0) (r.tail.headD 0) ∧
      (r.headD 0 ≠ 0 → ∃ ci, decCI (erecP m) dn (r.tail.headD 0).toNat = some ci) := by
  obtain ⟨t₂, ht₂, hm₂, -, hfind⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (envFind_refines p (hp.get "env_ix") (hp.get "env_row_get") (hp.get "env_find") n ⟨m, Locals.init []⟩ vis k hE hk) hc
  obtain ⟨t₂', ht₂', hm₂', -, hfound⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (envFind_found p (hp.get "env_ix") (hp.get "env_row_get") (hp.get "env_find") n ⟨m, Locals.init []⟩ vis k hk) hc
  refine ⟨by rw [← ht₂]; exact hm₂, hfind, fun h0 => ?_⟩
  obtain ⟨htag, hrow, hq⟩ := hfound h0
  obtain ⟨ci, hci⟩ := hE.found_some k hk htag hrow
  exact ⟨ci, by rw [hq]; exact hci⟩

/-- The head name of a `const` handle (the store's projection). -/
theorem pr_viewConstName (m : Mem) (a : AState) (hR : ArenaR m a) (h : Word) (hh : h.toNat < 2 ^ 32)
    (hv : viewOK m h CONST) (hg : h >>> 28 = 3) :
    a.store.viewConstName (decE h) = some (decI (tfld m CONST (tierW h) (idxW h) 0)) := by
  obtain ⟨k, hk, hn, hu⟩ := node_of m a h constCS CeRecRel (·.consts) _ hR.const hv.2
  have hfl := ConsR.flag hR.app
  have e : a.store.viewConstName (decE h) =
      ((if tierW h = 0 then a.store.pers else a.store.scr).consts.node? (idxW h).toNat).map
        (fun r => r.n) := by
    unfold EStore.viewConstName EStore.persGetConstName
    rw [decE_pers h hh]
    by_cases ht : tierW h = 0
    · simp [ht, ETables.getConstName, decE_idx h]
    · have hon : a.store.scratchOn = true := by
        rw [← hfl]; simp only [bne_iff_ne, ne_eq]; exact fun h1 => hv.1 ⟨ht, h1⟩
      simp [ht, hon, ETables.getConstName, decE_idx h]
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
  cases n with
  | zero => rw [callW_zero] at hc; cases hc
  | succ n =>
  obtain ⟨t, ht, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (unwrapStep_spec p hp n ⟨m, Locals.init []⟩ vis f e) hc
  rw [ht] at hW
  generalize r.headD 0 = fl at hW ⊢
  generalize r.tail.headD 0 = e' at hW ⊢
  have hR := hS.arena.1
  unfold uwsW at hW
  rcases hA : acaW m e f with _ | ⟨cnt, hh⟩ <;> rw [hA] at hW
  · cases hW
  simp only at hW
  obtain ⟨hgaf, -, hhh, -⟩ := acaW_ok hR he hA
  by_cases h3 : hh >>> 28 = 3
  rotate_left
  · simp only [h3, ne_eq, not_false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, -, rfl⟩ := hW
    refine ⟨RdAfter.refl hS, fun h => absurd rfl h, fun j => ?_⟩
    have ht : ((decE hh).tag == ETag.const) = false := by
      rw [tag_beq_w hh hhh 3 (by decide) ETag.const rfl 3 rfl]; simp [h3]
    simp only [unwrapIdDefs, StateT.run_bind, hgaf, except_ok_bind, ht, Bool.false_eq_true,
      ↓reduceIte]
    rfl
  simp only [h3, ne_eq, not_true_eq_false, ↓reduceIte] at hW
  by_cases hv1 : tierW hh ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · simp [hv1] at hW
  by_cases hv2 : tcnt m CONST (tierW hh) ≤ idxW hh
  · simp [hv1, hv2] at hW
  simp only [hv1, hv2, ↓reduceIte] at hW
  have hvo : viewOK m hh CONST := ⟨hv1, UInt64.not_le.mp hv2⟩
  have hvn := pr_viewConstName m a hR hh hhh hvo h3
  have hcw := (L.Ind.view_const_f m a hR hh hhh hvo h3).2.1
  generalize tfld m CONST (tierW hh) (idxW hh) 0 = cn at hvn hcw hW
  have htc : ((decE hh).tag == ETag.const) = true := by
    rw [tag_beq_w hh hhh 3 (by decide) ETag.const rfl 3 rfl]; simp [h3]
  have hpre : ∀ j : Nat, (unwrapIdDefs fe f.toNat (j + 1) (decE e)).run a =
      (match fe.find? (decI cn) with
        | some (.defnInfo _ v _) => do
          match ← lamProj? f.toNat 0 v with
          | some (k, i) => do
            let args ← getAppArgs f.toNat (decE e)
            if k ≤ args.length && args.length == k then
              unwrapIdDefs fe f.toNat j (args.getD (k - 1 - i) (decE e))
            else pure (decE e)
          | none => pure (decE e)
        | _ => pure (decE e)).run a := by
    intro j
    simp only [unwrapIdDefs, StateT.run_bind, hgaf, except_ok_bind, htc, ↓reduceIte,
      show ∀ x, (viewConstName x).run a = .ok (a.store.viewConstName x, a) from fun _ => rfl, hvn]
    rfl
  -- `env_find`
  rcases hc2 : callW p n "env_find" [cn, vis] m with _ | ⟨r₂, m₂⟩ <;> rw [hc2] at hW
  · cases hW
  obtain ⟨rfl, hfind, hfound⟩ := pr_envFind hp hS.env hcw hc2
  simp only [uwsK1] at hW
  by_cases h0 : r₂.headD 0 = 0
  · simp only [h0, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, -, rfl⟩ := hW
    have hnone : fe.find? (decI cn) = none := by rw [hfind]; simp only [decFound, h0, ↓reduceIte]
    refine ⟨RdAfter.refl hS, fun h => absurd rfl h, fun j => ?_⟩
    rw [hpre, hnone]; rfl
  obtain ⟨ci, hci⟩ := hfound h0
  have hfind' := find_of_found hfind h0 hci
  simp only [h0, ↓reduceIte] at hW
  by_cases h1 : rdW (m₂.arr64 EREC) (r₂.tail.headD 0) = 1
  rotate_left
  · simp only [h1, ne_eq, not_false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, -, rfl⟩ := hW
    have hnd := decCI_not_defn hci (erecP_ext _) hS.erec h1
    refine ⟨RdAfter.refl hS, fun h => absurd rfl h, fun j => ?_⟩
    rw [hpre, hfind']
    rcases ci with _ | ⟨cv, v, hint⟩ | _ | _ | _ | _ | _
    all_goals first | rfl | exact absurd rfl (hnd cv v hint)
  simp only [h1, ne_eq, not_true_eq_false, ↓reduceIte] at hW
  obtain ⟨cv, hint, hci_eq, hv5⟩ := decCI_defnV hci (erecP_ext _) hS.erec h1
  generalize rdW (m₂.arr64 EREC) (r₂.tail.headD 0 + 5) = vw at hci_eq hv5 hW
  rcases hlp : lamProjW m₂ f 0 vw with _ | ⟨lf, k, jj⟩ <;> rw [hlp] at hW
  · cases hW
  simp only at hW
  have hcwf : coreWalkFuel < 2 ^ 64 := by simp [coreWalkFuel]
  obtain ⟨hlrun, -, hlb⟩ := lamProjW_ok hR hv5 (by simp; omega) hlp
  simp only [UInt64.toNat_zero] at hlrun
  have hpre2 : ∀ j : Nat, (unwrapIdDefs fe f.toNat (j + 1) (decE e)).run a =
      (match (if lf = 0 then none else some (k.toNat, jj.toNat) : Option (Nat × Nat)) with
        | some (k, i) => do
          let args ← getAppArgs f.toNat (decE e)
          if k ≤ args.length && args.length == k then
            unwrapIdDefs fe f.toNat j (args.getD (k - 1 - i) (decE e))
          else pure (decE e)
        | none => pure (decE e)).run a := by
    intro j
    rw [hpre, hfind', hci_eq]
    simp only [StateT.run_bind, hlrun, except_ok_bind]
  by_cases hl0 : lf = 0
  · simp only [hl0, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, -, rfl⟩ := hW
    refine ⟨RdAfter.refl hS, fun h => absurd rfl h, fun j => ?_⟩
    rw [hpre2]; simp only [hl0, ↓reduceIte]; rfl
  simp only [hl0, ↓reduceIte] at hW
  obtain ⟨hjk, -⟩ := hlb hl0
  -- `get_app_args`
  rcases hc3 : callW p n "get_app_args" [e] m₂ with _ | ⟨r₃, m₃⟩ <;> rw [hc3] at hW
  · cases hW
  obtain ⟨t₃, ht₃, -, hf3, hg3, hao, -, xs, hargs, hsp⟩ := triple_of_callW (s₀ := ⟨m₂, Locals.init []⟩)
    (getAppArgs_refines' p (hp.get "get_app_args") (hp.get "app_count") (hp.get "app_fill") n ⟨m₂, Locals.init []⟩ a hR e he hS.spn) hc3
  rw [ht₃] at hf3 hg3 hsp
  simp only at hao
  have hargs' : (getAppArgs f.toNat (decE e)).run a = .ok (xs, a) := by
    rw [← acaW_args hR he hA coreWalkFuel hf]; exact hargs
  simp only [uwsK2] at hW
  have h136 : (136 : Word).toNat < (m₃.arr64 CTL).size := by
    by_cases h : (136 : Word).toNat < (m₃.arr64 CTL).size
    · exact h
    · simp only [h, ↓reduceIte] at hW; cases hW
  simp only [h136, ↓reduceIte] at hW
  obtain ⟨hS', hK'⟩ := hS.restoreTop hf3 hg3 h136
  have hfr : MemFrame [SPN, LH] [136, 192] m₂ (m₃.set64 CTL 136 (rdW (m₂.arr64 CTL) 136)) :=
    (hf3.mono (by simp) (by simp)).trans ((MemFrame.setCtl m₃ 136 _).mono (by simp) (by simp))
  have hRd : RdAfter dn m₂ (m₃.set64 CTL 136 (rdW (m₂.arr64 CTL) 136)) a a vis fe M eb :=
    ⟨hS', hK', hfr, rfl⟩
  have hlen : xs.length = (r₃.tail.headD 0).toNat := by
    have := hsp.size; simpa using this
  have hpre3 : ∀ j : Nat, (unwrapIdDefs fe f.toNat (j + 1) (decE e)).run a =
      (if k.toNat ≤ xs.length && xs.length == k.toNat then
        unwrapIdDefs fe f.toNat j (xs.getD (k.toNat - 1 - jj.toNat) (decE e))
      else pure (decE e)).run a := by
    intro j
    rw [hpre2]; simp only [hl0, ↓reduceIte, StateT.run_bind, hargs', except_ok_bind]
  by_cases hk : r₃.tail.headD 0 = k
  rotate_left
  · simp only [hk, ne_eq, not_false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, -, rfl⟩ := hW
    refine ⟨hRd, fun h => absurd rfl h, fun j => ?_⟩
    rw [hpre3]
    have : (k.toNat ≤ xs.length && xs.length == k.toNat) = false := by
      rw [hlen]; simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne]
      right; intro h; exact hk (UInt64.toNat_inj.mp h)
    rw [this]; rfl
  simp only [hk, ne_eq, not_true_eq_false, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨rfl, rfl, rfl⟩ := hW
  have hjk' := hjk
  have hk0 : k ≠ 0 := by intro h; subst h; simp at hjk
  have e1 : (k - 1).toNat = k.toNat - 1 := pr_word_sub1 k hk0
  have e2 : (k - 1 - jj).toNat = k.toNat - 1 - jj.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, e1]; omega), e1]
  have hidx : (k.toNat - 1 - jj.toNat) < xs.toArray.size := by
    simp only [List.size_toArray]; rw [hlen, hk]; omega
  have hw : r₃.headD 0 + (k - 1 - jj) = r₃.headD 0 + (k.toNat - 1 - jj.toNat).toUInt64 := by
    congr 1
    apply UInt64.toNat_inj.mp
    have := k.toNat_lt
    rw [e2]; simp; omega
  have hget := hsp.get _ hidx
  have hlt := hsp.lt _ (by simp only [List.size_toArray] at hidx; rw [← hlen]; exact hidx)
  refine ⟨hRd, fun _ => ?_, fun j => ?_⟩
  · simp only [spW] at hlt; rw [hw]; exact hlt
  · rw [hpre3]
    have : (k.toNat ≤ xs.length && xs.length == k.toNat) = true := by
      rw [hlen, hk]; simp
    rw [this]
    simp only [show (1 : Word) = 0 ↔ False by decide, ↓reduceIte, if_false]
    congr 2
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hidx),
      Option.getD_some]
    simp only [spW] at hget
    rw [hw]
    simpa using hget

end uws

/-! ## `unwrap_id_defs`, `peel_pis_w` -/

section uid
variable {p : Prog} (hp : PropReadProg p)
include hp

/-- **`unwrap_id_defs` refines `unwrapIdDefs`.** -/
@[refines ConRon.Arena.unwrapIdDefs]
theorem uid_ok : ∀ (n : Nat) {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState}
    {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb)
    {f k e : Word} (hf : f.toNat ≤ coreWalkFuel) (he : HW e) {r : List Word}
    (hc : callW p n "unwrap_id_defs" [vis, f, k, e] m = some (r, m')),
    (unwrapIdDefs fe f.toNat k.toNat (decE e)).run a = .ok (decE (r.headD 0), a) ∧
      RdAfter dn m m' a a vis fe M eb ∧ HW (r.headD 0) := by
  intro n
  induction n with
  | zero => intro dn m m' a vis fe M eb hS f k e hf he r hc; rw [callW_zero] at hc; cases hc
  | succ n ih =>
  intro dn m m' a vis fe M eb hS f k e hf he r hc
  obtain ⟨t, ht, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (unwrapIdDefs_spec p hp n ⟨m, Locals.init []⟩ vis f k e) hc
  rw [ht] at hW
  generalize r.headD 0 = x at hW ⊢
  unfold uidW at hW
  by_cases hk : k = 0
  · subst hk
    simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl⟩ := hW
    exact ⟨by simp [unwrapIdDefs]; rfl, RdAfter.refl hS, he⟩
  simp only [hk, ↓reduceIte] at hW
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (pr_word_ne0 k hk)
  rcases hc1 : callW p n "unwrap_step" [vis, f, e] m with _ | ⟨r₁, m₁⟩ <;> rw [hc1] at hW
  · cases hW
  obtain ⟨hRd₁, hb₁, hrun₁⟩ := uws_ok hp hS hf he hc1
  simp only [uidK] at hW
  by_cases h0 : r₁.headD 0 = 0
  · simp only [h0, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl⟩ := hW
    refine ⟨by rw [hj, hrun₁ j, if_pos h0], hRd₁, he⟩
  simp only [h0, ↓reduceIte] at hW
  rcases hc2 : callW p n "unwrap_id_defs" [vis, f, k - 1, r₁.tail.headD 0] m₁ with _ | ⟨r₂, m₂⟩
  · rw [call1W, hc2] at hW; cases hW
  rw [call1W_some _ _ _ _ _ _ _ hc2] at hW
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  obtain ⟨hrun₂, hRd₂, hb₂⟩ := ih hRd₁.rel hf (hb₁ h0) hc2
  refine ⟨?_, hRd₁.trans hRd₂, hb₂⟩
  rw [hj, hrun₁ j]
  simp only [h0, ↓reduceIte]
  rw [show j = (k - 1).toNat by rw [pr_word_sub1 k hk]; omega]
  exact hrun₂

/-- **`peel_pis_w` refines `peelPisW`.** -/
@[refines ConRon.Arena.peelPisW]
theorem ppw_ok : ∀ (n : Nat) {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState}
    {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb)
    {f k e : Word} (hf : f.toNat ≤ coreWalkFuel) (he : HW e) {r : List Word}
    (hc : callW p n "peel_pis_w" [vis, f, k, e] m = some (r, m')),
    (ConRon.Arena.peelPisW fe f.toNat k.toNat (decE e)).run a =
        .ok (decOpt (r.headD 0) (r.tail.headD 0), a) ∧
      RdAfter dn m m' a a vis fe M eb ∧ (r.headD 0 ≠ 0 → HW (r.tail.headD 0)) := by
  intro n
  induction n with
  | zero => intro dn m m' a vis fe M eb hS f k e hf he r hc; rw [callW_zero] at hc; cases hc
  | succ n ih =>
  intro dn m m' a vis fe M eb hS f k e hf he r hc
  obtain ⟨t, ht, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (peelPisW_spec p hp n ⟨m, Locals.init []⟩ vis f k e) hc
  rw [ht] at hW
  generalize r.headD 0 = x at hW ⊢
  generalize r.tail.headD 0 = y at hW ⊢
  -- the step at a `∀` node `u`, from memory `m₁`
  have step : ∀ {m₁ : Mem} (u : Word), RdAfter dn m m₁ a a vis fe M eb → HW u → u >>> 28 = 6 →
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
    have hvb := viewBind_forall m₁ a hS₁.arena.1 u hu ⟨hv1, hvo⟩ h6
    have h1 := (view_forall m₁ a hS₁.arena.1 u hu ⟨hv1, hvo⟩ h6).2.2
    rcases hc2 : callW p n "peel_pis_w" [vis, f, k - 1,
        tfld m₁ FORALL (tierW u) (idxW u) 1] m₁ with _ | ⟨r₂, m₂⟩
    · rw [hc2] at hK; cases hK
    rw [hc2] at hK
    simp only [t2W, Option.some.injEq, Prod.mk.injEq] at hK
    obtain ⟨rfl, rfl, rfl⟩ := hK
    obtain ⟨hrun₂, hRd₂, hb₂⟩ := ih hS₁ hf h1 hc2
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
    obtain ⟨hrun₁, hRd₁, hb₁⟩ := uid_ok hp n hS hf he hc1
    simp only [show (4 : Word).toNat = 4 from rfl] at hrun₁
    refine ⟨?_, hRd₁, fun _ => hb₁⟩
    simp only [UInt64.toNat_zero, ConRon.Arena.peelPisW, StateT.run_bind, hrun₁, except_ok_bind]
    rfl
  simp only [hk, ↓reduceIte] at hW
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (pr_word_ne0 k hk)
  have hj' : j = k.toNat - 1 := by omega
  by_cases h6 : e >>> 28 = 6
  · simp only [h6, ne_eq, not_true_eq_false, ↓reduceIte] at hW
    obtain ⟨hrun, hRd, hb⟩ := step e (RdAfter.refl hS) he h6 hk hW
    refine ⟨?_, hRd, hb⟩
    have ht : ((decE e).tag == ETag.forallE) = true := by
      rw [tag_beq_w e he 6 (by decide) ETag.forallE rfl 6 rfl]; simp [h6]
    rw [hj, ConRon.Arena.peelPisW, hj']
    simp only [ht, ↓reduceIte]
    exact hrun
  simp only [h6, ne_eq, not_false_eq_true, ↓reduceIte] at hW
  have ht : ((decE e).tag == ETag.forallE) = false := by
    rw [tag_beq_w e he 6 (by decide) ETag.forallE rfl 6 rfl]; simp [h6]
  rcases hc1 : callW p n "unwrap_id_defs" [vis, f, 4, e] m with _ | ⟨r₁, m₁⟩
  · rw [call1W, hc1] at hW; cases hW
  rw [call1W_some _ _ _ _ _ _ _ hc1] at hW
  obtain ⟨hrun₁, hRd₁, hb₁⟩ := uid_ok hp n hS hf he hc1
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
    simp only [ht, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, show (4 : Word).toNat = 4 from rfl,
      hrun₁, except_ok_bind, Nat.succ_sub_one]
    rfl
  by_cases hu6 : u >>> 28 = 6
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
