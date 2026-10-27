import ConAgua.Arena.PropRead
import ConAgua.Arena.DefEqLeaves
import ConAgua.Arena.GrindAttr
import ConAgua.Census.Attr
import ConAgua.L.GrindAttr

/-!
# The prop-ness readers' loops: models, specs, and the twin's walks (helper `defeq2-prop`)

The five walks over a chain of nodes (`PropRead.lean`): `binder_dom`, `app_count_at`, `lam_proj`,
and the loops of `type_sort_pw` and `proof_pw`. Each has a word-level model (`…W`, `none` where
the L code aborts), a spec (`vcgen` + `finish`), and a lemma that connects the model to the twin's
walk under `ArenaR` (the twin reads only, so its state is unchanged). The fuel words are the
twin's counters (`f.toNat`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

theorem pr_word_sub1 (f : Word) (hf : f ≠ 0) : (f - 1).toNat = f.toNat - 1 := by
  have : f.toNat ≠ 0 := fun h => hf (UInt64.toNat_inj.mp (by simpa using h))
  rw [UInt64.toNat_sub_of_le _ _ (by simp [UInt64.le_iff_toNat_le]; omega)]; simp

theorem pr_word_ne0 (f : Word) (hf : f ≠ 0) : f.toNat ≠ 0 :=
  fun h => hf (UInt64.toNat_inj.mp (by simpa using h))

/-! ## `binder_dom(k, e)` -/

/-- **The model of `binder_dom`**: `(flag, domain)`, `none` where the L code aborts. -/
def bdW (m : Mem) (k e : Word) : Option (Word × Word) :=
  if e >>> 28 ≠ 6 then some (0, 0)
  else if tierW e ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if tcnt m FORALL (tierW e) ≤ idxW e then none
  else if k = 0 then some (1, tfld m FORALL (tierW e) (idxW e) 0)
  else bdW m (k - 1) (tfld m FORALL (tierW e) (idxW e) 1)
termination_by k.toNat
decreasing_by
  have hk0 : k ≠ 0 := by assumption
  have := pr_word_sub1 k hk0
  have := pr_word_ne0 k hk0
  omega

theorem bdW_miss (m : Mem) (k e : Word) (h : e >>> 28 ≠ 6) : bdW m k e = some (0, 0) := by
  rw [bdW]; simp [h]

theorem bdW_hit (m : Mem) (e : Word) (h : e >>> 28 = 6)
    (hv1 : ¬ (tierW e ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0))
    (hv2 : ¬ tcnt m FORALL (tierW e) ≤ idxW e) :
    bdW m 0 e = some (1, tfld m FORALL (tierW e) (idxW e) 0) := by
  rw [bdW]; simp only [h, ne_eq, not_true_eq_false, ↓reduceIte, hv1, hv2]

theorem bdW_step (m : Mem) (k e e' : Word) (h : e >>> 28 = 6) (hk : k ≠ 0)
    (hv1 : ¬ (tierW e ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0))
    (hv2 : ¬ tcnt m FORALL (tierW e) ≤ idxW e)
    (he' : e' = tfld m FORALL (tierW e) (idxW e) 1) :
    bdW m k e = bdW m (k - 1) e' := by
  subst he'; rw [bdW]; simp only [h, ne_eq, not_true_eq_false, ↓reduceIte, hv1, hv2, hk]

grind_pattern [arena_grind] bdW_miss => bdW m k e
grind_pattern [arena_grind] bdW_hit => bdW m 0 e
grind_pattern [arena_grind] bdW_step => bdW m k e, bdW m (k - 1) e'

section bdLoop
variable (p : Prog)

theorem binderDomLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n binderDomLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      (r = .normal → bdW s₀.mem (s₀.loc 0) (s₀.loc 1) = some (0, 0)) ∧
      (∀ v, r = .ret v → bdW s₀.mem (s₀.loc 0) (s₀.loc 1) = some (v.headD 0, v.tail.headD 0)); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := binderDomLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih, evalE_tld, tld, evalE_cnt,
        tcntM, evalE_tierE, evalE_idxE] <;> finish [tierW, idxW]

theorem binderDomLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) binderDomLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r ≠ .brk ∧
      (r = .normal → bdW s₀.mem (s₀.loc 0) (s₀.loc 1) = some (0, 0)) ∧
      (∀ v, r = .ret v → bdW s₀.mem (s₀.loc 0) (s₀.loc 1) = some (v.headD 0, v.tail.headD 0)); ⊤⦄ :=
  Triple.step_exec (binderDomLoop_spec p (n + 1) s₀)

theorem binderDomL_spec (hp : p.lookup "binder_dom" = some binderDomL) (n : Nat) (s₀ : St)
    (k e : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "binder_dom" [k, e]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      bdW s₀.mem k e = some (r.headD 0, r.tail.headD 0); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, binderDomL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalArgs, setLocs, binderDomLoop_step_spec p n] <;> finish [LocEq]

end bdLoop

/-- **The model of `binder_dom` refines `binderDom`** (structural on `k`). -/
@[refines ConRon.Arena.binderDom]
theorem bdW_ok (m : Mem) (a : AState) (hR : ArenaR m a) :
    ∀ (N : Nat) (k e fl v : Word), k.toNat ≤ N → HW e → bdW m k e = some (fl, v) →
      (binderDom k.toNat (decE e)).run a = .ok (decOpt fl v, a) ∧ (fl ≠ 0 → HW v) := by
  intro N
  induction N with
  | zero =>
    intro k e fl v hkN he hL
    have hk0 : k = 0 := UInt64.toNat_inj.mp (by simp; omega)
    subst hk0
    by_cases hc : e >>> 28 = 6
    · have hv1 : ¬ (tierW e ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0) := by
        intro hv; rw [bdW] at hL; simp [hc, hv] at hL
      have hv2 : ¬ tcnt m FORALL (tierW e) ≤ idxW e := by
        intro hv; rw [bdW] at hL; simp [hc, hv1, hv] at hL
      rw [bdW_hit m e hc hv1 hv2] at hL
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hL)
      have hcnt : idxW e < tcnt m FORALL (tierW e) := UInt64.not_le.mp hv2
      have hvb := viewBind_forall m a hR e he ⟨hv1, hcnt⟩ hc
      have h1 := (view_forall m a hR e he ⟨hv1, hcnt⟩ hc).2.1
      refine ⟨?_, fun _ => h1⟩
      simp only [UInt64.toNat_zero, binderDom, (decE_tag_forall e he).mpr hc, beq_self_eq_true,
        ↓reduceIte]
      simp [viewBind_run' _ a, hvb, except_ok_bind, decOpt]
      rfl
    · rw [bdW_miss m 0 e hc] at hL
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hL)
      refine ⟨?_, fun h => absurd rfl h⟩
      have htag : (decE e).tag ≠ ETag.forallE := fun h => hc ((decE_tag_forall e he).mp h)
      simp [binderDom, htag, decOpt]
      rfl
  | succ N ih =>
    intro k e fl v hkN he hL
    by_cases hk0 : k = 0
    · exact ih k e fl v (by subst hk0; simp) he hL
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (pr_word_ne0 k hk0)
    by_cases hc : e >>> 28 = 6
    · have hv1 : ¬ (tierW e ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0) := by
        intro hv; rw [bdW] at hL; simp [hc, hv] at hL
      have hv2 : ¬ tcnt m FORALL (tierW e) ≤ idxW e := by
        intro hv; rw [bdW] at hL; simp [hc, hv1, hv] at hL
      rw [bdW_step m k e _ hc hk0 hv1 hv2 rfl] at hL
      have hkm1 := pr_word_sub1 k hk0
      have hcnt : idxW e < tcnt m FORALL (tierW e) := UInt64.not_le.mp hv2
      have hvb := viewBind_forall m a hR e he ⟨hv1, hcnt⟩ hc
      have h1 := (view_forall m a hR e he ⟨hv1, hcnt⟩ hc).2.2
      obtain ⟨ihr, ihb⟩ := ih _ _ fl v (by rw [hkm1]; omega) h1 hL
      refine ⟨?_, ihb⟩
      rw [hj, binderDom, (decE_tag_forall e he).mpr hc]
      rw [show j = (k - 1).toNat by rw [hkm1]; omega]
      simp [viewBind_run' _ a, hvb, except_ok_bind]
      exact ihr
    · rw [bdW_miss m k e hc] at hL
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hL)
      refine ⟨?_, fun h => absurd rfl h⟩
      have htag : (decE e).tag ≠ ETag.forallE := fun h => hc ((decE_tag_forall e he).mp h)
      rw [hj]
      simp [binderDom, htag, decOpt]
      rfl

/-! ## `app_count_at(e, f)`: `getAppFn f e` and `numArgs f e` -/

/-- **The model of `app_count_at`**: `(count, head)`. -/
def acaW (m : Mem) (e f : Word) : Option (Word × Word) :=
  match gafLoopW m e f with
  | none => none
  | some (e', f') => if f' = 0 then none else some (f - f', e')

section acaLoop
variable (p : Prog)

theorem appCountAtLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n appCountAtLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r = .normal ∧ s'.loc 4 = s₀.loc 4 ∧
      gafLoopW s₀.mem (s₀.loc 0) (s₀.loc 1) = some (s'.loc 0, s'.loc 1); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := appCountAtLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih, evalE_tld, tld, evalE_cnt,
        tcntM, evalE_tierE, evalE_idxE] <;> finish [tierW, idxW]

theorem appCountAtLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) appCountAtLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r = .normal ∧ s'.loc 4 = s₀.loc 4 ∧
      gafLoopW s₀.mem (s₀.loc 0) (s₀.loc 1) = some (s'.loc 0, s'.loc 1); ⊤⦄ :=
  Triple.step_exec (appCountAtLoop_spec p (n + 1) s₀)

end acaLoop

theorem appCountAtL_spec (p : Prog) (hp : p.lookup "app_count_at" = some appCountAtL) (n : Nat)
    (s₀ : St) (e f : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "app_count_at" [e, f]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      acaW s₀.mem e f = some (r.headD 0, r.tail.headD 0); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, appCountAtL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, appCountAtLoop_step_spec p n] <;>
      finish [acaW, LocEq]

/-- **The loop's count is `numArgs`.** -/
theorem gafLoopW_numArgs (m : Mem) (a : AState) (hR : ArenaR m a) :
    ∀ (N : Nat) (e f e' f' : Word), f.toNat ≤ N → HW e → gafLoopW m e f = some (e', f') →
      f' ≠ 0 → (numArgs f.toNat (decE e)).run a = .ok ((f - f').toNat, a) ∧
        f'.toNat ≤ f.toNat := by
  intro N
  induction N with
  | zero =>
    intro e f e' f' hfN he hL hf'
    have hf0 : f = 0 := UInt64.toNat_inj.mp (by simp; omega)
    subst hf0
    by_cases hc : e >>> 28 = 4
    · rw [gafLoopW] at hL; simp [hc] at hL
    · rw [gafLoopW_done m e 0 hc] at hL
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hL)
      exact absurd rfl hf'
  | succ N ih =>
    intro e f e' f' hfN he hL hf'
    by_cases hc : e >>> 28 = 4
    · have hf0 : f ≠ 0 := by
        intro hf0; rw [hf0, gafLoopW] at hL; simp [hc] at hL
      have hv1 : ¬ (tierW e ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0) := by
        intro hv; rw [gafLoopW] at hL; simp [hc, hf0, hv] at hL
      have hv2 : ¬ tcnt m APP (tierW e) ≤ idxW e := by
        intro hv; rw [gafLoopW] at hL; simp [hc, hf0, hv1, hv] at hL
      rw [gafLoopW_step m e f _ hc hf0 hv1 hv2 rfl] at hL
      have hfm1 := pr_word_sub1 f hf0
      have hcnt : idxW e < tcnt m APP (tierW e) := UInt64.not_le.mp hv2
      have hva := viewApp_ok m a hR e he ⟨hv1, hcnt⟩
      have h1 := (view_app m a hR e he ⟨hv1, hcnt⟩ hc).2.1
      obtain ⟨ihr, ihb⟩ := ih _ (f - 1) e' f' (by rw [hfm1]; omega) h1 hL hf'
      have hf1 := pr_word_ne0 f hf0
      obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hf1
      refine ⟨?_, by omega⟩
      have hsub : (f - f').toNat = (f - 1 - f').toNat + 1 := by
        rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega),
          UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hfm1]; omega), hfm1]
        omega
      rw [hj, numArgs, (decE_tag_app e he).mpr hc]
      rw [show j = (f - 1).toNat by rw [hfm1]; omega]
      simp [viewApp_run' _ a, hva, except_ok_bind, StateT.run_bind, ihr, hsub]
      rfl
    · rw [gafLoopW_done m e f hc] at hL
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hL)
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (pr_word_ne0 f hf')
      refine ⟨?_, Nat.le_refl _⟩
      rw [hk, numArgs]
      have htag : (decE e).tag ≠ ETag.app := fun h => hc ((decE_tag_app e he).mp h)
      simp [htag]
      rfl

/-- **A run of `app_count_at` model refines `getAppFn` and `numArgs`** at the counter. -/
@[refines ConRon.Arena.numArgs]
theorem acaW_ok {m : Mem} {a : AState} (hR : ArenaR m a) {e f c h : Word} (he : HW e)
    (hW : acaW m e f = some (c, h)) :
    (getAppFn f.toNat (decE e)).run a = .ok (decE h, a) ∧
      (numArgs f.toNat (decE e)).run a = .ok (c.toNat, a) ∧ HW h ∧ c.toNat < f.toNat := by
  unfold acaW at hW
  rcases hL : gafLoopW m e f with _ | ⟨e', f'⟩
  · rw [hL] at hW; cases hW
  rw [hL] at hW
  by_cases hf0 : f' = 0
  · simp [hf0] at hW
  simp only [hf0, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨rfl, rfl⟩ := hW
  obtain ⟨h1, h2⟩ := gafLoopW_ok m a hR _ e f _ _ (Nat.le_refl _) he hL hf0
  obtain ⟨h3, h4⟩ := gafLoopW_numArgs m a hR _ e f _ _ (Nat.le_refl _) he hL hf0
  refine ⟨h1, h3, h2, ?_⟩
  have := pr_word_ne0 f' hf0
  rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)]
  omega

/-- **`getAppArgs` does not depend on the counter** once `getAppFn` succeeds at the smaller one. -/
theorem gafLoopW_args (m : Mem) (a : AState) (hR : ArenaR m a) :
    ∀ (N : Nat) (e f e' f' : Word) (F : Nat), f.toNat ≤ N → HW e → gafLoopW m e f = some (e', f') →
      f' ≠ 0 → f.toNat ≤ F → (getAppArgs F (decE e)).run a = (getAppArgs f.toNat (decE e)).run a := by
  intro N
  induction N with
  | zero =>
    intro e f e' f' F hfN he hL hf' hF
    have hf0 : f = 0 := UInt64.toNat_inj.mp (by simp; omega)
    subst hf0
    by_cases hc : e >>> 28 = 4
    · rw [gafLoopW] at hL; simp [hc] at hL
    · rw [gafLoopW_done m e 0 hc] at hL
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hL)
      exact absurd rfl hf'
  | succ N ih =>
    intro e f e' f' F hfN he hL hf' hF
    by_cases hc : e >>> 28 = 4
    · have hf0 : f ≠ 0 := by
        intro hf0; rw [hf0, gafLoopW] at hL; simp [hc] at hL
      have hv1 : ¬ (tierW e ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0) := by
        intro hv; rw [gafLoopW] at hL; simp [hc, hf0, hv] at hL
      have hv2 : ¬ tcnt m APP (tierW e) ≤ idxW e := by
        intro hv; rw [gafLoopW] at hL; simp [hc, hf0, hv1, hv] at hL
      rw [gafLoopW_step m e f _ hc hf0 hv1 hv2 rfl] at hL
      have hfm1 := pr_word_sub1 f hf0
      have hcnt : idxW e < tcnt m APP (tierW e) := UInt64.not_le.mp hv2
      have hva := viewApp_ok m a hR e he ⟨hv1, hcnt⟩
      have h1 := (view_app m a hR e he ⟨hv1, hcnt⟩ hc).2.1
      have hf1 := pr_word_ne0 f hf0
      obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hf1
      obtain ⟨J, hJ⟩ : ∃ J, F = J + 1 := ⟨F - 1, by omega⟩
      have ihr := ih _ (f - 1) e' f' J (by rw [hfm1]; omega) h1 hL hf' (by rw [hfm1]; omega)
      rw [hj, hJ, getAppArgs, getAppArgs, (decE_tag_app e he).mpr hc]
      rw [show j = (f - 1).toNat by rw [hfm1]; omega]
      simp only [beq_self_eq_true, ↓reduceIte, StateT.run_bind, viewApp_run' _ a, hva,
        except_ok_bind, ihr]
    · obtain ⟨k, hk⟩ : ∃ k, F = k + 1 := by
        rw [gafLoopW_done m e f hc] at hL
        obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hL)
        have := pr_word_ne0 f hf'
        exact ⟨F - 1, by omega⟩
      obtain ⟨k', hk'⟩ : ∃ k', f.toNat = k' + 1 := by
        rw [gafLoopW_done m e f hc] at hL
        obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hL)
        exact Nat.exists_eq_succ_of_ne_zero (pr_word_ne0 f hf')
      have htag : (decE e).tag ≠ ETag.app := fun h => hc ((decE_tag_app e he).mp h)
      rw [hk, hk', getAppArgs, getAppArgs]
      simp [htag]

/-! ## `lam_proj(f, k, e)` -/

/-- **The model of `lam_proj`'s loop**: the final `(f, k, e)`. -/
def lpLoopW (m : Mem) (f k e : Word) : Option (Word × Word × Word) :=
  if e >>> 28 = 5 then
    if f = 0 then none
    else if tierW e ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if tcnt m LAM (tierW e) ≤ idxW e then none
    else lpLoopW m (f - 1) (k + 1) (tfld m LAM (tierW e) (idxW e) 1)
  else some (f, k, e)
termination_by f.toNat
decreasing_by
  have hf0 : f ≠ 0 := by assumption
  have := pr_word_sub1 f hf0
  have := pr_word_ne0 f hf0
  omega

theorem lpLoopW_done (m : Mem) (f k e : Word) (h : e >>> 28 ≠ 5) :
    lpLoopW m f k e = some (f, k, e) := by
  rw [lpLoopW]; simp [h]

theorem lpLoopW_step (m : Mem) (f k e e' : Word) (h : e >>> 28 = 5) (hf : f ≠ 0)
    (hv1 : ¬ (tierW e ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0))
    (hv2 : ¬ tcnt m LAM (tierW e) ≤ idxW e)
    (he' : e' = tfld m LAM (tierW e) (idxW e) 1) :
    lpLoopW m f k e = lpLoopW m (f - 1) (k + 1) e' := by
  subst he'; rw [lpLoopW]; simp only [h, ↓reduceIte, hf, hv1, hv2]

grind_pattern [arena_grind] lpLoopW_done => lpLoopW m f k e
grind_pattern [arena_grind] lpLoopW_step => lpLoopW m f k e, lpLoopW m (f - 1) (k + 1) e'

section lpLoop
variable (p : Prog)

theorem lamProjLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n lamProjLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r = .normal ∧
      lpLoopW s₀.mem (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) = some (s'.loc 0, s'.loc 1, s'.loc 2); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := lamProjLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih, evalE_tld, tld, evalE_cnt,
        tcntM, evalE_tierE, evalE_idxE] <;> finish [tierW, idxW]

theorem lamProjLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) lamProjLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r = .normal ∧
      lpLoopW s₀.mem (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) = some (s'.loc 0, s'.loc 1, s'.loc 2); ⊤⦄ :=
  Triple.step_exec (lamProjLoop_spec p (n + 1) s₀)

end lpLoop

/-- **The model of `lam_proj`**: `(flag, k, j)`. -/
def lamProjW (m : Mem) (f k e : Word) : Option (Word × Word × Word) :=
  match lpLoopW m f k e with
  | none => none
  | some (f', k', e') =>
    if f' = 0 then none
    else if e' >>> 28 ≠ 0 then some (0, 0, 0)
    else if tierW e' ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if tcnt m BVAR (tierW e') ≤ idxW e' then none
    else if tfld m BVAR (tierW e') (idxW e') 0 < k' then
      some (1, k', tfld m BVAR (tierW e') (idxW e') 0)
    else some (0, 0, 0)

theorem lamProjL_spec (p : Prog) (hp : p.lookup "lam_proj" = some lamProjL) (n : Nat)
    (s₀ : St) (f k e : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "lam_proj" [f, k, e]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧
      lamProjW s₀.mem f k e = some (r.headD 0, r.tail.headD 0, r.tail.tail.headD 0); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, lamProjL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        lamProjLoop_step_spec p n, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] <;>
      finish [lamProjW, LocEq, tierW, idxW]

/-- **The loop's model refines `lamProj?`'s descent** (`k + f` does not wrap). -/
theorem lpLoopW_ok (m : Mem) (a : AState) (hR : ArenaR m a) :
    ∀ (N : Nat) (f k e f' k' e' : Word), f.toNat ≤ N → HW e → k.toNat + f.toNat < 2 ^ 64 →
      lpLoopW m f k e = some (f', k', e') →
      (lamProj? f.toNat k.toNat (decE e)).run a = (lamProj? f'.toNat k'.toNat (decE e')).run a ∧
        HW e' ∧ k'.toNat + f'.toNat = k.toNat + f.toNat ∧ e' >>> 28 ≠ 5 := by
  intro N
  induction N with
  | zero =>
    intro f k e f' k' e' hfN he hkf hL
    have hf0 : f = 0 := UInt64.toNat_inj.mp (by simp; omega)
    subst hf0
    by_cases hc : e >>> 28 = 5
    · rw [lpLoopW] at hL; simp [hc] at hL
    · rw [lpLoopW_done m 0 k e hc] at hL
      simp only [Option.some.injEq, Prod.mk.injEq] at hL
      obtain ⟨rfl, rfl, rfl⟩ := hL
      exact ⟨rfl, he, rfl, hc⟩
  | succ N ih =>
    intro f k e f' k' e' hfN he hkf hL
    by_cases hc : e >>> 28 = 5
    · have hf0 : f ≠ 0 := by
        intro hf0; rw [hf0, lpLoopW] at hL; simp [hc] at hL
      have hv1 : ¬ (tierW e ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0) := by
        intro hv; rw [lpLoopW] at hL; simp [hc, hf0, hv] at hL
      have hv2 : ¬ tcnt m LAM (tierW e) ≤ idxW e := by
        intro hv; rw [lpLoopW] at hL; simp [hc, hf0, hv1, hv] at hL
      rw [lpLoopW_step m f k e _ hc hf0 hv1 hv2 rfl] at hL
      have hfm1 := pr_word_sub1 f hf0
      have hf1 := pr_word_ne0 f hf0
      have hk1 : (k + 1).toNat = k.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      have hcnt : idxW e < tcnt m LAM (tierW e) := UInt64.not_le.mp hv2
      have hvb := viewBind_lam m a hR e he ⟨hv1, hcnt⟩ hc
      have h1 := (view_lam m a hR e he ⟨hv1, hcnt⟩ hc).2.2
      obtain ⟨ihr, ihb, ihs, ihn⟩ := ih (f - 1) (k + 1) _ f' k' e' (by rw [hfm1]; omega) h1
        (by rw [hfm1, hk1]; omega) hL
      refine ⟨?_, ihb, by rw [ihs, hfm1, hk1]; omega, ihn⟩
      rw [← ihr]
      obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hf1
      have hlam : ((decE e).tag == ETag.lam) = true := by
        rw [tag_beq_w e he 5 (by decide) ETag.lam rfl 5 rfl]; simp [hc]
      rw [hj, lamProj?, hfm1, hj, hk1]
      simp only [hlam, ↓reduceIte, Nat.succ_sub_one, StateT.run_bind, viewBind_run' _ a, hvb,
        except_ok_bind]
    · rw [lpLoopW_done m f k e hc] at hL
      simp only [Option.some.injEq, Prod.mk.injEq] at hL
      obtain ⟨rfl, rfl, rfl⟩ := hL
      exact ⟨rfl, he, rfl, hc⟩

/-- **`lam_proj`'s model refines `lamProj?`.** -/
@[refines ConRon.Arena.lamProj?]
theorem lamProjW_ok {m : Mem} {a : AState} (hR : ArenaR m a) {f k e r0 r1 r2 : Word} (he : HW e)
    (hkf : k.toNat + f.toNat < 2 ^ 64) (hW : lamProjW m f k e = some (r0, r1, r2)) :
    (lamProj? f.toNat k.toNat (decE e)).run a =
      .ok ((if r0 = 0 then none else some (r1.toNat, r2.toNat)), a) ∧ (r0 = 0 ∨ r0 = 1) ∧
      (r0 ≠ 0 → r2.toNat < r1.toNat ∧ r1.toNat ≤ k.toNat + f.toNat) := by
  unfold lamProjW at hW
  rcases hL : lpLoopW m f k e with _ | ⟨f', k', e'⟩
  · rw [hL] at hW; cases hW
  rw [hL] at hW
  obtain ⟨hrun, he', hs, hn5⟩ := lpLoopW_ok m a hR _ f k e f' k' e' (Nat.le_refl _) he hkf hL
  rw [hrun]
  by_cases hf0 : f' = 0
  · simp [hf0] at hW
  simp only [hf0, ↓reduceIte] at hW
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (pr_word_ne0 f' hf0)
  have hlam : ((decE e').tag == ETag.lam) = false := by
    rw [tag_beq_w e' he' 5 (by decide) ETag.lam rfl 5 rfl]; simp [hn5]
  by_cases hg : e' >>> 28 = 0
  · simp only [hg, ne_eq, not_true_eq_false, ↓reduceIte] at hW
    have hbv : ((decE e').tag == ETag.bvar) = true := by
      rw [tag_beq_w e' he' 0 (by decide) ETag.bvar rfl 0 rfl]; simp [hg]
    by_cases hv1 : tierW e' ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
    · simp [hv1] at hW
    by_cases hv2 : tcnt m BVAR (tierW e') ≤ idxW e'
    · simp [hv1, hv2] at hW
    simp only [hv1, hv2, ↓reduceIte] at hW
    have hcnt : idxW e' < tcnt m BVAR (tierW e') := UInt64.not_le.mp hv2
    have hvb := viewBVar_ok m a hR e' he' ⟨hv1, hcnt⟩
    rw [hj, lamProj?]
    simp only [hlam, hbv, Bool.false_eq_true, ↓reduceIte, StateT.run_bind]
    simp only [show ∀ x, (viewBVar x).run a = .ok (a.store.viewBVar x, a) from fun _ => rfl, hvb,
      except_ok_bind]
    by_cases hlt : tfld m BVAR (tierW e') (idxW e') 0 < k'
    · simp only [hlt, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨rfl, rfl, rfl⟩ := hW
      have hlt' := UInt64.lt_iff_toNat_lt.mp hlt
      refine ⟨?_, Or.inr rfl, fun _ => ⟨hlt', by omega⟩⟩
      simp [hlt']; rfl
    · simp only [hlt, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨rfl, rfl, rfl⟩ := hW
      have hlt' : ¬ (tfld m BVAR (tierW e') (idxW e') 0).toNat < k'.toNat :=
        fun h => hlt (UInt64.lt_iff_toNat_lt.mpr h)
      refine ⟨?_, Or.inl rfl, fun h => absurd rfl h⟩
      simp [hlt']; rfl
  · simp only [hg, ne_eq, not_false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl, rfl⟩ := hW
    have hbv : ((decE e').tag == ETag.bvar) = false := by
      rw [tag_beq_w e' he' 0 (by decide) ETag.bvar rfl 0 rfl]; simp [hg]
    refine ⟨?_, Or.inl rfl, fun h => absurd rfl h⟩
    rw [hj, lamProj?]
    simp [hlam, hbv]
    rfl

/-! ## `type_sort_pw`'s loop -/

/-- **The model of `type_sort_pw`'s loop**: the final `(f, r, d)`. -/
def tsLoopW (m : Mem) (f r d : Word) : Option (Word × Word × Word) :=
  if r >>> 28 = 6 then
    if f = 0 then none
    else if tierW r ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if tcnt m FORALL (tierW r) ≤ idxW r then none
    else tsLoopW m (f - 1) (tfld m FORALL (tierW r) (idxW r) 1) (d + 1)
  else some (f, r, d)
termination_by f.toNat
decreasing_by
  have hf0 : f ≠ 0 := by assumption
  have := pr_word_sub1 f hf0
  have := pr_word_ne0 f hf0
  omega

theorem tsLoopW_done (m : Mem) (f r d : Word) (h : r >>> 28 ≠ 6) :
    tsLoopW m f r d = some (f, r, d) := by
  rw [tsLoopW]; simp [h]

theorem tsLoopW_step (m : Mem) (f r d r' : Word) (h : r >>> 28 = 6) (hf : f ≠ 0)
    (hv1 : ¬ (tierW r ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0))
    (hv2 : ¬ tcnt m FORALL (tierW r) ≤ idxW r)
    (hr' : r' = tfld m FORALL (tierW r) (idxW r) 1) :
    tsLoopW m f r d = tsLoopW m (f - 1) r' (d + 1) := by
  subst hr'; rw [tsLoopW]; simp only [h, ↓reduceIte, hf, hv1, hv2]

grind_pattern [arena_grind] tsLoopW_done => tsLoopW m f r d
grind_pattern [arena_grind] tsLoopW_step => tsLoopW m f r d, tsLoopW m (f - 1) r' (d + 1)

section tsLoop
variable (p : Prog)

theorem typeSortPWLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n typeSortPWLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r = .normal ∧ s'.loc 0 = s₀.loc 0 ∧ s'.loc 2 = s₀.loc 2 ∧
      tsLoopW s₀.mem (s₀.loc 1) (s₀.loc 3) (s₀.loc 4) = some (s'.loc 1, s'.loc 3, s'.loc 4); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := typeSortPWLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih, evalE_tld, tld, evalE_cnt,
        tcntM, evalE_tierE, evalE_idxE] <;> finish [tierW, idxW]

theorem typeSortPWLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) typeSortPWLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r = .normal ∧ s'.loc 0 = s₀.loc 0 ∧ s'.loc 2 = s₀.loc 2 ∧
      tsLoopW s₀.mem (s₀.loc 1) (s₀.loc 3) (s₀.loc 4) = some (s'.loc 1, s'.loc 3, s'.loc 4); ⊤⦄ :=
  Triple.step_exec (typeSortPWLoop_spec p (n + 1) s₀)

end tsLoop

/-- **The loop's model refines `typeSortPWGo`'s descent** (`d + f` does not wrap). -/
theorem tsLoopW_ok (m : Mem) (a : AState) (hR : ArenaR m a) (fe : IFEnv) (root : EIdx) :
    ∀ (N : Nat) (f r d f' r' d' : Word), f.toNat ≤ N → HW r → d.toNat + f.toNat < 2 ^ 64 →
      tsLoopW m f r d = some (f', r', d') →
      (typeSortPWGo fe root f.toNat (decE r) d.toNat).run a =
        (typeSortPWGo fe root f'.toNat (decE r') d'.toNat).run a ∧
        HW r' ∧ d'.toNat + f'.toNat = d.toNat + f.toNat ∧ r' >>> 28 ≠ 6 := by
  intro N
  induction N with
  | zero =>
    intro f r d f' r' d' hfN he hkf hL
    have hf0 : f = 0 := UInt64.toNat_inj.mp (by simp; omega)
    subst hf0
    by_cases hc : r >>> 28 = 6
    · rw [tsLoopW] at hL; simp [hc] at hL
    · rw [tsLoopW_done m 0 r d hc] at hL
      simp only [Option.some.injEq, Prod.mk.injEq] at hL
      obtain ⟨rfl, rfl, rfl⟩ := hL
      exact ⟨rfl, he, rfl, hc⟩
  | succ N ih =>
    intro f r d f' r' d' hfN he hkf hL
    by_cases hc : r >>> 28 = 6
    · have hf0 : f ≠ 0 := by
        intro hf0; rw [hf0, tsLoopW] at hL; simp [hc] at hL
      have hv1 : ¬ (tierW r ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0) := by
        intro hv; rw [tsLoopW] at hL; simp [hc, hf0, hv] at hL
      have hv2 : ¬ tcnt m FORALL (tierW r) ≤ idxW r := by
        intro hv; rw [tsLoopW] at hL; simp [hc, hf0, hv1, hv] at hL
      rw [tsLoopW_step m f r d _ hc hf0 hv1 hv2 rfl] at hL
      have hfm1 := pr_word_sub1 f hf0
      have hf1 := pr_word_ne0 f hf0
      have hd1 : (d + 1).toNat = d.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      have hcnt : idxW r < tcnt m FORALL (tierW r) := UInt64.not_le.mp hv2
      have hvb := viewBind_forall m a hR r he ⟨hv1, hcnt⟩ hc
      have h1 := (view_forall m a hR r he ⟨hv1, hcnt⟩ hc).2.2
      obtain ⟨ihr, ihb, ihs, ihn⟩ := ih (f - 1) _ (d + 1) f' r' d' (by rw [hfm1]; omega) h1
        (by rw [hfm1, hd1]; omega) hL
      refine ⟨?_, ihb, by rw [ihs, hfm1, hd1]; omega, ihn⟩
      rw [← ihr]
      obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hf1
      have hfa : ((decE r).tag == ETag.forallE) = true := by
        rw [tag_beq_w r he 6 (by decide) ETag.forallE rfl 6 rfl]; simp [hc]
      rw [hj, typeSortPWGo, hfm1, hj, hd1]
      simp only [hfa, ↓reduceIte, Nat.succ_sub_one, StateT.run_bind, viewBind_run' _ a, hvb,
        except_ok_bind]
    · rw [tsLoopW_done m f r d hc] at hL
      simp only [Option.some.injEq, Prod.mk.injEq] at hL
      obtain ⟨rfl, rfl, rfl⟩ := hL
      exact ⟨rfl, he, rfl, hc⟩

/-! ## `proof_pw`'s loop -/

/-- **The model of `proof_pw`'s loop**: the final `(f, e)`. -/
def ppLoopW (m : Mem) (f e : Word) : Option (Word × Word) :=
  if e >>> 28 = 5 ∨ e >>> 28 = 7 ∨ e >>> 28 = 4 then
    if f = 0 then none
    else if tierW e ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
    else if e >>> 28 = 5 then
      if tcnt m LAM (tierW e) ≤ idxW e then none
      else ppLoopW m (f - 1) (tfld m LAM (tierW e) (idxW e) 1)
    else if e >>> 28 = 7 then
      if tcnt m LET (tierW e) ≤ idxW e then none
      else ppLoopW m (f - 1) (tfld m LET (tierW e) (idxW e) 2)
    else if tcnt m APP (tierW e) ≤ idxW e then none
      else ppLoopW m (f - 1) (tfld m APP (tierW e) (idxW e) 0)
  else some (f, e)
termination_by f.toNat
decreasing_by
  all_goals
    have hf0 : f ≠ 0 := by assumption
    have := pr_word_sub1 f hf0
    have := pr_word_ne0 f hf0
    omega

theorem ppLoopW_done (m : Mem) (f e : Word) (h5 : e >>> 28 ≠ 5) (h7 : e >>> 28 ≠ 7)
    (h4 : e >>> 28 ≠ 4) : ppLoopW m f e = some (f, e) := by
  rw [ppLoopW]; simp [h5, h7, h4]

theorem ppLoopW_lam (m : Mem) (f e e' : Word) (h : e >>> 28 = 5) (hf : f ≠ 0)
    (hv1 : ¬ (tierW e ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0))
    (hv2 : ¬ tcnt m LAM (tierW e) ≤ idxW e)
    (he' : e' = tfld m LAM (tierW e) (idxW e) 1) :
    ppLoopW m f e = ppLoopW m (f - 1) e' := by
  subst he'; rw [ppLoopW]; simp only [h, true_or, ↓reduceIte, hf, hv1, hv2]

theorem ppLoopW_let (m : Mem) (f e e' : Word) (h : e >>> 28 = 7) (hf : f ≠ 0)
    (hv1 : ¬ (tierW e ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0))
    (hv2 : ¬ tcnt m LET (tierW e) ≤ idxW e)
    (he' : e' = tfld m LET (tierW e) (idxW e) 2) :
    ppLoopW m f e = ppLoopW m (f - 1) e' := by
  subst he'; rw [ppLoopW]
  simp only [h, or_true, true_or, ↓reduceIte, hf, hv1, hv2,
    show ¬ ((7 : Word) = 5) by decide]

theorem ppLoopW_app (m : Mem) (f e e' : Word) (h : e >>> 28 = 4) (hf : f ≠ 0)
    (hv1 : ¬ (tierW e ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0))
    (hv2 : ¬ tcnt m APP (tierW e) ≤ idxW e)
    (he' : e' = tfld m APP (tierW e) (idxW e) 0) :
    ppLoopW m f e = ppLoopW m (f - 1) e' := by
  subst he'; rw [ppLoopW]
  simp only [h, or_true, ↓reduceIte, hf, hv1, hv2, show ¬ ((4 : Word) = 5) by decide,
    show ¬ ((4 : Word) = 7) by decide]

grind_pattern [arena_grind] ppLoopW_done => ppLoopW m f e
grind_pattern [arena_grind] ppLoopW_lam => ppLoopW m f e, ppLoopW m (f - 1) e'
grind_pattern [arena_grind] ppLoopW_let => ppLoopW m f e, ppLoopW m (f - 1) e'
grind_pattern [arena_grind] ppLoopW_app => ppLoopW m f e, ppLoopW m (f - 1) e'

section ppLoop
variable (p : Prog)

theorem proofPWLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    exec p n proofPWLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r = .normal ∧ s'.loc 0 = s₀.loc 0 ∧
      ppLoopW s₀.mem (s₀.loc 1) (s₀.loc 2) = some (s'.loc 1, s'.loc 2); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := proofPWLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih, evalE_tld, tld, evalE_cnt,
        tcntM, evalE_tierE, evalE_idxE] <;> finish [tierW, idxW]

theorem proofPWLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    step p (exec p n) proofPWLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r = .normal ∧ s'.loc 0 = s₀.loc 0 ∧
      ppLoopW s₀.mem (s₀.loc 1) (s₀.loc 2) = some (s'.loc 1, s'.loc 2); ⊤⦄ :=
  Triple.step_exec (proofPWLoop_spec p (n + 1) s₀)

end ppLoop

/-- **The loop's model refines `proofPW`'s descent.** -/
theorem ppLoopW_ok (m : Mem) (a : AState) (hR : ArenaR m a) (fe : IFEnv) :
    ∀ (N : Nat) (f e f' e' : Word), f.toNat ≤ N → HW e → ppLoopW m f e = some (f', e') →
      (proofPW fe f.toNat (decE e)).run a = (proofPW fe f'.toNat (decE e')).run a ∧
        HW e' ∧ e' >>> 28 ≠ 5 ∧ e' >>> 28 ≠ 7 ∧ e' >>> 28 ≠ 4 := by
  intro N
  induction N with
  | zero =>
    intro f e f' e' hfN he hL
    have hf0 : f = 0 := UInt64.toNat_inj.mp (by simp; omega)
    subst hf0
    by_cases hc : e >>> 28 = 5 ∨ e >>> 28 = 7 ∨ e >>> 28 = 4
    · rw [ppLoopW] at hL; simp [hc] at hL
    · simp only [not_or] at hc
      rw [ppLoopW_done m 0 e hc.1 hc.2.1 hc.2.2] at hL
      simp only [Option.some.injEq, Prod.mk.injEq] at hL
      obtain ⟨rfl, rfl⟩ := hL
      exact ⟨rfl, he, hc.1, hc.2.1, hc.2.2⟩
  | succ N ih =>
    intro f e f' e' hfN he hL
    by_cases hc : e >>> 28 = 5 ∨ e >>> 28 = 7 ∨ e >>> 28 = 4
    · have hf0 : f ≠ 0 := by
        intro hf0; rw [hf0, ppLoopW] at hL; simp [hc] at hL
      have hv1 : ¬ (tierW e ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0) := by
        intro hv; rw [ppLoopW] at hL; simp [hc, hf0, hv] at hL
      have hfm1 := pr_word_sub1 f hf0
      have hf1 := pr_word_ne0 f hf0
      obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hf1
      have hjf : j = (f - 1).toNat := by rw [hfm1]; omega
      rcases hc with h5 | h7 | h4
      · have hv2 : ¬ tcnt m LAM (tierW e) ≤ idxW e := by
          intro hv; rw [ppLoopW] at hL; simp [h5, hf0, hv1, hv] at hL
        rw [ppLoopW_lam m f e _ h5 hf0 hv1 hv2 rfl] at hL
        have hcnt : idxW e < tcnt m LAM (tierW e) := UInt64.not_le.mp hv2
        have hvb := viewBind_lam m a hR e he ⟨hv1, hcnt⟩ h5
        have h1 := (view_lam m a hR e he ⟨hv1, hcnt⟩ h5).2.2
        obtain ⟨ihr, ihb⟩ := ih (f - 1) _ f' e' (by rw [hfm1]; omega) h1 hL
        refine ⟨?_, ihb⟩
        rw [← ihr]
        have ht : ((decE e).tag == ETag.lam) = true := by
          rw [tag_beq_w e he 5 (by decide) ETag.lam rfl 5 rfl]; simp [h5]
        rw [hj, proofPW, hjf]
        simp only [ht, ↓reduceIte, StateT.run_bind, viewBind_run' _ a, hvb, except_ok_bind]
      · have hv2 : ¬ tcnt m LET (tierW e) ≤ idxW e := by
          intro hv; rw [ppLoopW] at hL
          simp [h7, hf0, hv1, hv, show ¬ ((7 : Word) = 5) by decide] at hL
        rw [ppLoopW_let m f e _ h7 hf0 hv1 hv2 rfl] at hL
        have hcnt : idxW e < tcnt m LET (tierW e) := UInt64.not_le.mp hv2
        have hvl := viewLet_ok m a hR e he ⟨hv1, hcnt⟩
        have h1 := (view_let m a hR e he ⟨hv1, hcnt⟩ h7).2.2.2
        obtain ⟨ihr, ihb⟩ := ih (f - 1) _ f' e' (by rw [hfm1]; omega) h1 hL
        refine ⟨?_, ihb⟩
        rw [← ihr]
        have ht : ((decE e).tag == ETag.lam) = false := by
          rw [tag_beq_w e he 5 (by decide) ETag.lam rfl 5 rfl]; simp [h7]
        have ht7 : ((decE e).tag == ETag.letE) = true := by
          rw [tag_beq_w e he 7 (by decide) ETag.letE rfl 7 rfl]; simp [h7]
        rw [hj, proofPW, hjf]
        simp only [ht, ht7, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
          show ∀ x, (viewLet x).run a = .ok (a.store.viewLet x, a) from fun _ => rfl, hvl,
          except_ok_bind]
      · have hv2 : ¬ tcnt m APP (tierW e) ≤ idxW e := by
          intro hv; rw [ppLoopW] at hL
          simp [h4, hf0, hv1, hv, show ¬ ((4 : Word) = 5) by decide,
            show ¬ ((4 : Word) = 7) by decide] at hL
        rw [ppLoopW_app m f e _ h4 hf0 hv1 hv2 rfl] at hL
        have hcnt : idxW e < tcnt m APP (tierW e) := UInt64.not_le.mp hv2
        have hva := viewApp_ok m a hR e he ⟨hv1, hcnt⟩
        have h1 := (view_app m a hR e he ⟨hv1, hcnt⟩ h4).2.1
        obtain ⟨ihr, ihb⟩ := ih (f - 1) _ f' e' (by rw [hfm1]; omega) h1 hL
        refine ⟨?_, ihb⟩
        rw [← ihr]
        have ht : ((decE e).tag == ETag.lam) = false := by
          rw [tag_beq_w e he 5 (by decide) ETag.lam rfl 5 rfl]; simp [h4]
        have ht7 : ((decE e).tag == ETag.letE) = false := by
          rw [tag_beq_w e he 7 (by decide) ETag.letE rfl 7 rfl]; simp [h4]
        have ht4 : ((decE e).tag == ETag.app) = true := by
          rw [tag_beq_w e he 4 (by decide) ETag.app rfl 4 rfl]; simp [h4]
        rw [hj, proofPW, hjf]
        simp only [ht, ht7, ht4, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
          viewApp_run' _ a, hva, except_ok_bind]
    · simp only [not_or] at hc
      rw [ppLoopW_done m f e hc.1 hc.2.1 hc.2.2] at hL
      simp only [Option.some.injEq, Prod.mk.injEq] at hL
      obtain ⟨rfl, rfl⟩ := hL
      exact ⟨rfl, he, hc.1, hc.2.1, hc.2.2⟩

end L.Arena
