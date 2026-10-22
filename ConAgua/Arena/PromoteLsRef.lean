import ConAgua.Arena.PromoteLRef

/-!
# `promote_ls` refines `promoteLs`

`pool_rel`: `promote_l_pool(f, o, l, q)` is the twin's `promoteLList` over the handles of the
pool slice `(o, l)`, the results written at `[q, q + l)` above the pool top (`Grows` with the
top unchanged: no record below the top changes). `pls_rel`: `pls_arm` raises the top over the
results and interns the slice (`piLs_rel`), `promote_ls` around it with the memo.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false

namespace L.Arena

/-! ## The pool above its top -/

theorem set0_top (a : Array Word) (h : 0 < a.size) : a.set! 0 (rdW a 0) = a := by
  apply Array.ext_getElem?
  intro i
  simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  split
  · rename_i hi; subst hi; simp [rdW, h]
  · rfl

/-- **A pool write above the top** grows the pool, the top unchanged. -/
theorem grows_poolSet (m : Mem) (q x : Word) (hc : 0 < (m.arr64 CTL).size)
    (hq : m.top.toNat ≤ q.toNat) (hs : q.toNat < (m.arr64 POOL).size) :
    Grows m (m.set64 POOL q x) := by
  have htop : (m.set64 POOL q x).top = m.top := by
    simp only [top_rdW, Mem.arr64_set64_ne _ _ _ _ _ (show CTL ≠ POOL by decide)]
  have hfr : Frame POOL (m.set64 CTL 0 m.top) m := by
    refine ⟨rfl, (Mem.words_size_set64 _ _ _ _).symm, fun b hb => ?_⟩
    by_cases hbc : b = CTL
    · subst hbc; rw [Mem.arr64_set64_same, top_rdW, UInt64.toNat_zero, set0_top _ hc]
    · rw [Mem.arr64_set64_ne _ _ _ _ _ hbc]
  refine ⟨?_, fun j hj => ?_, by rw [htop]; exact Nat.le_refl _, by rw [htop, size_set64]; omega, size_set64 _ _ _ _ _⟩
  · rw [htop]; exact Frame.set64 _ _ _ _ _ hfr
  · rw [Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    simp; omega

/-- **Raising the top** over words already written grows the pool. -/
theorem grows_top (m : Mem) (t : Word) (hc : 0 < (m.arr64 CTL).size) (ht : m.top.toNat ≤ t.toNat)
    (hs : t.toNat ≤ (m.arr64 POOL).size) : Grows m (m.set64 CTL 0 t) := by
  have htop := Mem.top_set64 m t hc
  refine ⟨?_, fun j _ => by rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)], by rw [htop]; exact ht,
    by rw [htop, Mem.arr64_set64_ne _ _ _ _ _ (by decide)]; exact hs,
    by rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]⟩
  rw [htop]; exact Frame.refl _ _

theorem pmemo_grow {m m' : Mem} {pm : PMemo} (hg : Grows m m') (h : PMemoR m pm) : PMemoR m' pm :=
  h.frameLo (by simp) (by simp) (grows_frame m m' hg)

theorem ctl_pos {m : Mem} {a : AState} (hR : ArenaR m a) : 0 < (m.arr64 CTL).size := by
  have := ctl_size hR; omega

/-! ## The twin's lists -/

theorem promoteLList_nil (pm : PMemo) (fuel : Nat) : promoteLList pm fuel [] = pure (pm, []) := by
  rw [promoteLList]

theorem promoteLList_cons (pm : PMemo) (fuel : Nat) (u : LIdx) (us : List LIdx) :
    promoteLList pm fuel (u :: us) = (do
      let (m, u) ← promoteL pm fuel u
      let (m, us) ← promoteLList m fuel us
      pure (m, u :: us)) := by
  rw [promoteLList]

theorem Agree.trans' {p q r : Array Word} {t : Nat} (h₁ : Agree p q t) (h₂ : Agree q r t) :
    Agree p r t := fun j hj => (h₁ j hj).trans (h₂ j hj)

theorem Agree.mono' {p q : Array Word} {t t' : Nat} (h : Agree p q t) (ht : t' ≤ t) : Agree p q t' :=
  fun j hj => h j (by omega)

theorem toNat_add1 (x : Word) (h : x.toNat + 1 < 2 ^ 64) : (x + 1).toNat = x.toNat + 1 := by
  rw [UInt64.toNat_add]; simp; omega

theorem toNat_sub1 (x : Word) (h : x ≠ 0) : (x - 1).toNat = x.toNat - 1 := by
  have : x.toNat ≠ 0 := fun h' => h (UInt64.toNat_inj.mp (by simpa using h'))
  rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp

/-! ## `promote_l_pool` -/

/-- **What a run of `promote_l_pool` gives**: the twin's `promoteLList` succeeds with `us'`,
whose handle words are the slice `(q, l)`, persistent; the relations after; the pool below `q`,
its size and the top unchanged. -/
def LLOk (pm : PMemo) (f : Word) (us : List LIdx) (m : Mem) (a : AState) (q l : Word) (m' : Mem) :
    Prop :=
  ∃ a' pm' us', (promoteLList pm f.toNat us).run a = .ok ((pm', us'), a') ∧ ArenaD m' a' ∧
    PMemoR m' pm' ∧ sliceL (m'.arr64 POOL) q.toNat l.toNat = lsWords us' ∧ lsKids us' ∧
    cp a' = cp a ∧ m'.top = m.top ∧ Agree (m'.arr64 POOL) (m.arr64 POOL) q.toNat ∧
    (m'.arr64 POOL).size = (m.arr64 POOL).size ∧ MemFrame (POOL :: lArrs) lCtl m m' ∧
    pm'.eM = pm.eM ∧ pm'.lsM = pm.lsM

section pool
variable (p : Prog) (hp : PromoteProg p)
include hp

theorem pool_rel : ∀ n : Nat, ∀ (m : Mem) (a : AState) (pm : PMemo) (f o l q : Word)
    (us : List LIdx) (r : List Word) (m' : Mem),
    ArenaD m a → PMemoR m pm → sliceL (m.arr64 POOL) o.toNat l.toNat = lsWords us →
    o.toNat + l.toNat ≤ q.toNat → m.top.toNat ≤ q.toNat →
    q.toNat + l.toNat ≤ (m.arr64 POOL).size →
    callW p n "promote_l_pool" [f, o, l, q] m = some (r, m') → LLOk pm f us m a q l m' := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc; rw [callW_zero'] at hc; cases hc
  | succ n ih =>
  intro m a pm f o l q us r m' hD hP hsl hoq htq hqs hc
  obtain ⟨s', rfl, -, hW⟩ := callW_triple (promoteLPool_spec p hp n ⟨m, Locals.init []⟩ f o l q) hc
  simp only at hW
  have hps := hD.1.lit.1.2.2.1
  by_cases hl : l = 0
  · rw [plPoolW_nil _ _ _ _ _ _ _ hl] at hW
    cases hW
    subst hl
    have hus : us = [] := by
      have : lsWords us = [] := by rw [← hsl]; simp [sliceL]
      simpa [lsWords] using this
    subst hus
    refine ⟨a, pm, [], ?_, hD, hP, by simp [sliceL, lsWords], fun _ h => by simp at h, rfl, rfl,
      Agree.refl _ _, rfl, MemFrame.refl _ _ _, rfl, rfl⟩
    rw [promoteLList_nil]; rfl
  have hl1 : l.toNat = (l - 1).toNat + 1 := by rw [toNat_sub1 l hl]; have := toNat_pred l hl; omega
  rw [hl1, sliceL_succ] at hsl
  cases us with
  | nil => simp [lsWords] at hsl
  | cons u us₀ =>
  simp only [lsWords, List.map_cons, List.cons.injEq] at hsl
  obtain ⟨hu, hus⟩ := hsl
  have ho : ¬ (m.arr64 POOL).size ≤ o.toNat := by omega
  rw [plPoolW_cons _ _ _ _ _ _ _ hl ho] at hW
  have hrd : rdW (m.arr64 POOL) o = u.word.toUInt64 := by rw [rdW, hu]
  rw [hrd] at hW
  cases hca : callW p n "promote_l" [f, u.word.toUInt64] m with
  | none => rw [hca] at hW; cases hW
  | some x =>
  obtain ⟨r₁, m₁⟩ := x
  rw [hca] at hW
  obtain ⟨a₁, pm₁, hrun₁, hD₁, hP₁, hpw₁, hcp₁, hfr₁, he₁, hls₁⟩ :=
    (pl_rel p hp n).1 m a pm f _ r₁ m₁ hD hP (word_lt u) hca
  rw [decI_word] at hrun₁
  have hpool₁ : m₁.arr64 POOL = m.arr64 POOL := hfr₁.1 POOL (by decide) (by decide)
  have htop₁ : m₁.top = m.top := by simp only [top_rdW]; exact hfr₁.2.1 0 (by decide)
  by_cases hq₁ : (m₁.arr64 POOL).size ≤ q.toNat
  · simp [poolK, hq₁] at hW
  rw [poolK_some (hq := hq₁)] at hW
  cases hcb : callW p n "promote_l_pool" [f, o + 1, l - 1, q + 1]
      (m₁.set64 POOL q (r₁.headD 0)) with
  | none => rw [hcb] at hW; cases hW
  | some x =>
  obtain ⟨r₂, m₂⟩ := x
  rw [hcb, memK_some] at hW
  cases hW
  have hg : Grows m₁ (m₁.set64 POOL q (r₁.headD 0)) :=
    grows_poolSet m₁ q _ (ctl_pos hD₁.1) (by rw [htop₁]; exact htq) (by omega)
  have hD₁' := ArenaD.grow _ _ hg _ hD₁
  have hP₁' := pmemo_grow hg hP₁
  have hpool₁' : (m₁.set64 POOL q (r₁.headD 0)).arr64 POOL = (m₁.arr64 POOL).set! q.toNat (r₁.headD 0) :=
    Mem.arr64_set64_same _ _ _ _
  have hag₁ : Agree ((m₁.set64 POOL q (r₁.headD 0)).arr64 POOL) (m.arr64 POOL) q.toNat := by
    rw [hpool₁', ← hpool₁]; exact Agree.set _ _ _ _ _ (Agree.refl _ _) (Nat.le_refl _)
  have ho1 : (o + 1).toNat = o.toNat + 1 := toNat_add1 o (by omega)
  have hq1 : (q + 1).toNat = q.toNat + 1 := toNat_add1 q (by omega)
  have hsl₁ : sliceL ((m₁.set64 POOL q (r₁.headD 0)).arr64 POOL) (o + 1).toNat (l - 1).toNat =
      lsWords us₀ := by
    rw [ho1, Agree.sliceL _ _ _ _ _ hag₁ (by omega)]; exact hus
  have htop₁' : (m₁.set64 POOL q (r₁.headD 0)).top = m.top := by
    rw [top_rdW, Mem.arr64_set64_ne _ _ _ _ _ (show CTL ≠ POOL by decide), ← top_rdW, htop₁]
  obtain ⟨a₂, pm₂, us₂, hrun₂, hD₂, hP₂, hsl₂, hk₂, hcp₂, htop₂, hag₂, hsz₂, hfr₂, he₂, hls₂⟩ :=
    ih _ a₁ pm₁ f (o + 1) (l - 1) (q + 1) us₀ r₂ _ hD₁' hP₁' hsl₁ (by rw [ho1, hq1]; omega)
      (by rw [htop₁', hq1]; omega) (by rw [hq1, size_set64, hpool₁]; omega) hcb
  refine ⟨a₂, pm₂, decI (r₁.headD 0) :: us₂, ?_, hD₂, hP₂, ?_, ?_, hcp₂.trans hcp₁,
    by rw [htop₂, htop₁'], ?_, ?_, ?_, he₂.trans he₁, hls₂.trans hls₁⟩
  · rw [promoteLList_cons, run_bind_ok hrun₁]
    simp only
    rw [run_bind_ok hrun₂]; rfl
  · rw [hl1, sliceL_succ, ← hq1, hsl₂]
    simp only [lsWords, List.map_cons, List.cons.injEq, and_true]
    rw [(word_decI _ _ hpw₁.1).mpr rfl]
    have := hag₂ q.toNat (by omega)
    rw [this, hpool₁']
    simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, show q.toNat < (m₁.arr64 POOL).size by omega]
  · intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hpw₁.pers
    · exact hk₂ x hx
  · exact Agree.trans' (hag₂.mono' (by omega)) hag₁
  · rw [hsz₂, size_set64, hpool₁]
  · exact ((hfr₁.mono (by simp) (by simp)).trans
      ((MemFrame.set64 _ POOL (by decide) _ _).mono (by simp) (by simp))).trans hfr₂

end pool

end L.Arena
