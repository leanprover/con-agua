import ConAgua.Arena.PromoteLRef
import ConAgua.Census.Attr

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

/-! ## `pls_arm`, `promote_ls` -/

/-- The twin's arm of `promoteLs` after a memo miss. -/
def plsArmT (m : PMemo) (fuel : Nat) (h : LsIdx) : AM (PMemo × LsIdx) := do
  let (m, us) ← promoteLList m fuel (← viewLs h)
  let r ← internPersistentLs us
  pure (m, r)

theorem promoteLs_eq (m : PMemo) (fuel : Nat) (h : LsIdx) :
    promoteLs m fuel h =
      if h.isPersistent then pure (m, h)
      else match m.lsM[h]? with
        | some r => pure (m, r)
        | none => (do
          let (m, r) ← plsArmT m fuel h
          pure ({ m with lsM := m.lsM.insert h r }, r)) := by
  rw [promoteLs]
  by_cases hp : h.isPersistent
  · simp only [hp, ↓reduceIte]
  · simp only [hp, Bool.false_eq_true, ↓reduceIte]
    cases hm : m.lsM[h]? with
    | some r => rfl
    | none =>
      simp only [plsArmT, bind_assoc]
      apply bind_congr; intro v
      apply bind_congr; intro w
      cases w; simp

theorem promote_viewLs_run {a : AState} {h : LsIdx} {v : LsNodeView} (hw : a.store.lss.view h = some v) :
    (viewLs h).run a = .ok (v, a) := by
  simp only [viewLs, StateT.run_bind, StateT.run_get, pure_bind, hw]; rfl

/-- **L's view of a level-list handle is the arena's**: a returning `ls_node` read a node. -/
theorem promote_lsNodeW_view {m : Mem} {a : AState} (hR : ArenaR m a) {h : Word} (hh : h.toNat < 2 ^ 32)
    (hne : lsNodeW m h ≠ []) : ∃ ids, a.store.lss.view (decI h) = some ids := by
  have hfl := ConsR.flag hR.ls
  unfold lsNodeW at hne
  by_cases g0 : h >>> 28 ≠ 0
  · simp [g0] at hne
  by_cases hsc : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · simp [g0, hsc] at hne
  by_cases hc : tcnt m LS (tierW h) ≤ idxW h
  · simp [g0, hsc, hc] at hne
  have hview : a.store.lss.view (decI h) =
      (if tierW h = 0 then a.store.lss.pers else a.store.lss.scr).get (decI h) := by
    unfold LsStore.view
    rw [isPersistent_decI h hh]
    by_cases ht : tierW h = 0
    · simp only [show (h >>> 27) &&& 1 = tierW h from rfl, ht, beq_self_eq_true, ↓reduceIte]
    · have hon : a.store.lss.scratchOn = true := by
        rw [← hfl]; simp only [bne_iff_ne, ne_eq]; exact fun e => hsc ⟨ht, e⟩
      simp only [show (h >>> 27) &&& 1 = tierW h from rfl, beq_iff_eq, ht, ↓reduceIte, hon]
  rw [hview]
  obtain ⟨x, hx, -⟩ := ConsR.node hR.ls (tierW h) (tierW_le h)
    (idxW h) (UInt64.not_le.mp hc)
  simp only [LsTables.get, decLs_tag0 h hh, show h >>> 28 = 0 from by simpa using g0,
    beq_self_eq_true, ↓reduceIte, Tbl.node?, decLs_idx, apply_ite LsTables.lists, hx,
    Option.map_some]
  exact ⟨_, rfl⟩

/-- The arrays and `CTL` words a level-list promotion writes. -/
abbrev lsArrs : List ArrId := POOL :: lArrs ++ [LSREC, LSSLOT, PLSM, LSHP]
abbrev lsCtl : List Word := lCtl ++ [0, 40, 41, 145]

theorem plsSch_wf : plsSch.WF := ⟨by decide, by decide⟩

/-- The level-list memo gains an entry. -/
theorem PMemoR.setLs {m m' : Mem} {pm : PMemo} (hP : PMemoR m pm) (h r : Word)
    (hh : h.toNat < 2 ^ 32) (hr : PW r) (hs : msetG plsSch m h 0 r = some m') :
    PMemoR m' { pm with lsM := pm.lsM.insert (decI h) (decI r) } := by
  have hf := msetG_frame plsSch plsSch_wf m m' h 0 r hs
  exact ⟨memoRV_frame pnSch pnSch_wf _ _ _ _ (by decide) (by decide) m m' hf
      (fun _ _ h => h) _ hP.n,
    memoRV_frame plSch plSch_wf _ _ _ _ (by decide) (by decide) m m' hf
      (fun _ _ h => h) _ hP.l,
    memoRV_set plsSch plsSch_wf (hKey .levels) (VP .levels) (vp_stable _ _) m pm.lsM hP.ls h 0 r
      ⟨hh, rfl⟩ (decI r) ⟨rfl, hr.1, hr.2⟩ m' hs,
    memoRV_frame peSch ⟨by decide, by decide⟩ _ _ _ _ (by decide) (by decide) m m' hf
      (fun _ _ h => h) _ hP.e⟩

/-- **What a successful run of a level-list promotion gives.** -/
def PLsOk (op : AM (PMemo × LsIdx)) (m : Mem) (a : AState) (pm : PMemo) (r : Word) (m' : Mem) :
    Prop :=
  ∃ a' pm', op.run a = .ok ((pm', decI r), a') ∧ ArenaD m' a' ∧ PMemoR m' pm' ∧ PW r ∧
    cp a' = cp a ∧ MemFrame lsArrs lsCtl m m' ∧ pm'.eM = pm.eM

section pls
variable (p : Prog) (hp : PromoteProg p)
include hp

theorem plsArm_rel (n : Nat) (m : Mem) (a : AState) (pm : PMemo) (f h : Word) (r : List Word)
    (m' : Mem) (hD : ArenaD m a) (hP : PMemoR m pm) (hh : h.toNat < 2 ^ 32)
    (hc : callW p n "pls_arm" [f, h] m = some (r, m')) :
    PLsOk (plsArmT pm f.toNat (decI h)) m a pm (r.headD 0) m' := by
  cases n with
  | zero => rw [callW_zero'] at hc; cases hc
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := callW_triple (plsArm_spec p hp n ⟨m, Locals.init []⟩ f h) hc
  simp only at hW
  have hh' : ¬ 4294967295 < h := fun e => by
    have : (4294967295 : Nat) < h.toNat := e
    omega
  by_cases hne : lsNodeW m h = []
  · simp [plsArmW, hne] at hW
  have hc0 : (m.arr64 CTL).size ≠ 0 := by have := ctl_pos hD.1; omega
  by_cases h1 : m.len64 POOL < m.top
  · simp [plsArmW, hh', hne, hc0, h1] at hW
  by_cases h2 : m.len64 POOL - m.top < (lsNodeW m h).tail.headD 0
  · unfold plsArmW at hW
    rw [if_neg (by simp [hh', hne]), if_neg hc0, if_neg h1, if_pos h2] at hW; cases hW
  rw [plsArmW_eq p n m f h hh' hne hc0 h1 h2] at hW
  obtain ⟨ids, hv⟩ := promote_lsNodeW_view hD.1 hh hne
  obtain ⟨hw, hol, hsl⟩ := lsNodeW_store hD.1 hh hv
  rw [hw] at hW h2
  simp only [List.headD_cons, List.tail_cons] at hW h2
  have hps := hD.1.lit.1.2.2.1
  have hpt := hD.1.lit.1.2.2.2
  have hlen : m.len64 POOL = UInt64.ofNat (m.arr64 POOL).size := len64_eq _ _
  have h1' : m.top.toNat ≤ (m.arr64 POOL).size := hpt
  have hroom : m.top.toNat + (tfld m LS (tierW h) (idxW h) 1).toNat ≤ (m.arr64 POOL).size := by
    rw [hlen] at h2
    have h2' := UInt64.not_lt.mp h2
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ (by
      rw [UInt64.le_iff_toNat_le]; simp; omega)] at h2'
    simp at h2'; omega
  cases hca : callW p n "promote_l_pool"
      [f, tfld m LS (tierW h) (idxW h) 0, tfld m LS (tierW h) (idxW h) 1, m.top] m with
  | none => rw [hca] at hW; cases hW
  | some x =>
  obtain ⟨r₁, m₁⟩ := x
  rw [hca] at hW
  obtain ⟨a₁, pm₁, us', hrun₁, hD₁, hP₁, hsl₁, hk₁, hcp₁, htop₁, hag₁, hsz₁, hfr₁, he₁, hls₁⟩ :=
    pool_rel p hp n m a pm f _ _ m.top ids r₁ m₁ hD hP hsl hol (Nat.le_refl _) hroom hca
  have hc₁ : (m₁.arr64 CTL).size ≠ 0 := by have := ctl_pos hD₁.1; omega
  rw [plsK_some (hc := hc₁)] at hW
  cases n with
  | zero => rw [callW_zero', hd1] at hW; cases hW
  | succ n =>
  cases hcb : callW p (n + 1) "pi_ls" [m.top, tfld m LS (tierW h) (idxW h) 1]
      (m₁.set64 CTL 0 (m.top + tfld m LS (tierW h) (idxW h) 1)) with
  | none => rw [hcb] at hW; cases hW
  | some x =>
  obtain ⟨r₂, m₂⟩ := x
  rw [hcb, hd1_some] at hW
  obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
  have hT : (m.top + tfld m LS (tierW h) (idxW h) 1).toNat =
      m.top.toNat + (tfld m LS (tierW h) (idxW h) 1).toNat := by
    rw [UInt64.toNat_add]; simp; omega
  have hg : Grows m₁ (m₁.set64 CTL 0 (m.top + tfld m LS (tierW h) (idxW h) 1)) :=
    grows_top m₁ _ (by omega) (by rw [htop₁, hT]; omega) (by rw [hT, hsz₁]; exact hroom)
  have hD₂ := ArenaD.grow _ _ hg _ hD₁
  have hP₂ := pmemo_grow hg hP₁
  have htop₂ := Mem.top_set64 m₁ (m.top + tfld m LS (tierW h) (idxW h) 1) (by omega)
  have hpool₂ : (m₁.set64 CTL 0 (m.top + tfld m LS (tierW h) (idxW h) 1)).arr64 POOL = m₁.arr64 POOL :=
    Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  obtain ⟨s₂, hs₂, -, hW₂⟩ := callW_triple (piLs_spec p hp n ⟨_, Locals.init []⟩ _ _) hcb
  rw [hs₂] at hW₂
  obtain ⟨a₂, hrun₂, hD₂', hpw₂, hcp₂, hfr₂⟩ := piLs_rel p hp n _ a₁ hD₂ m.top
    (tfld m LS (tierW h) (idxW h) 1) (by simp only [SliceOK, htop₂, hT]; omega) us'
    (by rw [hpool₂]; exact hsl₁) hk₁ _ _ hW₂
  rw [← hm]
  refine ⟨a₂, pm₁, ?_, hD₂', hP₂.frameLo (by simp [LSREC, LSSLOT, LSHP]) (by simp) hfr₂, hr ▸ hpw₂,
    hcp₂.trans hcp₁, ?_, he₁⟩
  · unfold plsArmT
    rw [run_bind_ok (promote_viewLs_run hv), run_bind_ok hrun₁]
    simp only
    rw [run_bind_ok hrun₂, ← hr]; rfl
  · exact ((hfr₁.mono (by simp) (by simp)).trans
      ((MemFrame.setCtl _ 0 _).mono (by simp) (by simp))).trans (hfr₂.mono (by simp) (by simp))

/-- **`promote_ls` refines `promoteLs`** (the fuel passed on unchanged). -/
theorem pls_rel (n : Nat) (m : Mem) (a : AState) (pm : PMemo) (f h : Word) (r : List Word)
    (m' : Mem) (hD : ArenaD m a) (hP : PMemoR m pm) (hh : h.toNat < 2 ^ 32)
    (hc : callW p n "promote_ls" [f, h] m = some (r, m')) :
    PLsOk (promoteLs pm f.toNat (decI h)) m a pm (r.headD 0) m' := by
  cases n with
  | zero => rw [callW_zero'] at hc; cases hc
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := callW_triple (promoteLs_spec p hp n ⟨m, Locals.init []⟩ f h) hc
  simp only at hW
  rw [promoteLs_eq]
  by_cases ht : tierW h = 0
  · rw [plsW_pers p n m f h ht] at hW
    obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    have hpers : (decI h : LsIdx).isPersistent = true := PW.pers ⟨hh, ht⟩
    rw [if_pos hpers, ← hr]
    exact ⟨a, pm, rfl, hD, hP, ⟨hh, ht⟩, rfl, MemFrame.refl _ _ _, rfl⟩
  have hnp : (decI h : LsIdx).isPersistent = false := by
    rw [isPersistent_decI h hh]; exact beq_eq_false_iff_ne.mpr ht
  rw [if_neg (by simp [hnp])]
  have hk : (hKey .levels).ok h 0 := ⟨hh, rfl⟩
  by_cases h0 : mfindG plsSch m h 0 = []
  · simp [plsW, ht, h0] at hW
  by_cases h1 : (mfindG plsSch m h 0).headD 0 ≠ 0
  · obtain ⟨v, hv, hvr⟩ := memoRV_hit plsSch (hKey .levels) (VP .levels) m pm.lsM hP.ls h 0 h0 h1 hk
    rw [plsW_hit p n m f h ht h0 h1] at hW
    obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    have hv' : pm.lsM[decI h]? = some v := hv
    rw [hv']
    obtain ⟨rfl, hw1, hw2⟩ := hvr
    rw [← hr]
    exact ⟨_, pm, rfl, hD, hP, ⟨hw1, hw2⟩, rfl, MemFrame.refl _ _ _, rfl⟩
  have h1' : (mfindG plsSch m h 0).headD 0 = 0 := by simpa using h1
  rw [plsW_miss p n m f h ht h0 h1'] at hW
  have hmiss : pm.lsM[decI h]? = none :=
    memoRV_miss plsSch (hKey .levels) (VP .levels) m pm.lsM hP.ls h 0 hk h0 h1'
  rw [hmiss]
  cases hca : callW p n "pls_arm" [f, h] m with
  | none => rw [hca] at hW; cases hW
  | some q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [hca] at hW
  cases hs : msetG plsSch m₁ h 0 (r₁.headD 0) with
  | none => simp only [memoK, hs] at hW; cases hW
  | some m₂ =>
  rw [memoK_some _ _ _ _ _ hs] at hW
  obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  obtain ⟨a₁, pm₁, hrun, hD₁, hP₁, hpw, hcp, hfr, he⟩ := plsArm_rel p hp n m a pm f h r₁ m₁ hD hP hh hca
  refine ⟨a₁, { pm₁ with lsM := pm₁.lsM.insert (decI h) (decI (r₁.headD 0)) }, ?_,
    hD₁.memo plsSch plsSch_wf (by decide) (by decide) h _ hs,
    hP₁.setLs h _ hh hpw hs, by rw [← hr]; exact hpw, hcp, ?_, he⟩
  · rw [run_bind_ok hrun, ← hr]; rfl
  · exact hfr.trans ((msetG_frame plsSch plsSch_wf _ _ _ _ _ hs).mono (by simp) (by simp))

/-- **`promote_ls` refines `promoteLs`** (`PLsOk`). -/
@[refines ConRon.Arena.promoteLs]
theorem promoteLs_refines (n : Nat) (s₀ : St) (a₀ : AState) (pm : PMemo) (f h : Word)
    (hD : ArenaD s₀.mem a₀) (hP : PMemoR s₀.mem pm) (hh : h.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "promote_ls" [f, h]
    ⦃fun r s' => LocEq s' s₀ ∧
      PLsOk (promoteLs pm f.toNat (decI h)) s₀.mem a₀ pm (r.headD 0) s'.mem; ⊤⦄ :=
  triple_post (callW_spec p n "promote_ls" [f, h] s₀) fun _ _ ⟨hl, hc⟩ =>
    ⟨hl, pls_rel p hp n _ _ _ _ _ _ _ hD hP hh hc⟩

end pls

end L.Arena
