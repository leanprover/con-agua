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


namespace L.Arena

/-! ## The pool above its top (in the top's tier) -/

theorem set0_top (a : Array Word) (h : 0 < a.size) : a.set! 0 (rdW a 0) = a := by
  apply Array.ext_getElem?
  intro i
  simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  split
  · rename_i hi; subst hi; simp [rdW, h]
  · rfl

/-- Storing the top over itself is a pool frame. -/
theorem PFrame.self_top (m : Mem) (hc : 0 < (m.arr64 CTL).size) : PFrame (m.set64 CTL 0 m.top) m := by
  refine ⟨rfl, (Mem.words_size_set64 _ _ _ _).symm, fun b _ _ => ?_, ?_, ?_, rfl⟩
  · by_cases hbc : b = CTL
    · subst hbc; rw [Mem.arr64_set64_same, top_rdW, UInt64.toNat_zero, set0_top _ hc]
    · rw [Mem.arr64_set64_ne _ _ _ _ _ hbc]
  · rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]
  · rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]

theorem idx_eq (q : Word) : q - (q >>> 40 <<< 40) = q &&& 1099511627775 := by
  apply UInt64.toNat_inj.mp
  have hb := tag_base_toNat q
  rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hb]; exact Nat.div_mul_le_self _ _),
    hb, tag_idx_toNat]
  have := Nat.div_add_mod q.toNat (2 ^ 40)
  rw [Nat.mul_comm] at this; omega

/-- **A word stored at or above the top, in the top's tier**, grows the pool, the top unchanged. -/
theorem poolSetT_facts (m : Mem) (q x : Word) (hp : PoolOK m) (hq : m.top.toNat ≤ q.toNat)
    (hq41 : q.toNat < 2 ^ 41) (hs : (q &&& 1099511627775).toNat < (m.arr64 (tierA 0 (q >>> 40))).size) :
    Grows m (m.set64 (tierA 0 (q >>> 40)) (q - (q >>> 40 <<< 40)) x) ∧
    vpool (m.set64 (tierA 0 (q >>> 40)) (q - (q >>> 40 <<< 40)) x) = (vpool m).set! q.toNat x ∧
    (m.set64 (tierA 0 (q >>> 40)) (q - (q >>> 40 <<< 40)) x).top = m.top := by
  rw [idx_eq]
  have hsz := hp.small.tier (q >>> 40)
  have hv := vpool_stidx0 m q x hq41 hs (by omega)
  have hne : CTL ≠ tierA 0 (q >>> 40) := fun e => by
    rcases tierA_pool (q >>> 40) with h | h <;> rw [h] at e <;> exact absurd e (by decide)
  have ht : (m.set64 (tierA 0 (q >>> 40)) (q &&& 1099511627775) x).top = m.top := by
    simp only [top_rdW]; rw [Mem.arr64_set64_ne _ _ _ _ _ hne]
  refine ⟨Grows.intro m _ hp ?_ ?_ (by rw [ht]; exact Nat.le_refl _) ?_, hv, ht⟩
  · rw [ht]; exact PFrame.set64 _ _ _ (PFrame.self_top m hp.2.1)
  · rw [hv]; exact Agree.set _ _ _ _ _ (Agree.refl _ _) hq
  · rw [ht]; simp only [Nat.sub_self, Nat.add_zero]; exact hp.2.2.2.2.2

theorem pmemo_grow {m m' : Mem} {pm : PMemo} (hg : Grows m m') (h : PMemoR m pm) : PMemoR m' pm :=
  h.frameLo (by decide) (by simp) (grows_frame m m' hg)

theorem ctl_pos {m : Mem} {a : AState} (hR : ArenaR m a) : 0 < (m.arr64 CTL).size := by
  have := ctl_size hR; omega

/-- The next address of a run inside one tier's array. -/
theorem q_step (q : Word) (l : Nat) (S : Nat) (hroom : (q &&& 1099511627775).toNat + l ≤ S)
    (hl : 1 ≤ l) (hS : S < 2 ^ 40) (hq41 : q.toNat < 2 ^ 41) :
    (q + 1) >>> 40 = q >>> 40 ∧ ((q + 1) &&& 1099511627775).toNat = (q &&& 1099511627775).toNat + 1 ∧
      (q + 1).toNat = q.toNat + 1 := by
  rw [tag_idx_toNat] at hroom
  have h1 : (q + 1).toNat = q.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  refine ⟨tag_tier_eq (by rw [h1]; omega), by rw [tag_idx_toNat, tag_idx_toNat, h1]; omega, h1⟩

/-- A word of a slice in use lies in its tier's array. -/
theorem SliceOK.inb {m : Mem} {o l : Word} (hp : PoolOK m) (h : SliceOK m o l) (hl : 0 < l.toNat) :
    (o &&& 1099511627775).toNat < (m.arr64 (tierA 0 (o >>> 40))).size := by
  have h41 := hp.top41
  have hs := hp.small
  obtain ⟨h1, h2⟩ := h
  obtain ⟨-, -, -, -, a5, a6⟩ := hp
  have ho := tag_split o
  have ht := tag_split m.top
  have := tag_idx_lt o
  have := tag_idx_lt m.top
  have hot := tag_tier_le o (by omega)
  have htt := tag_tier_le m.top h41
  rcases tierA_pool (o >>> 40) with e | e <;> rw [e]
  · have : (o >>> 40).toNat = 0 := by
      rw [tierA_word _ hot] at e; split at e
      · assumption
      · exact absurd e (by decide)
    rcases tierA_pool (m.top >>> 40) with e' | e'
    · rw [e'] at a6
      have : (m.top >>> 40).toNat = 0 := by
        rw [tierA_word _ htt] at e'; split at e'
        · assumption
        · exact absurd e' (by decide)
      omega
    · rcases h2 with h2 | h2 | h2
      · have : (m.top >>> 40).toNat = 0 := by rw [tag_tier_toNat]; omega
        rw [tierA_word _ htt] at e'; simp [this] at e'
      · omega
      · rcases a5 with a5 | a5
        · have : (m.top >>> 40).toNat = 0 := by rw [tag_tier_toNat]; omega
          rw [tierA_word _ htt] at e'; simp [this] at e'
        · omega
  · have : (o >>> 40).toNat = 1 := by
      rw [tierA_word _ hot] at e; split at e
      · exact absurd e (by decide)
      · omega
    have : (m.top >>> 40).toNat = 1 := by rw [tag_tier_toNat] at *; omega
    rcases tierA_pool (m.top >>> 40) with e' | e'
    · rw [tierA_word _ htt] at e'; simp [this] at e'
    · rw [e'] at a6; omega

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
whose handle words are the slice `(q, l)`, persistent; the relations after; the top, the capacity,
every slice in use and the pool above the top in its tier outside `[q, q + l)` unchanged. -/
def LLOk (pm : PMemo) (f : Word) (us : List LIdx) (m : Mem) (a : AState) (q l : Word) (m' : Mem) :
    Prop :=
  ∃ a' pm' us', (promoteLList pm f.toNat us).run a = .ok ((pm', us'), a') ∧ ArenaD m' a' ∧
    PMemoR m' pm' ∧ sliceL (vpool m') q.toNat l.toNat = lsWords us' ∧ lsKids us' ∧
    cp a' = cp a ∧ m'.top = m.top ∧ pcap m' = pcap m ∧
    (∀ x : Nat, m.top.toNat ≤ x → x < 2 ^ 41 → (x < 2 ^ 40 ↔ m.top.toNat < 2 ^ 40) →
      (x < q.toNat ∨ q.toNat + l.toNat ≤ x) → (vpool m')[x]? = (vpool m)[x]?) ∧
    (∀ o l : Word, SliceOK m o l → SliceOK m' o l ∧
      ∀ k < l.toNat, (vpool m')[o.toNat + k]?.getD 0 = (vpool m)[o.toNat + k]?.getD 0) ∧
    MemFrame (POOL1 :: lArrs) lCtl m m' ∧ pm'.eM = pm.eM ∧ pm'.lsM = pm.lsM

section pool
variable (p : Prog) (hp : PromoteProg p)
include hp

theorem pool_rel : ∀ n : Nat, ∀ (m : Mem) (a : AState) (pm : PMemo) (f o l q : Word)
    (us : List LIdx) (r : List Word) (m' : Mem),
    ArenaD m a → PMemoR m pm → sliceL (vpool m) o.toNat l.toNat = lsWords us → SliceOK m o l →
    m.top.toNat ≤ q.toNat → (q.toNat < 2 ^ 40 ↔ m.top.toNat < 2 ^ 40) → q.toNat < 2 ^ 41 →
    (q &&& 1099511627775).toNat + l.toNat ≤ (m.arr64 (tierA 0 (q >>> 40))).size →
    callW p n "promote_l_pool" [f, o, l, q] m = some (r, m') → LLOk pm f us m a q l m' := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc; rw [callW_zero'] at hc; cases hc
  | succ n ih =>
  intro m a pm f o l q us r m' hD hP hsl hso htq hqt hq41 hroom hc
  obtain ⟨s', rfl, -, hW⟩ := callW_triple (promoteLPool_spec p hp n ⟨m, Locals.init []⟩ f o l q) hc
  simp only at hW
  have hpk := hD.1.lit.1
  have h41 := hpk.top41
  by_cases hl : l = 0
  · rw [plPoolW_nil _ _ _ _ _ _ _ hl] at hW
    cases hW
    subst hl
    have hus : us = [] := by
      have : lsWords us = [] := by rw [← hsl]; simp [sliceL]
      simpa [lsWords] using this
    subst hus
    refine ⟨a, pm, [], ?_, hD, hP, by simp [sliceL, lsWords], fun _ h => by simp at h, rfl, rfl, rfl,
      fun _ _ _ _ _ => rfl, fun _ _ h => ⟨h, fun _ _ => rfl⟩, MemFrame.refl _ _ _, rfl, rfl⟩
    rw [promoteLList_nil]; rfl
  have hl0 : 0 < l.toNat := by
    have : l.toNat ≠ 0 := fun h => hl (UInt64.toNat_inj.mp (by simpa using h)); omega
  have hl1 : l.toNat = (l - 1).toNat + 1 := by rw [toNat_sub1 l hl]; omega
  have hsl' := hsl
  rw [hl1, sliceL_succ] at hsl'
  cases us with
  | nil => simp [lsWords] at hsl'
  | cons u us₀ =>
  simp only [lsWords, List.map_cons, List.cons.injEq] at hsl'
  obtain ⟨hu, hus⟩ := hsl'
  have hol := hso.1
  have hin := hso.inb hpk hl0
  have ho : ¬ (m.arr64 (tierA 0 (o >>> 40))).size ≤ (o &&& 1099511627775).toNat := by omega
  rw [plPoolW_cons _ _ _ _ _ _ _ hl ho] at hW
  have hrd : prd m o = u.word.toUInt64 := by rw [← vpool_getD m o (by omega)]; exact hu
  rw [hrd] at hW
  cases hca : callW p n "promote_l" [f, u.word.toUInt64] m with
  | none => rw [hca] at hW; cases hW
  | some x =>
  obtain ⟨r₁, m₁⟩ := x
  rw [hca] at hW
  obtain ⟨a₁, pm₁, hrun₁, hD₁, hP₁, hpw₁, hcp₁, hfr₁, he₁, hls₁, hsk₁⟩ :=
    (pl_rel p hp n).1 m a pm f _ r₁ m₁ hD hP (word_lt u) hca
  rw [decI_word] at hrun₁
  have htop₁ : m₁.top = m.top := hsk₁.1
  have hpk₁ := hD₁.1.lit.1
  have hsz₁ : (m₁.arr64 (tierA 0 (q >>> 40))).size = (m.arr64 (tierA 0 (q >>> 40))).size := by
    rcases tierA_pool (q >>> 40) with e | e <;> rw [e]
    · exact hfr₁.2.2.1 POOL
    · exact hfr₁.2.2.1 POOL1
  have hq₁ : ¬ (m₁.arr64 (tierA 0 (q >>> 40))).size ≤ (q - (q >>> 40 <<< 40)).toNat := by
    rw [idx_eq, hsz₁]; omega
  rw [poolK_some (hq := hq₁)] at hW
  obtain ⟨hg, hvg, htg⟩ := poolSetT_facts m₁ q (r₁.headD 0) hpk₁ (by rw [htop₁]; exact htq) hq41
    (by rw [hsz₁]; omega)
  set_option linter.unusedVariables false in
  generalize hm₁' : m₁.set64 (tierA 0 (q >>> 40)) (q - (q >>> 40 <<< 40)) (r₁.headD 0) = m₁' at hW hg hvg htg
  cases hcb : callW p n "promote_l_pool" [f, o + 1, l - 1, q + 1] m₁' with
  | none => rw [hcb] at hW; cases hW
  | some x =>
  obtain ⟨r₂, m₂⟩ := x
  rw [hcb, memK_some] at hW
  cases hW
  have hD₁' := ArenaD.grow _ _ hg _ hD₁
  have hP₁' := pmemo_grow hg hP₁
  have htop₁' : m₁'.top = m.top := htg.trans htop₁
  have hS40 := hpk.small.tier (q >>> 40)
  obtain ⟨hqt1, hqi1, hq1⟩ := q_step q l.toNat _ hroom hl0 hS40 hq41
  have ho1 : (o + 1).toNat = o.toNat + 1 := toNat_add1 o (by omega)
  have hqd : (q + 1).toNat / 2 ^ 40 = q.toNat / 2 ^ 40 := by
    have := congrArg UInt64.toNat hqt1; rwa [tag_tier_toNat, tag_tier_toNat] at this
  have hq40 : ((q + 1).toNat < 2 ^ 40 ↔ q.toNat < 2 ^ 40) := by
    rw [hq1] at hqd ⊢; constructor <;> intro h <;> omega
  -- the slice `(o, l)` at `m₁'`
  obtain ⟨hso₁, hv₁⟩ := hsk₁.2.2 o l hso
  have hso₁' : SliceOK m₁' o l := hso₁.grows hg
  have hag₁ := hg.agree
  have hso₂ : SliceOK m₁' (o + 1) (l - 1) := by
    obtain ⟨a1, a2⟩ := hso₁'
    refine ⟨by rw [ho1]; omega, ?_⟩
    rw [ho1]; omega
  have hsl₁ : sliceL (vpool m₁') (o + 1).toNat (l - 1).toNat = lsWords us₀ := by
    unfold lsWords; rw [← hus, sliceL_eq_iff, ho1]
    intro k hk
    rw [hag₁ _ (by rw [htop₁]; omega)]
    have := hv₁ (k + 1) (by omega)
    rw [show o.toNat + (k + 1) = o.toNat + 1 + k by omega] at this
    exact this
  obtain ⟨a₂, pm₂, us₂, hrun₂, hD₂, hP₂, hsl₂, hk₂, hcp₂, htop₂, hpc₂, hab₂, hsk₂, hfr₂, he₂, hls₂⟩ :=
    ih _ a₁ pm₁ f (o + 1) (l - 1) (q + 1) us₀ r₂ _ hD₁' hP₁' hsl₁ hso₂
      (by rw [htop₁', hq1]; omega) (by rw [htop₁']; exact hq40.trans hqt) (by rw [hq1]; omega)
      (by rw [hqt1, hqi1, ← hm₁', size_set64, hsz₁]; omega) hcb
  have hpc₁ : pcap m₁ = pcap m := pcap_congr (hfr₁.2.2.1 _) (hfr₁.2.2.1 _)
  refine ⟨a₂, pm₂, decI (r₁.headD 0) :: us₂, ?_, hD₂, hP₂, ?_, ?_, hcp₂.trans hcp₁,
    by rw [htop₂, htop₁'], by rw [hpc₂, hg.pcapEq, hpc₁], ?_, ?_, ?_, he₂.trans he₁, hls₂.trans hls₁⟩
  · rw [promoteLList_cons, run_bind_ok hrun₁]
    simp only
    rw [run_bind_ok hrun₂]; rfl
  · rw [hl1, sliceL_succ, ← hq1, hsl₂]
    simp only [lsWords, List.map_cons, List.cons.injEq, and_true]
    rw [(word_decI _ _ hpw₁.1).mpr rfl]
    rw [hab₂ q.toNat (by rw [htop₁']; exact htq) hq41 (by rw [htop₁']; exact hqt) (.inl (by rw [hq1]; omega)),
      hvg, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    simp [show q.toNat < (vpool m₁).size by rw [vpool_size]; exact hq41]
  · intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hpw₁.pers
    · exact hk₂ x hx
  · intro x h1 h2 h3 h4
    rw [hab₂ x (by rw [htop₁']; exact h1) h2 (by rw [htop₁']; exact h3) (by rw [hq1, toNat_sub1 l hl]; omega),
      hvg, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    simp only [show q.toNat ≠ x by omega, ↓reduceIte]
    exact hsk₁.2.1 x h1 h2 h3
  · intro o' l' h
    obtain ⟨h1, h2⟩ := hsk₁.2.2 o' l' h
    have h1' := h1.grows hg
    obtain ⟨h3, h4⟩ := hsk₂ o' l' h1'
    refine ⟨h3, fun k hk => ?_⟩
    rw [h4 k hk, hag₁ _ (by have := h1.1; omega)]
    exact h2 k hk
  · have hfw : MemFrame (POOL1 :: lArrs) lCtl m₁ m₁' := by
      rw [← hm₁']; rcases tierA_pool (q >>> 40) with e | e <;> rw [e] <;>
        exact (MemFrame.set64 _ _ (by decide) _ _).mono (by simp) (by simp)
    exact ((hfr₁.mono (by simp) (by simp)).trans hfw).trans hfr₂

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
  by_cases hc : tcnt m LVLS (tierW h) ≤ idxW h
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
abbrev lsArrs : List ArrId := POOL :: POOL1 :: lArrs ++ [LSREC, LSREC + 256, LSSLOT, LSSLOT + 256, PLSM,
  LSHP, LSHP + 256]
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
    cp a' = cp a ∧ MemFrame lsArrs lsCtl m m' ∧ pm'.eM = pm.eM ∧ TierKeep m m'

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
  by_cases h1 : m.len64 (tierA 0 (m.top >>> 40)) < (m.top &&& 1099511627775)
  · simp [plsArmW, hh', hne, hc0, h1] at hW
  by_cases h2 : m.len64 (tierA 0 (m.top >>> 40)) - (m.top &&& 1099511627775) < (lsNodeW m h).tail.headD 0
  · unfold plsArmW at hW
    rw [ite_eq_right (by simp [hh', hne]), ite_eq_right hc0, ite_eq_right h1, ite_eq_left h2] at hW; cases hW
  rw [plsArmW_eq p n m f h hh' hne hc0 h1 h2] at hW
  obtain ⟨ids, hv⟩ := promote_lsNodeW_view hD.1 hh hne
  obtain ⟨hw, hso, hsl⟩ := lsNodeW_store' hD.1 hh hv
  rw [hw] at hW h2
  simp only [List.headD_cons, List.tail_cons] at hW h2
  have hpk := hD.1.lit.1
  have h41 := hpk.top41
  have hsz := hpk.small.tier (m.top >>> 40)
  have hlen : (m.len64 (tierA 0 (m.top >>> 40))).toNat = (m.arr64 (tierA 0 (m.top >>> 40))).size := by
    simp only [Mem.len64]; exact UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  have hidx := tag_idx_lt m.top
  have hroom : (m.top &&& 1099511627775).toNat + (tfld m LVLS (tierW h) (idxW h) 1).toNat ≤
      (m.arr64 (tierA 0 (m.top >>> 40))).size := by
    have h1' := UInt64.not_lt.mp h1
    have h2' := UInt64.not_lt.mp h2
    rw [UInt64.le_iff_toNat_le, hlen] at h1'
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hlen]; exact h1'),
      hlen] at h2'
    omega
  have hidxle : (m.top &&& 1099511627775).toNat ≤ (m.arr64 (tierA 0 (m.top >>> 40))).size := by omega
  cases hca : callW p n "promote_l_pool"
      [f, tfld m LVLS (tierW h) (idxW h) 0, tfld m LVLS (tierW h) (idxW h) 1, m.top] m with
  | none => rw [hca] at hW; cases hW
  | some x =>
  obtain ⟨r₁, m₁⟩ := x
  rw [hca] at hW
  obtain ⟨a₁, pm₁, us', hrun₁, hD₁, hP₁, hsl₁, hk₁, hcp₁, htop₁, hpc₁, -, -, hfr₁, he₁, hls₁⟩ :=
    pool_rel p hp n m a pm f _ _ m.top ids r₁ m₁ hD hP hsl hso (Nat.le_refl _) Iff.rfl h41 hroom hca
  have hc₁ : (m₁.arr64 CTL).size ≠ 0 := by have := ctl_pos hD₁.1; omega
  rw [plsK_some (hc := hc₁)] at hW
  cases n with
  | zero => rw [callW_zero', hd1] at hW; cases hW
  | succ n =>
  cases hcb : callW p (n + 1) "pi_ls" [m.top, tfld m LVLS (tierW h) (idxW h) 1]
      (m₁.set64 CTL 0 (m.top + tfld m LVLS (tierW h) (idxW h) 1)) with
  | none => rw [hcb] at hW; cases hW
  | some x =>
  obtain ⟨r₂, m₂⟩ := x
  rw [hcb, hd1_some] at hW
  obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
  have hpk₁ := hD₁.1.lit.1
  have hsz₁ : (m₁.arr64 (tierA 0 (m₁.top >>> 40))).size = (m.arr64 (tierA 0 (m.top >>> 40))).size := by
    rw [htop₁]
    rcases tierA_pool (m.top >>> 40) with e | e <;> rw [e]
    · exact hfr₁.2.2.1 POOL
    · exact hfr₁.2.2.1 POOL1
  have hg : Grows m₁ (m₁.set64 CTL 0 (m₁.top + tfld m LVLS (tierW h) (idxW h) 1)) :=
    Grows.write m₁ m₁ _ hpk₁ (PFrame.refl _) (Agree.refl _ _) (by rw [hsz₁, htop₁]; exact hroom)
  rw [htop₁] at hg
  have hD₂ := ArenaD.grow _ _ hg _ hD₁
  have hP₂ := pmemo_grow hg hP₁
  have htop₂ := Mem.top_set64 m₁ (m.top + tfld m LVLS (tierW h) (idxW h) 1) (by omega)
  have hsl₂ : SliceOK (m₁.set64 CTL 0 (m.top + tfld m LVLS (tierW h) (idxW h) 1)) m.top
      (tfld m LVLS (tierW h) (idxW h) 1) := by
    have := SliceOK.fresh hg (by rw [htop₂, htop₁])
    rwa [htop₁] at this
  have hvp₂ : vpool (m₁.set64 CTL 0 (m.top + tfld m LVLS (tierW h) (idxW h) 1)) = vpool m₁ :=
    vpool_congr (Mem.arr64_set64_ne _ _ _ _ _ (by decide)) (Mem.arr64_set64_ne _ _ _ _ _ (by decide))
  obtain ⟨s₂, hs₂, -, hW₂⟩ := callW_triple (piLs_spec p hp n ⟨_, Locals.init []⟩ _ _) hcb
  rw [hs₂] at hW₂
  obtain ⟨a₂, hrun₂, hD₂', hpw₂, hcp₂, hfr₂⟩ := piLs_rel p hp n _ a₁ hD₂ m.top
    (tfld m LVLS (tierW h) (idxW h) 1) hsl₂ us' (by rw [hvp₂]; exact hsl₁) hk₁ _ _ hW₂
  rw [← hm]
  refine ⟨a₂, pm₁, ?_, hD₂', hP₂.frameLo (by simp [POOL, PT0, LSREC, LSSLOT, LSHP]) (by simp) hfr₂,
    hr ▸ hpw₂, hcp₂.trans hcp₁, ?_, he₁,
    ((TierKeep.of_frame hfr₁ (by decide)).trans (TierKeep.of_grows hg)).trans
      (TierKeep.of_frame hfr₂ (by decide))⟩
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
    rw [ite_eq_left hpers, ← hr]
    exact ⟨a, pm, rfl, hD, hP, ⟨hh, ht⟩, rfl, MemFrame.refl _ _ _, rfl, TierKeep.refl _⟩
  have hnp : (decI h : LsIdx).isPersistent = false := by
    rw [isPersistent_decI h hh]; exact beq_eq_false_iff_ne.mpr ht
  rw [ite_eq_right (by simp [hnp])]
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
    exact ⟨_, pm, rfl, hD, hP, ⟨hw1, hw2⟩, rfl, MemFrame.refl _ _ _, rfl, TierKeep.refl _⟩
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
  obtain ⟨a₁, pm₁, hrun, hD₁, hP₁, hpw, hcp, hfr, he, tk⟩ := plsArm_rel p hp n m a pm f h r₁ m₁ hD hP hh hca
  refine ⟨a₁, { pm₁ with lsM := pm₁.lsM.insert (decI h) (decI (r₁.headD 0)) }, ?_,
    hD₁.memo plsSch plsSch_wf (by decide) (by decide) (by decide) h _ hs,
    hP₁.setLs h _ hh hpw hs, by rw [← hr]; exact hpw, hcp, ?_, he,
    tk.trans (TierKeep.of_frame (msetG_frame plsSch plsSch_wf _ _ _ _ _ hs) (by decide))⟩
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
