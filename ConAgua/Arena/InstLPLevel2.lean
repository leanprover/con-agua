import ConAgua.Arena.InstLPLevel
import ConAgua.Arena.InstLPRef2
import ConAgua.Arena.StrLitBase

/-!
# `sls_memo` under `CoreS` (helper `whnf4-ilp-lev`)

The list arm: the list's pool slice substituted element by element (`sls_go`, each element a
`lv_sub_int` under `CoreS`, `lvSubIntW_core`, its result written to the spine stack above the top),
then interned as a list (`spn_ls`: the pool grows, `CoreK.grow`, then the list node,
`CoreS.of_ls`), the result recorded in `instLPLsC`.
-/

open ConRon.Arena ConLeche
open Std.WP
open scoped Lean.Order


namespace L.Arena

section lev
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word}

/-! ## `sls_go`: the elements -/

/-- **The model of `sls_go` refines `internLevelList (substLevelList ks vs ls)`** under `CoreS`,
over the pool slice `(o, l)` of a list that reads back as `ls`: the results land at
`SPN[b ‥ b + l)`, at or above the stack top. -/
theorem slsElemW_core {ko kc vo vc : Word} {ks : List Name} {us : List LIdx} {vs : List Level} :
    ∀ (ids : List LIdx) (Ls : List Level) (n : Nat) (m m' : Mem) (a : AState) (o l b : Word),
    CoreS dn m a vis fe M eb → ILWMemo m a → ILWEnv m a ko kc vo vc ks us vs →
    denoteLList a.store.ls ids = some Ls →
    sliceL (vpool m) o.toNat l.toNat = lsWords ids → o.toNat + l.toNat ≤ m.top.toNat →
    (spTop m).toNat ≤ b.toNat → b.toNat + l.toNat ≤ (m.arr64 SPN).size →
    slElemW POOL n m o l b ko kc vo vc = some m' →
    ∃ hs a', (internLevelList (substLevelList ks vs Ls)).run a = .ok (hs, a') ∧
      CoreS dn m' a' vis fe M eb ∧ ILWMemo m' a' ∧ ILWGrow a a' ∧ StackKept m m' ∧
      a'.memos = a.memos ∧
      sliceL (m'.arr64 SPN) b.toNat l.toNat = lsWords hs ∧
      (∀ i : Word, i.toNat < b.toNat → rdW (m'.arr64 SPN) i = rdW (m.arr64 SPN) i) ∧
      (∀ c ∈ hs, ∃ L, denoteL a'.store.ls c = some L) := by
  intro ids
  induction ids with
  | nil =>
    intro Ls n m m' a o l b hS hM hE hd hsl hot hb hbs hW
    have hl : l.toNat = 0 := by
      have := sliceL_length (vpool m) o.toNat l.toNat
      rw [hsl] at this; simpa [lsWords] using this.symm
    have hl0 : l = 0 := UInt64.toNat_inj.mp (by simpa using hl)
    subst hl0
    simp only [denoteLList, Option.some.injEq] at hd; subst hd
    cases n with
    | zero => simp [slElemW] at hW
    | succ n =>
    rw [slElemW_nil _ n m o 0 b ko kc vo vc rfl] at hW; cases hW
    exact ⟨[], a, rfl, hS, hM, ILWGrow.refl a, StackKept.refl m, rfl, by simp [sliceL, lsWords],
      fun _ _ => rfl, by simp⟩
  | cons u ids ih =>
    intro Ls n m m' a o l b hS hM hE hd hsl hot hb hbs hW
    have hlen := sliceL_length (vpool m) o.toNat l.toNat
    rw [hsl] at hlen
    simp only [lsWords, List.length_map, List.length_cons] at hlen
    obtain ⟨k, hk⟩ : ∃ k, l.toNat = k + 1 := ⟨ids.length, hlen.symm⟩
    rw [hk, sliceL_succ] at hsl
    simp only [lsWords, List.map_cons, List.cons.injEq] at hsl
    obtain ⟨hsl1, hsl2⟩ := hsl
    simp only [denoteLList, opt2_eq_some_iff] at hd
    obtain ⟨L, Ls', hL, hLs, rfl⟩ := hd
    have hl0 : l ≠ 0 := fun e => by subst e; simp at hk
    have hrd : elemRd POOL m o = u.word.toUInt64 := by
      have h41 := hS.arena.1.lit.1.top41
      rw [elemRd_pool, ← vpool_getD m o (by omega)]; simpa using hsl1
    cases n with
    | zero => simp [slElemW] at hW
    | succ n =>
    rw [slElemW_cons _ n m o l b ko kc vo vc hl0, hrd] at hW
    cases hSb : lvSubIntW n m u.word.toUInt64 ko kc vo vc with
    | none => rw [hSb] at hW; simp [slElemK] at hW
    | some r =>
    obtain ⟨h, m₁⟩ := r
    rw [hSb, slElemK_some] at hW
    have hh : ¬ 4294967296 ≤ h := fun hh => by simp only [hh, ↓reduceIte] at hW; cases hW
    simp only [hh, ↓reduceIte] at hW
    obtain ⟨a₁, hrun₁, o₁⟩ := lvSubIntW_core hS hE (word_lt u) (by rw [decI_word]; exact hL) hSb
    -- the result on the stack
    have hf₂ : MemFrame [SPN] [] m₁ (m₁.set64 SPN b h) := MemFrame.set64 _ _ (by decide) _ _
    have hS₂ := o₁.core.frame_stk hf₂ (by simp) (by simp)
    have hspn₁ : m₁.arr64 SPN = m.arr64 SPN := o₁.frame.1 SPN (by decide) (by decide)
    have htop₁ : spTop m₁ = spTop m := o₁.stack.top
    have htop₂ : spTop (m₁.set64 SPN b h) = spTop m₁ := by
      simp only [spTop, Mem.arr64_set64_ne _ _ _ _ _ (show CTL ≠ SPN by decide)]
    have hk₂ : StackKept m₁ (m₁.set64 SPN b h) :=
      StackKept.of_spnFrame (hf₂.mono (by simp) (by simp)) htop₂ (fun i hi => by
        simp only [spW]; rw [rdW_set64]
        have : ¬ b = i := fun e => by
          subst e; rw [htop₁] at hi; have := UInt64.lt_iff_toNat_lt.mp hi; omega
        simp [this])
    have hM₁ : ILWMemo m₁ a₁ := hM.frame o₁.frame (by decide) (by decide) o₁.memos o₁.grow
    have hM₂ : ILWMemo (m₁.set64 SPN b h) a₁ :=
      hM₁.frame hf₂ (by decide) (by decide) rfl (ILWGrow.refl _)
    have hk₀₂ := o₁.stack.trans hk₂
    have hE₂ := hE.keep hk₀₂ o₁.grow
    have hspn := hS.spn
    have hb1 : (b + 1).toNat = b.toNat + 1 := toNat_succ_lt (by omega)
    have ho1 : (o + 1).toNat = o.toNat + 1 := toNat_succ_lt (by have := m.top.toNat_lt; omega)
    have hl1 : (l - 1).toNat = k := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp; omega
    have hsz₂ : ((m₁.set64 SPN b h).arr64 SPN).size = (m.arr64 SPN).size := by
      rw [Mem.size_arr64_set64, hspn₁]
    obtain ⟨hs', a', hrun', hS', hM', hg', hk', hme', hsl', hbl', hel'⟩ :=
      ih Ls' n (m₁.set64 SPN b h) m' a₁ (o + 1) (l - 1) (b + 1) hS₂ hM₂ hE₂
        (denoteLList_mono o₁.grow.ext.ls _ _ hLs)
        (by rw [Agree.sliceL _ _ _ _ _ hk₀₂.pool.below (by rw [ho1, hl1]; omega), ho1, hl1]
            exact hsl2)
        (by have := hk₀₂.pool.top; rw [ho1, hl1]; omega)
        (by rw [hb1, htop₂, htop₁]; omega) (by rw [hsz₂, hb1, hl1]; omega) hW
    have hhw : h.toNat < 2 ^ 32 := o₁.hw
    refine ⟨decI h :: hs', a', ?_, hS', hM', o₁.grow.trans hg', hk₀₂.trans hk', hme'.trans o₁.memos,
      ?_, ?_, ?_⟩
    · simp only [substLevelList, internLevelList, StateT.run_bind, hrun₁, except_ok_bind, hrun']; rfl
    · rw [hk, sliceL_succ]
      have hbb : rdW (m'.arr64 SPN) b = h := by
        rw [hbl' b (by rw [hb1]; omega), rdW_set64]
        simp [show b.toNat < (m₁.arr64 SPN).size by rw [hspn₁]; omega]
      simp only [lsWords, List.map_cons, List.cons.injEq]
      refine ⟨?_, ?_⟩
      · have : (m'.arr64 SPN)[b.toNat]?.getD 0 = rdW (m'.arr64 SPN) b := rfl
        rw [this, hbb]
        exact ((word_decI _ h hhw).mpr rfl).symm
      · rw [hb1, hl1] at hsl'; simpa [lsWords] using hsl'
    · intro i hi
      rw [hbl' i (by rw [hb1]; omega), rdW_set64, hspn₁]
      have : ¬ b = i := fun e => by subst e; omega
      simp [this]
    · intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · obtain ⟨l', hl'⟩ := o₁.den; exact ⟨l', hg'.ext.ls.lvl _ _ hl'⟩
      · exact hel' c hc

/-! ## `spn_ls`: the list node -/

/-- **`spn_ls` refines `internLsNode hs` under `CoreS`**, at a stack slice holding the list's
words whose elements read back: the pool grows by the copy, the list store by the node, and the
result reads back. -/
theorem spnLs_core (p : Prog) (hL : LsProg p) {n : Nat} {m m' : Mem} {a : AState} {b l : Word}
    {hs : List LIdx} {rs : List Word} (hS : CoreS dn m a vis fe M eb)
    (hsl : sliceL (m.arr64 SPN) b.toNat l.toNat = lsWords hs) (hb : b.toNat + l.toNat < 2 ^ 64)
    (hel : ∀ c ∈ hs, ∃ L, denoteL a.store.ls c = some L)
    (h : callW p n "spn_ls" [b, l] m = some (rs, m')) :
    ∃ a', (internLsNode hs).run a = .ok (decI (rs.headD 0), a') ∧ CoreS dn m' a' vis fe M eb ∧
      StackKept m m' ∧ HW (rs.headD 0) ∧ (∃ ls, denoteLs a'.store.lss (decI (rs.headD 0)) = some ls) ∧
      ILWGrow a a' ∧ a'.memos = a.memos ∧ MemFrame [POOL, POOL1, LSREC, LSSLOT, LSHP, tier1 LSREC, tier1 LSSLOT, tier1 LSHP] [0, 40, 41] m m' := by
  have hp := hS.arena.1.lit.1
  obtain ⟨s₄, hs₄m, -, hW⟩ := triple_of_callW (spnLs_spec p hL n ⟨m, Locals.init []⟩ b l
    (by show pcap m < 2 ^ 64; have := hp.2.2.1; omega) hp.top41) h
  rw [hs₄m] at hW
  change spnLsW n m b l = some (rs.headD 0, m') at hW
  generalize rs.headD 0 = r' at hW ⊢
  obtain ⟨m₂, hg, htop₂, htl, hsl₁, hmf, -, hI, hr'⟩ := spnLsW_pool n m m' b l r' hp hb hW
  have hK := CoreK.grow (dn := dn) (vis := vis) (fe := fe) (M := M) (eb := eb) (m₀ := m)
    ⟨hS, StackKept.refl _⟩ hg
  have hq : SliceOK m₂ m.top l := SliceOK.fresh hg htop₂
  have hq0 : m₂.flag = 0 → m.top.toNat < 2 ^ 40 := fun hf =>
    (hS.mode.poolGrew (PoolGrew.of_grows hg)).slice0 hq hf
  have hr : ¬ 4294967296 ≤ r' := fun h => by
    have := UInt64.le_iff_toNat_le.mp h; simp at this; omega
  obtain ⟨ok, hA₃, res, hf₃⟩ := L.Front.internLs_D m₂ a hK.1.arena r' m' m.top l hq
    hs (by rw [hsl₁, hsl]) hq0 hI
  have hrun := AM.run_of_ok _ _ ok
  rw [res] at hrun
  have hst := internLsNode_step _ _ _ _ hrun
  obtain ⟨hS₃, hk₃⟩ := hK.1.of_ls hst hA₃.1 hf₃
    (fun b hb => by simp only [lsSch, List.mem_cons, List.mem_nil_iff, or_false] at hb
                    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (fun x hx => by simp only [lsSch, List.mem_cons, List.mem_nil_iff, or_false] at hx
                    rcases hx with rfl | rfl <;> decide)
    (lsAll_internLsNode hK.1.arena.1 hK.1.den.lsAll hel hrun).1
    (lvlCnt_internLsNode hK.1.arena.1 hA₃.1 (hf₃.2.1 1 (by decide)) hrun)
  obtain ⟨hden, hext⟩ := denoteLs_internLsNode hK.1.arena.1 hel hrun
  obtain ⟨-, -, hme⟩ := internLsNode_keep _ _ _ _ hrun
  obtain ⟨hls, -⟩ := internLsNode_ext _ _ _ _ hrun
  refine ⟨_, hrun, hS₃, hK.2.trans hk₃, UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hr), hden,
    ⟨hext, by rw [hls]⟩, hme, ?_⟩
  exact (hmf.mono (by simp) (by simp)).trans (hf₃.mono (by simp [lsSch]) (by simp [lsSch]))

end lev

/-! ## `sls_memo` -/

/-- **`sls_memo` refines `substLsMemoAt`** under the walk's invariants. -/
@[refines ConRon.Arena.substLsMemoAt]
theorem slsMemo_ok (p : Prog) (hp : ILWLevProg p) : SlsMemoOK p := by
  intro n m m' a dn vis fe M eb w ko kc vo vc ks us vs rs hS hM hE hw hdw' hc
  obtain ⟨LS, hdls⟩ := hdw'
  cases n with
  | zero => rw [callW_zero] at hc; cases hc
  | succ k =>
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (slsMemo_spec p hp.ilw k _ w ko kc vo vc) hc
  rw [hs'] at hW
  change ilwSlsW p k m w ko kc vo vc = some (rs.headD 0, m') at hW
  unfold ilwSlsW at hW
  have hr : ¬ mfindG lplsSch m w 0 = [] := fun hr => by simp [hr] at hW
  simp only [hr, ↓reduceIte] at hW
  by_cases hh : (mfindG lplsSch m w 0).headD 0 ≠ 0
  · -- a hit: the memo's value
    simp only [ne_eq, hh, not_false_eq_true, ↓reduceIte] at hW
    obtain ⟨hw', rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    obtain ⟨v, hv, hvv, hvl⟩ := memoRV_hit lplsSch ilKey VI m _ hM.lpls w 0 hr hh ⟨hw, rfl⟩
    have hval : mvG lplsSch m ((mfindG lplsSch m w 0).tail.headD 0) = rs.headD 0 := hw'
    rw [hval] at hvv hvl
    have hget : a.memos.instLPLsC[(decI w : LsIdx)]? = some (decI (rs.headD 0)) := by
      rw [← hvv]; exact hv
    refine ⟨a, ?_, ⟨M, hS, KeptAll.refl _ _, StackKept.refl _⟩, hM, ILWGrow.refl a, hvl,
      hM.lplsDen _ _ hget⟩
    simp only [substLsMemoAt, StateT.run_bind, instLPLsGet_run, except_ok_bind, hget]; rfl
  -- a miss: read back, substitute each element onto the stack, intern the list, record
  have hh0 : (mfindG lplsSch m w 0).headD 0 = 0 := by simpa using hh
  simp only [hh0, ne_eq, not_true_eq_false, ↓reduceIte] at hW
  have hmiss : a.memos.instLPLsC[(decI w : LsIdx)]? = none :=
    memoRV_miss lplsSch ilKey VI m _ hM.lpls w 0 ⟨hw, rfl⟩ hr hh0
  obtain ⟨ids, hv, hdl⟩ := denoteLs_view a (decI w) LS hdls
  obtain ⟨e₁, t₁, s₁⟩ := lsNodeW_store hS.arena.1 hw hv
  rw [e₁] at hW
  simp only [List.headD_cons, List.tail_cons] at hW
  generalize tfld m LVLS (tierW w) (idxW w) 0 = o at hW t₁ s₁
  generalize tfld m LVLS (tierW w) (idxW w) 1 = l at hW t₁ s₁
  have u1 : ¬ m.len64 SPN < spTop m := fun u1 => by simp [u1] at hW
  have u2 : ¬ m.len64 SPN - spTop m < l := fun u2 => by simp [u1, u2] at hW
  simp only [u1, u2, ↓reduceIte] at hW
  have hspn := hS.spn
  have hlen : (m.len64 SPN).toNat = (m.arr64 SPN).size := L.Front.toNat_ofNat_size _ hspn
  have u1' := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp u1)
  have u2' := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp u2)
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.not_lt.mp u1), hlen] at u2'
  rw [hlen] at u1'
  cases h1 : callW p k "sls_go" [o, l, spTop m, ko, kc, vo, vc] m with
  | none => rw [h1] at hW; cases hW
  | some q =>
  obtain ⟨x, m₁⟩ := q
  rw [h1, ilwSlsK₁_some] at hW
  obtain ⟨s₁', hs₁, -, hW₁⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (slsGo_spec p hp.ls k _ o l (spTop m) ko kc vo vc) h1
  rw [hs₁] at hW₁
  obtain ⟨X, hrl, hrc⟩ := readLevelsM_run' a (decI w) LS hdls hS.readLs
  have hSR := hS.withReadLsC X hrc
  obtain ⟨hs, a₁, hrun₁, hS₁, hM₁, hg₁, hk₁, hme₁, hsl₁, -, hel₁⟩ :=
    slsElemW_core ids LS k m m₁ _ o l (spTop m) hSR (hM.congr rfl rfl) (hE.congr rfl) hdl s₁ t₁
      (Nat.le_refl _) (by omega) hW₁
  cases h2 : callW p k "spn_ls" [spTop m, l] m₁ with
  | none => rw [h2] at hW; cases hW
  | some q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [h2] at hW
  obtain ⟨a₂, hrun₂, hS₂, hk₂, hw₂, hden₂, hg₂, hme₂, hf₂⟩ :=
    spnLs_core p hp.ls hS₁ hsl₁ (by omega) hel₁ h2
  rw [ilwSlsK₂_some] at hW
  rcases h3 : msetG lplsSch m₂ w 0 (r₂.headD 0) with _ | m₃ <;> simp only [h3, reduceCtorEq] at hW
  obtain ⟨hr₂, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  rw [← hr₂]
  have hM₂ : ILWMemo m₂ a₂ := hM₁.frame hf₂ (by decide) (by decide) hme₂ hg₂
  have hM₃ := hM₂.setLPLs w (r₂.headD 0) hw hw₂ hden₂ h3
  have hf₃ := msetG_frame lplsSch lplsSch_wf m₂ m₃ w 0 _ h3
  have hf₃' : MemFrame [lplsSch.arr] [lplsSch.cs, lplsSch.cs + 1] m₂ m₃ := hf₃.mono (by simp) (by simp)
  obtain ⟨hS₃, hk₃⟩ := CoreS.frameLP lplsSch (.inr (.inr rfl)) hS₂ hf₃'
    (hS₂.memos.frameLP hf₃' hM₃.lpMemos (by decide) (by simp))
  refine ⟨_, ?_, ⟨M, hS₃.lpMemos a₂.memos.instLPC a₂.memos.instLPLC
      (a₂.memos.instLPLsC.insert (decI w) (decI (r₂.headD 0))),
    KeptAll.refl _ _, hk₁.trans (hk₂.trans hk₃)⟩, hM₃, ?_, hw₂, hden₂⟩
  · simp only [substLsMemoAt, StateT.run_bind, instLPLsGet_run, except_ok_bind, hmiss, hrl,
      internLevels, hrun₁, hrun₂, instLPLsSet_run]; rfl
  · exact ILWGrow.trans (a₂ := a₂) (ILWGrow.trans (a₂ := a₁)
      (ILWGrow.trans (a₂ := { a with caches := { a.caches with readLsC := X } }) (ILWGrow.of_lss rfl) hg₁)
      hg₂) (ILWGrow.of_lss rfl)

end L.Arena
