import ConAgua.Arena.InstLPLevel2
import ConAgua.Arena.CapsNeverZeroCore

/-!
# `rec_fire_levels` under `CoreS` (lane `defeq2`)

`RecFireLevelsOK` (`WhnfIota.lean`), the last `KnotCallees` field of lane `defeq2`'s, from the
pieces of `InstLPRef2.lean`'s `recFireLevelsW_ok` (helper `whnf3-lp`, at `ArenaD` and
`StoreWF`), each redone under `CoreS` with lane `whnf4`'s level arms (`InstLPLevel*.lean`):

* `ls_node(us)` returns only on a stored list, so `StoreDen.lsAll` reads it back;
* `keys_push` writes the recursor's level-parameter names above the stack top (`CoreS.frame_stk`);
* the elements: `sle_go` (a nested rule's stored levels, each read back and substituted,
  `lvSubIntW_core`) or `slp_go` (a plain rule's constructor parameters, each looked up and
  interned, `lvInternW_core`, or interned as a parameter node), the results on the stack;
* `spn_ls` interns them as a list (`spnLs_core`), and the stack top is put back.
-/

open ConRon.Arena ConLeche
open Std.WP
open scoped Lean.Order


namespace L.Arena

section lev
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word}

/-- `CTL[136]` (the stack top) is a word of the control array: the walk memos' counters sit above
it (`CoreMemos`). -/
theorem CoreS.ctl136 {m : Mem} {a : AState} (hS : CoreS dn m a vis fe M eb) :
    136 < (m.arr64 CTL).size := by
  obtain ⟨mp, h⟩ := hS.memos.2.2.2.2.1
  unfold MemoRG MemoRV at h
  have := h.1
  simp only at this
  have e : (156 : Word).toNat = 156 := rfl
  omega

/-- `CoreS` with the name readback cache replaced by one that holds readbacks. -/
theorem CoreS.withReadNC {m : Mem} {a : AState} (hS : CoreS dn m a vis fe M eb)
    (X : Std.HashMap NIdx Name) (hc : ReadNCOK { a with caches := { a.caches with readNC := X } }) :
    CoreS dn m { a with caches := { a.caches with readNC := X } } vis fe M eb :=
  CoreS.readCaches hS X a.caches.readLsC (by exact hS.readLs) hc

/-- **A result put on the stack at or above the top** keeps the relation and the stack. -/
theorem stackPut_core {m₀ m₁ : Mem} {a : AState} {b h : Word} (hS : CoreS dn m₁ a vis fe M eb)
    (hk : StackKept m₀ m₁) (hb : (spTop m₀).toNat ≤ b.toNat) :
    CoreS dn (m₁.set64 SPN b h) a vis fe M eb ∧ StackKept m₀ (m₁.set64 SPN b h) := by
  have hf₂ : MemFrame [SPN] [] m₁ (m₁.set64 SPN b h) := MemFrame.set64 _ _ (by decide) _ _
  have htop₂ : spTop (m₁.set64 SPN b h) = spTop m₁ := by
    simp only [spTop, Mem.arr64_set64_ne _ _ _ _ _ (show CTL ≠ SPN by decide)]
  refine ⟨hS.frame_stk hf₂ (by simp) (by simp), hk.trans ?_⟩
  exact StackKept.of_spnFrame (hf₂.mono (by simp) (by simp)) htop₂ (fun i hi => by
    simp only [spW]; rw [rdW_set64]
    have : ¬ b = i := fun e => by
      subst e; rw [hk.top] at hi; have := UInt64.lt_iff_toNat_lt.mp hi; omega
    simp [this])

/-- A handle word of a record-pool slice. -/
theorem hslice_cons {k : IdxKind} {b : Array Word} {o : Word} {j : Nat} {x : Idx k}
    {xs : List (Idx k)} (h : hslice? b o.toNat (j + 1) = some (x :: xs)) :
    ∃ w : Word, HW w ∧ x = decI w ∧ rdW b o = w ∧ hslice? b (o.toNat + 1) j = some xs := by
  rw [lp_hslice_succ] at h
  simp only [Option.bind_eq_bind] at h
  cases e : (hd? b o.toNat : Option (Idx k)) with
  | none => simp [e] at h
  | some x' =>
  cases e' : (hslice? b (o.toNat + 1) j : Option (List (Idx k))) with
  | none => simp [e, e'] at h
  | some xs' =>
  simp only [e, e', Option.bind_some, Option.pure_def, Option.some.injEq, List.cons.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [hd?] at e
  cases ew : b[o.toNat]? with
  | none => simp [ew] at e
  | some w =>
  simp only [ew] at e
  have hw : w.toNat < 2 ^ 32 := Classical.byContradiction fun hw => by simp [hw] at e
  simp [hw] at e
  exact ⟨w, hw, e.symm, by simp [rdW, ew], rfl⟩

/-- An empty slice. -/
theorem hslice_nil {k : IdxKind} {b : Array Word} {o l : Word}
    (h : hslice? b o.toNat l.toNat = some ([] : List (Idx k))) : l = 0 := by
  rcases hk : l.toNat with _ | j
  · exact UInt64.toNat_inj.mp (by simpa using hk)
  · rw [hk, lp_hslice_succ] at h
    simp only [Option.bind_eq_bind] at h
    cases e : (hd? b o.toNat : Option (Idx k)) with
    | none => simp [e] at h
    | some x =>
      cases e' : (hslice? b (o.toNat + 1) j : Option (List (Idx k))) with
      | none => simp [e, e'] at h
      | some xs => simp [e, e'] at h

/-! ## `sle_go`: a nested rule's stored levels -/

/-- **The model of `sle_go` refines `substLevelsAt ks vs lvls`** under `CoreS`, over the record-pool
slice `(o, l)` of levels that read back: the results land at `SPN[b ‥ b + l)`, at or above the
stack top. -/
theorem sleElemW_core {ko kc vo vc : Word} {ks : List Name} {us : List LIdx} {vs : List Level} :
    ∀ (lvls : List LIdx) (n : Nat) (m m' : Mem) (a : AState) (o l b : Word),
    CoreS dn m a vis fe M eb → ILWEnv m a ko kc vo vc ks us vs →
    hslice? (m.arr64 EREC) o.toNat l.toNat = some lvls → o.toNat + l.toNat < 2 ^ 64 →
    (∀ u ∈ lvls, ∃ L, denoteL a.store.ls u = some L) →
    (spTop m).toNat ≤ b.toNat → b.toNat + l.toNat ≤ (m.arr64 SPN).size →
    slElemW EREC n m o l b ko kc vo vc = some m' →
    ∃ hs a', (substLevelsAt ks vs lvls).run a = .ok (hs, a') ∧
      CoreS dn m' a' vis fe M eb ∧ ILWGrow a a' ∧ StackKept m m' ∧
      sliceL (m'.arr64 SPN) b.toNat l.toNat = lsWords hs ∧
      (∀ i : Word, i.toNat < b.toNat → rdW (m'.arr64 SPN) i = rdW (m.arr64 SPN) i) ∧
      (∀ c ∈ hs, ∃ L, denoteL a'.store.ls c = some L) := by
  intro lvls
  induction lvls with
  | nil =>
    intro n m m' a o l b hS hE hsl hob hd hb hbs hW
    have hl0 := hslice_nil hsl
    subst hl0
    cases n with
    | zero => simp [slElemW] at hW
    | succ n =>
    rw [slElemW_nil _ n m o 0 b ko kc vo vc rfl] at hW; cases hW
    exact ⟨[], a, rfl, hS, ILWGrow.refl a, StackKept.refl m, by simp [sliceL, lsWords],
      fun _ _ => rfl, by simp⟩
  | cons u lvls ih =>
    intro n m m' a o l b hS hE hsl hob hd hb hbs hW
    rcases hk : l.toNat with _ | j
    · rw [hk] at hsl; simp [hslice?] at hsl
    rw [hk] at hsl
    obtain ⟨w, hw, rfl, hrd, hsl'⟩ := hslice_cons hsl
    have hl0 : l ≠ 0 := fun h0 => by subst h0; simp at hk
    obtain ⟨L, hL⟩ := hd _ (List.mem_cons_self ..)
    cases n with
    | zero => simp [slElemW] at hW
    | succ n =>
    rw [slElemW_cons _ n m o l b ko kc vo vc hl0, elemRd_erec, hrd] at hW
    cases hSb : lvSubIntW n m w ko kc vo vc with
    | none => rw [hSb] at hW; simp [slElemK] at hW
    | some r =>
    obtain ⟨h, m₁⟩ := r
    rw [hSb, slElemK_some] at hW
    by_cases hh : 4294967296 ≤ h
    · simp only [hh, ↓reduceIte] at hW; cases hW
    simp only [hh, ↓reduceIte] at hW
    -- the twin reads the level back
    obtain ⟨X, hrl, hX⟩ := readLevelM_run' a (decI w) L hL hS.readL
    have hSc := hS.withReadLC X hX
    have hEc : ILWEnv m { a with caches := { a.caches with readLC := X } } ko kc vo vc ks us vs :=
      hE.keep (StackKept.refl m) (ILWGrow.of_lss rfl)
    obtain ⟨a₁, hrun₁, o₁⟩ := lvSubIntW_core hSc hEc hw hL hSb
    obtain ⟨hS₂, hk₂⟩ := stackPut_core (h := h) o₁.core o₁.stack hb
    have herec₁ : m₁.arr64 EREC = m.arr64 EREC := o₁.frame.1 EREC (by decide) (by decide)
    have herec₂ : (m₁.set64 SPN b h).arr64 EREC = m.arr64 EREC := by
      rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide), herec₁]
    have hE₂ := hEc.keep hk₂ o₁.grow
    have hspn := hS.spn
    have hb1 : (b + 1).toNat = b.toNat + 1 := toNat_succ_lt (by omega)
    have ho1 : (o + 1).toNat = o.toNat + 1 := toNat_succ_lt (by omega)
    have hl1 : (l - 1).toNat = j := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp; omega
    have hspn₁ : m₁.arr64 SPN = m.arr64 SPN := o₁.frame.1 SPN (by decide) (by decide)
    have hsz₂ : ((m₁.set64 SPN b h).arr64 SPN).size = (m.arr64 SPN).size := by
      rw [Mem.size_arr64_set64, hspn₁]
    obtain ⟨hs', a', hrun', hS', hg', hk', hsl'', hbl', hel'⟩ :=
      ih n (m₁.set64 SPN b h) m' a₁ (o + 1) (l - 1) (b + 1) hS₂ hE₂
        (by rw [herec₂, ho1, hl1]; exact hsl') (by rw [ho1, hl1]; omega)
        (fun u hu => (hd u (List.mem_cons_of_mem _ hu)).elim fun L hL => ⟨L, o₁.grow.ext.ls.lvl _ _ hL⟩)
        (by rw [hb1, hk₂.top]; omega) (by rw [hsz₂, hb1, hl1]; omega) hW
    have hhw : h.toNat < 2 ^ 32 := o₁.hw
    refine ⟨decI h :: hs', a', ?_, hS', ((ILWGrow.of_lss (a := a)
      (a' := { a with caches := { a.caches with readLC := X } }) rfl).trans o₁.grow).trans hg',
      hk₂.trans hk', ?_, ?_, ?_⟩
    · simp only [substLevelsAt, StateT.run_bind, hrl, except_ok_bind, hrun₁, hrun']; rfl
    · rw [sliceL_succ]
      have hbb : rdW (m'.arr64 SPN) b = h := by
        rw [hbl' b (by rw [hb1]; omega), rdW_set64]
        simp [show b.toNat < (m₁.arr64 SPN).size by rw [hspn₁]; omega]
      simp only [lsWords, List.map_cons, List.cons.injEq]
      refine ⟨?_, ?_⟩
      · have : (m'.arr64 SPN)[b.toNat]?.getD 0 = rdW (m'.arr64 SPN) b := rfl
        rw [this, hbb]
        exact ((word_decI _ h hhw).mpr rfl).symm
      · rw [hb1, hl1] at hsl''; simpa [lsWords] using hsl''
    · intro i hi
      rw [hbl' i (by rw [hb1]; omega), rdW_set64, hspn₁]
      have : ¬ b = i := fun e => by subst e; omega
      simp [this]
    · intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · obtain ⟨l', hl'⟩ := o₁.den; exact ⟨l', hg'.ext.ls.lvl _ _ hl'⟩
      · exact hel' c hc

/-! ## `slp_go`: a plain rule's constructor parameters -/

/-- **One parameter's substitute under `CoreS`**: its value interned on a hit, the parameter
node on a miss. -/
theorem slpOne_core {n : Nat} {m m₁ : Mem} {a : AState} {ko kc vo vc w h : Word} {nm : Name}
    {ks : List Name} {us : List LIdx} {vs : List Level}
    (hS : CoreS dn m a vis fe M eb) (hE : ILWEnv m a ko kc vo vc ks us vs)
    (hn : nameN a.store.lss.ls.ns w nm) (hh : h.toNat < 2 ^ 32)
    (hW : slpOne n m w (lookupW SPN POOL n m ko kc vo vc w) = some (h, m₁)) :
    ∃ a₁, (internLevel (Level.subst ks vs (.param nm))).run a = .ok (decI h, a₁) ∧
      LvOut dn vis fe M eb m m₁ a a₁ h := by
  have htop := m.top.toNat_lt
  have h41 := hS.arena.1.lit.1.top41
  have hv := lvsR_of_slice hS.arena.1 us vs vo vc hE.vals (by have := hE.vtop; omega) hE.vden
  cases e : lookupW SPN POOL n m ko kc vo vc w with
  | none => rw [e] at hW; simp [slpOne] at hW
  | some fv =>
  obtain ⟨f, v⟩ := fv
  rw [e] at hW
  rcases lookupW_ok (nameN_rel _ hS.nwf) n _ _ _ _ _ _ _ _ _ _ _ hE.keys hv.toAR hn e with
    ⟨hf, hvl⟩ | ⟨rfl, hgo⟩
  · rw [slpOne_hit n m w f v hf] at hW
    obtain ⟨a₁, hrun, o⟩ := lvInternW_core _ n m a v h m₁ hS hvl hW
    exact ⟨a₁, by simpa [Level.subst] using hrun, o⟩
  · rw [slpOne_miss] at hW
    have hnb : ¬ (4294967296 : Word) ≤ h := fun c => by
      have := UInt64.le_iff_toNat_le.mp c; simp at this; omega
    have hW' : liNodeK (pinternW m w) = some (h, m₁) := by rw [hW]; simp [liNodeK, hnb]
    obtain ⟨a', hrun, ho⟩ := liNode_core (.param (decI w)) (fun m => pinternW m w)
      (fun m a w' m' hA hI => by
        obtain ⟨ok, hR, res, hfr⟩ := L.Front.param_A m a hA w' m' w hn.1 hI
        exact ⟨ok, hR, res, hfr.mono lvSch_sub.2.2.2.2.2.2.2.2.1 lvSch_sub.2.2.2.2.2.2.2.2.2⟩)
      hS (fun c hc => by simp [LNodeView.lchildren] at hc)
      (fun n hn' => by
        simp only [LNodeView.nchildren, List.mem_cons, List.mem_nil_iff, or_false] at hn'
        subst hn'; exact ⟨nm, hn.2⟩) hW'
    refine ⟨a', ?_, ho⟩
    simp only [Level.subst, hgo]
    show (internName nm >>= fun hn => internLNode (.param hn)).run a = _
    rw [StateT.run_bind, internName_nameN_run a hS.nwf hn]; exact hrun

/-- **The model of `slp_go` refines `substParamLevels ks vs ids`** under `CoreS`, over the
record-pool name slice `(o, l)` of names that read back: the results land at `SPN[b ‥ b + l)`. -/
theorem slpElemW_core {ko kc vo vc : Word} {ks : List Name} {us : List LIdx} {vs : List Level} :
    ∀ (ids : List NIdx) (n : Nat) (m m' : Mem) (a : AState) (o l b : Word),
    CoreS dn m a vis fe M eb → ILWEnv m a ko kc vo vc ks us vs →
    hslice? (m.arr64 EREC) o.toNat l.toNat = some ids → o.toNat + l.toNat < 2 ^ 64 →
    (∀ u ∈ ids, ∃ nm, denoteN a.store.ns u = some nm) →
    (spTop m).toNat ≤ b.toNat → b.toNat + l.toNat ≤ (m.arr64 SPN).size →
    slpW n m o l b ko kc vo vc = some m' →
    ∃ hs a', (substParamLevels ks vs ids).run a = .ok (hs, a') ∧
      CoreS dn m' a' vis fe M eb ∧ ILWGrow a a' ∧ StackKept m m' ∧
      sliceL (m'.arr64 SPN) b.toNat l.toNat = lsWords hs ∧
      (∀ i : Word, i.toNat < b.toNat → rdW (m'.arr64 SPN) i = rdW (m.arr64 SPN) i) ∧
      (∀ c ∈ hs, ∃ L, denoteL a'.store.ls c = some L) := by
  intro ids
  induction ids with
  | nil =>
    intro n m m' a o l b hS hE hsl hob hd hb hbs hW
    have hl0 := hslice_nil hsl
    subst hl0
    cases n with
    | zero => simp [slpW] at hW
    | succ n =>
    rw [slpW_nil n m o 0 b ko kc vo vc rfl] at hW; cases hW
    exact ⟨[], a, rfl, hS, ILWGrow.refl a, StackKept.refl m, by simp [sliceL, lsWords],
      fun _ _ => rfl, by simp⟩
  | cons u ids ih =>
    intro n m m' a o l b hS hE hsl hob hd hb hbs hW
    rcases hk : l.toNat with _ | j
    · rw [hk] at hsl; simp [hslice?] at hsl
    rw [hk] at hsl
    obtain ⟨w, hw, rfl, hrd, hsl'⟩ := hslice_cons hsl
    have hl0 : l ≠ 0 := fun h0 => by subst h0; simp at hk
    obtain ⟨nm, hnm⟩ := hd _ (List.mem_cons_self ..)
    cases n with
    | zero => simp [slpW] at hW
    | succ n =>
    rw [slpW_cons n m o l b ko kc vo vc hl0, hrd] at hW
    cases hSb : slpOne n m w (lookupW SPN POOL n m ko kc vo vc w) with
    | none => rw [hSb] at hW; simp [slpK] at hW
    | some r =>
    obtain ⟨h, m₁⟩ := r
    rw [hSb, slpK_some] at hW
    by_cases hh : 4294967296 ≤ h
    · simp only [hh, ↓reduceIte] at hW; cases hW
    simp only [hh, ↓reduceIte] at hW
    have hhw : h.toNat < 2 ^ 32 := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hh)
    -- the twin reads the name back
    obtain ⟨X, hrl, hX⟩ := readNameM_run' a (decI w) nm hnm hS.den.readN
    have hSc := hS.withReadNC X hX
    have hEc : ILWEnv m { a with caches := { a.caches with readNC := X } } ko kc vo vc ks us vs :=
      hE.keep (StackKept.refl m) (ILWGrow.of_lss rfl)
    obtain ⟨a₁, hrun₁, o₁⟩ := slpOne_core hSc hEc ⟨hw, hnm⟩ hhw hSb
    obtain ⟨hS₂, hk₂⟩ := stackPut_core (h := h) o₁.core o₁.stack hb
    have hg₁ : ILWGrow { a with caches := { a.caches with readNC := X } } a₁ := o₁.step.grow
    have herec₁ : m₁.arr64 EREC = m.arr64 EREC := o₁.frame.1 EREC (by decide) (by decide)
    have herec₂ : (m₁.set64 SPN b h).arr64 EREC = m.arr64 EREC := by
      rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide), herec₁]
    have hE₂ := hEc.keep hk₂ hg₁
    have hspn := hS.spn
    have hb1 : (b + 1).toNat = b.toNat + 1 := toNat_succ_lt (by omega)
    have ho1 : (o + 1).toNat = o.toNat + 1 := toNat_succ_lt (by omega)
    have hl1 : (l - 1).toNat = j := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp; omega
    have hspn₁ : m₁.arr64 SPN = m.arr64 SPN := o₁.frame.1 SPN (by decide) (by decide)
    have hsz₂ : ((m₁.set64 SPN b h).arr64 SPN).size = (m.arr64 SPN).size := by
      rw [Mem.size_arr64_set64, hspn₁]
    obtain ⟨hs', a', hrun', hS', hg', hk', hsl'', hbl', hel'⟩ :=
      ih n (m₁.set64 SPN b h) m' a₁ (o + 1) (l - 1) (b + 1) hS₂ hE₂
        (by rw [herec₂, ho1, hl1]; exact hsl') (by rw [ho1, hl1]; omega)
        (fun u hu => (hd u (List.mem_cons_of_mem _ hu)).elim fun x hx => ⟨x, by
          have := hx; simp only [EStore.ns] at this ⊢; rw [hg₁.ns]; exact this⟩)
        (by rw [hb1, hk₂.top]; omega) (by rw [hsz₂, hb1, hl1]; omega) hW
    refine ⟨decI h :: hs', a', ?_, hS', ((ILWGrow.of_lss (a := a)
      (a' := { a with caches := { a.caches with readNC := X } }) rfl).trans hg₁).trans hg',
      hk₂.trans hk', ?_, ?_, ?_⟩
    · simp only [substParamLevels, StateT.run_bind, hrl, except_ok_bind, hrun₁, hrun']; rfl
    · rw [sliceL_succ]
      have hbb : rdW (m'.arr64 SPN) b = h := by
        rw [hbl' b (by rw [hb1]; omega), rdW_set64]
        simp [show b.toNat < (m₁.arr64 SPN).size by rw [hspn₁]; omega]
      simp only [lsWords, List.map_cons, List.cons.injEq]
      refine ⟨?_, ?_⟩
      · have : (m'.arr64 SPN)[b.toNat]?.getD 0 = rdW (m'.arr64 SPN) b := rfl
        rw [this, hbb]
        exact ((word_decI _ h hhw).mpr rfl).symm
      · rw [hb1, hl1] at hsl''; simpa [lsWords] using hsl''
    · intro i hi
      rw [hbl' i (by rw [hb1]; omega), rdW_set64, hspn₁]
      have : ¬ b = i := fun e => by subst e; omega
      simp [this]
    · intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · obtain ⟨l', hl'⟩ := o₁.den; exact ⟨l', hg'.ext.ls.lvl _ _ hl'⟩
      · exact hel' c hc

end lev

/-! ## `rec_fire_levels` -/

theorem mapM_some_mem {α β : Type} {f : α → Option β} :
    ∀ (l : List α) (ys : List β), l.mapM f = some ys → ∀ x ∈ l, ∃ y, f x = some y
  | [], _, _, x, hx => by simp at hx
  | y :: ys, zs, h, x, hx => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨z, hz, ws, hws, rfl⟩ := h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨z, hz⟩
    · exact mapM_some_mem ys ws hws x hx

/-- **The tail of `rec_fire_levels` under `CoreS`**: the list interned from the stack slice, the
stack top put back. -/
theorem rflTail_core {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {M : ModeMaps}
    {eb : Word} (p : Prog) (hL : LsProg p) {n : Nat} {m₀ m₂ m₃ : Mem} {a₂ : AState}
    {b c l : Word} {hs : List LIdx} {rs : List Word} (hS₃ : CoreS dn m₂ a₂ vis fe M eb)
    (hgr : StackGrew m₀ m₂) (hb : b = spTop m₀)
    (hsl : sliceL (m₂.arr64 SPN) c.toNat l.toNat = lsWords hs) (hcl : c.toNat + l.toNat < 2 ^ 64)
    (hel : ∀ c ∈ hs, ∃ L, denoteL a₂.store.ls c = some L)
    (h4 : callW p n "spn_ls" [c, l] m₂ = some (rs, m₃)) :
    ∃ a₄, (internLsNode hs).run a₂ = .ok (decI (rs.headD 0), a₄) ∧
      CoreS dn (m₃.set64 CTL 136 b) a₄ vis fe M eb ∧ StackKept m₀ (m₃.set64 CTL 136 b) ∧
      HW (rs.headD 0) := by
  obtain ⟨a₄, hrun, hS₄, hk₄, hw₄, -⟩ := spnLs_core p hL hS₃ hsl hcl hel h4
  refine ⟨a₄, hrun, hS₄.frame_stk (MemFrame.setCtl m₃ 136 _) (by simp) (by simp), ?_, hw₄⟩
  rw [hb]
  exact StackKept.restoreG (hgr.trans hk₄.toGrew) (by have := hS₄.ctl136; simpa using this)

/-- **`rec_fire_levels` refines `recFireLevels` under `CoreS`** (`RecFireLevelsOK`). -/
theorem recFireLevelsOK_of (p : Prog) (hL : LsProg p) : RecFireLevelsOK p := by
  intro n s₀ a₀ dn vis fe MM eb fk fvo fvc po pc us qo qc rl lps cvjLps hS hus hlps hks hfc
  cases n with
  | zero => exact CoreSpec.zeroW hL.rec_fire_levels _ _ _ _ _ _ _ _ _ _ _
  | succ n =>
  obtain ⟨ks, hks⟩ := hks
  apply L.M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs hrun
    (recFireLevels_spec p hL n s₀ fk fvo fvc po pc us qo qc)
  subst hs
  refine ⟨hloc, ?_⟩
  unfold recFireLevelsW at hW
  generalize hM₀ : s.mem = m₀ at hS hlps hfc hW ⊢
  -- the universe arguments: `ls_node` returned, so the list is stored and reads back
  cases h1 : callW p n "ls_node" [us] m₀ with
  | none => rw [h1] at hW; cases hW
  | some q =>
  obtain ⟨vs', mx⟩ := q
  rw [h1] at hW
  obtain ⟨s₁, hs₁m, hs₁, hne, hv'⟩ :=
    triple_of_callW (lsNode_spec p hL.ls_node n ⟨m₀, Locals.init []⟩ us) h1
  have hmx : mx = m₀ := by rw [← hs₁m, hs₁]
  rw [hmx] at hW
  have hne' : lsNodeW m₀ us ≠ [] := by rw [← hv']; exact hne
  obtain ⟨vs, hdus⟩ := hS.den.lsAll _ (by
    obtain ⟨ids, e, -⟩ := lsNodeW_view hS.arena.1 hus hne'; rw [e]; rfl)
  obtain ⟨ids, hvw, hdl'⟩ := denoteLs_view a₀ (decI us) vs hdus
  obtain ⟨e₁, t₁, sl₁⟩ := lsNodeW_store hS.arena.1 hus hvw
  rw [hv', e₁] at hW
  simp only [List.headD_cons, List.tail_cons] at hW
  -- the keys
  cases h2 : callW p n "keys_push" [po, pc] m₀ with
  | none => rw [h2] at hW; cases hW
  | some q =>
  obtain ⟨bs, m₁⟩ := q
  rw [h2] at hW
  obtain ⟨s₂, hs₂m, -, hW₂⟩ :=
    triple_of_callW (keysPush_spec p hL.toLvSubProg n ⟨m₀, Locals.init []⟩ po pc) h2
  rw [hs₂m] at hW₂
  have hk := lp_nmsR_of_hslice a₀.store.lss.ls.ns m₀ EREC lps ks po pc hlps
    (hslice_noWrap hS.erec hlps) hks
  obtain ⟨hb, hk₁, hf₁, htop₁, hroom, hbel₁⟩ :=
    keysPushW_ok n m₀ m₁ po pc (bs.headD 0) ks hk hS.spn hS.ctl136 hW₂
  have hS₁ := hS.frame_stk hf₁ (by simp) (by simp)
  have hgr₁ : StackGrew m₀ m₁ := StackGrew.of_spnFrame hf₁
    (UInt64.le_iff_toNat_le.mpr (by rw [htop₁, hb]; omega))
    (fun i hi => by
      simp only [spW]
      exact hbel₁ i (by rw [hb]; exact UInt64.lt_iff_toNat_lt.mp hi))
  -- the twin's two readbacks
  obtain ⟨X, hX, hcX⟩ := pr_readNamesM_run lps a₀ ks hks hS.den.readN
  obtain ⟨Y, hY, hcY⟩ := readLevelsM_run' { a₀ with caches := { a₀.caches with readNC := X } }
    (decI us) vs hdus (by exact hS.readLs)
  have hS₂ := CoreS.readCaches hS₁ X Y (by exact hcY) hcX
  have herec₁ : m₁.arr64 EREC = m₀.arr64 EREC := hf₁.1 EREC (by simp [SPN, EREC]) (by decide)
  have hpool₁ : m₁.arr64 POOL = m₀.arr64 POOL := hf₁.1 POOL (by simp [SPN, POOL]) (by decide)
  have hpool₁' : m₁.arr64 POOL1 = m₀.arr64 POOL1 := hf₁.1 POOL1 (by simp [SPN, POOL1]) (by decide)
  have hpool₁v := vpool_congr hpool₁ hpool₁'
  have hpool₁c := pcap_congr' hpool₁ hpool₁'
  have htopm₁ : m₁.top = m₀.top := by simp only [top_rdW]; exact hf₁.2.1 0 (by simp)
  have hsz₁ : (m₁.arr64 SPN).size = (m₀.arr64 SPN).size := hf₁.2.2.1 SPN
  have hspn := hS.spn
  have hlen : (m₁.len64 SPN).toNat = (m₀.arr64 SPN).size := by
    rw [← hsz₁]; exact L.Front.toNat_ofNat_size _ (by rw [hsz₁]; exact hspn)
  have hE : ILWEnv m₁ { a₀ with caches := { a₀.caches with readNC := X, readLsC := Y } }
      (bs.headD 0) pc (tfld m₀ LVLS (tierW us) (idxW us) 0) (tfld m₀ LVLS (tierW us) (idxW us) 1) ks ids vs :=
    ⟨hk₁, by omega, by rw [hpool₁v]; exact sl₁, by rw [htopm₁]; exact t₁, hdl'⟩
  unfold rflK at hW
  rcases hfc with ⟨hfk, hpl, hq, cks, hcks⟩ | ⟨hfk, lvls, pins, hnest, hfv, hfvd⟩
  · -- plain
    simp only [hfk, ne_eq, not_true_eq_false, ↓reduceIte] at hW
    by_cases u1 : m₁.len64 SPN < spTop m₁
    · simp [u1] at hW
    by_cases u2 : m₁.len64 SPN - spTop m₁ < qc
    · simp [u1, u2] at hW
    simp only [u1, u2, ↓reduceIte] at hW
    have u2' := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp u2)
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.not_lt.mp u1), hlen] at u2'
    have u1' := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp u1)
    rw [hlen] at u1'
    cases h3 : callW p n "slp_go" [qo, qc, spTop m₁, bs.headD 0, pc, tfld m₀ LVLS (tierW us) (idxW us) 0,
        tfld m₀ LVLS (tierW us) (idxW us) 1] m₁ with
    | none => rw [h3] at hW; cases hW
    | some q =>
    obtain ⟨xs, m₂⟩ := q
    rw [h3] at hW
    dsimp only at hW
    obtain ⟨s₃, hs₃m, -, hW₃⟩ :=
      triple_of_callW (slpGo_spec p hL n ⟨m₁, Locals.init []⟩ _ _ _ _ _ _ _) h3
    rw [hs₃m] at hW₃
    obtain ⟨hs, a₃, hrun₂, hS₃, -, hk₃, hsl₂, -, hel₃⟩ :=
      slpElemW_core cvjLps n m₁ m₂ _ qo qc (spTop m₁) hS₂ hE (by rw [herec₁]; exact hq)
        (hslice_noWrap hS.erec hq)
        (mapM_some_mem cvjLps cks hcks) (Nat.le_refl _) (by rw [hsz₁]; omega) hW₃
    cases h4 : callW p n "spn_ls" [spTop m₁, qc] m₂ with
    | none => rw [h4] at hW; cases hW
    | some q =>
    obtain ⟨rs, m₃⟩ := q
    rw [h4] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    obtain ⟨a₄, hrun₄, hS₄, hk₄, hw₄⟩ := rflTail_core p hL hS₃ (hgr₁.trans hk₃.toGrew) hb hsl₂
      (by omega) hel₃ h4
    have hrun : (recFireLevels rl lps (decI us) cvjLps).run a₀ = .ok (decI (rs.headD 0), a₄) := by
      simp only [recFireLevels, hpl, StateT.run_bind, hX, except_ok_bind, hY, hrun₂, hrun₄]
    obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
    refine ⟨hok, ?_, by rw [hres, decLs, hr], by unfold ResH; rw [← hr]; exact hw₄⟩
    rw [hst, ← hm]
    exact ⟨MM, hS₄, KeptAll.refl _ _, hk₄⟩
  · -- nested
    simp only [ne_eq, hfk, not_false_eq_true, ↓reduceIte] at hW
    by_cases u1 : m₁.len64 SPN < spTop m₁
    · simp [u1] at hW
    by_cases u2 : m₁.len64 SPN - spTop m₁ < fvc
    · simp [u1, u2] at hW
    simp only [u1, u2, ↓reduceIte] at hW
    have u2' := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp u2)
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.not_lt.mp u1), hlen] at u2'
    have u1' := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp u1)
    rw [hlen] at u1'
    cases h3 : callW p n "sle_go" [fvo, fvc, spTop m₁, bs.headD 0, pc, tfld m₀ LVLS (tierW us) (idxW us) 0,
        tfld m₀ LVLS (tierW us) (idxW us) 1] m₁ with
    | none => rw [h3] at hW; cases hW
    | some q =>
    obtain ⟨xs, m₂⟩ := q
    rw [h3] at hW
    dsimp only at hW
    obtain ⟨s₃, hs₃m, -, hW₃⟩ :=
      triple_of_callW (sleGo_spec p hL n ⟨m₁, Locals.init []⟩ _ _ _ _ _ _ _) h3
    rw [hs₃m] at hW₃
    obtain ⟨hs, a₃, hrun₂, hS₃, -, hk₃, hsl₂, -, hel₃⟩ :=
      sleElemW_core lvls n m₁ m₂ _ fvo fvc (spTop m₁) hS₂ hE (by rw [herec₁]; exact hfv)
        (hslice_noWrap hS.erec hfv)
        hfvd (Nat.le_refl _) (by rw [hsz₁]; omega) hW₃
    cases h4 : callW p n "spn_ls" [spTop m₁, fvc] m₂ with
    | none => rw [h4] at hW; cases hW
    | some q =>
    obtain ⟨rs, m₃⟩ := q
    rw [h4] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    obtain ⟨a₄, hrun₄, hS₄, hk₄, hw₄⟩ := rflTail_core p hL hS₃ (hgr₁.trans hk₃.toGrew) hb hsl₂
      (by omega) hel₃ h4
    have hrun : (recFireLevels rl lps (decI us) cvjLps).run a₀ = .ok (decI (rs.headD 0), a₄) := by
      simp only [recFireLevels, hnest, StateT.run_bind, hX, except_ok_bind, hY, hrun₂, hrun₄]
    obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
    refine ⟨hok, ?_, by rw [hres, decLs, hr], by unfold ResH; rw [← hr]; exact hw₄⟩
    rw [hst, ← hm]
    exact ⟨MM, hS₄, KeptAll.refl _ _, hk₄⟩

end L.Arena
