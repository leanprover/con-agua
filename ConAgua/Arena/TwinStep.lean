import ConAgua.Arena.IndTwin

/-!
# `TwinOK` across a twin step that only grows the store (lane `loopt2`)

`TwinOK` (`DeclLvlStage.lean`) is mostly about the twin state alone; a twin operation that grows
the store well formed and leaves the caches and the pins alone keeps every such part:

* what reads the old store (the readback caches, the zero pin, the empty list pin, the name cache,
  the environment's level parameters and tables, the recursors' levels, `dnN`) by `Ext`;
* what speaks of every node (a `sort` node's level, a `const` node's list, every level handle,
  every level-list handle reads back; the name store's well-formedness) from the new store's
  well-formedness, as con-ron's fold invariant gives them (`TwinOK.of_check`).

The memory's half (the sizes, the core memos) is the caller's, from the step's frame. This is
con-ron's `IStepS` (`StateOK` after, `Ext`, caches and pins unchanged: `internName_sstep`,
`internExprGo_sstep`, `internCIList_sstep`, …), so every interning-only twin operation keeps
`TwinOK` (`TwinOK.of_istep`), with `StateOK` before.

`StageS` (`StageT` and con-ron's `StateOK`) is the relation on stretches without a core call
(`StateOK` is not re-derived after one): every interning step keeps it (`StageS.of_istep`).
Shared with lane `indproofs3`.
-/

open ConRon.Arena

namespace L.Arena

/-! ## `TwinOK` across memory writers -/

section frames
variable {dn : NIdx → Option ConLeche.Name} {fe : IFEnv}

/-- **`TwinOK` across a writer** that leaves the core memos (arrays 49, 50, 52‥54, 151‥153, `CTL`
48, 50, 54, 56, 58, 152, 154, 156) alone, `EREC` writers included (no part of `TwinOK` reads the
records: `StoreDen.mem`); the twin state and the environment unchanged. -/
theorem TwinOK.frame {A : List ArrId} {C : List Word} {m m' : Mem} {a : AState}
    (hf : MemFrame A C m m') (hA : (50 : ArrId) ∉ A ∧ (49 : ArrId) ∉ A)
    (hC : (50 : Word) ∉ C ∧ (48 : Word) ∉ C)
    (hWA : (151 : ArrId) ∉ A ∧ (152 : ArrId) ∉ A ∧ (153 : ArrId) ∉ A)
    (hWC : (152 : Word) ∉ C ∧ (154 : Word) ∉ C ∧ (156 : Word) ∉ C)
    (hLA : (52 : ArrId) ∉ A ∧ (53 : ArrId) ∉ A ∧ (54 : ArrId) ∉ A)
    (hLC : (54 : Word) ∉ C ∧ (56 : Word) ∉ C ∧ (58 : Word) ∉ C)
    (h : TwinOK dn m a fe) : TwinOK dn m' a fe :=
  ⟨h.readL, h.readLs, h.nwf, by rw [hf.2.2.1]; exact h.erec, by rw [hf.2.2.1]; exact h.spn,
    h.memos.frame hf hA hC hWA hWC hLA hLC, by rw [hf.2.2.1]; exact h.bstk, h.den.mem m'⟩

/-- `TwinOK` across a writer of `PT0`, arrays from 256 on and `CTL` words below 48 or in 60‥127
only (the bracket's). -/
theorem TwinOK.frameLo {A : List ArrId} {C : List Word} {m m' : Mem} {a : AState}
    (hf : MemFrame A C m m') (hA : ∀ b ∈ A, b = 62 ∨ 256 ≤ b)
    (hC : ∀ x ∈ C, x.toNat < 48 ∨ (60 ≤ x.toNat ∧ x.toNat < 128))
    (h : TwinOK dn m a fe) : TwinOK dn m' a fe := by
  have n : ∀ k : Word, 48 ≤ k.toNat → k.toNat < 60 ∨ 128 ≤ k.toNat → k ∉ C := fun k h1 h2 hk => by
    have := hC k hk; omega
  have na : ∀ b : ArrId, b ≠ 62 → b < 256 → b ∉ A := fun b h1 h2 hb => by
    have := hA b hb; simp only [ArrId] at *; omega
  exact h.frame hf ⟨na 50 (by decide) (by decide), na 49 (by decide) (by decide)⟩
    ⟨n 50 (by decide) (by decide), n 48 (by decide) (by decide)⟩
    ⟨na 151 (by decide) (by decide), na 152 (by decide) (by decide), na 153 (by decide) (by decide)⟩
    ⟨n 152 (by decide) (by decide), n 154 (by decide) (by decide), n 156 (by decide) (by decide)⟩
    ⟨na 52 (by decide) (by decide), na 53 (by decide) (by decide), na 54 (by decide) (by decide)⟩
    ⟨n 54 (by decide) (by decide), n 56 (by decide) (by decide), n 58 (by decide) (by decide)⟩

end frames

theorem pinW_frame {A : List ArrId} {C : List Word} {m m' : Mem} (hf : MemFrame A C m m')
    (hP : PINS ∉ A) : pinW m' 0 = pinW m 0 := by
  simp only [pinW, hf.1 PINS hP (by decide)]


/-! ## The twin's half of `TwinOK` from the fold's invariant

Every part of `TwinOK` that speaks of the twin state alone follows from con-ron's fold invariant
(`FoldOK`, which `TwinFold` carries at every loop head): the readback caches from `CacheOK`, the name
store's well-formedness from `StateOK`, the stored levels' readbacks from the store's
well-formedness (a handle with a view denotes: con-ron's `denoteL_of_view`), the pins' from
`PinsOK`, the environment's level parameters and recursor levels from `IFEnvOK.hit`. What is left
is the memory's half (`TwinMem`: three sizes, the core's memos) and the record decoder's agreement
with the name store (`dnN`). The projection tables' readbacks are the environment's tables'
(`StoreDen.proj`, lane `loopt2`), from `IFEnvOK.tblHit`. -/

/-- **The memory's half of `TwinOK`**, and the name decoder's agreement with the store. -/
structure TwinMem (dn : NIdx → Option ConLeche.Name) (m : Mem) (a : AState) : Prop where
  erec : (m.arr64 EREC).size < 2 ^ 63
  spn : (m.arr64 SPN).size < 2 ^ 63
  bstk : (m.arr64 145).size < 2 ^ 63
  memos : CoreMemos m
  dnN : ∀ (k : NIdx) (x : ConLeche.Name), dn k = some x → denoteN a.store.ns k = some x

/-- The memory's half of a `TwinOK`. -/
theorem TwinOK.mem {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState} {fe : IFEnv}
    (h : TwinOK dn m a fe) : TwinMem dn m a :=
  ⟨h.erec, h.spn, h.bstk, h.memos, h.den.dnN⟩

/-- **The memory's half across a step** that grows the name store (every old name keeps its
readback), keeps the arrays' sizes and the core memos. -/
theorem TwinMem.step {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a a' : AState}
    (h : TwinMem dn m a)
    (hN : ∀ (k : NIdx) (x : ConLeche.Name), denoteN a.store.ns k = some x →
      denoteN a'.store.ns k = some x)
    (hsz : ∀ b, (m'.arr64 b).size = (m.arr64 b).size) (hmem : CoreMemos m') :
    TwinMem dn m' a' :=
  ⟨by rw [hsz]; exact h.erec, by rw [hsz]; exact h.spn, by rw [hsz]; exact h.bstk, hmem,
    fun k x e => hN k x (h.dnN k x e)⟩

theorem denoteNList_mapM {st : NStore} :
    ∀ {l : List NIdx} {xs : List ConLeche.Name}, ConRon.Arena.Frontend.denoteNList st l = some xs →
      l.mapM (denoteN st) = some xs
  | [], xs, h => by simp [ConRon.Arena.Frontend.denoteNList] at h; subst h; rfl
  | c :: cs, xs, h => by
    simp only [ConRon.Arena.Frontend.denoteNList] at h
    cases h1 : denoteN st c with
    | none => rw [h1] at h; simp at h
    | some x =>
      cases h2 : ConRon.Arena.Frontend.denoteNList st cs with
      | none => rw [h1, h2] at h; simp at h
      | some ys =>
        rw [h1, h2] at h
        simp only [Option.some.injEq] at h
        subst h
        simp [List.mapM_cons, h1, denoteNList_mapM h2]

theorem denoteCV_lps {st : EStore} {cv : IConstantVal} {c : ConLeche.ConstantVal}
    (h : ConRon.Arena.Frontend.denoteCV st cv = some c) :
    ∃ ks, cv.levelParams.mapM (denoteN st.ns) = some ks := by
  simp only [ConRon.Arena.Frontend.denoteCV] at h
  cases h2 : ConRon.Arena.Frontend.denoteNList st.ns cv.levelParams with
  | none => rw [h2] at h; split at h <;> simp_all
  | some ks => exact ⟨ks, denoteNList_mapM h2⟩

theorem denoteLList_mem {ls : LStore} :
    ∀ {us : List LIdx} {xs : List ConLeche.Level}, denoteLList ls us = some xs →
      ∀ u ∈ us, ∃ L, denoteL ls u = some L
  | [], _, _, u, hu => absurd hu (by simp)
  | v :: vs, xs, h, u, hu => by
    simp only [denoteLList, opt2_eq_some_iff] at h
    obtain ⟨a, b, ha, hb, -⟩ := h
    rcases List.mem_cons.mp hu with rfl | hu
    · exact ⟨a, ha⟩
    · exact denoteLList_mem hb u hu

theorem denoteRules_mem {st : EStore} :
    ∀ {rs : List IRecRule} {xs : List ConLeche.RecRule},
      ConRon.Arena.Frontend.denoteRules st rs = some xs →
      ∀ r ∈ rs, ∀ lvls pins, r.fire = .nested lvls pins → ∀ u ∈ lvls, ∃ L, denoteL st.ls u = some L
  | [], _, _, r, hr, _, _, _, _, _ => absurd hr (by simp)
  | q :: qs, xs, h, r, hr, lvls, pins, hf, u, hu => by
    simp only [ConRon.Arena.Frontend.denoteRules] at h
    cases h1 : ConRon.Arena.Frontend.denoteRule st q with
    | none => rw [h1] at h; simp at h
    | some y =>
      cases h2 : ConRon.Arena.Frontend.denoteRules st qs with
      | none => rw [h1, h2] at h; simp at h
      | some ys =>
        rcases List.mem_cons.mp hr with rfl | hr
        · simp only [ConRon.Arena.Frontend.denoteRule, hf, ConRon.Arena.Frontend.denoteFire] at h1
          cases h3 : denoteLList st.ls lvls with
          | none => rw [h3] at h1; split at h1 <;> simp_all
          | some ls => exact denoteLList_mem h3 u hu
        · exact denoteRules_mem h2 r hr lvls pins hf u hu

/-- A denoting projection table's structure sort, guards and level parameters read back. -/
theorem denoteProjTable_parts {st : EStore} {t : IProjTable} {pt : ConLeche.ProjTable}
    (h : ConRon.Arena.Frontend.denoteProjTable st t = some pt) :
    (∃ l, denoteL st.ls t.structSort = some l) ∧
    (∃ gs, denoteLList st.ls t.guards = some gs) ∧
    (∃ ks, ConRon.Arena.Frontend.denoteNList st.ns t.levelParams = some ks) := by
  unfold ConRon.Arena.Frontend.denoteProjTable at h
  cases h1 : denoteN st.ns t.structName <;>
    cases h2 : ConRon.Arena.Frontend.denoteNList st.ns t.levelParams <;>
    cases h3 : denoteN st.ns t.ctor <;> simp only [h1, h2, h3] at h <;> try cases h
  cases h4 : denoteL st.ls t.structSort <;>
    cases h5 : ConRon.Arena.Frontend.denoteEArray st t.bodies <;>
    cases h6 : denoteLList st.ls t.guards <;> simp only [h4, h5, h6] at h <;> try cases h
  exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩⟩

theorem denoteCI_cv {st : EStore} {ci : IConstantInfo} {d : ConLeche.ConstantInfo}
    (hd : ConRon.Arena.Frontend.denoteCI st ci = some d) :
    ∃ y, ConRon.Arena.Frontend.denoteCV st ci.toConstantVal = some y := by
  cases ci with
  | axiomInfo v =>
    simp only [ConRon.Arena.Frontend.denoteCI, Option.map_eq_some_iff] at hd
    obtain ⟨y, hy, -⟩ := hd; exact ⟨y, hy⟩
  | thmInfo v =>
    simp only [ConRon.Arena.Frontend.denoteCI, Option.map_eq_some_iff] at hd
    obtain ⟨y, hy, -⟩ := hd; exact ⟨y, hy⟩
  | ctorInfo v _ _ =>
    simp only [ConRon.Arena.Frontend.denoteCI, Option.map_eq_some_iff] at hd
    obtain ⟨y, hy, -⟩ := hd; exact ⟨y, hy⟩
  | defnInfo v _ _ =>
    simp only [ConRon.Arena.Frontend.denoteCI] at hd
    split at hd
    · rename_i y _ hy _; exact ⟨y, hy⟩
    · cases hd
  | indInfo v _ =>
    simp only [ConRon.Arena.Frontend.denoteCI] at hd
    split at hd
    · rename_i y _ hy _; exact ⟨y, hy⟩
    · cases hd
  | recInfo v _ _ _ =>
    simp only [ConRon.Arena.Frontend.denoteCI] at hd
    split at hd
    · rename_i y _ hy _; exact ⟨y, hy⟩
    · cases hd

/-- **`TwinOK` from con-ron's check invariant** (`CheckOK`: the store's well-formedness, the
caches, the pins, the environment index) and the memory's half. Every point of a step where
con-ron's bridge lemmas give `CheckOK` (they carry it across the twin's operations) has `TwinOK`
once the memory's half is kept. -/
theorem TwinOK.of_check {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState} {fe : IFEnv}
    {env : ConLeche.Env} (hok : ConRon.Bridge.CheckOK .verified env fe a) (hm : TwinMem dn m a) :
    TwinOK dn m a fe := by
  have hwf := hok.state.wf
  obtain ⟨rk, hw⟩ := hwf
  have hw' : StoreWF' a.store := StoreWF'.of_wf ⟨rk, hw⟩
  obtain ⟨rk', hw''⟩ := hw'
  have hLs : LsStoreWF' a.store.lss := hw''.lss
  have hL : LStoreWF' a.store.ls := hLs.ls
  have hc := hok.caches
  have hp := hok.pins
  have hi := hok.ienv
  refine ⟨hc.readL, hc.readLs, hw.nsWF, hm.erec, hm.spn, hm.memos, hm.bstk, ?_⟩
  refine ⟨fun x u hv => ?_, fun x c us hv => ?_, ⟨_, hp.zeroLevel⟩, ⟨_, hp.emptyLevels⟩, hc.readN,
    fun c ci hf => ?_, fun c tbl hf => ?_, fun u hu => ConRon.Bridge.denoteL_of_view hL hu,
    fun us hus => ?_, hm.dnN, fun c cv mI rP rules hf r hr lvls pins hfi u hu => ?_⟩
  · exact ConRon.Bridge.denoteL_of_view hL (hw.lchildOK x _ hv u (by simp [ENodeView.lchildren])).1
  · have hs := (hw.lschildOK x _ hv us (by simp [ENodeView.lschildren])).1
    obtain ⟨vs, hvs⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨xs, hxs⟩ := ConRon.Bridge.denoteLs_of_view hLs hvs
    exact ⟨xs, by simp only [denoteLs, hvs]; exact hxs⟩
  · obtain ⟨-, d, -, hd, -⟩ := hi.hit c ci hf
    obtain ⟨y, hy⟩ := denoteCI_cv hd
    exact denoteCV_lps hy
  · obtain ⟨-, pt, -, hpt, -, htok⟩ := hi.tblHit c tbl hf
    obtain ⟨hss, ⟨gs, hgs⟩, ⟨ks, hks⟩⟩ := denoteProjTable_parts hpt
    have hlen := htok.guards
    refine ⟨hss, fun i hi' => denoteLList_mem hgs _ ?_, ⟨ks, denoteNList_mapM hks⟩⟩
    have hlt : i < tbl.guards.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
    exact List.getElem_mem hlt
  · obtain ⟨vs, hvs⟩ := Option.isSome_iff_exists.mp hus
    obtain ⟨xs, hxs⟩ := ConRon.Bridge.denoteLs_of_view hLs hvs
    exact ⟨xs, by simp only [denoteLs, hvs]; exact hxs⟩
  · obtain ⟨-, d, -, hd, -⟩ := hi.hit c _ hf
    simp only [ConRon.Arena.Frontend.denoteCI] at hd
    cases h2 : ConRon.Arena.Frontend.denoteRules a.store rules with
    | none => rw [h2] at hd; split at hd <;> simp_all
    | some ys => exact denoteRules_mem h2 r hr lvls pins hfi u hu


/-- **`TwinOK` across a twin step that grows the store**: the new store well formed, the old one
extended (`Ext`), the caches and the pins unchanged; the memory's sizes and core memos given. -/
theorem TwinOK.of_grow {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a a' : AState}
    {fe : IFEnv} (h : TwinOK dn m a fe) (hwf : StoreWF a'.store) (hx : Ext a.store a'.store)
    (hc : a'.caches = a.caches) (hp : a'.pins = a.pins)
    (hE : (m'.arr64 EREC).size < 2 ^ 63) (hS : (m'.arr64 SPN).size < 2 ^ 63)
    (hB : (m'.arr64 145).size < 2 ^ 63) (hM : CoreMemos m') : TwinOK dn m' a' fe := by
  obtain ⟨rk, hw⟩ := hwf
  have hw' : StoreWF' a'.store := StoreWF'.of_wf ⟨rk, hw⟩
  obtain ⟨rk', hw''⟩ := hw'
  have hLs : LsStoreWF' a'.store.lss := hw''.lss
  have hL : LStoreWF' a'.store.ls := hLs.ls
  have hN : ∀ i n, denoteN a.store.ns i = some n → denoteN a'.store.ns i = some n :=
    hx.lss.ls.ns
  have hNs : ∀ (l : List NIdx) ks, l.mapM (denoteN a.store.ns) = some ks →
      l.mapM (denoteN a'.store.ns) = some ks := by
    intro l; induction l with
    | nil => intro ks h; simpa using h
    | cons x xs ih =>
      intro ks h
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h ⊢
      obtain ⟨y, hy, ys, hys, rfl⟩ := h
      exact ⟨y, hN _ _ hy, ys, ih _ hys, rfl⟩
  have hLv : ∀ u l, denoteL a.store.ls u = some l → denoteL a'.store.ls u = some l :=
    hx.lss.ls.lvl
  refine ⟨fun k l hk => ?_, fun k l hk => ?_, hw.nsWF, hE, hS, hM, hB, ?_⟩
  · rw [hc] at hk; exact hLv _ _ (h.readL k l hk)
  · rw [hc] at hk; exact hx.lss.lst _ _ (h.readLs k l hk)
  refine ⟨fun x u hv => ?_, fun x c us hv => ?_, ?_, ?_, fun k x hk => ?_,
    fun c ci hf => ?_, fun c tbl hf => ?_, fun u hu => ConRon.Bridge.denoteL_of_view hL hu,
    fun us hus => ?_, fun k x e => hN _ _ (h.den.dnN k x e),
    fun c cv mI rP rules hf r hr lvls pins hfi u hu => ?_⟩
  · exact ConRon.Bridge.denoteL_of_view hL (hw.lchildOK x _ hv u (by simp [ENodeView.lchildren])).1
  · have hs := (hw.lschildOK x _ hv us (by simp [ENodeView.lschildren])).1
    obtain ⟨vs, hvs⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨xs, hxs⟩ := ConRon.Bridge.denoteLs_of_view hLs hvs
    exact ⟨xs, by simp only [denoteLs, hvs]; exact hxs⟩
  · obtain ⟨l, hl⟩ := h.den.zero; exact ⟨l, by rw [hp]; exact hLv _ _ hl⟩
  · obtain ⟨l, hl⟩ := h.den.emptyLs; exact ⟨l, by rw [hp]; exact hx.lss.lst _ _ hl⟩
  · rw [hc] at hk; exact hN _ _ (h.den.readN k x hk)
  · obtain ⟨ks, hks⟩ := h.den.constLps c ci hf; exact ⟨ks, hNs _ _ hks⟩
  · obtain ⟨⟨l, hl⟩, hg, ⟨ks, hks⟩⟩ := h.den.proj c tbl hf
    exact ⟨⟨l, hLv _ _ hl⟩, fun i hi => (hg i hi).elim fun l hl => ⟨l, hLv _ _ hl⟩,
      ⟨ks, hNs _ _ hks⟩⟩
  · obtain ⟨vs, hvs⟩ := Option.isSome_iff_exists.mp hus
    obtain ⟨xs, hxs⟩ := ConRon.Bridge.denoteLs_of_view hLs hvs
    exact ⟨xs, by simp only [denoteLs, hvs]; exact hxs⟩
  · obtain ⟨L, hL'⟩ := h.den.recRules c cv mI rP rules hf r hr lvls pins hfi u hu
    exact ⟨L, hLv _ _ hL'⟩

/-- **`TwinOK` across a twin step con-ron's `IStepS` describes** (an interning-only operation from
a well-formed store: `internName_sstep`, `internExprGo_sstep`, `internCIList_sstep`, …). -/
theorem TwinOK.of_istep {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a a' : AState}
    {fe : IFEnv} (h : TwinOK dn m a fe) (hs : ConRon.Bridge.Frontend.IStepS a a')
    (hE : (m'.arr64 EREC).size < 2 ^ 63) (hS : (m'.arr64 SPN).size < 2 ^ 63)
    (hB : (m'.arr64 145).size < 2 ^ 63) (hM : CoreMemos m') : TwinOK dn m' a' fe :=
  h.of_grow hs.ok.wf hs.ext hs.caches hs.pins hE hS hB hM

end L.Arena

namespace L.Ind

open L.Arena

/-- **`StageT` and the twin store's well-formedness** (con-ron's `StateOK`): the relation on
stretches of interning without a core call. -/
structure StageS (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m : Mem)
    (a : AState) : Prop where
  stageT : StageT dn vis fe m a
  ok : ConRon.Bridge.StateOK a

/-- **`StageS` across an interning step**: the step's stage relation after it, the twin step's
`IStepS`, the memory's sizes, core memos and pin flag kept. -/
theorem StageS.of_istep {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {m m' : Mem} {a a' : AState} (h : StageS dn vis fe m a) (hS : StageR dn vis fe m' a')
    (hs : ConRon.Bridge.Frontend.IStepS a a')
    (hsz : ∀ b, (m'.arr64 b).size = (m.arr64 b).size) (hM : CoreMemos m')
    (hP : pinW m' 0 = pinW m 0) : StageS dn vis fe m' a' :=
  ⟨⟨hS, h.stageT.twin.of_istep hs (by rw [hsz]; exact h.stageT.twin.erec)
      (by rw [hsz]; exact h.stageT.twin.spn) (by rw [hsz]; exact h.stageT.twin.bstk) hM,
    by rw [hP]; exact h.stageT.flag⟩, hs.ok⟩

/-- **The stage relation with con-ron's check invariant** (`CheckOK` at the denoted environment
`env`) and the memory's half of `TwinOK`: what carries the twin's invariants across operations
whose `TwinOK` the L side cannot track (store growth after a core call); `TwinOK` from it by
`TwinOK.of_check` (`StageC.stageT`). -/
structure StageC (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m : Mem) (a : AState) : Prop where
  stage : StageR dn vis fe m a
  check : ConRon.Bridge.CheckOK .verified env fe a
  mem : TwinMem dn m a
  flag : pinW m 0 ≠ 0

theorem StageC.stageT {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {env : ConLeche.Env} {m : Mem} {a : AState} (h : StageC dn vis fe env m a) :
    StageT dn vis fe m a :=
  ⟨h.stage, TwinOK.of_check h.check h.mem, h.flag⟩

end L.Ind
