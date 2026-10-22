import ConAgua.Arena.EnvRec
import ConAgua.Arena.Tiers
import ConAgua.Arena.ArenaRel
import ConRon.Arena.Core

/-!
# Stored levels read back: the invariant the knot's level readers need (lane `defeq2`)

The twin compares and substitutes levels on their **readbacks** (`readLevelM`, `readLevelsM`,
`readNamesM`, `denoteL`/`denoteLs`/`denoteN`), and a readback of a dangling handle fails. L works
on the handles themselves and never reads back (deviation D13), so an L run that succeeds refines
the twin's only where the handles L compares do read back. Which handles those are:

* a `sort` node's level (`quick_sort`, `proof_irrel`, `PropRead`'s `residualPW`);
* a `const` node's level list (`spine_cmp`, `struct_eta_cert_tail`, `PropRead`'s `substPWAt`);
* the pinned zero level (`proof_irrel`, `infer_proj`) and empty level list (`constE`);
* the names in the twin's name readback cache (`readNC`: `readNameM` answers a hit unchecked;
  `field_sort_zero`, `PropRead`);
* a stored constant's level-parameter names (`PropRead`'s `substPWAt`);
* a projection table's structure sort, its fields' sorts and its level parameters
  (`infer_proj`), read from the table records in `EREC` (`decTbl`).

`StoreDen m a fe` states all six. **It is meant as one field of `CoreS`** (`CoreS.den`, the twin's
store being well formed: `StoreWF` gives the first four, the environment loader the fifth);
until that field exists the knot takes `CoreDen` (`DefEqKnot.lean`) as a hypothesis.

Maintenance, when it is a field: the twin's store only grows inside the core (`Ext`), so an old
handle keeps its readback; the two clauses over node views need a proof only where a `sort` or a
`const` node is interned (its level or list came from a node that reads back, or was built from
ones that do); `zero`, `constLps` and `proj` follow from `Ext` and from `EREC` being kept; `readN` where the
name cache is written (`readNameM`, which caches a readback).
-/

open ConRon.Arena

namespace L.Arena

/-- **Stored levels read back** (see the module note). -/
structure StoreDen (m : Mem) (a : AState) (fe : IFEnv) : Prop where
  sort : ∀ (h : EIdx) (u : LIdx), a.store.view h = some (.sort u) →
    ∃ l, denoteL a.store.ls u = some l
  constLs : ∀ (h : EIdx) (c : NIdx) (us : LsIdx), a.store.view h = some (.const c us) →
    ∃ ls, denoteLs a.store.lss us = some ls
  zero : ∃ l, denoteL a.store.ls a.pins.zeroLevel = some l
  /-- The pinned empty level list (`constE`'s). -/
  emptyLs : ∃ ls, denoteLs a.store.lss a.pins.emptyLevels = some ls
  readN : ∀ (h : NIdx) (x : ConLeche.Name), a.caches.readNC[h]? = some x →
    denoteN a.store.ns h = some x
  /-- A stored constant's level-parameter names read back (`PropRead`'s `substPWAt`). -/
  constLps : ∀ (c : NIdx) (ci : IConstantInfo) (cv : IConstantVal), fe.find? c = some ci →
    ci.isTowerEntry = false → (∀ s, ci.toConstantVal.run s = .ok (cv, s)) →
    ∃ ks, cv.levelParams.mapM (denoteN a.store.ns) = some ks
  /-- A projection table record's levels read back. -/
  proj : ∀ (q : Nat) (tbl : IProjTable), decTbl (m.arr64 EREC) q = some tbl →
    (∃ l, denoteL a.store.ls tbl.structSort = some l) ∧
    (∀ i, i < tbl.numFields → ∃ l, denoteL a.store.ls (tbl.guards.getD i default) = some l) ∧
    (∃ ks, tbl.levelParams.mapM (denoteN a.store.ns) = some ks)

/-! ## Keeping `StoreDen` -/

/-- The `sort` and `const` tables (and the scratch flag): what `StoreDen`'s view clauses read. -/
def scTabs (a : AState) :=
  (a.store.scratchOn, a.store.pers.sorts.nodes, a.store.scr.sorts.nodes, a.store.pers.consts.nodes,
    a.store.scr.consts.nodes)

theorem get_sort_iff (t : ETables) (x : EIdx) (u : LIdx) :
    t.get x = some (.sort u) ↔ x.tag = ETag.sort ∧ (t.sorts.nodes[x.idxNat]?).map SortNode.u = some u := by
  unfold ETables.get Tbl.node?
  by_cases ht : x.tag = ETag.sort
  · simp [ht, ETag.sort, ETag.bvar, ETag.fvar]
  · simp only [ht, false_and, iff_false]
    repeat' split
    all_goals first | (exfalso; exact ht (beq_iff_eq.mp ‹_›)) | simp

theorem get_const_iff (t : ETables) (x : EIdx) (c : NIdx) (us : LsIdx) :
    t.get x = some (.const c us) ↔
      x.tag = ETag.const ∧ (t.consts.nodes[x.idxNat]?).map (fun r => (r.n, r.us)) = some (c, us) := by
  unfold ETables.get Tbl.node?
  by_cases ht : x.tag = ETag.const
  · simp [ht, ETag.sort, ETag.bvar, ETag.fvar, ETag.const]
  · simp only [ht, false_and, iff_false]
    repeat' split
    all_goals first | (exfalso; exact ht (beq_iff_eq.mp ‹_›)) | simp

theorem view_sort_keep {a a' : AState} (h : scTabs a' = scTabs a) {x : EIdx} {u : LIdx}
    (hv : a'.store.view x = some (.sort u)) : a.store.view x = some (.sort u) := by
  simp only [scTabs, Prod.mk.injEq] at h
  obtain ⟨h0, h1, h2, -, -⟩ := h
  unfold EStore.view at hv ⊢
  rw [h0] at hv
  split at hv
  · rw [if_pos (by assumption), get_sort_iff] at *; rw [← h1]; exact hv
  · rw [if_neg (by assumption)]
    split at hv
    · rw [if_pos (by assumption), get_sort_iff] at *; rw [← h2]; exact hv
    · cases hv

theorem view_const_keep {a a' : AState} (h : scTabs a' = scTabs a) {x : EIdx} {c : NIdx}
    {us : LsIdx} (hv : a'.store.view x = some (.const c us)) : a.store.view x = some (.const c us) := by
  simp only [scTabs, Prod.mk.injEq] at h
  obtain ⟨h0, -, -, h3, h4⟩ := h
  unfold EStore.view at hv ⊢
  rw [h0] at hv
  split at hv
  · rw [if_pos (by assumption), get_const_iff] at *; rw [← h3]; exact hv
  · rw [if_neg (by assumption)]
    split at hv
    · rw [if_pos (by assumption), get_const_iff] at *; rw [← h4]; exact hv
    · cases hv

/-- A tier's nodes are determined by the memory, when the record relation is. -/
theorem nodes_eq_of_tierR {α δ : Type} {k : IdxKind} [BEq α] [Hashable α] {S : Schema}
    {R : Mem → Word → Word → α → Prop} {hs : Mem → Word → Word → Word} {m m' : Mem} {t : Word}
    {tb tb' : Tbl α (Idx k) δ} (hT : TierR S R hs m t tb) (hT' : TierR S R hs m' t tb')
    (hc : cntW S m' t = cntW S m t) (hinj : ∀ (i : Word) x y, R m t i x → R m' t i y → x = y) :
    tb'.nodes = tb.nodes := by
  have hsz : tb'.nodes.size = tb.nodes.size := by rw [← hT.1, ← hT'.1, hc]
  apply Array.ext hsz
  intro i h1 h2
  have hlt : i < 2 ^ 64 := by have := hT.2.1; omega
  have e : (i.toUInt64).toNat = i := by simp; omega
  have g1 : tb.nodes[(i.toUInt64).toNat]? = some tb.nodes[i] := by rw [e]; simp [h2]
  have g2 : tb'.nodes[(i.toUInt64).toNat]? = some tb'.nodes[i] := by rw [e]; simp [h1]
  exact (hinj _ _ _ (hT.2.2.2.1 _ _ g1) (hT'.2.2.2.1 _ _ g2)).symm

theorem word_toUInt64_inj {k : IdxKind} {x y : Idx k} (h : x.word.toUInt64 = y.word.toUInt64) :
    x = y := by
  cases x; cases y; simp only [Idx.ofWord.injEq]
  exact UInt32.toUInt64_inj.mp h

/-- **The `sort` and `const` tables are determined by their memory**: under `ArenaR` at both
states, equal `SOREC`/`CREC`, equal counts `CTL[16‥19]` and scratch flag `CTL[1]` give equal
tables. -/
theorem scTabs_eq {m m' : Mem} {a a' : AState} (hR : ArenaR m a) (hR' : ArenaR m' a')
    (hs : m'.arr64 SOREC = m.arr64 SOREC) (hc : m'.arr64 CREC = m.arr64 CREC)
    (hctl : ∀ x : Word, x = 1 ∨ x = 16 ∨ x = 17 ∨ x = 18 ∨ x = 19 →
      rdW (m'.arr64 CTL) x = rdW (m.arr64 CTL) x) :
    scTabs a' = scTabs a := by
  have hon : a'.store.scratchOn = a.store.scratchOn := by
    have h1 := hR.sort.2.1; have h2 := hR'.sort.2.1
    rw [← h1, ← h2, hctl 1 (.inl rfl)]
  have hsi : ∀ (t i : Word) x y, SoRecRel m t i x → SoRecRel m' t i y → x = y := by
    intro t i x y h1 h2
    simp only [SoRecRel, hs] at h1 h2
    cases x; cases y; simp only [SortNode.mk.injEq]
    exact word_toUInt64_inj (h1.symm.trans h2)
  have hci : ∀ (t i : Word) x y, CeRecRel m t i x → CeRecRel m' t i y → x = y := by
    intro t i x y h1 h2
    simp only [CeRecRel, hc] at h1 h2
    cases x; cases y; simp only [ConstNode.mk.injEq]
    exact ⟨word_toUInt64_inj (h1.1.symm.trans h2.1), word_toUInt64_inj (h1.2.symm.trans h2.2)⟩
  simp only [scTabs, Prod.mk.injEq]
  refine ⟨hon, nodes_eq_of_tierR hR.sort.2.2.1 hR'.sort.2.2.1 ?_ (hsi 0),
    nodes_eq_of_tierR hR.sort.2.2.2 hR'.sort.2.2.2 ?_ (hsi 1),
    nodes_eq_of_tierR hR.const.2.2.1 hR'.const.2.2.1 ?_ (hci 0),
    nodes_eq_of_tierR hR.const.2.2.2 hR'.const.2.2.2 ?_ (hci 1)⟩
  · exact hctl _ (by simp [sortSch])
  · exact hctl _ (by simp [sortSch])
  · exact hctl _ (by simp [constSch])
  · exact hctl _ (by simp [constSch])

/-- **`StoreDen` across a step** that extends the level stores, keeps the zero pin and `EREC`,
caches only readbacks of names, and creates no new `sort`/`const` views. -/
theorem StoreDen.mono {m m' : Mem} {a a' : AState} {fe : IFEnv} (h : StoreDen m a fe)
    (hx : LsExt a.store.lss a'.store.lss) (hz : a'.pins.zeroLevel = a.pins.zeroLevel)
    (hzs : a'.pins.emptyLevels = a.pins.emptyLevels)
    (hr : ∀ (k : NIdx) (x : ConLeche.Name), a'.caches.readNC[k]? = some x →
      a.caches.readNC[k]? = some x ∨ denoteN a'.store.ns k = some x)
    (he : m'.arr64 EREC = m.arr64 EREC)
    (hs : ∀ x u, a'.store.view x = some (.sort u) → a.store.view x = some (.sort u))
    (hc : ∀ x c us, a'.store.view x = some (.const c us) → a.store.view x = some (.const c us)) :
    StoreDen m' a' fe := by
  have hN : ∀ i n, denoteN a.store.ns i = some n → denoteN a'.store.ns i = some n := hx.ls.ns
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
  refine ⟨fun x u hv => ?_, fun x c us hv => ?_, ?_, ?_, fun k x hk => ?_,
    fun c ci cv hf ht hcv => ?_, fun q tbl ht => ?_⟩
  · obtain ⟨l, hl⟩ := h.sort x u (hs x u hv); exact ⟨l, hx.ls.lvl _ _ hl⟩
  · obtain ⟨l, hl⟩ := h.constLs x c us (hc x c us hv); exact ⟨l, hx.lst _ _ hl⟩
  · obtain ⟨l, hl⟩ := h.zero; exact ⟨l, by rw [hz]; exact hx.ls.lvl _ _ hl⟩
  · obtain ⟨l, hl⟩ := h.emptyLs; exact ⟨l, by rw [hzs]; exact hx.lst _ _ hl⟩
  · rcases hr k x hk with h' | h'
    · exact hN _ _ (h.readN k x h')
    · exact h'
  · obtain ⟨ks, hks⟩ := h.constLps c ci cv hf ht hcv; exact ⟨ks, hNs _ _ hks⟩
  · rw [he] at ht
    obtain ⟨⟨l, hl⟩, hg, ⟨ks, hks⟩⟩ := h.proj q tbl ht
    exact ⟨⟨l, hx.ls.lvl _ _ hl⟩, fun i hi => (hg i hi).elim fun l hl => ⟨l, hx.ls.lvl _ _ hl⟩,
      ⟨ks, hNs _ _ hks⟩⟩

/-- **`StoreDen` across an interning step** that keeps the caches, the pins and the level stores
(`cpl`) and writes neither `EREC` nor the `sort`/`const` tables (`SOREC`, `CREC`, `CTL` 1, 16‥19). -/
theorem StoreDen.of_arena {m m' : Mem} {a a' : AState} {fe : IFEnv} {A : List ArrId} {C : List Word}
    (h : StoreDen m a fe) (hR : ArenaR m a) (hR' : ArenaR m' a') (hc : a'.caches = a.caches)
    (hp : a'.pins = a.pins) (hl : a'.store.lss = a.store.lss) (hf : MemFrame A C m m')
    (heA : EREC ∉ A) (hscA : SOREC ∉ A ∧ CREC ∉ A)
    (hscC : (1 : Word) ∉ C ∧ (16 : Word) ∉ C ∧ (17 : Word) ∉ C ∧ (18 : Word) ∉ C ∧ (19 : Word) ∉ C) :
    StoreDen m' a' fe := by
  have hsc : scTabs a' = scTabs a := scTabs_eq hR hR' (hf.1 SOREC hscA.1 (by decide))
    (hf.1 CREC hscA.2 (by decide)) (fun x hx => hf.2.1 x (by
      rcases hx with rfl | rfl | rfl | rfl | rfl <;>
        first | exact hscC.1 | exact hscC.2.1 | exact hscC.2.2.1 | exact hscC.2.2.2.1 | exact hscC.2.2.2.2))
  exact h.mono (by rw [hl]; exact LsExt.refl _) (by rw [hp]) (by rw [hp]) (fun _ _ hk => .inl (hc ▸ hk))
    (hf.1 EREC heA (by decide)) (fun _ _ hv => view_sort_keep hsc hv)
    (fun _ _ _ hv => view_const_keep hsc hv)

/-- `StoreDen` across a memory step that keeps `EREC` (the twin unchanged). -/
theorem StoreDen.frameE {m m' : Mem} {a : AState} {fe : IFEnv} (h : StoreDen m a fe)
    (he : m'.arr64 EREC = m.arr64 EREC) : StoreDen m' a fe :=
  h.mono (LsExt.refl _) rfl rfl (fun _ _ hk => .inl hk) he (fun _ _ hv => hv) (fun _ _ _ hv => hv)

/-- `StoreDen` across a step that changes only the twin's caches other than `readNC`. -/
theorem StoreDen.caches {m : Mem} {a a' : AState} {fe : IFEnv} (h : StoreDen m a fe)
    (hst : a'.store = a.store) (hp : a'.pins = a.pins) (hn : a'.caches.readNC = a.caches.readNC) :
    StoreDen m a' fe :=
  h.mono (by rw [hst]; exact LsExt.refl _) (by rw [hp]) (by rw [hp]) (fun _ _ hk => .inl (hn ▸ hk))
    rfl
    (fun _ _ hv => hst ▸ hv) (fun _ _ _ hv => hst ▸ hv)

end L.Arena
