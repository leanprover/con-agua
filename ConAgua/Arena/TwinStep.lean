import ConAgua.Arena.IndTwin
import ConRon.Bridge.Promote.Walk
import ConRon.Bridge.Frontend.Shared

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
    fun c ci cv hf ht hcv => ?_, fun c tbl hf => ?_, fun u hu => ConRon.Bridge.denoteL_of_view hL hu,
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
  · obtain ⟨ks, hks⟩ := h.den.constLps c ci cv hf ht hcv; exact ⟨ks, hNs _ _ hks⟩
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

end L.Ind
