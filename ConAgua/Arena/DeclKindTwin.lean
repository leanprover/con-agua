module

public import ConAgua.Arena.TwinStep
public import ConAgua.Arena.DeclKindEnv

@[expose] public section

/-!
# `TwinOK` after a declaration's own checks and the cache flush

`checkDecl`'s reserved names' check runs at the environment `fe'` the kind's check returned,
with the caches flushed. `TwinOK.of_kind`: from `TwinOK` at the record's start (environment
`fe`), the store well formed and extended, the caches empty, the pins the same, the memory's
sizes and core memos, and `fe'` growing `fe` by `EnvGrowDen` (`DeclKindEnv.lean`), `TwinOK` at
`fe'`.
-/

namespace L.Arena

open ConRon.Arena

theorem TwinOK.of_kind {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a a' : AState}
    {fe fe' : IFEnv} (h : TwinOK dn m a fe) (hwf : StoreWF a'.store) (hx : Ext a.store a'.store)
    (hc : a'.caches = Caches.empty) (hp : a'.pins = a.pins)
    (hE : (m'.arr64 EREC).size < 2 ^ 63) (hS : (m'.arr64 SPN).size < 2 ^ 63)
    (hB : (m'.arr64 BSTK).size < 2 ^ 63) (hM : CoreMemos m') (hg : EnvGrowDen a'.store fe fe') :
    TwinOK dn m' a' fe' := by
  obtain ⟨rk, hw⟩ := hwf
  have hLs : LsStoreWF a'.store.lss := hw.lss
  have hL : LStoreWF a'.store.ls := hLs.ls
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
  · rw [hc] at hk; simp [Caches.empty] at hk
  · rw [hc] at hk; simp [Caches.empty] at hk
  refine ⟨fun x u hv => ?_, fun x c us hv => ?_, ?_, ?_, fun k x hk => ?_,
    fun c ci hf => ?_, fun c tbl hf => ?_, fun u hu => denoteL_of_viewW hL hu,
    fun us hus => ?_, fun k x e => hN _ _ (h.den.dnN k x e),
    fun c cv mI rP isK rules hf r hr lvls pins hfi u hu => ?_,
    fun c cv mI rP isK rules hf r hr lvls hfi u hu => ?_⟩
  · exact denoteL_of_viewW hL (hw.lchildOK x _ hv u (by simp [ENodeView.lchildren])).1
  · have hs := (hw.lschildOK x _ hv us (by simp [ENodeView.lschildren])).1
    obtain ⟨vs, hvs⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨xs, hxs⟩ := denoteLs_of_viewW hLs hvs
    exact ⟨xs, by simp only [denoteLs, hvs]; exact hxs⟩
  · rw [hp]; exact hLv _ _ h.den.zero
  · obtain ⟨l, hl⟩ := h.den.emptyLs; exact ⟨l, by rw [hp]; exact hx.lss.lst _ _ hl⟩
  · rw [hc] at hk; simp [Caches.empty] at hk
  · rcases hg.find c ci hf with hf | hd
    · obtain ⟨ks, hks⟩ := h.den.constLps c ci hf; exact ⟨ks, hNs _ _ hks⟩
    · exact hd.1
  · rcases hg.tbl c tbl hf with hf | hd
    · obtain ⟨ks, hks⟩ := h.den.proj c tbl hf; exact ⟨ks, hNs _ _ hks⟩
    · exact hd
  · obtain ⟨vs, hvs⟩ := Option.isSome_iff_exists.mp hus
    obtain ⟨xs, hxs⟩ := denoteLs_of_viewW hLs hvs
    exact ⟨xs, by simp only [denoteLs, hvs]; exact hxs⟩
  · rcases hg.find c _ hf with hf | hd
    · obtain ⟨L, hL'⟩ := h.den.recRules c cv mI rP isK rules hf r hr lvls pins hfi u hu
      exact ⟨L, hLv _ _ hL'⟩
    · exact (hd.2 cv mI rP isK rules rfl r hr).1 lvls pins hfi u hu
  · rcases hg.find c _ hf with hf | hd
    · obtain ⟨L, hL'⟩ := h.den.recLevels c cv mI rP isK rules hf r hr lvls hfi u hu
      exact ⟨L, hLv _ _ hL'⟩
    · exact (hd.2 cv mI rP isK rules rfl r hr).2 lvls hfi u hu

end L.Arena
