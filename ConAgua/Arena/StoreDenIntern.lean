import ConAgua.Arena.StoreDen

/-!
# `StoreDen` across the interning of a `sort` or a `const` node (lane `defeq2`)

Interning `v` either finds it (the state unchanged) or pushes it onto one tier's table of `v`'s
kind: a `sort` or `const` view of the new state is an old view or `v` itself. With `v`'s level
(list) reading back, `StoreDen` carries over (`StoreDen.of_internSort`, `StoreDen.of_internConst`).
-/

open ConRon.Arena

namespace L.Arena

/-- A `sort`/`const` view of a tier after a push: an old one or the pushed view. -/
theorem push_get_sc (t : ETables) (v : ENodeView) (d : UInt64) (tier : UInt32) (x : EIdx)
    (w : ENodeView) (hw : (∃ u, w = .sort u) ∨ (∃ c us, w = .const c us))
    (h : (t.push v d tier).1.get x = some w) : t.get x = some w ∨ w = v := by
  rcases hw with ⟨u, rfl⟩ | ⟨c, us, rfl⟩
  · rw [get_sort_iff] at h ⊢
    obtain ⟨ht, hn⟩ := h
    cases v <;> simp only [ETables.push, Tbl.push] at hn <;>
      first
      | exact .inl ⟨ht, hn⟩
      | (rw [Array.getElem?_push] at hn
         split at hn
         · right; subst_vars; simp at hn ⊢; exact hn.symm
         · exact .inl ⟨ht, hn⟩)
  · rw [get_const_iff] at h ⊢
    obtain ⟨ht, hn⟩ := h
    cases v <;> simp only [ETables.push, Tbl.push] at hn <;>
      first
      | exact .inl ⟨ht, hn⟩
      | (rw [Array.getElem?_push] at hn
         split at hn
         · right; subst_vars; simp at hn ⊢; obtain ⟨h1, h2⟩ := hn; exact ⟨h1.symm, h2.symm⟩
         · exact .inl ⟨ht, hn⟩)

/-- A `sort`/`const` view after `EStore.intern v`: an old one or `v`. -/
theorem intern_view_sc (st : EStore) (v : ENodeView) (x : EIdx) (w : ENodeView)
    (hw : (∃ u, w = .sort u) ∨ (∃ c us, w = .const c us))
    (h : (st.intern v).1.view x = some w) : st.view x = some w ∨ w = v := by
  unfold EStore.intern at h
  split at h
  · exact .inl h
  · split at h
    · rename_i hon
      split at h
      · exact .inl h
      · simp only [EStore.view] at h ⊢
        by_cases hp : x.isPersistent = true
        · rw [if_pos hp] at h ⊢; exact .inl h
        · rw [if_neg hp] at h ⊢; rw [if_pos hon] at h ⊢
          exact push_get_sc _ _ _ _ _ _ hw h
    · rename_i hon
      simp only [EStore.view] at h ⊢
      by_cases hp : x.isPersistent = true
      · rw [if_pos hp] at h ⊢; exact push_get_sc _ _ _ _ _ _ hw h
      · rw [if_neg hp] at h ⊢; rw [if_neg hon] at h; cases h

/-- A `sort`/`const` view after a successful `internNodeE v`: an old one or `v`; the caches, the
pins and the level stores are kept. -/
theorem internNodeE_sc {v : ENodeView} {a a' : AState} {r : EIdx}
    (hrun : (internNodeE v).run a = .ok (r, a')) :
    a'.caches = a.caches ∧ a'.pins = a.pins ∧ a'.store.lss = a.store.lss ∧
      ∀ x w, ((∃ u, w = .sort u) ∨ (∃ c us, w = .const c us)) →
        a'.store.view x = some w → a.store.view x = some w ∨ w = v := by
  simp only [internNodeE, StateT.run_bind, StateT.run_get, pure_bind] at hrun
  repeat' split at hrun
  all_goals simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
    ConRon.Arena.fail, throwThe, MonadExceptOf.throw] at hrun
  all_goals first
    | (cases hrun; exact ⟨rfl, rfl, rfl, fun x w _ hv => .inl hv⟩)
    | (cases hrun
       exact ⟨rfl, rfl, EStore.lss_intern _ _, fun x w hw hv => intern_view_sc _ _ x w hw hv⟩)
    | (simp [throwThe, Functor.map, Except.map] at hrun)

/-- **`StoreDen` across interning `sort u`**, `u` reading back. -/
theorem StoreDen.of_internSort {m m' : Mem} {a a' : AState} {fe : IFEnv} {u : LIdx} {r : EIdx}
    (h : StoreDen m a fe) (hu : ∃ l, denoteL a.store.ls u = some l)
    (hrun : (internE (.sort u)).run a = .ok (r, a')) (he : m'.arr64 EREC = m.arr64 EREC) :
    StoreDen m' a' fe := by
  obtain ⟨hc, hp, hl, hv⟩ := internNodeE_sc (v := .sort u) (by simpa [internE] using hrun)
  have hls : a'.store.ls = a.store.ls := by simp only [EStore.ls, hl]
  refine ⟨fun x u' hx => ?_, fun x c us hx => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases hv x _ (.inl ⟨_, rfl⟩) hx with h' | h'
    · rw [hls]; exact h.sort x u' h'
    · cases h'; rw [hls]; exact hu
  · rcases hv x _ (.inr ⟨_, _, rfl⟩) hx with h' | h'
    · rw [hl]; exact h.constLs x c us h'
    · cases h'
  · rw [hp, hls]; exact h.zero
  · rw [hp, hl]; exact h.emptyLs
  · intro k x hk; rw [hc] at hk; have := h.readN k x hk
    simp only [EStore.ns, EStore.ls, hl] at this ⊢; exact this
  · intro c ci cv hf ht hcv; have := h.constLps c ci cv hf ht hcv
    simp only [EStore.ns, EStore.ls, hl] at this ⊢; exact this
  · intro q tbl ht; rw [he] at ht; have := h.proj q tbl ht
    simp only [EStore.ns, EStore.ls, hl] at this ⊢; exact this

/-- **`StoreDen` across interning `const c us`**, `us` reading back. -/
theorem StoreDen.of_internConst {m m' : Mem} {a a' : AState} {fe : IFEnv} {c : NIdx} {us : LsIdx}
    {r : EIdx} (h : StoreDen m a fe) (hus : ∃ ls, denoteLs a.store.lss us = some ls)
    (hrun : (internE (.const c us)).run a = .ok (r, a')) (he : m'.arr64 EREC = m.arr64 EREC) :
    StoreDen m' a' fe := by
  obtain ⟨hc, hp, hl, hv⟩ := internNodeE_sc (v := .const c us) (by simpa [internE] using hrun)
  have hls : a'.store.ls = a.store.ls := by simp only [EStore.ls, hl]
  refine ⟨fun x u' hx => ?_, fun x c' us' hx => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases hv x _ (.inl ⟨_, rfl⟩) hx with h' | h'
    · rw [hls]; exact h.sort x u' h'
    · cases h'
  · rcases hv x _ (.inr ⟨_, _, rfl⟩) hx with h' | h'
    · rw [hl]; exact h.constLs x c' us' h'
    · cases h'; rw [hl]; exact hus
  · rw [hp, hls]; exact h.zero
  · rw [hp, hl]; exact h.emptyLs
  · intro k x hk; rw [hc] at hk; have := h.readN k x hk
    simp only [EStore.ns, EStore.ls, hl] at this ⊢; exact this
  · intro c ci cv hf ht hcv; have := h.constLps c ci cv hf ht hcv
    simp only [EStore.ns, EStore.ls, hl] at this ⊢; exact this
  · intro q tbl ht; rw [he] at ht; have := h.proj q tbl ht
    simp only [EStore.ns, EStore.ls, hl] at this ⊢; exact this

end L.Arena
