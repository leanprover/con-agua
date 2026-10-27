import ConAgua.Arena.StoreDen
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Interned levels read back (lane `defeq2`)

`LvlAll` (every valid level handle reads back) across `internLNode`, and the readback of an
interned level list across `internLsNode`. A cons-table hit names a node with the probed view
(under `ArenaR`, the tables' `ConsR.cons_hitP`/`cons_hitS`); a push appends a node whose view is the interned
one and raises the node count, so the new handle reads back through its children, and old handles
keep their readbacks (`LExt`).
-/

open ConRon.Arena

namespace L.Arena

set_option linter.unusedSimpArgs false in
/-- **Under `ArenaR`, a level cons hit names a node with the probed view.** -/
theorem lview_of_find {m : Mem} {a : AState} (hR : ArenaR m a) {v : LNodeView} {i : LIdx}
    (hf : a.store.ls.find? v = some i) : a.store.ls.view i = some v := by
  simp only [EStore.ls, LStore.find?] at hf ⊢
  split at hf
  · rename_i j hp
    cases hf
    cases v <;> simp only [LTables.find?, Tbl.find?] at hp
    · obtain ⟨hn, htag, hpers⟩ := ConsR.cons_hitP zeroCS_wf hR.zero hp
      simp [LStore.view, hpers, LTables.get, htag, Tbl.node?, hn, zeroCS, zeroSch, LTag.zero, LTag.succ,
        LTag.max, LTag.imax, LTag.param]
    · obtain ⟨hn, htag, hpers⟩ := ConsR.cons_hitP succCS_wf hR.succ hp
      simp [LStore.view, hpers, LTables.get, htag, Tbl.node?, hn, succCS, succSch, LTag.zero, LTag.succ,
        LTag.max, LTag.imax, LTag.param]
    · obtain ⟨hn, htag, hpers⟩ := ConsR.cons_hitP maxCS_wf hR.max hp
      simp [LStore.view, hpers, LTables.get, htag, Tbl.node?, hn, maxCS, maxSch, LTag.zero, LTag.succ,
        LTag.max, LTag.imax, LTag.param]
    · obtain ⟨hn, htag, hpers⟩ := ConsR.cons_hitP imaxCS_wf hR.imax hp
      simp [LStore.view, hpers, LTables.get, htag, Tbl.node?, hn, imaxCS, imaxSch, LTag.zero, LTag.succ,
        LTag.max, LTag.imax, LTag.param]
    · obtain ⟨hn, htag, hpers⟩ := ConsR.cons_hitP paramCS_wf hR.param hp
      simp [LStore.view, hpers, LTables.get, htag, Tbl.node?, hn, paramCS, paramSch, LTag.zero, LTag.succ,
        LTag.max, LTag.imax, LTag.param]
  · by_cases hon : a.store.lss.ls.scratchOn = true
    · simp only [hon, ↓reduceIte] at hf
      cases v <;> simp only [LTables.find?, Tbl.find?] at hf
      · obtain ⟨hn, htag, hpers⟩ := ConsR.cons_hitS zeroCS_wf hR.zero hf
        simp [LStore.view, hpers, LTables.get, htag, Tbl.node?, hn, zeroCS, zeroSch, LTag.zero, LTag.succ,
          LTag.max, LTag.imax, LTag.param, hon]
      · obtain ⟨hn, htag, hpers⟩ := ConsR.cons_hitS succCS_wf hR.succ hf
        simp [LStore.view, hpers, LTables.get, htag, Tbl.node?, hn, succCS, succSch, LTag.zero, LTag.succ,
          LTag.max, LTag.imax, LTag.param, hon]
      · obtain ⟨hn, htag, hpers⟩ := ConsR.cons_hitS maxCS_wf hR.max hf
        simp [LStore.view, hpers, LTables.get, htag, Tbl.node?, hn, maxCS, maxSch, LTag.zero, LTag.succ,
          LTag.max, LTag.imax, LTag.param, hon]
      · obtain ⟨hn, htag, hpers⟩ := ConsR.cons_hitS imaxCS_wf hR.imax hf
        simp [LStore.view, hpers, LTables.get, htag, Tbl.node?, hn, imaxCS, imaxSch, LTag.zero, LTag.succ,
          LTag.max, LTag.imax, LTag.param, hon]
      · obtain ⟨hn, htag, hpers⟩ := ConsR.cons_hitS paramCS_wf hR.param hf
        simp [LStore.view, hpers, LTables.get, htag, Tbl.node?, hn, paramCS, paramSch, LTag.zero, LTag.succ,
          LTag.max, LTag.imax, LTag.param, hon]
    · simp [hon] at hf

/-! ## A push onto the level store -/

theorem Tbl.nodes_push' {α ι δ : Type} [BEq α] [Hashable α] (tb : Tbl α ι δ) (a : α) (d : δ)
    (i : ι) : (tb.push a d i).nodes = tb.nodes.push a := by
  cases tb; rfl

theorem LTables.count_push (t : LTables) (v : LNodeView) (d : LDer) (tr : UInt32) :
    (t.push v d tr).1.count = t.count + 1 := by
  cases v <;> simp [LTables.push, LTables.count, Tbl.nodes_push', Tbl.size] <;> omega

/-- A view of a tier after a push: an old one or the pushed view. -/
theorem LTables.push_get_cases (t : LTables) (v : LNodeView) (d : LDer) (tr : UInt32) (u : LIdx)
    (w : LNodeView) (h : (t.push v d tr).1.get u = some w) : t.get u = some w ∨ w = v := by
  cases v <;> simp only [LTables.push, LTables.get, Tbl.nodes_push', Tbl.node?] at h ⊢ <;>
    repeat' split at h
  all_goals simp only [*, ↓reduceIte, Bool.false_eq_true, true_or]
  all_goals first
    | exact .inl h
    | (rw [Array.getElem?_push] at h
       split at h
       · right; simp at h; exact h.symm
       · exact .inl h)

/-- **Interning a level node**: every view of the new store is an old one or the interned one. -/
theorem LStore.intern_view_cases (st : LStore) (v : LNodeView) (u : LIdx) (w : LNodeView)
    (h : (st.intern v).1.view u = some w) : st.view u = some w ∨ w = v := by
  unfold LStore.intern at h
  split at h
  · exact .inl h
  · split at h
    · rename_i hon
      split at h
      · exact .inl h
      · simp only [LStore.view] at h ⊢
        by_cases hp : u.isPersistent = true
        · rw [ite_eq_left hp] at h ⊢; exact .inl h
        · rw [ite_eq_right hp] at h ⊢; rw [ite_eq_left hon] at h ⊢
          exact LTables.push_get_cases _ _ _ _ _ _ h
    · rename_i hon
      simp only [LStore.view] at h ⊢
      by_cases hp : u.isPersistent = true
      · rw [ite_eq_left hp] at h ⊢; exact LTables.push_get_cases _ _ _ _ _ _ h
      · rw [ite_eq_right hp] at h ⊢; rw [ite_eq_right hon] at h; cases h

/-- On a miss (with room), the new level handle has the interned view and the node count goes up
by one. -/
theorem LStore.intern_miss {st : LStore} {v : LNodeView} (hf : st.find? v = none)
    (hcap : st.capOK v) :
    (st.intern v).1.view (st.intern v).2 = some v ∧
      (st.intern v).1.nodeCount = st.nodeCount + 1 := by
  simp only [LStore.capOK] at hcap
  simp only [LStore.find?] at hf
  split at hf
  · cases hf
  · rename_i hp
    simp only [LStore.intern, hp]
    by_cases hon : st.scratchOn = true
    · simp only [hon, ↓reduceIte] at hf hcap ⊢
      simp only [hf]
      have hspec := LTables.push_spec st.scr v (st.derOfView v) Idx.tierS (by decide) hcap
      have hpp : ((st.scr.push v (st.derOfView v) Idx.tierS).2).isPersistent = false := by
        show (_ == 0) = false
        rw [hspec.2]; decide
      refine ⟨?_, ?_⟩
      · simp only [LStore.view, hpp]; exact hspec.1
      · simp only [LStore.nodeCount, LStore.persCount, LStore.scrCount, LTables.count_push]
        omega
    · simp only [hon, Bool.false_eq_true, ↓reduceIte] at hcap ⊢
      have hspec := LTables.push_spec st.pers v (st.derOfView v) Idx.tierP (by decide) hcap
      have hpp : ((st.pers.push v (st.derOfView v) Idx.tierP).2).isPersistent = true := by
        show (_ == 0) = true
        rw [hspec.2]; decide
      refine ⟨?_, ?_⟩
      · simp only [LStore.view, hpp]; exact hspec.1
      · simp only [LStore.nodeCount, LStore.persCount, LStore.scrCount, LTables.count_push]
        omega

/-- A handle whose view's children read back (at the store's node count) reads back. -/
theorem denoteL_of_view {st : LStore} {u : LIdx} {v : LNodeView} (hv : st.view u = some v)
    (hch : ∀ c ∈ v.lchildren, ∃ l, denoteLAux st st.nodeCount c = some l)
    (hn : ∀ n ∈ v.nchildren, ∃ x, denoteN st.ns n = some x) : ∃ l, denoteL st u = some l := by
  simp only [denoteL, denoteLAux, hv, Option.bind_some]
  cases v <;> simp only [LNodeView.lchildren, LNodeView.nchildren, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hch hn
  · exact ⟨_, rfl⟩
  · obtain ⟨l, hl⟩ := hch; exact ⟨_, by simp [hl]; rfl⟩
  · obtain ⟨⟨l1, h1⟩, l2, h2⟩ := hch; exact ⟨_, by simp [h1, h2, opt2]; rfl⟩
  · obtain ⟨⟨l1, h1⟩, l2, h2⟩ := hch; exact ⟨_, by simp [h1, h2, opt2]; rfl⟩
  · obtain ⟨x, hx⟩ := hn; exact ⟨_, by simp [hx]; rfl⟩

/-! ## `internLNode` -/

/-- `internLNode`'s two outcomes: a cons hit (the state unchanged) or `LStore.intern`'s push. -/
theorem internLNode_run_cases {a a' : AState} {v : LNodeView} {h : LIdx}
    (hrun : (internLNode v).run a = .ok (h, a')) :
    (a.store.ls.find? v = some h ∧ a' = a) ∨
      (a.store.ls.find? v = none ∧ a.store.ls.capOK v ∧ a'.store.ls = (a.store.ls.intern v).1 ∧
        h = (a.store.ls.intern v).2) := by
  unfold internLNode at hrun
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hrun
  split at hrun
  · rename_i hf
    simp only [StateT.run_pure] at hrun
    cases hrun
    exact .inl ⟨hf, rfl⟩
  · rename_i hf
    by_cases hcap : a.store.ls.capOK v
    · have hc := hcap
      simp only [LStore.capOK] at hc
      simp only [hc, ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
        at hrun
      cases hrun
      exact .inr ⟨hf, hcap, rfl, rfl⟩
    · have hc := hcap
      simp only [LStore.capOK] at hc
      simp [hc, fail, throwThe, MonadExceptOf.throw, StateT.run, StateT.lift, bind, Except.bind]
        at hrun

/-- **Interning a level node keeps every level handle reading back, and the new handle reads
back**, when the node's children do. `ArenaR` is used only at a cons hit (the hit names a node
with the probed view). -/
theorem lvlAll_internLNode {m : Mem} {a a' : AState} {v : LNodeView} {h : LIdx}
    (hR : ArenaR m a) (hall : LvlAll a)
    (hch : ∀ c ∈ v.lchildren, ∃ l, denoteL a.store.ls c = some l)
    (hnch : ∀ n ∈ v.nchildren, ∃ x, denoteN a.store.ls.ns n = some x)
    (hrun : (internLNode v).run a = .ok (h, a')) :
    LvlAll a' ∧ ∃ l, denoteL a'.store.ls h = some l := by
  rcases internLNode_run_cases hrun with ⟨hf, rfl⟩ | ⟨hf, hcap, hls, rfl⟩
  · exact ⟨hall, hall h (by rw [lview_of_find hR hf]; rfl)⟩
  · obtain ⟨hv, hcnt⟩ := LStore.intern_miss hf hcap
    have hext := LStore.intern_ext a.store.ls v
    have key : ∀ u, (a.store.ls.intern v).1.view u = some v →
        ∃ l, denoteL (a.store.ls.intern v).1 u = some l := by
      intro u hu
      refine denoteL_of_view hu (fun c hc => ?_) (fun n hn => ?_)
      · obtain ⟨l, hl⟩ := hch c hc
        rw [hcnt]
        exact ⟨l, denoteLAux_store_mono (fun _ _ hh => LStore.view_intern_mono _ v hh)
          (LStore.ns_intern _ v) _ c l hl⟩
      · rw [LStore.ns_intern]; exact hnch n hn
    refine ⟨fun u hu => ?_, by rw [hls]; exact key _ hv⟩
    change (a'.store.ls.view u).isSome at hu
    rw [hls] at hu ⊢
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hu
    rcases LStore.intern_view_cases _ v u w hw with ho | rfl
    · obtain ⟨l, hl⟩ := hall u (by rw [ho]; rfl)
      exact ⟨l, hext.lvl u l hl⟩
    · exact key u hw

/-- `internLNode` extends the level store. -/
theorem internLNode_lext {a a' : AState} {v : LNodeView} {h : LIdx}
    (hrun : (internLNode v).run a = .ok (h, a')) : LExt a.store.lss.ls a'.store.lss.ls := by
  rcases internLNode_run_cases hrun with ⟨-, rfl⟩ | ⟨-, -, hls, -⟩
  · exact LExt.refl _
  · change LExt a.store.ls a'.store.ls
    rw [hls]; exact LStore.intern_ext _ v

/-- An extension that adds no level views beyond readable ones keeps `LvlAll`. -/
theorem LvlAll.of_lext {a a' : AState} (hall : LvlAll a)
    (hv : ∀ u, (a'.store.ls.view u).isSome → (a.store.ls.view u).isSome)
    (he : LExt a.store.lss.ls a'.store.lss.ls) : LvlAll a' :=
  fun u hu => (hall u (hv u hu)).imp fun _ hl => he.lvl u _ hl

/-! ## `internLsNode` -/

/-- **Under `ArenaR`, a level-list cons hit names a node with the probed view.** -/
theorem lsview_of_find {m : Mem} {a : AState} (hR : ArenaR m a) {v : LsNodeView} {i : LsIdx}
    (hf : a.store.lss.find? v = some i) : a.store.lss.view i = some v := by
  simp only [LsStore.find?] at hf
  split at hf
  · rename_i j hp
    cases hf
    simp only [LsTables.find?, Tbl.find?] at hp
    obtain ⟨hn, htag, hpers⟩ := ConsR.cons_hitP lsCS_wf hR.ls hp
    simp [LsStore.view, hpers, LsTables.get, htag, Tbl.node?, hn, lsCS, LsTag.list]
  · by_cases hon : a.store.lss.scratchOn = true
    · simp only [hon, ↓reduceIte, LsTables.find?, Tbl.find?] at hf
      obtain ⟨hn, htag, hpers⟩ := ConsR.cons_hitS lsCS_wf hR.ls hf
      simp [LsStore.view, hpers, LsTables.get, htag, Tbl.node?, hn, lsCS, LsTag.list, hon]
    · simp [hon] at hf

/-- On a miss (with room), the new level-list handle has the interned view. -/
theorem LsStore.intern_miss {st : LsStore} {v : LsNodeView} (hf : st.find? v = none)
    (hcap : st.capOK v) : (st.intern v).1.view (st.intern v).2 = some v := by
  simp only [LsStore.capOK] at hcap
  simp only [LsStore.find?] at hf
  split at hf
  · cases hf
  · rename_i hp
    simp only [LsStore.intern, hp]
    by_cases hon : st.scratchOn = true
    · simp only [hon, ↓reduceIte] at hf hcap ⊢
      simp only [hf]
      have hspec := LsTables.push_spec st.scr v (st.derOfView v) Idx.tierS (by decide) hcap
      have hpp : ((st.scr.push v (st.derOfView v) Idx.tierS).2).isPersistent = false := by
        show (_ == 0) = false
        rw [hspec.2]; decide
      simp only [LsStore.view, hpp]; exact hspec.1
    · simp only [hon, Bool.false_eq_true, ↓reduceIte] at hcap ⊢
      have hspec := LsTables.push_spec st.pers v (st.derOfView v) Idx.tierP (by decide) hcap
      have hpp : ((st.pers.push v (st.derOfView v) Idx.tierP).2).isPersistent = true := by
        show (_ == 0) = true
        rw [hspec.2]; decide
      simp only [LsStore.view, hpp]; exact hspec.1

/-- `internLsNode`'s two outcomes: a cons hit (the state unchanged) or `LsStore.intern`'s push. -/
theorem internLsNode_run_cases {a a' : AState} {v : LsNodeView} {h : LsIdx}
    (hrun : (internLsNode v).run a = .ok (h, a')) :
    (a.store.lss.find? v = some h ∧ a' = a) ∨
      (a.store.lss.find? v = none ∧ a.store.lss.capOK v ∧
        a'.store.lss = (a.store.lss.intern v).1 ∧ h = (a.store.lss.intern v).2) := by
  unfold internLsNode at hrun
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hrun
  split at hrun
  · rename_i hf
    simp only [StateT.run_pure] at hrun
    cases hrun
    exact .inl ⟨hf, rfl⟩
  · rename_i hf
    by_cases hcap : a.store.lss.capOK v
    · have hc := hcap
      simp only [LsStore.capOK] at hc
      simp only [hc, ↓reduceIte, StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind]
        at hrun
      cases hrun
      exact .inr ⟨hf, hcap, rfl, rfl⟩
    · have hc := hcap
      simp only [LsStore.capOK] at hc
      simp [hc, fail, throwThe, MonadExceptOf.throw, StateT.run, StateT.lift, bind, Except.bind]
        at hrun

theorem denoteLList_of_all {st : LStore} :
    ∀ (us : List LIdx), (∀ c ∈ us, ∃ l, denoteL st c = some l) →
      ∃ ls, denoteLList st us = some ls
  | [], _ => ⟨[], rfl⟩
  | u :: us, h => by
    obtain ⟨l, hl⟩ := h u (by simp)
    obtain ⟨ls, hls⟩ := denoteLList_of_all us (fun c hc => h c (by simp [hc]))
    exact ⟨l :: ls, by simp [denoteLList, hl, hls, opt2]⟩

/-- **Interning a level list all of whose elements read back gives a handle that reads back**,
and extends the level-list store (old list handles keep their readbacks). `ArenaR` is used only
at a cons hit. -/
theorem denoteLs_internLsNode {m : Mem} {a a' : AState} {v : LsNodeView} {h : LsIdx}
    (hR : ArenaR m a) (hel : ∀ c ∈ v, ∃ l, denoteL a.store.ls c = some l)
    (hrun : (internLsNode v).run a = .ok (h, a')) :
    (∃ ls, denoteLs a'.store.lss h = some ls) ∧ LsExt a.store.lss a'.store.lss := by
  obtain ⟨ls, hls⟩ := denoteLList_of_all v hel
  rcases internLsNode_run_cases hrun with ⟨hf, rfl⟩ | ⟨hf, hcap, hss, rfl⟩
  · refine ⟨⟨ls, ?_⟩, LsExt.refl _⟩
    rw [denoteLs, lsview_of_find hR hf]; exact hls
  · rw [hss]
    refine ⟨⟨ls, ?_⟩, LsStore.intern_ext _ v⟩
    rw [denoteLs, LsStore.intern_miss hf hcap, LsStore.ls_intern]; exact hls

end L.Arena
