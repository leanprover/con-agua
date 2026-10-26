import ConAgua.Arena.StoreDen
import ConAgua.Arena.Keeps

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
        · rw [ite_eq_left hp] at h ⊢; exact .inl h
        · rw [ite_eq_right hp] at h ⊢; rw [ite_eq_left hon] at h ⊢
          exact push_get_sc _ _ _ _ _ _ hw h
    · rename_i hon
      simp only [EStore.view] at h ⊢
      by_cases hp : x.isPersistent = true
      · rw [ite_eq_left hp] at h ⊢; exact push_get_sc _ _ _ _ _ _ hw h
      · rw [ite_eq_right hp] at h ⊢; rw [ite_eq_right hon] at h; cases h

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

/-! ## Forward: `sort`/`const` views survive an interning -/

/-- A `sort` or `const` view. -/
def IsSC (w : ENodeView) : Prop := (∃ u, w = .sort u) ∨ (∃ c us, w = .const c us)

theorem push_get_fwd (t : ETables) (v : ENodeView) (d : UInt64) (tier : UInt32) (x : EIdx)
    (w : ENodeView) (hw : IsSC w) (h : t.get x = some w) : (t.push v d tier).1.get x = some w := by
  rcases hw with ⟨u, rfl⟩ | ⟨c, us, rfl⟩
  · rw [get_sort_iff] at h ⊢
    obtain ⟨ht, hn⟩ := h
    refine ⟨ht, ?_⟩
    cases v <;> simp only [ETables.push, Tbl.push] <;>
      first
      | exact hn
      | (rw [Array.getElem?_push]
         have hlt : x.idxNat < t.sorts.nodes.size := by
           rcases e : t.sorts.nodes[x.idxNat]? with _ | _ <;> simp_all
           exact (Array.getElem?_eq_some_iff.mp e).1
         rw [ite_eq_right (Nat.ne_of_lt hlt)]; exact hn)
  · rw [get_const_iff] at h ⊢
    obtain ⟨ht, hn⟩ := h
    refine ⟨ht, ?_⟩
    cases v <;> simp only [ETables.push, Tbl.push] <;>
      first
      | exact hn
      | (rw [Array.getElem?_push]
         have hlt : x.idxNat < t.consts.nodes.size := by
           rcases e : t.consts.nodes[x.idxNat]? with _ | _ <;> simp_all
           exact (Array.getElem?_eq_some_iff.mp e).1
         rw [ite_eq_right (Nat.ne_of_lt hlt)]; exact hn)

theorem intern_view_fwd (st : EStore) (v : ENodeView) (x : EIdx) (w : ENodeView) (hw : IsSC w)
    (h : st.view x = some w) : (st.intern v).1.view x = some w := by
  unfold EStore.intern
  split
  · exact h
  · split
    · rename_i hon
      split
      · exact h
      · simp only [EStore.view] at h ⊢
        by_cases hp : x.isPersistent = true
        · rw [ite_eq_left hp] at h ⊢; exact h
        · rw [ite_eq_right hp] at h ⊢; rw [ite_eq_left hon] at h ⊢
          exact push_get_fwd _ _ _ _ _ _ hw h
    · rename_i hon
      simp only [EStore.view] at h ⊢
      by_cases hp : x.isPersistent = true
      · rw [ite_eq_left hp] at h ⊢; exact push_get_fwd _ _ _ _ _ _ hw h
      · rw [ite_eq_right hp] at h ⊢; rw [ite_eq_right hon] at h; cases h

/-- **`sort`/`const` views survive a successful `internNodeE`.** -/
theorem internNodeE_fwd {v : ENodeView} {a a' : AState} {r : EIdx}
    (hrun : (internNodeE v).run a = .ok (r, a')) :
    ∀ x w, IsSC w → a.store.view x = some w → a'.store.view x = some w := by
  simp only [internNodeE, StateT.run_bind, StateT.run_get, pure_bind] at hrun
  repeat' split at hrun
  all_goals simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
    ConRon.Arena.fail, throwThe, MonadExceptOf.throw] at hrun
  all_goals first
    | (cases hrun; exact fun x w _ hv => hv)
    | (cases hrun; exact fun x w hw hv => intern_view_fwd _ _ x w hw hv)
    | (simp [throwThe, Functor.map, Except.map] at hrun)

/-- The views survive the `.proj` spine of a structure eta. -/
theorem projNodesGo_fwd (T : NIdx) (b : EIdx) :
    ∀ (n j : Nat) (a a' : AState) (r : List EIdx), (projNodesGo T b n j).run a = .ok (r, a') →
      ∀ x w, IsSC w → a.store.view x = some w → a'.store.view x = some w := by
  intro n
  induction n with
  | zero =>
    intro j a a' r h
    rw [projNodesGo] at h
    change (Except.ok ([], a) : Except CheckError (List EIdx × AState)) = _ at h
    cases h; exact fun _ _ _ hv => hv
  | succ n ih =>
    intro j a a' r h x w hw hv
    rw [projNodesGo] at h
    simp only [StateT.run_bind] at h
    cases h1 : (internE (.proj T j b)).run a with
    | error e => rw [h1] at h; cases h
    | ok q =>
      obtain ⟨p1, a1⟩ := q
      rw [h1] at h
      change (do
        let p_1 ← StateT.run (projNodesGo T b n (j + 1)) a1
        StateT.run (pure (p1 :: p_1.fst)) p_1.snd) = _ at h
      cases h2 : (projNodesGo T b n (j + 1)).run a1 with
      | error e => rw [h2] at h; cases h
      | ok q2 =>
        obtain ⟨ps, a2⟩ := q2
        rw [h2] at h
        change (Except.ok (p1 :: ps, a2) : Except CheckError _) = _ at h
        cases h
        exact ih _ _ _ _ h2 x w hw
          (internNodeE_fwd (v := .proj T j b) (by simpa [internE] using h1) x w hw hv)

/-- The views survive `etaFabArgsE`. -/
theorem etaFabArgsE_fwd {T : NIdx} {targs : List EIdx} {major : EIdx} {nF : Nat} {a a' : AState}
    {r : List EIdx} (h : (etaFabArgsE T targs major nF).run a = .ok (r, a')) :
    ∀ x w, IsSC w → a.store.view x = some w → a'.store.view x = some w := by
  simp only [etaFabArgsE, etaProjs, StateT.run_bind] at h
  cases h1 : (projNodesGo T major nF 0).run a with
  | error e => rw [h1] at h; cases h
  | ok q =>
    obtain ⟨ps, a1⟩ := q
    rw [h1] at h; cases h
    exact projNodesGo_fwd T major nF 0 a a1 ps h1

/-! ## `towerSlotsAll` keeps the expression views

It interns name nodes only (`projTableName`), which leaves the expression tables alone: a
`const` node seen before the call is still there after it, so its level list still reads back
(`StoreDen.constLs` at the later state). -/

/-- The store without its level/name part (what `EStore.view` reads). -/
def noLss (a : AState) : EStore := { a.store with lss := LsStore.empty }

theorem view_of_noLss {a a' : AState} (h : noLss a' = noLss a) (x : EIdx) :
    a'.store.view x = a.store.view x := by
  have : (noLss a').view x = (noLss a).view x := by rw [h]
  exact this

theorem keeps_noLss_internNNode (v : NNodeView) : Keeps noLss (internNNode v) := by
  unfold Keeps; intro a r a' h
  simp only [internNNode, StateT.run_bind, StateT.run_get, pure_bind] at h
  repeat' split at h
  all_goals simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
    ConRon.Arena.fail, throwThe, MonadExceptOf.throw] at h
  all_goals first
    | (cases h; rfl)
    | (simp [throwThe, Functor.map, Except.map] at h)

/-- A view survives an operation that keeps the store minus its level part. -/
theorem view_after_noLss {α : Type} {op : AM α} (hk : Keeps noLss op) {a : AState} {x : EIdx}
    {v : ENodeView} (hv : a.store.view x = some v) : (AM.st op a).store.view x = some v := by
  unfold AM.st
  split
  · rename_i a' heq
    rw [view_of_noLss (Keeps.run hk heq)]; exact hv
  · exact hv

/-! ## Cache-only readers keep the store -/

/-- The store. -/
def stDenP (a : AState) : EStore := a.store

theorem keeps_stP_readLevelM (h : LIdx) : Keeps stDenP (readLevelM h) := by prim_keeps readLevelM
theorem keeps_stP_readNameM (h : NIdx) : Keeps stDenP (readNameM h) := by prim_keeps readNameM
theorem keeps_stP_readLevelsM (h : LsIdx) : Keeps stDenP (readLevelsM h) := by
  unfold Keeps; intro a r a' h'
  simp only [readLevelsM, StateT.run_bind, StateT.run_get, pure_bind] at h'
  repeat' split at h'
  all_goals simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind, failDanglingLs,
    ConRon.Arena.fail, throwThe, MonadExceptOf.throw] at h'
  all_goals first | (cases h'; rfl) | (simp [throwThe, Functor.map, Except.map] at h')
theorem keeps_stP_readNamesM : ∀ l : List NIdx, Keeps stDenP (readNamesM l)
  | [] => by rw [readNamesM]; exact Keeps.pure _
  | h :: hs => by
    rw [readNamesM]
    exact Keeps.bind (keeps_stP_readNameM h) fun _ =>
      Keeps.bind (keeps_stP_readNamesM hs) fun _ => Keeps.pure _
theorem keeps_stP_lvlEq? (u v : LIdx) : Keeps stDenP (lvlEq? u v) := by
  unfold lvlEq?
  refine Keeps.bind (by unfold Keeps; intro a r a' h; cases h; rfl) fun s => ?_
  split
  · exact Keeps.pure _
  · refine Keeps.bind (keeps_stP_readLevelM _) fun _ => Keeps.bind (keeps_stP_readLevelM _) fun _ => ?_
    split
    · unfold Keeps; intro a r a' h
      simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure, pure_bind] at h
      cases h; rfl
    · exact Keeps.pure _
theorem keeps_stP_zeroLevel : Keeps stDenP zeroLevel := by
  unfold zeroLevel; prim_keeps pinZeroLevel
theorem keeps_stP_fireOk (e : IProjEntry) (us : LsIdx) : Keeps stDenP (e.fireOk us) := by
  unfold IProjEntry.fireOk
  refine Keeps.bind keeps_stP_zeroLevel fun _ => Keeps.bind (keeps_stP_lvlEq? _ _) fun _ => ?_
  split
  · exact Keeps.pure _
  · exact Keeps.bind (keeps_stP_readNamesM _) fun _ => Keeps.bind (keeps_stP_readLevelsM _) fun _ =>
      Keeps.bind (keeps_stP_readLevelM _) fun _ => Keeps.pure _

theorem Keeps.noLss_of_stP {α : Type} {op : AM α} (h : Keeps stDenP op) : Keeps noLss op :=
  Keeps.map (fun st => ({ st with lss := LsStore.empty } : EStore)) h

theorem keeps_noLss_andRescueSlots (fe : IFEnv) (c : NIdx) (nP : Nat) (us : LsIdx) :
    Keeps noLss (andRescueSlots fe c nP us) := by
  unfold andRescueSlots
  refine Keeps.bind (by unfold pinAnd; prim_keeps pinAt) fun an => ?_
  suffices ∀ n j, Keeps noLss (andRescueSlotsGo fe an c nP us n j) from this _ _
  intro n
  induction n with
  | zero => intro j; rw [andRescueSlotsGo]; exact Keeps.pure _
  | succ n ih =>
    intro j; rw [andRescueSlotsGo]
    split
    · refine Keeps.bind (Keeps.noLss_of_stP (keeps_stP_fireOk _ _)) fun b => ?_
      split
      · exact ih _
      · exact Keeps.pure _
    · exact Keeps.pure _

/-- **`StoreDen` across a step that keeps the caches, the pins and the level stores** and creates
no new `sort`/`const` view (`hv`). -/
theorem StoreDen.of_views {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a a' : AState} {fe : IFEnv} (h : StoreDen dn m a fe)
    (hc : a'.caches = a.caches) (hp : a'.pins = a.pins) (hl : a'.store.lss = a.store.lss)
    (_he : m'.arr64 EREC = m.arr64 EREC)
    (hv : ∀ x w, IsSC w → a'.store.view x = some w → a.store.view x = some w) :
    StoreDen dn m' a' fe :=
  h.mono (by rw [hl]; exact LsExt.refl _) (by rw [hp]) (by rw [hp]) (fun _ _ hk => .inl (hc ▸ hk))
    (fun x u hx => hv x _ (.inl ⟨_, rfl⟩) hx) (fun x c us hx => .inl (hv x _ (.inr ⟨_, _, rfl⟩) hx))
    (h.lvlAll.congr (by simp only [EStore.ls, hl])) (h.lsAll.congr hl)

/-- Interning a node that is neither a `sort` nor a `const` creates no such view. -/
theorem internNodeE_views {v : ENodeView} (hv : ¬ IsSC v) {a a' : AState} {r : EIdx}
    (hrun : (internNodeE v).run a = .ok (r, a')) :
    ∀ x w, IsSC w → a'.store.view x = some w → a.store.view x = some w := by
  obtain ⟨-, -, -, h⟩ := internNodeE_sc hrun
  intro x w hw hx
  rcases h x w hw hx with h' | rfl
  · exact h'
  · exact absurd hw hv

/-- `internE v`, then a pure answer: no new `sort`/`const` view when `v` is neither (and not a
binder, `hn`). -/
theorem internE_pure_views {β : Type} {v : ENodeView} (hv : ¬ IsSC v)
    (hn : internE v = internNodeE v) (f : EIdx → β) {a a' : AState}
    {r : β} (hrun : (internE v >>= fun x => pure (f x)).run a = .ok (r, a')) :
    ∀ x w, IsSC w → a'.store.view x = some w → a.store.view x = some w := by
  simp only [StateT.run_bind] at hrun
  cases hq : (internE v).run a with
  | error e => rw [hq] at hrun; cases hrun
  | ok q =>
    obtain ⟨y, a1⟩ := q
    rw [hq] at hrun
    change (Except.ok (f y, a1) : Except CheckError _) = _ at hrun
    cases hrun
    rw [hn] at hq
    exact internNodeE_views hv hq

/-- **`StoreDen` across interning `sort u`**, `u` reading back. -/
theorem StoreDen.of_internSort {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a a' : AState} {fe : IFEnv} {u : LIdx} {r : EIdx}
    (h : StoreDen dn m a fe) (hu : ∃ l, denoteL a.store.ls u = some l)
    (hrun : (internE (.sort u)).run a = .ok (r, a')) (_he : m'.arr64 EREC = m.arr64 EREC) :
    StoreDen dn m' a' fe := by
  obtain ⟨hc, hp, hl, hv⟩ := internNodeE_sc (v := .sort u) (by simpa [internE] using hrun)
  have hls : a'.store.ls = a.store.ls := by simp only [EStore.ls, hl]
  refine ⟨fun x u' hx => ?_, fun x c us hx => ?_, ?_, ?_, ?_, ?_, ?_, h.lvlAll.congr hls, h.lsAll.congr hl,
    fun k x e => by have := h.dnN k x e; simp only [EStore.ns, hl] at this ⊢; exact this,
    fun c cv mI rP rules hf r hr lvls pins hfi u hu => by
      rw [hls]; exact h.recRules c cv mI rP rules hf r hr lvls pins hfi u hu⟩
  · rcases hv x _ (.inl ⟨_, rfl⟩) hx with h' | h'
    · rw [hls]; exact h.sort x u' h'
    · cases h'; rw [hls]; exact hu
  · rcases hv x _ (.inr ⟨_, _, rfl⟩) hx with h' | h'
    · rw [hl]; exact h.constLs x c us h'
    · cases h'
  · rw [hp, hls]; exact h.zero
  · rw [hp, hl]; exact h.emptyLs
  · intro k x hk; rw [hc] at hk; have := h.readN k x hk
    simp only [EStore.ns, hl] at this ⊢; exact this
  · intro c ci hf; have := h.constLps c ci hf
    simp only [EStore.ns, hl] at this ⊢; exact this
  · intro q tbl ht; have := h.proj q tbl ht
    simp only [EStore.ns, EStore.ls, hl] at this ⊢; exact this

/-- **`StoreDen` across interning `const c us`**, `us` reading back. -/
theorem StoreDen.of_internConst {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a a' : AState} {fe : IFEnv} {c : NIdx} {us : LsIdx}
    {r : EIdx} (h : StoreDen dn m a fe) (hus : ∃ ls, denoteLs a.store.lss us = some ls)
    (hrun : (internE (.const c us)).run a = .ok (r, a')) (_he : m'.arr64 EREC = m.arr64 EREC) :
    StoreDen dn m' a' fe := by
  obtain ⟨hc, hp, hl, hv⟩ := internNodeE_sc (v := .const c us) (by simpa [internE] using hrun)
  have hls : a'.store.ls = a.store.ls := by simp only [EStore.ls, hl]
  refine ⟨fun x u' hx => ?_, fun x c' us' hx => ?_, ?_, ?_, ?_, ?_, ?_, h.lvlAll.congr hls, h.lsAll.congr hl,
    fun k x e => by have := h.dnN k x e; simp only [EStore.ns, hl] at this ⊢; exact this,
    fun c cv mI rP rules hf r hr lvls pins hfi u hu => by
      rw [hls]; exact h.recRules c cv mI rP rules hf r hr lvls pins hfi u hu⟩
  · rcases hv x _ (.inl ⟨_, rfl⟩) hx with h' | h'
    · rw [hls]; exact h.sort x u' h'
    · cases h'
  · rcases hv x _ (.inr ⟨_, _, rfl⟩) hx with h' | h'
    · rw [hl]; exact h.constLs x c' us' h'
    · cases h'; rw [hl]; exact hus
  · rw [hp, hls]; exact h.zero
  · rw [hp, hl]; exact h.emptyLs
  · intro k x hk; rw [hc] at hk; have := h.readN k x hk
    simp only [EStore.ns, hl] at this ⊢; exact this
  · intro c ci hf; have := h.constLps c ci hf
    simp only [EStore.ns, hl] at this ⊢; exact this
  · intro q tbl ht; have := h.proj q tbl ht
    simp only [EStore.ns, EStore.ls, hl] at this ⊢; exact this

end L.Arena
