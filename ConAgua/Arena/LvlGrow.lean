import ConAgua.Arena.WhnfBase
import ConAgua.Arena.StoreDenLvl
import ConAgua.Arena.LevelView
import ConAgua.Arena.InferLeaves

/-!
# The level tables only grow (lane `defeq2`)

`LvlCnt m m'` (`WhnfBase.lean`, a field of `PoolGrew`): the scratch flag is kept and no level
table's count drops. A frame that avoids those `CTL` words keeps it trivially; a level interning
grows one table, so under `ArenaR` at both ends (the counts are the twin tables' sizes, `ConsR.cntP`/`cntS`)
it follows from the twin's `LStore.intern` growing its tables (`lvlCnt_of_arena`).
-/

open ConRon.Arena

namespace L.Arena

/-- Every level table of a tier at least as large. -/
structure LTGrow (t t' : LTables) : Prop where
  zeros : t.zeros.nodes.size ≤ t'.zeros.nodes.size
  succs : t.succs.nodes.size ≤ t'.succs.nodes.size
  maxs : t.maxs.nodes.size ≤ t'.maxs.nodes.size
  imaxs : t.imaxs.nodes.size ≤ t'.imaxs.nodes.size
  params : t.params.nodes.size ≤ t'.params.nodes.size

theorem LTGrow.refl (t : LTables) : LTGrow t t := ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

theorem LTGrow.push (t : LTables) (v : LNodeView) (d : LDer) (tier : UInt32) :
    LTGrow t (t.push v d tier).1 := by
  cases v <;> simp only [LTables.push, Tbl.push] <;>
    exact ⟨by simp, by simp, by simp, by simp, by simp⟩

theorem LTGrow.intern (st : LStore) (v : LNodeView) :
    LTGrow st.pers (st.intern v).1.pers ∧ LTGrow st.scr (st.intern v).1.scr := by
  unfold LStore.intern
  split
  · exact ⟨LTGrow.refl _, LTGrow.refl _⟩
  · split
    · split
      · exact ⟨LTGrow.refl _, LTGrow.refl _⟩
      · exact ⟨LTGrow.refl _, LTGrow.push _ _ _ _⟩
    · exact ⟨LTGrow.push _ _ _ _, LTGrow.refl _⟩

theorem cnt_le {C : ConsSch} {m m' : Mem} {t x : Word} {n n' : Nat} (h1 : (cntC C m t).toNat = n)
    (h2 : (cntC C m' t).toNat = n') (hn : n ≤ n') (hx : C.ca + t = x) :
    (rdW (m.arr64 CTL) x).toNat ≤ (rdW (m'.arr64 CTL) x).toNat := by
  subst hx; simp only [cntC] at h1 h2; omega

/-- **Level-table growth from the twin**: under `ArenaR` at both ends, a kept scratch flag and
twin level tables that only grew give `LvlCnt`. -/
theorem lvlCnt_of_arena {m m' : Mem} {a a' : AState} (hR : ArenaR m a) (hR' : ArenaR m' a')
    (hflag : rdW (m'.arr64 CTL) 1 = rdW (m.arr64 CTL) 1)
    (hp : LTGrow a.store.lss.ls.pers a'.store.lss.ls.pers)
    (hs : LTGrow a.store.lss.ls.scr a'.store.lss.ls.scr)
    (hlp : a.store.lss.pers.lists.nodes.size ≤ a'.store.lss.pers.lists.nodes.size)
    (hls : a.store.lss.scr.lists.nodes.size ≤ a'.store.lss.scr.lists.nodes.size) : LvlCnt m m' := by
  refine ⟨hflag, fun x hx => ?_⟩
  simp only [lvlCtlW, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [hflag]; exact Nat.le_refl _
  · exact cnt_le (ConsR.cntP hR.succ) (ConsR.cntP hR'.succ) hp.succs (by decide)
  · exact cnt_le (ConsR.cntS hR.succ) (ConsR.cntS hR'.succ) hs.succs (by decide)
  · exact cnt_le (ConsR.cntP hR.zero) (ConsR.cntP hR'.zero) hp.zeros (by decide)
  · exact cnt_le (ConsR.cntS hR.zero) (ConsR.cntS hR'.zero) hs.zeros (by decide)
  · exact cnt_le (ConsR.cntP hR.max) (ConsR.cntP hR'.max) hp.maxs (by decide)
  · exact cnt_le (ConsR.cntS hR.max) (ConsR.cntS hR'.max) hs.maxs (by decide)
  · exact cnt_le (ConsR.cntP hR.imax) (ConsR.cntP hR'.imax) hp.imaxs (by decide)
  · exact cnt_le (ConsR.cntS hR.imax) (ConsR.cntS hR'.imax) hs.imaxs (by decide)
  · exact cnt_le (ConsR.cntP hR.param) (ConsR.cntP hR'.param) hp.params (by decide)
  · exact cnt_le (ConsR.cntS hR.param) (ConsR.cntS hR'.param) hs.params (by decide)
  · exact cnt_le (ConsR.cntP hR.ls) (ConsR.cntP hR'.ls) hlp (by decide)
  · exact cnt_le (ConsR.cntS hR.ls) (ConsR.cntS hR'.ls) hls (by decide)

/-- **A level interning grows the level tables** (a hit changes nothing, a miss is
`LStore.intern`). -/
theorem LTGrow.internLNode {a a' : AState} {v : LNodeView} {h : LIdx}
    (hrun : (internLNode v).run a = .ok (h, a')) :
    LTGrow a.store.lss.ls.pers a'.store.lss.ls.pers ∧ LTGrow a.store.lss.ls.scr a'.store.lss.ls.scr := by
  rcases internLNode_run_cases hrun with ⟨-, rfl⟩ | ⟨-, -, he, -⟩
  · exact ⟨LTGrow.refl _, LTGrow.refl _⟩
  · have e : a'.store.lss.ls = (a.store.lss.ls.intern v).1 := he
    rw [e]; exact LTGrow.intern _ _

/-! ## A stored level stays stored -/

theorem lvNodeW_mono {m m' : Mem} (hl : LvlCnt m m') {u : Word} (hu : HW u)
    (h : lvNodeW m u ≠ []) : lvNodeW m' u ≠ [] := by
  have ht := tierW_le u
  have key : ∀ k : Word, k ∈ ([6, 8, 10, 12, 14] : List Word) →
      ¬ rdW (m.arr64 CTL) (k + tierW u) ≤ idxW u → ¬ rdW (m'.arr64 CTL) (k + tierW u) ≤ idxW u := by
    intro k hk h1 h2
    apply h1
    have hx : k + tierW u ∈ lvlCtlW := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
      rcases word_le_one (tierW u) ht with e | e <;> rw [e] <;>
        rcases hk with rfl | rfl | rfl | rfl | rfl <;> decide
    have := hl.cnt _ hx
    rw [UInt64.le_iff_toNat_le] at h2 ⊢; omega
  have h32' : ¬ (u >>> 32 ≠ 0) := by simpa using h32 hu
  unfold lvNodeW at h ⊢
  rw [ite_eq_right h32'] at h ⊢
  rw [hl.flag]
  by_cases hs : tierW u ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [ite_eq_left hs] at h; exact absurd rfl h
  rw [ite_eq_right hs] at h ⊢
  by_cases g0 : u >>> 28 = 0
  · simp only [g0, ↓reduceIte] at h ⊢
    by_cases c : tcnt m ZERO (tierW u) ≤ idxW u
    · rw [ite_eq_left c] at h; exact absurd rfl h
    · rw [ite_eq_right (show ¬ tcnt m' ZERO (tierW u) ≤ idxW u from key 8 (by simp) c)]; simp
  by_cases g1 : u >>> 28 = 1
  · simp only [g1, ↓reduceIte] at h ⊢
    by_cases c : tcnt m SUCC (tierW u) ≤ idxW u
    · rw [ite_eq_left c] at h; exact absurd rfl h
    · rw [ite_eq_right (show ¬ tcnt m' SUCC (tierW u) ≤ idxW u from key 6 (by simp) c)]; simp
  by_cases g2 : u >>> 28 = 2
  · simp only [g2, ↓reduceIte] at h ⊢
    by_cases c : tcnt m MAX (tierW u) ≤ idxW u
    · rw [ite_eq_left c] at h; exact absurd rfl h
    · rw [ite_eq_right (show ¬ tcnt m' MAX (tierW u) ≤ idxW u from key 10 (by simp) c)]; simp
  by_cases g3 : u >>> 28 = 3
  · simp only [g3, ↓reduceIte] at h ⊢
    by_cases c : tcnt m IMAX (tierW u) ≤ idxW u
    · rw [ite_eq_left c] at h; exact absurd rfl h
    · rw [ite_eq_right (show ¬ tcnt m' IMAX (tierW u) ≤ idxW u from key 12 (by simp) c)]; simp
  by_cases g4 : u >>> 28 = 4
  · simp only [g4, ↓reduceIte] at h ⊢
    by_cases c : tcnt m PARAM (tierW u) ≤ idxW u
    · rw [ite_eq_left c] at h; exact absurd rfl h
    · rw [ite_eq_right (show ¬ tcnt m' PARAM (tierW u) ≤ idxW u from key 14 (by simp) c)]; simp
  simp only [g0, g1, g2, g3, g4, ↓reduceIte] at h; exact absurd rfl h

/-- **A level read back before a core run reads back after it** (`LvlCnt` from `PoolGrew`):
stored at the start (`lvNodeW_store`), stored at the end (`lvNodeW_mono`, `lview_of_lvNodeW`),
read back by `StoreDen.lvlAll`. -/
theorem lvl_den_later {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a a' : AState} {fe : IFEnv} (hR : ArenaR m a)
    (hR' : ArenaR m' a') (hD' : StoreDen dn m' a' fe) (hl : LvlCnt m m') {u : Word} (hu : HW u)
    (hd : ∃ l, denoteL a.store.ls (decI u) = some l) : ∃ l, denoteL a'.store.ls (decI u) = some l := by
  obtain ⟨l, hl'⟩ := hd
  have hv : ∃ v, a.store.lss.ls.view (decI u) = some v := by
    unfold denoteL denoteLAux at hl'
    cases e : a.store.ls.view (decI u) with
    | none => rw [e] at hl'; simp at hl'
    | some v => exact ⟨v, e⟩
  obtain ⟨v, hv⟩ := hv
  have hne : lvNodeW m u ≠ [] := by
    rw [lvNodeW_store hR hu hv]; cases v <;> simp [lvEnc]
  obtain ⟨v', hv'⟩ := L.Ind.lview_of_lvNodeW hR' hu (lvNodeW_mono hl hu hne)
  exact hD'.lvlAll _ (by show (a'.store.lss.ls.view (decI u)).isSome = true; rw [hv']; rfl)

/-- `ensureSort`'s answer is a stored `sort` node's level (at the state after it). -/
theorem ensureSort_view {r : CoreFnsA} {fe : IFEnv} {d : Nat} {e : EIdx} {a a' : AState} {u : LIdx}
    (h : (ensureSort r fe d e).run a = .ok (u, a')) : ∃ x, a'.store.view x = some (.sort u) := by
  simp only [ensureSort, StateT.run_bind] at h
  cases h1 : (r.whnf d e).run a with
  | error err => rw [h1] at h; cases h
  | ok q =>
    obtain ⟨hh, a1⟩ := q
    rw [h1] at h
    change (if hh.tag == ETag.sort then (do
        match ← view hh with
        | .sort u => pure u
        | _ => fail (.invalid "expected a sort")) else fail (.invalid "expected a sort")).run a1 = _ at h
    split at h
    · simp only [view, StateT.run_bind, StateT.run_get, pure_bind] at h
      cases hv : a1.store.view hh with
      | none =>
        rw [hv] at h
        simp [ConRon.Arena.fail, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
      | some w =>
        rw [hv] at h
        cases w with
        | sort u' =>
          simp [StateT.run, pure, StateT.pure, Except.pure, bind, Except.bind] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨hh, hv⟩
        | _ =>
          simp [ConRon.Arena.fail, throwThe, MonadExceptOf.throw, StateT.run, pure,
            StateT.pure, Except.pure, bind, Except.bind, StateT.lift] at h
    · simp [ConRon.Arena.fail, throwThe, MonadExceptOf.throw, StateT.run, StateT.lift, bind,
        Except.bind] at h

/-- A level that reads back is stored, and `lv_node` accepts it. -/
theorem lvNodeW_of_den {m : Mem} {a : AState} (hR : ArenaR m a) {u : Word} (hu : HW u)
    (hd : ∃ l, denoteL a.store.ls (decI u) = some l) : lvNodeW m u ≠ [] := by
  obtain ⟨l, hl'⟩ := hd
  have hv : ∃ v, a.store.lss.ls.view (decI u) = some v := by
    unfold denoteL denoteLAux at hl'
    cases e : a.store.ls.view (decI u) with
    | none => rw [e] at hl'; simp at hl'
    | some v => exact ⟨v, e⟩
  obtain ⟨v, hv⟩ := hv
  rw [lvNodeW_store hR hu hv]; cases v <;> simp [lvEnc]

/-! ## Level lists -/

theorem LsTables.push_get (t : LsTables) (v : LsNodeView) (d : LDer) (tier : UInt32) (i : LsIdx)
    (w : LsNodeView) (h : (t.push v d tier).1.get i = some w) : t.get i = some w ∨ w = v := by
  simp only [LsTables.push, LsTables.get, Tbl.push, Tbl.node?] at h ⊢
  split at h
  · rename_i ht
    rw [ite_eq_left ht]
    rw [Array.getElem?_push] at h
    split at h
    · right; simp at h; exact h.symm
    · left; exact h
  · cases h

theorem LsStore.intern_view (st : LsStore) (v : LsNodeView) (i : LsIdx) (w : LsNodeView)
    (h : (st.intern v).1.view i = some w) : st.view i = some w ∨ w = v := by
  unfold LsStore.intern at h
  split at h
  · exact .inl h
  · split at h
    · rename_i hon
      split at h
      · exact .inl h
      · simp only [LsStore.view] at h ⊢
        by_cases hp : i.isPersistent = true
        · rw [ite_eq_left hp] at h ⊢; exact .inl h
        · rw [ite_eq_right hp] at h ⊢; rw [ite_eq_left hon] at h ⊢
          exact LsTables.push_get _ _ _ _ _ _ h
    · rename_i hon
      simp only [LsStore.view] at h ⊢
      by_cases hp : i.isPersistent = true
      · rw [ite_eq_left hp] at h ⊢; exact LsTables.push_get _ _ _ _ _ _ h
      · rw [ite_eq_right hp] at h ⊢; rw [ite_eq_right hon] at h; cases h

/-- **`LsAll` across a level-list interning** whose levels read back; the new list reads back. -/
theorem lsAll_internLsNode {m : Mem} {a a' : AState} {v : LsNodeView} {h : LsIdx}
    (hR : ArenaR m a) (hall : LsAll a) (hel : ∀ c ∈ v, ∃ l, denoteL a.store.ls c = some l)
    (hrun : (internLsNode v).run a = .ok (h, a')) :
    LsAll a' ∧ (∃ ls, denoteLs a'.store.lss h = some ls) := by
  obtain ⟨hd, hx⟩ := denoteLs_internLsNode hR hel hrun
  refine ⟨fun i hi => ?_, hd⟩
  obtain ⟨ls, hls⟩ := denoteLList_of_all v hel
  rcases internLsNode_run_cases hrun with ⟨-, rfl⟩ | ⟨-, -, hss, -⟩
  · exact hall i hi
  · cases e : a'.store.lss.view i with
    | none => rw [e] at hi; cases hi
    | some w =>
      have e' : (a.store.lss.intern v).1.view i = some w := by rw [← hss]; exact e
      rcases LsStore.intern_view _ _ _ _ e' with ho | rfl
      · obtain ⟨l, hl⟩ := hall i (by rw [ho]; rfl)
        exact ⟨l, hx.lst _ _ hl⟩
      · refine ⟨ls, ?_⟩
        unfold denoteLs; rw [e]
        have hls' : a'.store.lss.ls = a.store.lss.ls := by
          rw [hss]; exact LsStore.ls_intern _ _
        rw [hls']; exact hls

/-- **A level-list interning grows the list tables and keeps the level store.** -/
theorem lsGrow_internLsNode {a a' : AState} {v : LsNodeView} {h : LsIdx}
    (hrun : (internLsNode v).run a = .ok (h, a')) :
    a.store.lss.pers.lists.nodes.size ≤ a'.store.lss.pers.lists.nodes.size ∧
      a.store.lss.scr.lists.nodes.size ≤ a'.store.lss.scr.lists.nodes.size ∧
      a'.store.lss.ls = a.store.lss.ls := by
  rcases internLsNode_run_cases hrun with ⟨-, rfl⟩ | ⟨-, -, hss, -⟩
  · exact ⟨Nat.le_refl _, Nat.le_refl _, rfl⟩
  · rw [hss]
    refine ⟨?_, ?_, LsStore.ls_intern _ _⟩ <;> unfold LsStore.intern <;> split <;>
      (try split) <;> (try split) <;> simp [LsTables.push, Tbl.push]

/-- `LvlCnt` across a level-list interning (under `ArenaR` at both ends). -/
theorem lvlCnt_internLsNode {m m' : Mem} {a a' : AState} {v : LsNodeView} {h : LsIdx}
    (hR : ArenaR m a) (hR' : ArenaR m' a') (hflag : rdW (m'.arr64 CTL) 1 = rdW (m.arr64 CTL) 1)
    (hrun : (internLsNode v).run a = .ok (h, a')) : LvlCnt m m' := by
  obtain ⟨h1, h2, h3⟩ := lsGrow_internLsNode hrun
  exact lvlCnt_of_arena hR hR' hflag (by rw [h3]; exact LTGrow.refl _) (by rw [h3]; exact LTGrow.refl _)
    h1 h2

end L.Arena
