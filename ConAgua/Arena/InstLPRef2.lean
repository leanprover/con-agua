import ConAgua.Arena.InstLPRef
import ConAgua.Census.Attr

/-!
# `rec_fire_levels` refines `recFireLevels`

The model (`InstLPSpec.lean`, over its callees' runs) at the specs of `ls_node`, `keys_push`,
`sle_go`/`slp_go`, `spn_ls`, then the lemmas of `InstLPRef.lean`: the readbacks of the keys and
the universe arguments (`readNamesM_run`, `lp_readLevelsM_run`), the list (`sleW_ok`, `slpW_ok`),
the list node (`spnLsW_ok`), the stack top put back.
-/

open ConRon.Arena ConLeche
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false

namespace L.Arena

theorem LsStore.intern_ls' (st : LsStore) (w : LsNodeView) : (st.intern w).1.ls = st.ls := by
  simp only [LsStore.intern]
  split
  · rfl
  · split
    · split <;> rfl
    · rfl

/-- **The twin's `internLsNode` extends the list store and keeps the level store.** -/
theorem internLsNode_ext (v : LsNodeView) (a a' : AState) (i : LsIdx)
    (h : (internLsNode v).run a = .ok (i, a')) :
    a'.store.lss.ls = a.store.lss.ls ∧ LsExt a.store.lss a'.store.lss := by
  unfold internLsNode at h
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at h
  split at h
  · simp only [StateT.run_pure] at h
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
    exact ⟨rfl, LsExt.refl _⟩
  · split at h <;> split at h <;> first
      | (simp only [StateT.run_pure, pure_bind, StateT.bind, StateT.set, StateT.pure, StateT.run,
          bind, Except.bind, pure, Except.pure] at h
         injection h with h
         obtain ⟨-, rfl⟩ := Prod.mk.inj h
         refine ⟨LsStore.intern_ls' _ v, LsExt.of_view_mono ?_ fun j w hw => LsStore.view_intern_mono _ v hw⟩
         rw [show ∀ st : EStore, (st.internLevels v).1.lss.ls = st.lss.ls from
           fun st => LsStore.intern_ls' _ v]
         exact LExt.refl _)
      | simp [fail, throwThe, MonadExceptOf.throw, StateT.run, bind, StateT.bind, StateT.lift,
          Except.bind] at h

end L.Arena
