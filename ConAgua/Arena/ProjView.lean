import ConRon.Arena.Core
import Std.Do.Triple.SpecLemmas

/-!
# What the twin's `findProj?` and `IProjEntry.fireOk` leave alone (helper `whnf4-leaves`)

Two facts of the twin the projection callers need: `findProj?` (a pure lookup) answers an entry
only below the table's `numFields` (`findProj?_lt`), and `fireOk` does not change a stored
expression node's view (`fireOk_store`): it writes the readback and verdict caches only. With them `and_rescue_slots`' loop carries
"`ust` is a stored `const` node's list" from one slot to the next (`FireOkOK`'s hypothesis).
-/

open ConRon.Arena

namespace L.Arena

theorem pv_ok_bind {ε α β : Type} (x : α) (f : α → Except ε β) : (Except.ok x >>= f) = f x := rfl

theorem pv_get_bind {β : Type} (f : AState → AM β) (lst : AState) :
    ((do let s ← get; f s : AM β)).run lst = (f lst).run lst := rfl

theorem findProj?_lt {fe : IFEnv} {T : NIdx} {i : Nat} {e : IProjEntry}
    (h : fe.findProj? T i = some e) : i < e.numFields := by
  unfold IFEnv.findProj? at h
  split at h
  · split at h
    · cases h; simpa [IProjTable.entry] using ‹i < _›
    · cases h
  · cases h

/-- A stored expression node's view, unchanged from `a` to `a'`. -/
def EViewKept (a a' : AState) : Prop := ∀ x : EIdx, a'.store.view x = a.store.view x

theorem EViewKept.trans {a b c : AState} (h₁ : EViewKept a b) (h₂ : EViewKept b c) :
    EViewKept a c := fun x => (h₂ x).trans (h₁ x)

theorem EViewKept.of_store {a a' : AState} (h : a'.store = a.store) : EViewKept a a' :=
  fun x => by rw [h]

theorem internNNode_eview {v : NNodeView} {a a' : AState} {h : NIdx}
    (hrun : (internNNode v).run a = .ok (h, a')) : EViewKept a a' := by
  simp only [internNNode, pv_get_bind] at hrun
  cases hf : a.store.ns.find? v with
  | some i =>
    rw [hf] at hrun
    simp only [pure, StateT.pure, StateT.run] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    intro x; rfl
  | none =>
    rw [hf] at hrun
    by_cases hcap : (if a.store.ns.scratchOn then a.store.ns.scr.sizeOf v
        else a.store.ns.pers.sizeOf v) < Idx.idxCap
    · rw [ite_eq_left hcap] at hrun
      simp only [EStore.internName, LsStore.internName, LStore.internName, set, StateT.set, pure, StateT.pure, bind, StateT.bind, StateT.run] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      intro x; rfl
    · rw [ite_eq_right hcap] at hrun
      simp [ConRon.Arena.fail, throwThe, MonadExceptOf.throw, StateT.run, StateT.lift, bind,
        Except.bind] at hrun

/-! ## The readers write caches only -/

theorem readLevelM_store {h : LIdx} {a a' : AState} {l : ConLeche.Level}
    (hr : (readLevelM h).run a = .ok (l, a')) : a'.store = a.store := by
  cases e : a.caches.readLC[h]? with
  | some l' =>
    have : (readLevelM h).run a = .ok (l', a) := by simp [readLevelM, e]; rfl
    rw [this] at hr; cases hr; rfl
  | none =>
    cases d : denoteL a.store.ls h with
    | none =>
      simp [readLevelM, e, d, ConRon.Arena.fail, throwThe, MonadExceptOf.throw, StateT.run,
        StateT.lift, bind, StateT.bind, Except.bind, get, getThe, MonadStateOf.get, StateT.get,
        pure, Except.pure] at hr
    | some l' =>
      have : (readLevelM h).run a =
          .ok (l', { a with caches := { a.caches with readLC := a.caches.readLC.insert h l' } }) := by
        simp [readLevelM, e, d]; rfl
      rw [this] at hr; cases hr; rfl

theorem readNameM_store {h : NIdx} {a a' : AState} {x : ConLeche.Name}
    (hr : (readNameM h).run a = .ok (x, a')) : a'.store = a.store := by
  cases e : a.caches.readNC[h]? with
  | some x' =>
    have : (readNameM h).run a = .ok (x', a) := by simp [readNameM, e]; rfl
    rw [this] at hr; cases hr; rfl
  | none =>
    cases d : denoteN a.store.ns h with
    | none =>
      simp [readNameM, e, d, ConRon.Arena.fail, throwThe, MonadExceptOf.throw, StateT.run,
        StateT.lift, bind, StateT.bind, Except.bind, get, getThe, MonadStateOf.get, StateT.get,
        pure, Except.pure] at hr
    | some x' =>
      have : (readNameM h).run a =
          .ok (x', { a with caches := { a.caches with readNC := a.caches.readNC.insert h x' } }) := by
        simp [readNameM, e, d]; rfl
      rw [this] at hr; cases hr; rfl

theorem readLevelsM_store {h : LsIdx} {a a' : AState} {l : List ConLeche.Level}
    (hr : (readLevelsM h).run a = .ok (l, a')) : a'.store = a.store := by
  cases e : a.caches.readLsC[h]? with
  | some l' =>
    have : (readLevelsM h).run a = .ok (l', a) := by simp [readLevelsM, e]; rfl
    rw [this] at hr; cases hr; rfl
  | none =>
    cases d : denoteLs a.store.lss h with
    | none =>
      simp [readLevelsM, e, d, failDanglingLs, ConRon.Arena.fail, throwThe, MonadExceptOf.throw,
        StateT.run, StateT.lift, bind, StateT.bind, Except.bind, get, getThe, MonadStateOf.get,
        StateT.get, pure, Except.pure] at hr
    | some l' =>
      have : (readLevelsM h).run a =
          .ok (l', { a with caches := { a.caches with readLsC := a.caches.readLsC.insert h l' } }) := by
        simp [readLevelsM, e, d]; rfl
      rw [this] at hr; cases hr; rfl

theorem readNamesM_store : ∀ {lps : List NIdx} {a a' : AState} {ks : List ConLeche.Name},
    (readNamesM lps).run a = .ok (ks, a') → a'.store = a.store
  | [], a, a', ks, h => by
    have : (readNamesM []).run a = .ok ([], a) := rfl
    rw [this] at h; cases h; rfl
  | x :: xs, a, a', ks, h => by
    simp only [readNamesM, StateT.run_bind] at h
    cases h1 : (readNameM x).run a with
    | error e => rw [h1] at h; cases h
    | ok p =>
      rw [h1] at h
      cases h2 : (readNamesM xs).run p.2 with
      | error e => simp only [pv_ok_bind, h2] at h; cases h
      | ok q =>
        simp only [pv_ok_bind, h2] at h
        cases h
        exact (readNamesM_store h2).trans (readNameM_store h1)

theorem pinZeroLevel_store {a a' : AState} {z : LIdx} (h : pinZeroLevel.run a = .ok (z, a')) :
    a'.store = a.store := by
  by_cases hr : pinsReady a = true
  · have : pinZeroLevel.run a = .ok (a.pins.zeroLevel, a) := by
      simp [pinZeroLevel, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
        Except.bind, pure, StateT.pure, Except.pure, hr]
    rw [this] at h; cases h; rfl
  · simp [pinZeroLevel, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      Except.bind, pure, Except.pure, hr, ConRon.Arena.fail, throwThe,
      MonadExceptOf.throw, StateT.lift] at h

theorem lvlEq?_store' {u v : LIdx} {a a' : AState} {o : Option Bool}
    (h : (lvlEq? u v).run a = .ok (o, a')) : a'.store = a.store := by
  cases hm : a.caches.lvlEqC[(u, v)]? with
  | some r =>
    have : (lvlEq? u v).run a = .ok (some r, a) := by simp [lvlEq?, hm]; rfl
    rw [this] at h; cases h; rfl
  | none =>
    simp only [lvlEq?] at h
    rw [pv_get_bind] at h
    simp only [hm, StateT.run_bind] at h
    cases h1 : (readLevelM u).run a with
    | error e => rw [h1] at h; cases h
    | ok p =>
      rw [h1] at h
      cases h2 : (readLevelM v).run p.2 with
      | error e => simp only [pv_ok_bind, h2] at h; cases h
      | ok q =>
        simp only [pv_ok_bind, h2] at h
        have hs := (readLevelM_store h2).trans (readLevelM_store h1)
        split at h
        · simp [set, StateT.set, bind, StateT.bind, Except.bind,
            pure, StateT.pure, Except.pure, StateT.run] at h
          obtain ⟨-, rfl⟩ := h
          exact hs
        · cases h; exact hs

/-- **`fireOk` writes caches only.** -/
theorem fireOk_store {e : IProjEntry} {us : LsIdx} {a a' : AState} {b : Bool}
    (h : (e.fireOk us).run a = .ok (b, a')) : a'.store = a.store := by
  simp only [IProjEntry.fireOk, zeroLevel, StateT.run_bind] at h
  cases h1 : pinZeroLevel.run a with
  | error x => rw [h1] at h; cases h
  | ok p =>
    rw [h1] at h
    have s1 := pinZeroLevel_store h1
    cases h2 : (lvlEq? e.structSort p.1).run p.2 with
    | error x => simp only [pv_ok_bind, h2] at h; cases h
    | ok q =>
      simp only [pv_ok_bind, h2] at h
      have s2 := (lvlEq?_store' h2).trans s1
      split at h
      · cases h; exact s2
      · simp only [StateT.run_bind] at h
        cases h3 : (readNamesM e.levelParams).run q.2 with
        | error x => simp only [h3] at h; cases h
        | ok r =>
          simp only [pv_ok_bind, h3] at h
          cases h4 : (readLevelsM us).run r.2 with
          | error x => simp only [h4] at h; cases h
          | ok t =>
            simp only [pv_ok_bind, h4] at h
            cases h5 : (readLevelM e.fieldSort).run t.2 with
            | error x => simp only [h5] at h; cases h
            | ok w =>
              simp only [pv_ok_bind, h5] at h
              cases h
              exact (readLevelM_store h5).trans ((readLevelsM_store h4).trans
                ((readNamesM_store h3).trans s2))

end L.Arena
