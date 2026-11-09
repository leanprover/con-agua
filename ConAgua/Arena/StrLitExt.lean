module

public import ConAgua.Arena.StrLitKeep
public import ConRon.Arena.WFProofs

@[expose] public section

/-!
# The twin's literal-shape gates extend the store

`EMono op`: every successful run of `op` extends the store (`Ext`), so a denotation read before
the run reads the same after it (`denoteCV_ext`). Closed under `pure`, `fail`, `bind`, `if` and
`match`; leaves: the pin readers, `view` and the interners (`EStore.intern_ext`, …).
`emono_litShapeOk`: the ten gates of `litShapeOk` and their dispatcher.
-/

open ConRon.Arena
namespace L.Arena

/-- Every successful run of `op` extends the store (`Ext`). -/
@[irreducible] def EMono {α : Type} (op : AM α) : Prop :=
  ∀ a r a', op.run a = .ok (r, a') → Ext a.store a'.store

theorem EMono.pure {α : Type} (x : α) : EMono (Pure.pure x : AM α) := by
  unfold EMono; intro a r a' h; cases h; exact Ext.refl _
theorem EMono.fail {α : Type} (e : CheckError) : EMono (ConRon.Arena.fail e : AM α) := by
  unfold EMono; intro a r a' h; cases h
theorem EMono.bind {α γ : Type} {x : AM α} {f : α → AM γ} (hx : EMono x)
    (hf : ∀ v, EMono (f v)) : EMono (x >>= f) := by
  unfold EMono at *; intro a r a' h
  simp only [StateT.run_bind] at h
  cases h1 : x.run a with
  | error e => rw [h1] at h; cases h
  | ok p =>
    obtain ⟨v, a₁⟩ := p
    rw [h1] at h
    exact (hx a v a₁ h1).trans (hf v a₁ r a' h)
theorem EMono.ite {α : Type} {c : Prop} [Decidable c] {t e : AM α} (ht : EMono t)
    (he : EMono e) : EMono (if c then t else e) := by
  split <;> assumption
theorem EMono.of_keeps {α : Type} {op : AM α} (h : Keeps (fun a => a.store) op) : EMono op := by
  unfold EMono; intro a r a' hr; rw [h.run hr]; exact Ext.refl _

theorem emono_view (h : EIdx) : EMono (view h) := EMono.of_keeps (keeps_view h)
theorem emono_pinAt (i : Nat) : EMono (pinAt i) := EMono.of_keeps (by prim_keeps pinAt)
theorem emono_pinSortOne : EMono pinSortOne := EMono.of_keeps (by prim_keeps pinSortOne)
theorem emono_pinZeroLevel : EMono pinZeroLevel := EMono.of_keeps (by prim_keeps pinZeroLevel)
theorem emono_pinEmptyLevels : EMono pinEmptyLevels := EMono.of_keeps (by prim_keeps pinEmptyLevels)

set_option hygiene false in
/-- Close the leaves of an interner's run: a hit (`pure`), the full-array decline, a write-back. -/
macro "emono_close " e:term : tactic => `(tactic| (
  repeat' split at h
  all_goals first
    | (cases h; exact Ext.refl _)
    | (simp only [StateT.run_map, StateT.run_set] at h; cases h; exact $e)
    | (simp only [StateT.run, StateT.bind, set, StateT.set, pure, StateT.pure, bind, Except.bind,
        MonadStateOf.set, Except.pure] at h
       cases h; exact $e)
    | (exfalso; revert h; simp [ConRon.Arena.fail, StateT.run, StateT.lift, throwThe, MonadExceptOf.throw, throw, Function.comp, liftM, monadLift, MonadLift.monadLift, MonadLiftT.monadLift,
        bind, Except.bind]; done)))

theorem emono_internNodeE (v : ENodeView) : EMono (internNodeE v) := by
  unfold EMono; intro a r a' h
  simp only [internNodeE, StateT.run_bind, StateT.run_get, pure_bind] at h
  emono_close (EStore.intern_ext _ _)

theorem emono_internLamE (ty b : EIdx) : EMono (internLamE ty b) := by
  unfold EMono; intro a r a' h
  simp only [internLamE, StateT.run_bind, StateT.run_get, pure_bind] at h
  emono_close (by
    show Ext _ (EStore.internBind _ _ _ _).1
    rw [EStore.internBind_eq_intern _ _ _ _ (.inl rfl)]; exact EStore.intern_ext _ _)

theorem emono_internForallEE (ty b : EIdx) : EMono (internForallEE ty b) := by
  unfold EMono; intro a r a' h
  simp only [internForallEE, StateT.run_bind, StateT.run_get, pure_bind] at h
  emono_close (by
    show Ext _ (EStore.internBind _ _ _ _).1
    rw [EStore.internBind_eq_intern _ _ _ _ (.inr rfl)]; exact EStore.intern_ext _ _)

theorem emono_internLNode (v : LNodeView) : EMono (internLNode v) := by
  unfold EMono; intro a r a' h
  simp only [internLNode, StateT.run_bind, StateT.run_get, pure_bind] at h
  emono_close (EStore.internLevel_ext _ _)

theorem emono_internLsNode (v : LsNodeView) : EMono (internLsNode v) := by
  unfold EMono; intro a r a' h
  simp only [internLsNode, StateT.run_bind, StateT.run_get, pure_bind] at h
  emono_close (EStore.internLevels_ext _ _)

theorem emono_internE (v : ENodeView) : EMono (internE v) := by
  cases v <;> simp only [internE] <;> first | exact emono_internNodeE _ | exact emono_internLamE _ _ |
    exact emono_internForallEE _ _

theorem emono_constE (n : NIdx) : EMono (constE n) :=
  EMono.bind emono_pinEmptyLevels fun _ => emono_internE _

/-- One step through a `do` block: split binds, `if`s and `match`es, close leaves. -/
macro "emono_auto" : tactic => `(tactic| (
  repeat' (first
    | exact EMono.pure _ | exact EMono.fail _
    | exact emono_view _ | exact emono_pinAt _ | exact emono_pinSortOne
    | exact emono_pinZeroLevel | exact emono_pinEmptyLevels | exact emono_internLNode _
    | exact emono_internLsNode _ | exact emono_internE _ | exact emono_constE _
    | (unfold pinNat) | (unfold pinNatZero) | (unfold pinNatSucc) | (unfold pinString)
    | (unfold pinStringOfList) | (unfold pinList) | (unfold pinListNil) | (unfold pinListCons)
    | (unfold pinChar) | (unfold pinCharOfNat) | (unfold sortOne) | (unfold zeroLevel)
    | with_reducible apply EMono.bind | apply EMono.ite | intro _ | split | (dsimp only))))

theorem emono_natIndOk (o : Option IConstantInfo) : EMono (natIndOk o) := by
  unfold natIndOk; emono_auto
theorem emono_natZeroOk (o : Option IConstantInfo) : EMono (natZeroOk o) := by
  unfold natZeroOk; emono_auto
theorem emono_natSuccOk (o : Option IConstantInfo) : EMono (natSuccOk o) := by
  unfold natSuccOk; emono_auto
theorem emono_stringTyOk (o : Option IConstantInfo) : EMono (stringTyOk o) := by
  unfold stringTyOk; emono_auto
theorem emono_charTyOk (o : Option IConstantInfo) : EMono (charTyOk o) := by
  unfold charTyOk; emono_auto
theorem emono_listTyOk (o : Option IConstantInfo) : EMono (listTyOk o) := by
  unfold listTyOk; emono_auto
theorem emono_listNilTyOk (o : Option IConstantInfo) : EMono (listNilTyOk o) := by
  unfold listNilTyOk; emono_auto
theorem emono_listConsTyOk (o : Option IConstantInfo) : EMono (listConsTyOk o) := by
  unfold listConsTyOk; emono_auto
theorem emono_charOfNatTyOk (o : Option IConstantInfo) : EMono (charOfNatTyOk o) := by
  unfold charOfNatTyOk; emono_auto
theorem emono_stringOfListTyOk (o : Option IConstantInfo) : EMono (stringOfListTyOk o) := by
  unfold stringOfListTyOk; emono_auto

/-- **`litShapeOk` extends the store.** -/
theorem emono_litShapeOk (c : IConstantInfo) : EMono (litShapeOk c) := by
  unfold litShapeOk
  repeat' (first
    | exact EMono.pure _ | exact emono_natIndOk _ | exact emono_natZeroOk _ | exact emono_natSuccOk _
    | exact emono_stringTyOk _ | exact emono_charTyOk _ | exact emono_listTyOk _
    | exact emono_listNilTyOk _ | exact emono_listConsTyOk _ | exact emono_charOfNatTyOk _
    | exact emono_stringOfListTyOk _ | exact emono_pinAt _
    | (unfold pinNat) | (unfold pinNatZero) | (unfold pinNatSucc) | (unfold pinString)
    | (unfold pinStringOfList) | (unfold pinList) | (unfold pinListNil) | (unfold pinListCons)
    | (unfold pinChar) | (unfold pinCharOfNat)
    | with_reducible apply EMono.bind | apply EMono.ite | intro _ | split | (dsimp only))

theorem EMono.run {α : Type} {op : AM α} (h : EMono op) {a : AState} {r : α} {a' : AState}
    (hr : op.run a = .ok (r, a')) : Ext a.store a'.store := by
  unfold EMono at h; exact h a r a' hr

end L.Arena
