import ConAgua.Arena.WhnfBase
import ConAgua.Arena.Keeps
import ConRon.Bridge.ExprOps.MemoSpecs

/-!
# `strLitSupported` keeps every stored node's view

`VMono op`: every successful run of `op` keeps each `view` the store already answers. Closed
under `pure`, `fail`, `bind`, `if` and `match` (by `split`), with leaves for the pin readers,
`view` and the three interners. `supKeep_of` discharges `SupKeep`
(`WhnfBase.lean`) by unfolding the twin's guards and composing.
-/

namespace L.Arena

open ConRon.Arena

/-- Every successful run of `op` keeps every node view of the store. Irreducible, so that
`intro` in `vmono_auto` stops at it. -/
@[irreducible] def VMono {α : Type} (op : AM α) : Prop :=
  ∀ a r a', op.run a = .ok (r, a') → ∀ h w, a.store.view h = some w → a'.store.view h = some w

theorem VMono.pure {α : Type} (x : α) : VMono (Pure.pure x : AM α) := by
  unfold VMono; intro a r a' h; cases h; exact fun _ _ hw => hw

theorem VMono.fail {α : Type} (e : CheckError) : VMono (ConRon.Arena.fail e : AM α) := by
  unfold VMono; intro a r a' h; cases h

theorem VMono.bind {α γ : Type} {x : AM α} {f : α → AM γ} (hx : VMono x)
    (hf : ∀ v, VMono (f v)) : VMono (x >>= f) := by
  unfold VMono at *; intro a r a' h
  simp only [StateT.run_bind] at h
  cases h1 : x.run a with
  | error e => rw [h1] at h; cases h
  | ok p =>
    obtain ⟨v, a₁⟩ := p
    rw [h1] at h
    exact fun i w hw => hf v a₁ r a' h i w (hx a v a₁ h1 i w hw)

/-- An operation that keeps the store's `view` function is `VMono`. -/
theorem VMono.of_keeps {α : Type} {op : AM α} (h : Keeps (fun a => a.store.view) op) :
    VMono op := by
  unfold VMono; intro a r a' hr i w hw; rw [h.run hr]; exact hw


/-! ## The leaves -/

theorem vmono_view (h : EIdx) : VMono (view h) := VMono.of_keeps (keeps_view h)

theorem vmono_pinAt (i : Nat) : VMono (pinAt i) := VMono.of_keeps (by prim_keeps pinAt)

theorem vmono_pinSortOne : VMono pinSortOne := VMono.of_keeps (by prim_keeps pinSortOne)

theorem vmono_pinZeroLevel : VMono pinZeroLevel := VMono.of_keeps (by prim_keeps pinZeroLevel)

theorem vmono_pinEmptyLevels : VMono pinEmptyLevels :=
  VMono.of_keeps (by prim_keeps pinEmptyLevels)

theorem vmono_internLNode (v : LNodeView) : VMono (internLNode v) :=
  VMono.of_keeps (by prim_keeps internLNode)

theorem vmono_internLsNode (v : LsNodeView) : VMono (internLsNode v) :=
  VMono.of_keeps (by prim_keeps internLsNode)

theorem vmono_internE (v : ENodeView) : VMono (internE v) := by
  unfold VMono; intro a r a' h; exact ConRon.Bridge.ExprOps.internE_view_mono h

theorem vmono_constE (n : NIdx) : VMono (constE n) :=
  VMono.bind vmono_pinEmptyLevels fun _ => vmono_internE _

theorem VMono.ite {α : Type} {c : Prop} [Decidable c] {t e : AM α} (ht : VMono t)
    (he : VMono e) : VMono (if c then t else e) := by
  split <;> assumption

/-- One step through a `do` block: split binds, `if`s and `match`es, close leaves. -/
macro "vmono_auto" : tactic => `(tactic| (
  repeat' (first
    | exact VMono.pure _ | exact VMono.fail _
    | exact vmono_view _ | exact vmono_pinAt _ | exact vmono_pinSortOne
    | exact vmono_pinZeroLevel | exact vmono_pinEmptyLevels | exact vmono_internLNode _
    | exact vmono_internLsNode _ | exact vmono_internE _ | exact vmono_constE _
    | (unfold pinNat) | (unfold pinNatZero) | (unfold pinNatSucc) | (unfold pinString)
    | (unfold pinStringOfList) | (unfold pinList) | (unfold pinListNil) | (unfold pinListCons)
    | (unfold pinChar) | (unfold pinCharOfNat) | (unfold sortOne) | (unfold zeroLevel)
    | with_reducible apply VMono.bind | apply VMono.ite | intro _ | split | (dsimp only))))

theorem vmono_natIndOk (o : Option IConstantInfo) : VMono (natIndOk o) := by
  unfold natIndOk; vmono_auto
theorem vmono_natZeroOk (o : Option IConstantInfo) : VMono (natZeroOk o) := by
  unfold natZeroOk; vmono_auto
theorem vmono_natSuccOk (o : Option IConstantInfo) : VMono (natSuccOk o) := by
  unfold natSuccOk; vmono_auto
theorem vmono_stringTyOk (o : Option IConstantInfo) : VMono (stringTyOk o) := by
  unfold stringTyOk; vmono_auto
theorem vmono_charTyOk (o : Option IConstantInfo) : VMono (charTyOk o) := by
  unfold charTyOk; vmono_auto
theorem vmono_listTyOk (o : Option IConstantInfo) : VMono (listTyOk o) := by
  unfold listTyOk; vmono_auto
theorem vmono_listNilTyOk (o : Option IConstantInfo) : VMono (listNilTyOk o) := by
  unfold listNilTyOk; vmono_auto
theorem vmono_listConsTyOk (o : Option IConstantInfo) : VMono (listConsTyOk o) := by
  unfold listConsTyOk; vmono_auto
theorem vmono_charOfNatTyOk (o : Option IConstantInfo) : VMono (charOfNatTyOk o) := by
  unfold charOfNatTyOk; vmono_auto
theorem vmono_stringOfListTyOk (o : Option IConstantInfo) : VMono (stringOfListTyOk o) := by
  unfold stringOfListTyOk; vmono_auto

theorem vmono_natLitSupported (fe : IFEnv) : VMono (natLitSupported fe) := by
  unfold natLitSupported
  repeat' (first
    | exact VMono.pure _ | exact vmono_pinAt _ | exact vmono_natIndOk _
    | exact vmono_natZeroOk _ | exact vmono_natSuccOk _
    | (unfold pinNat) | (unfold pinNatZero) | (unfold pinNatSucc)
    | with_reducible apply VMono.bind | apply VMono.ite | intro _)

theorem vmono_strLitSupported (fe : IFEnv) : VMono (strLitSupported fe) := by
  unfold strLitSupported pinString pinStringOfList pinList pinListNil pinListCons pinChar
    pinCharOfNat
  repeat' (first
    | with_reducible exact VMono.pure _ | with_reducible exact vmono_pinAt _
    | with_reducible exact vmono_natLitSupported _
    | with_reducible exact vmono_stringTyOk _ | with_reducible exact vmono_charTyOk _
    | with_reducible exact vmono_listTyOk _ | with_reducible exact vmono_listNilTyOk _
    | with_reducible exact vmono_listConsTyOk _ | with_reducible exact vmono_charOfNatTyOk _
    | with_reducible exact vmono_stringOfListTyOk _
    | with_reducible apply VMono.bind | with_reducible apply VMono.ite | intro _)

/-- **`strLitSupported` keeps every stored node's view.** -/
theorem supKeep_of (fe : IFEnv) : SupKeep fe := by
  intro a h w hw
  have hm := vmono_strLitSupported fe
  unfold VMono at hm
  unfold AM.st
  split
  · next r a' hr => exact hm a r a' hr h w hw
  · exact hw

end L.Arena
