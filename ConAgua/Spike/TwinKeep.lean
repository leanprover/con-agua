import ConRon.Arena.ExprOps

/-!
# Spike (lane `scale`): twin-side frames by composition

`Keeps π op`: every successful run of `op` leaves the projection `π` of the state alone. Closed
under `bind`, `pure`, `if`, `match`; the store/memo primitives keep `(caches, pins)`. A whole
twin walk family then keeps it by one induction on fuel, with no L and no relation involved:
here `instantiate1Go` (mutual with its four arms). Not imported by `ConAgua`.
-/

namespace ConRon.Arena.Spike

open ConRon.Arena

/-- The checker-tier part of the state an `ExprOps` walk must not touch. -/
def cp (a : AState) : Caches × Pins := (a.caches, a.pins)

def Keeps {β α : Type} (π : AState → β) (op : AM α) : Prop :=
  ∀ a r a', op.run a = .ok (r, a') → π a' = π a

variable {β : Type} {π : AState → β}

theorem Keeps.pure {α : Type} (x : α) : Keeps π (Pure.pure x : AM α) := by
  intro a r a' h; cases h; rfl

theorem Keeps.fail {α : Type} (e : CheckError) : Keeps π (ConRon.Arena.fail e : AM α) := by
  intro a r a' h; cases h

theorem Keeps.bind {α γ : Type} {x : AM α} {f : α → AM γ} (hx : Keeps π x) (hf : ∀ v, Keeps π (f v)) :
    Keeps π (x >>= f) := by
  intro a r a' h
  simp only [StateT.run_bind] at h
  cases h1 : x.run a with
  | error e => rw [h1] at h; cases h
  | ok p =>
    obtain ⟨v, a₁⟩ := p
    rw [h1] at h
    exact (hf v a₁ r a' h).trans (hx a v a₁ h1)

theorem Keeps.ite {α : Type} {c : Prop} [Decidable c] {x y : AM α} (hx : Keeps π x) (hy : Keeps π y) :
    Keeps π (if c then x else y) := by
  split <;> assumption

/-- A read of the state. -/
theorem Keeps.read {α : Type} (f : AState → α) : Keeps π (do let s ← get; Pure.pure (f s) : AM α) := by
  intro a r a' h; cases h; rfl

/-- A store primitive: read the state, then answer, fail, or write back with only the store changed. -/
macro "prim_keeps " d:ident : tactic => `(tactic| (
  intro a r a' h
  simp only [$d:ident, StateT.run_bind, StateT.run_get, pure_bind] at h
  repeat' split at h
  all_goals simp only [StateT.run_bind, StateT.run_set, StateT.run_pure, pure_bind,
    ConRon.Arena.fail, throwThe, MonadExceptOf.throw] at h
  all_goals first | (cases h; rfl) | (simp [throwThe, throw, Functor.map, Except.map] at h)))

set_option linter.unusedSimpArgs false

theorem keeps_internNodeE (v : ENodeView) : Keeps cp (internNodeE v) := by prim_keeps internNodeE
theorem keeps_internLamE (ty b : EIdx) : Keeps cp (internLamE ty b) := by prim_keeps internLamE
theorem keeps_internForallEE (ty b : EIdx) : Keeps cp (internForallEE ty b) := by
  prim_keeps internForallEE

theorem keeps_internE (v : ENodeView) : Keeps cp (internE v) := by
  cases v <;> simp only [internE] <;> first | exact keeps_internNodeE _ | exact keeps_internLamE _ _ |
    exact keeps_internForallEE _ _

theorem keeps_inst1Set (k : EIdx × Nat) (r : EIdx) : Keeps cp (inst1Set k r) := by
  intro a x a' h; cases h; rfl
theorem keeps_inst1Clear : Keeps cp inst1Clear := by
  intro a x a' h; cases h; rfl

/-- The primitives a walk is made of, for `Keeps.bind`'s first argument. -/
theorem keeps_derivedE (h : EIdx) : Keeps cp (derivedE h) := Keeps.read _
theorem keeps_inst1Get (k : EIdx × Nat) : Keeps cp (inst1Get k) := Keeps.read _
theorem keeps_viewApp (h : EIdx) : Keeps cp (viewApp h) := Keeps.read _
theorem keeps_viewBind (h : EIdx) : Keeps cp (viewBind h) := Keeps.read _
theorem keeps_viewLet (h : EIdx) : Keeps cp (viewLet h) := Keeps.read _
theorem keeps_viewProj (h : EIdx) : Keeps cp (viewProj h) := Keeps.read _
theorem keeps_viewBVar (h : EIdx) : Keeps cp (viewBVar h) := Keeps.read _

theorem keeps_instArmBVar (v h : EIdx) (d : Nat) : Keeps cp (instantiate1ArmBVar v h d) := by
  unfold instantiate1ArmBVar
  refine Keeps.bind (keeps_viewBVar h) fun o => ?_
  cases o with
  | none => exact Keeps.fail _
  | some i => exact Keeps.ite (Keeps.pure _) (Keeps.ite (keeps_internE _) (Keeps.pure _))

/-- **`instantiate1Go` keeps `(caches, pins)`**, every fuel: one induction, one line per arm. -/
theorem keeps_inst1Go (v : EIdx) (F : Nat) : ∀ h d, Keeps cp (instantiate1Go v F h d) := by
  induction F with
  | zero => intro h d; rw [instantiate1Go_zero]; exact Keeps.fail _
  | succ F ih =>
    intro h d
    rw [instantiate1Go_succ]
    refine Keeps.bind (keeps_derivedE h) fun _ => Keeps.ite (Keeps.pure _) (Keeps.ite ?_ (Keeps.ite ?_
      (Keeps.ite (keeps_instArmBVar v h d) (Keeps.ite ?_ (Keeps.ite ?_ (Keeps.pure _))))))
    · rw [instantiate1ArmApp]
      refine Keeps.bind (keeps_inst1Get _) fun o => ?_
      cases o with
      | some r => exact Keeps.pure r
      | none =>
        refine Keeps.bind (keeps_viewApp _) fun o => ?_
        cases o with
        | none => exact Keeps.fail _
        | some p => exact Keeps.bind (ih _ _) fun _ => Keeps.bind (ih _ _) fun _ =>
            Keeps.bind (keeps_internE _) fun r => Keeps.bind (keeps_inst1Set _ _) fun _ => Keeps.pure r
    · rw [instantiate1ArmBind]
      refine Keeps.bind (keeps_inst1Get _) fun o => ?_
      cases o with
      | some r => exact Keeps.pure r
      | none =>
        refine Keeps.bind (keeps_viewBind _) fun o => ?_
        cases o with
        | none => exact Keeps.fail _
        | some p => exact Keeps.bind (ih _ _) fun _ => Keeps.bind (ih _ _) fun _ =>
            Keeps.bind (Keeps.ite (keeps_internLamE _ _) (keeps_internForallEE _ _)) fun r =>
              Keeps.bind (keeps_inst1Set _ _) fun _ => Keeps.pure r
    · rw [instantiate1ArmLet]
      refine Keeps.bind (keeps_inst1Get _) fun o => ?_
      cases o with
      | some r => exact Keeps.pure r
      | none =>
        refine Keeps.bind (keeps_viewLet _) fun o => ?_
        cases o with
        | none => exact Keeps.fail _
        | some p => exact Keeps.bind (ih _ _) fun _ => Keeps.bind (ih _ _) fun _ =>
            Keeps.bind (ih _ _) fun _ => Keeps.bind (keeps_internE _) fun r =>
              Keeps.bind (keeps_inst1Set _ _) fun _ => Keeps.pure r
    · rw [instantiate1ArmProj]
      refine Keeps.bind (keeps_inst1Get _) fun o => ?_
      cases o with
      | some r => exact Keeps.pure r
      | none =>
        refine Keeps.bind (keeps_viewProj _) fun o => ?_
        cases o with
        | none => exact Keeps.fail _
        | some p => exact Keeps.bind (ih _ _) fun _ => Keeps.bind (keeps_internE _) fun r =>
            Keeps.bind (keeps_inst1Set _ _) fun _ => Keeps.pure r

theorem keeps_inst1Fast (F : Nat) (e v : EIdx) (d : Nat) : Keeps cp (instantiate1Fast F e v d) := by
  unfold instantiate1Fast
  exact Keeps.bind keeps_inst1Clear fun _ => Keeps.bind (keeps_inst1Go v F e d) fun _ =>
    Keeps.bind keeps_inst1Clear fun _ => Keeps.pure _

end ConRon.Arena.Spike
