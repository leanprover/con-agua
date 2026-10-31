import ConAgua.Arena.Verdict
import ConAgua.Arena.SimLib

/-!
# The lockstep walk of a unified model against its twin (lane `refgen`, pilot)

A `RefE` proof walks the model (`l_model … unified`: a chain of continuations `K`, one per call,
each a `match` on the callee's outcome followed by the arm's guards) and the twin (a `do` block)
in step. This file is the walk's step rules, one per pair of shapes, both outcomes at once
(docs/design/refgen.md):

* `RefE.bindSim`: a lifted callee (`K (liftE c)`, outside the verdict closure) against the twin's
  bind, by the callee's `Sim` (its registered step): no `rcases`, `liftE_none`, `K.none`,
  `of_cls0`, `liftE_some`, `bind_right`;
* `RefE.bindE` / `RefE.lastE`: a unified callee (`K x`) by its own `RefE`, then the rest / as the
  twin's last step;
* `RefE.onlySim`: a lifted callee the twin has no step for (an L helper: `sl_eq`);
* `RefE.guard`: an abort guard of the model against the twin's `unless … do fail` (its
  do-elaboration `if b = true then jp () else fail ce >>= jp`), the two conditions related by
  one implication each way;
* `RefE.guardOpt`: an abort guard against the twin's `unwrapOr o ce >>= g`;
* `RefE.twinFail`: the model aborts where the twin's guard fails (a guard of the twin that L
  checks in pieces).

`walk_k` unfolds the continuation at the head of the model (`K (.ok (r, m))` to its arm).
-/

open ConRon.Arena

namespace L.Arena

section walk
variable {α β γ ρ : Type} {G : Prop} {a : AState} {R : α → β → AState → Prop}

/-- **A lifted callee, then the rest**, both outcomes: the callee's `Sim` (its step under the
caller's invariant package) runs the twin's first step; the model's `none` is class `0`. -/
theorem RefE.bindSim {K : Except Err (ρ × Mem) → Except Err α}
    (hK : ∀ e, K (.error e) = .error e) {c : Option (ρ × Mem)} {op : AM γ} {g : γ → AM β}
    {Q : ρ → γ → Mem → AState → Prop} (h1 : Sim c op a Q)
    (h2 : ∀ r x m₁ a₁, op.run a = .ok (x, a₁) → Q r x m₁ a₁ → RefE G (K (.ok (r, m₁))) (g x) a₁ R) :
    RefE G (K (liftE c)) (op >>= g) a R := by
  rcases hc : c with _ | ⟨r, m₁⟩
  · rw [liftE_none, hK]; exact RefE.of_cls0 (by simp)
  obtain ⟨x, a₁, hr, hQ⟩ := h1 r m₁ hc
  exact RefE.bind_right hr (h2 r x m₁ a₁ hr hQ)

/-- **A lifted callee the twin has no step for** (an L helper): its model fact `Q`, the twin
unchanged. -/
theorem RefE.onlySim {K : Except Err (ρ × Mem) → Except Err α}
    (hK : ∀ e, K (.error e) = .error e) {c : Option (ρ × Mem)} {T : AM β}
    {Q : ρ → Mem → Prop} (h1 : ∀ r m₁, c = some (r, m₁) → Q r m₁)
    (h2 : ∀ r m₁, Q r m₁ → RefE G (K (.ok (r, m₁))) T a R) :
    RefE G (K (liftE c)) T a R := by
  rcases hc : c with _ | ⟨r, m₁⟩
  · rw [liftE_none, hK]; exact RefE.of_cls0 (by simp)
  exact h2 r m₁ (h1 r m₁ hc)

/-- **A unified callee, then the rest**, both outcomes: its own `RefE` (under its `G'`). -/
theorem RefE.bindE {K : Except Err ρ → Except Err α} (hK : ∀ e, K (.error e) = .error e)
    {G' : Prop} (hG : G → G') {x : Except Err ρ} {op : AM γ} {g : γ → AM β}
    {Q : ρ → γ → AState → Prop} (h1 : RefE G' x op a Q)
    (h2 : ∀ v y a₁, op.run a = .ok (y, a₁) → Q v y a₁ → RefE G (K (.ok v)) (g y) a₁ R) :
    RefE G (K x) (op >>= g) a R := by
  cases x with
  | error e => rw [hK]; exact RefE.bind_left fun hg => h1 (hG hg)
  | ok v =>
    obtain ⟨y, a₁, hr, hQ⟩ := h1
    exact RefE.bind_right hr (h2 v y a₁ hr hQ)

/-- **A unified callee as the twin's last step**: the model's ok arm returns `f v`. -/
theorem RefE.lastE {K : Except Err ρ → Except Err α} (hK : ∀ e, K (.error e) = .error e)
    {f : ρ → α} (hK' : ∀ v, K (.ok v) = .ok (f v)) {G' : Prop} (hG : G → G')
    {x : Except Err ρ} {op : AM β} {Q : ρ → β → AState → Prop} (h1 : RefE G' x op a Q)
    (h2 : ∀ v y a₁, op.run a = .ok (y, a₁) → Q v y a₁ → R (f v) y a₁) : RefE G (K x) op a R := by
  cases x with
  | error e => rw [hK]; exact fun hg => h1 (hG hg)
  | ok v =>
    obtain ⟨y, a₁, hr, hQ⟩ := h1
    rw [hK']; exact ⟨y, a₁, hr, h2 v y a₁ hr hQ⟩

/-- **A guard of the model alone whose abort claims nothing** (class `0`: a capacity, a range). -/
theorem RefE.abort0 {c : Prop} [Decidable c] {e : Err} {rest : Except Err α} {T : AM β}
    (he : e.cls = 0) (h : ¬ c → RefE G rest T a R) : RefE G (if c then .error e else rest) T a R := by
  by_cases hc : c
  · rw [ite_eq_left hc]; exact RefE.of_cls0 he
  · rw [ite_eq_right hc]; exact h hc

/-- **An abort guard against the twin's `unless b do fail ce`**: the model aborts with `e`
exactly when `b` is false; the error classes agree. -/
theorem RefE.guard {c : Prop} [Decidable c] {b : Bool} {e : Err} {ce : CheckError}
    {rest : Except Err α} {jp : Unit → AM β} (hcls : e.cls = twinCls ce) (hcb : c → b = false)
    (hbc : b = false → c) (h : ¬ c → b = true → RefE G rest (jp ()) a R) :
    RefE G (if c then .error e else rest) (if b = true then jp () else fail ce >>= jp) a R := by
  by_cases hc : c
  · rw [ite_eq_left hc, ite_eq_right (by simp [hcb hc])]
    exact RefE.bind_left fun _ => ErrClaim.fail _ _ hcls
  · have hb : b = true := by cases hb : b; exact absurd (hbc hb) hc; rfl
    rw [ite_eq_right hc, ite_eq_left hb]; exact h hc hb

/-- **An abort guard against the twin's `unwrapOr o ce`**: the model aborts with `e` exactly when
`o` is `none`. -/
theorem RefE.guardOpt {c : Prop} [Decidable c] {o : Option γ} {e : Err} {ce : CheckError}
    {rest : Except Err α} {g : γ → AM β} (hcls : e.cls = twinCls ce) (hc : c → o = none)
    (hn : o = none → c) (h : ∀ v, o = some v → ¬ c → RefE G rest (g v) a R) :
    RefE G (if c then .error e else rest) (unwrapOr o ce >>= g) a R := by
  cases ho : o with
  | none =>
    rw [ite_eq_left (hn ho)]
    exact RefE.bind_left fun _ => ErrClaim.fail _ _ hcls
  | some v =>
    have hnc : ¬ c := fun h' => by simp [ho] at hc; exact hc h'
    rw [ite_eq_right hnc]
    exact RefE.bind_right rfl (h v ho hnc)

/-- **The model aborts where the twin's guard fails** (`b` false, the model's error of the
twin's class). -/
theorem RefE.twinFail {b : Bool} {e : Err} {ce : CheckError} {jp : Unit → AM β}
    (hcls : e.cls = twinCls ce) (hb : b = false) :
    RefE G (.error e : Except Err α) (if b = true then jp () else fail ce >>= jp) a R := by
  rw [ite_eq_right (by simp [hb])]
  exact RefE.bind_left fun _ => ErrClaim.fail _ _ hcls

/-- The twin's guard holds: its join point. -/
theorem RefE.twinPass {b : Bool} {ce : CheckError} {jp : Unit → AM β} {x : Except Err α}
    (hb : b = true) (h : RefE G x (jp ()) a R) :
    RefE G x (if b = true then jp () else fail ce >>= jp) a R := by
  rw [ite_eq_left hb]; exact h

end walk

/-- **`walk_k`**: unfold the continuation `K` applied at the head of the model (the arm of a
`K (.ok (r, m))` and its `match`), and beta-reduce the twin's continuation. -/
syntax "walk_k " ident : tactic
macro_rules
  | `(tactic| walk_k $k:ident) => `(tactic| dsimp only [$k:ident])

end L.Arena
