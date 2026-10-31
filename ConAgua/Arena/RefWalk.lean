import ConAgua.Arena.Verdict
import ConAgua.Arena.SimLib

/-!
# The lockstep walk of a unified model against its twin

A `RefE` proof walks the model (`l_model … unified`: a chain of continuations `K`, one per call,
each a `match` on the callee's outcome followed by the arm's guards) and the twin (a `do` block)
in step. This file is the walk's step rules, one per pair of shapes, both outcomes at once
(docs/design/refgen.md):

* `RefE.bindSim`: a lifted callee (`K (liftE c)`, outside the verdict closure) against the twin's
  bind, by the callee's `Sim` (its registered step): no `rcases`, `liftE_none`, `K.none`,
  `of_cls0`, `liftE_some`, `bind_right`; `RefE.bindLift` is the same for a callee without a step
  lemma, its run and the rest proved at the call site;
* `RefE.bindE` / `RefE.lastE`: a unified callee (`K x`) by its own `RefE`, then the rest / as the
  twin's last step; `RefE.bindRun`: a unified callee read through its call's run
  (`K (callE …)`, its model spec and its `RefE`); `RefE.bindCall`: a knot callee read through its
  call (`K (callE …)`, its error by `G`, its ok run by an `RSim`);
* `RefE.onlySim`: a lifted callee the twin has no step for (an L helper: `sl_eq`);
* the guards of the model (`if c then .error e else rest`): `RefE.guard` against the twin's
  `unless … do fail` (its do-elaboration `if b = true then jp () else fail ce >>= jp`),
  `RefE.guardIf` / `RefE.guardThen` against `if b then rest else fail ce` / `if b then fail ce
  else rest`, `RefE.guardOpt` against `unwrapOr o ce >>= g`, the two conditions related by one
  implication each way; `RefE.abort0` for a guard of the model alone with a class-`0` abort;
  `RefE.abortAt` / `RefE.pass` where a split of the proof already decided the guard;
* `RefE.twinFail` / `RefE.twinPass`: a guard of the twin that L checks in pieces;
* `RefE.ofArms`: an irreducible continuation (a recursive model's) read through its guarded
  equations as the `if` the guard rules take.

Between two rules, `dsimp only [K]` unfolds the continuation `K` at the head of the model
(`K (.ok (r, m))` to its arm), or `rw [K.arm1]` where `K` is irreducible. docs/design/refgen.md, "Migration recipe", is the shape of a
converted proof.
-/

open ConRon.Arena
open Std.WP

namespace L.Arena

section walk
variable {α β γ ρ : Type} {G : Prop} {a : AState} {R : α → β → AState → Prop}

/-- **A lifted callee, then the rest**, both outcomes: the callee's `Sim` (its step under the
caller's invariant package) runs the twin's first step; the model's `none` is class `0`. -/
theorem RefE.bindSim {K : Except Err (ρ × Mem) → Except Err α}
    (hK : ∀ e, K (.error e) = .error e) {c : Option (ρ × Mem)} {op : AM γ} {g : γ → AM β}
    {Q : ρ → γ → Mem → AState → Prop} (h1 : Sim c op a Q)
    (h2 : ∀ r x m₁ a₁, c = some (r, m₁) → op.run a = .ok (x, a₁) → Q r x m₁ a₁ →
      RefE G (K (.ok (r, m₁))) (g x) a₁ R) :
    RefE G (K (liftE c)) (op >>= g) a R := by
  rcases hc : c with _ | ⟨r, m₁⟩
  · rw [liftE_none, hK]; exact RefE.of_cls0 (by simp)
  obtain ⟨x, a₁, hr, hQ⟩ := h1 r m₁ hc
  exact RefE.bind_right hr (h2 r x m₁ a₁ hc hr hQ)

/-- **A lifted callee without a step lemma** (one call site): `bindSim` with the rest as the
callee's post; the call site proves the twin's run and the rest from the model's result. -/
theorem RefE.bindLift {K : Except Err (ρ × Mem) → Except Err α}
    (hK : ∀ e, K (.error e) = .error e) {c : Option (ρ × Mem)} {op : AM γ} {g : γ → AM β}
    (h : ∀ r m₁, c = some (r, m₁) → ∃ x a₁, op.run a = .ok (x, a₁) ∧ RefE G (K (.ok (r, m₁))) (g x) a₁ R) :
    RefE G (K (liftE c)) (op >>= g) a R :=
  RefE.bindSim (Q := fun r x m₁ a₁ => RefE G (K (.ok (r, m₁))) (g x) a₁ R) hK h fun _ _ _ _ _ _ h => h

/-- **A unified callee read through its call's run** (`callE` and the callee's model spec), then
the rest, both outcomes: the ok half by `RefE.run_ok`, the error half by `RefE.run_err` under the
callee's `G'` and its spec's `Gs`. -/
theorem RefE.bindRun {p : Prog} {n : Nat} {f : FnName} {args : List Word} {s₀ : St}
    {K : Except Err (List Word × Mem) → Except Err α} (hK : ∀ e, K (.error e) = .error e)
    {G' Gs : Prop} {fx : Except Err ρ} {V : List Word → St → ρ} {Q : List Word → St → Prop}
    {op : AM γ} {g : γ → AM β} {S : ρ → γ → AState → Prop}
    (hs : ⦃fun s => s = s₀⦄ invoke p (exec p n) f args
      ⦃fun r s' => Q r s' ∧ fx = .ok (V r s'); fun ε => Gs → ε.cls ≠ 0 → fx = .error ε⦄)
    (hGs : G → Gs) (hG' : G → G') (h1 : RefE G' fx op a S)
    (h2 : ∀ r s' y a₁, callE p n f args s₀.mem = .ok (r, s'.mem) → Q r s' → op.run a = .ok (y, a₁) →
      S (V r s') y a₁ → RefE G (K (.ok (r, s'.mem))) (g y) a₁ R) :
    RefE G (K (callE p n f args s₀.mem)) (op >>= g) a R := by
  rcases c : callE p n f args s₀.mem with e | ⟨r, m'⟩
  · rw [hK]; exact RefE.bind_left fun hG => RefE.run_err hs (hGs hG) (hG' hG) h1 c
  obtain ⟨s', rfl, hQ, y, a₁, hr, hS⟩ := RefE.run_ok hs h1 c
  exact RefE.bind_right hr (h2 r s' y a₁ c hQ hr hS)

/-- **A unified callee read through its call outside `RefE`** (a knot function: `whnf_top`,
`infer_type_core`), both outcomes: its error by the caller's `G` (the knot's `ErrClaim`), its ok
run by an `RSim` of its call (`whnfC_rsim`, `inferC_rsim`). -/
theorem RefE.bindCall {p : Prog} {n : Nat} {f : FnName} {args : List Word} {m : Mem}
    {K : Except Err (List Word × Mem) → Except Err α} (hK : ∀ e, K (.error e) = .error e)
    {op : AM γ} {g : γ → AM β} {Q : List Word × Mem → AState → γ → Prop}
    (herr : G → ∀ e, callE p n f args m = .error e → ErrClaim op a e)
    (h1 : ∀ b, callW p n f args m = some b → ∃ x a₁, op.run a = .ok (x, a₁) ∧ Q b a₁ x)
    (h2 : ∀ r m₁ x a₁, callE p n f args m = .ok (r, m₁) → op.run a = .ok (x, a₁) → Q (r, m₁) a₁ x →
      RefE G (K (.ok (r, m₁))) (g x) a₁ R) :
    RefE G (K (callE p n f args m)) (op >>= g) a R := by
  rcases c : callE p n f args m with e | ⟨r, m₁⟩
  · rw [hK]; exact RefE.bind_left fun hG => herr hG e c
  obtain ⟨x, a₁, hr, hQ⟩ := h1 _ (callW_of_callE c)
  exact RefE.bind_right hr (h2 r m₁ x a₁ c hr hQ)

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

/-- **A guard of an irreducible continuation** (the model of a recursive function): its guarded
equations `K.abortᵢ`/`K.armᵢ`, given as `fun h => K.abort1 (hc1 := h)`, as the `if` the other
guard rules read. -/
theorem RefE.ofArms {x rest : Except Err α} {T : AM β} {c : Prop} [Decidable c] {e : Err}
    (hab : c → x = .error e) (harm : ¬ c → x = rest) (h : RefE G (if c then .error e else rest) T a R) :
    RefE G x T a R := by
  by_cases hc : c
  · rw [hab hc]; rw [ite_eq_left hc] at h; exact h
  · rw [harm hc]; rw [ite_eq_right hc] at h; exact h

/-- **A guard of the model that fires** where the twin's own split already decided (a `match` on a
callee's result): the abort's claim on the twin. -/
theorem RefE.abortAt {c : Prop} [Decidable c] {e : Err} {rest : Except Err α} {T : AM β} (hc : c)
    (h : G → ErrClaim T a e) : RefE G (if c then .error e else rest) T a R := by
  rw [ite_eq_left hc]; exact h

/-- **A guard of the model that passes.** -/
theorem RefE.pass {c : Prop} [Decidable c] {e : Err} {rest : Except Err α} {T : AM β} (hc : ¬ c)
    (h : RefE G rest T a R) : RefE G (if c then .error e else rest) T a R := by
  rw [ite_eq_right hc]; exact h

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

/-- **An abort guard against the twin's `if b then rest else fail ce`** (no join point). -/
theorem RefE.guardIf {c : Prop} [Decidable c] {b : Bool} {e : Err} {ce : CheckError}
    {rest : Except Err α} {T : AM β} (hcls : e.cls = twinCls ce) (hcb : c → b = false)
    (hbc : b = false → c) (h : ¬ c → b = true → RefE G rest T a R) :
    RefE G (if c then .error e else rest) (if b = true then T else fail ce) a R := by
  by_cases hc : c
  · rw [ite_eq_left hc, ite_eq_right (by simp [hcb hc])]
    exact fun _ => ErrClaim.fail _ _ hcls
  · have hb : b = true := by cases hb : b; exact absurd (hbc hb) hc; rfl
    rw [ite_eq_right hc, ite_eq_left hb]; exact h hc hb

/-- **An abort guard against the twin's `if b then fail ce else rest`**. -/
theorem RefE.guardThen {c : Prop} [Decidable c] {b : Bool} {e : Err} {ce : CheckError}
    {rest : Except Err α} {T : AM β} (hcls : e.cls = twinCls ce) (hcb : c → b = true)
    (hbc : b = true → c) (h : ¬ c → b = false → RefE G rest T a R) :
    RefE G (if c then .error e else rest) (if b = true then fail ce else T) a R := by
  by_cases hc : c
  · rw [ite_eq_left hc, ite_eq_left (hcb hc)]
    exact fun _ => ErrClaim.fail _ _ hcls
  · have hb : b = false := by cases hb : b; rfl; exact absurd (hbc hb) hc
    rw [ite_eq_right hc, ite_eq_right (by simp [hb])]; exact h hc hb

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

end L.Arena
