import ConAgua.Arena.WhnfBase
import ConAgua.L.FuelMono
import ConAgua.Arena.Env

/-!
# A real callee as a program-free, fuel-free word model (`callF`)

A caller's word model must not depend on the program (or its proof needs the lookups of every
callee's callees) nor, ideally, on the fuel of the call (an opaque stub `stubM f` had neither).
For a callee `f` whose functions are a call-closed list `P` (a concrete program, e.g. a walk's
test program), its run in any program that agrees with `P` on those functions is its run in `P`
(`invoke_agree`: the closure is the `closedW` check of the text, which also gives the write
set), and a run that returns at some fuel returns the same at every larger one (`exec_le`). So
`callF P f m vs` — the result of a returning run in `P` (at any fuel: they agree) — is what every call of
`f` returns, at any fuel, in any such program (`callF_spec`). Facts about `callF` come from facts
about runs in `P` (`callF_run`).
-/

open Std.WP
open scoped Lean.Order

namespace L.Arena

open L

section agree
variable {ctl : ArrId} {p q : Prog} {A : List ArrId} {C : List Word} {fs : List FnName}

/-- **Programs that agree on a call-closed set execute its statements alike.** -/
theorem exec_agree (hq : closedW ctl q A C fs = true) (hpq : ∀ f ∈ fs, p.lookup f = q.lookup f) :
    ∀ (n : Nat) (t : Stmt), t.okW ctl A C fs = true → exec p n t = exec q n t := by
  intro n
  induction n with
  | zero => intro t _; rfl
  | succ n ih =>
    intro t ht
    show step p (exec p n) t = step q (exec q n) t
    induction t with
    | «skip» => rfl
    | set x e => rfl
    | st8 a i e => rfl
    | st64 a i e => rfl
    | seq s t ihs iht =>
      simp only [Stmt.okW, Bool.and_eq_true] at ht
      simp only [step, ihs ht.1, iht ht.2]
    | ite c s t ihs iht =>
      simp only [Stmt.okW, Bool.and_eq_true] at ht
      simp only [step, ihs ht.1, iht ht.2]
    | «while» c s ihs =>
      have ht' : s.okW ctl A C fs = true := by simpa [Stmt.okW] using ht
      simp only [step, ihs ht', ih (.while c s) ht]
    | brk => rfl
    | ret es => rfl
    | «call» xs f args =>
      have hf : f ∈ fs := by simpa [Stmt.okW] using ht
      have hi : invoke p (exec p n) f = invoke q (exec q n) f := by
        funext vs
        simp only [invoke, lookupFn, hpq f hf]
        cases hl : q.lookup f with
        | none => rfl
        | some fd =>
          simp only [callFn, pure_bind]
          rw [ih fd.body (closedW_lookup hq hf hl)]
      simp only [step, hi]
    | «abort» e => rfl
    | «gset» g e => rfl
    | st64t a t i e => rfl
    | copy64 d di s si n => rfl
    | copy8w d di s si n => rfl
    | scan8 x s i e c => rfl

theorem invoke_agree (hq : closedW ctl q A C fs = true) (hpq : ∀ f ∈ fs, p.lookup f = q.lookup f)
    (n : Nat) {f : FnName} (hf : f ∈ fs) : invoke p (exec p n) f = invoke q (exec q n) f := by
  funext vs
  simp only [invoke, lookupFn, hpq f hf]
  cases hl : q.lookup f with
  | none => rfl
  | some fd =>
    simp only [callFn, pure_bind]
    rw [exec_agree hq hpq n fd.body (closedW_lookup hq hf hl)]

theorem callW_agree (hq : closedW ctl q A C fs = true) (hpq : ∀ f ∈ fs, p.lookup f = q.lookup f)
    (n : Nat) {f : FnName} (hf : f ∈ fs) (vs : List Word) (m : Mem) :
    callW p n f vs m = callW q n f vs m := by
  simp only [callW, invoke_agree hq hpq n hf]

end agree

/-- More fuel, the same returning call. -/
theorem callW_mono {P : Prog} {n n' : Nat} {f : FnName} {vs : List Word} {m : Mem}
    {x : List Word × Mem} (h : callW P n f vs m = some x) (hn : n ≤ n') : callW P n' f vs m = some x := by
  simp only [callW] at h ⊢
  cases hr : (invoke P (exec P n) f vs).run ⟨m, Locals.init []⟩ with
  | error e => rw [hr] at h; cases h
  | ok q =>
    rw [hr] at h
    rw [invoke_mono (exec_le P hn) hr]
    exact h

open Classical in
/-- **The fuel-free model of a call of `f` in the program `P`**: the result of a returning run
at some fuel (all agree, `callW_mono`). -/
noncomputable def callF (P : Prog) (f : FnName) (m : Mem) (vs : List Word) : Option (List Word × Mem) :=
  if h : ∃ x n, callW P n f vs m = some x then some (Classical.choose h) else none

theorem callF_of_callW {P : Prog} {n : Nat} {f : FnName} {vs : List Word} {m : Mem}
    {x : List Word × Mem} (h : callW P n f vs m = some x) : callF P f m vs = some x := by
  have hex : ∃ x n, callW P n f vs m = some x := ⟨x, n, h⟩
  simp only [callF, dite_eq_left hex]
  obtain ⟨n', hn'⟩ := Classical.choose_spec hex
  have h1 := callW_mono h (Nat.le_max_left n n')
  have h2 := callW_mono hn' (Nat.le_max_right n n')
  rw [h1] at h2
  exact congrArg some (Option.some.inj h2).symm

/-- **A model fact is a run fact**: a returning `callF` is a returning run in `P` at some fuel. -/
theorem callF_run {P : Prog} {f : FnName} {vs : List Word} {m : Mem} {x : List Word × Mem}
    (h : callF P f m vs = some x) : ∃ n, callW P n f vs m = some x := by
  simp only [callF] at h
  split at h
  · rename_i hex
    obtain ⟨n, hn⟩ := Classical.choose_spec hex
    exact ⟨n, by rw [hn]; exact h⟩
  · cases h

/-- **Every call of `f` returns `callF P f`**, in a program that binds `P`'s functions as `P`
does, `P` call-closed over `fs ∋ f`. -/
theorem callF_spec {ctl : ArrId} {p P : Prog} {A : List ArrId} {C : List Word} {fs : List FnName}
    (hq : closedW ctl P A C fs = true) (hp : ∀ g ∈ fs, p.lookup g = P.lookup g) {f : FnName}
    (hf : f ∈ fs) (n : Nat) (s₀ : St) (vs : List Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) f vs
    ⦃fun r s' => LocEq s' s₀ ∧ callF P f s₀.mem vs = some (r, s'.mem); ⊤⦄ :=
  triple_post (callW_spec p n f vs s₀) fun _ _ ⟨hl, hc⟩ =>
    ⟨hl, callF_of_callW (by rw [← callW_agree hq hp n hf]; exact hc)⟩

end L.Arena
