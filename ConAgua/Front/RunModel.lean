import ConAgua.L.FuelMono

/-!
# The run of a function as its model

`runF p f vs m`: the memory after a successful run of `f vs` on `m` with some fuel (`none` if no
fuel gives one). It is well defined because a run that succeeds with fuel `n` gives the same result
with more fuel (`exec_mono`, `L/FuelMono.lean`), and the
caller's locals do not matter (`invoke_loc`). `runF_spec`: every successful run of `f` ends in
`runF`'s memory, so a function whose own model carries a fuel index (the apply step of an
`inductive` line) can be called from a fuel-free model.
-/

open Std.WP
open scoped Lean.Order

namespace L.Front

open L

export L (KExt run_bind_ok run_bind_of invoke_mono step_mono exec_mono exec_le)

/-- A call's run does not depend on the caller's locals, which it restores. -/
theorem invoke_loc {p : Prog} {k : Stmt → M Sig} {f : FnName} {vs : List Word} {s : St}
    {r : List Word} {t : St} (h : (invoke p k f vs).run s = .ok (r, t)) :
    t.loc = s.loc ∧ ∀ s' : St, s'.mem = s.mem → (invoke p k f vs).run s' = .ok (r, { t with loc := s'.loc }) := by
  unfold invoke at h ⊢
  obtain ⟨fd, s1, h1, h2⟩ := run_bind_ok h
  have hl : ∀ s' : St, (lookupFn p f).run s' = .ok (fd, s') ∧ s1 = s := by
    intro s'
    unfold lookupFn at h1 ⊢
    cases hp : p.lookup f with
    | none => rw [hp] at h1; cases h1
    | some fd' =>
      rw [hp] at h1
      simp only [StateT.run_pure] at h1
      obtain ⟨rfl, rfl⟩ := h1
      exact ⟨rfl, rfl⟩
  obtain ⟨-, rfl⟩ := hl s
  unfold callFn at h2
  obtain ⟨s2, s3, h3, h4⟩ := run_bind_ok h2
  simp only [StateT.run_get] at h3
  obtain ⟨rfl, rfl⟩ := h3
  obtain ⟨u, s4, h5, h6⟩ := run_bind_ok h4
  simp only [StateT.run_set] at h5
  obtain ⟨-, rfl⟩ := h5
  obtain ⟨rr, s5, h7, h8⟩ := run_bind_ok h6
  obtain ⟨u2, s6, h9, h10⟩ := run_bind_ok h8
  simp only [StateT.run_modify] at h9
  obtain ⟨-, rfl⟩ := h9
  simp only [StateT.run_pure] at h10
  obtain ⟨rfl, rfl⟩ := h10
  refine ⟨rfl, fun s' hs' => ?_⟩
  refine run_bind_of (hl s').1 ?_
  unfold callFn
  refine run_bind_of (s' := s') (a := s') rfl ?_
  refine run_bind_of (a := ()) (s' := { s' with loc := Locals.init vs }) rfl ?_
  have e : ({ s' with loc := Locals.init vs } : St) = { s1 with loc := Locals.init vs } := by
    cases s1; cases s'; simp only at hs'; subst hs'; rfl
  rw [e]
  refine run_bind_of h7 ?_
  refine run_bind_of (a := ()) (s' := { s5 with loc := s'.loc }) rfl ?_
  rfl

/-- The run of `f vs` on `m` with fuel `n`: its results and final state. -/
def RunOK (p : Prog) (f : FnName) (vs : List Word) (m : Mem) (x : Nat × List Word × St) : Prop :=
  (invoke p (exec p x.1) f vs).run ⟨m, Locals.init []⟩ = .ok (x.2.1, x.2.2)

open Classical in
/-- **The memory after a successful run of `f vs` on `m`** (any fuel), `none` if there is none. -/
noncomputable def runF (p : Prog) (f : FnName) (vs : List Word) (m : Mem) : Option Mem :=
  if h : ∃ x, RunOK p f vs m x then some (Classical.choose h).2.2.mem else none

/-- Two successful runs from the same memory end in the same memory. -/
theorem runOK_mem {p : Prog} {f : FnName} {vs : List Word} {m : Mem} {x y : Nat × List Word × St}
    (hx : RunOK p f vs m x) (hy : RunOK p f vs m y) : x.2.2.mem = y.2.2.mem := by
  unfold RunOK at hx hy
  have h1 := invoke_mono (exec_le p (Nat.le_max_left x.1 y.1)) hx
  have h2 := invoke_mono (exec_le p (Nat.le_max_right x.1 y.1)) hy
  rw [h1] at h2
  simp only [Except.ok.injEq, Prod.mk.injEq] at h2
  rw [h2.2]

theorem runF_of {p : Prog} {f : FnName} {vs : List Word} {m : Mem} {x : Nat × List Word × St}
    (hx : RunOK p f vs m x) : runF p f vs m = some x.2.2.mem := by
  have h : ∃ x, RunOK p f vs m x := ⟨x, hx⟩
  unfold runF
  rw [dite_eq_left h, runOK_mem (Classical.choose_spec h) hx]

theorem runF_some {p : Prog} {f : FnName} {vs : List Word} {m m' : Mem} (h : runF p f vs m = some m') :
    ∃ x, RunOK p f vs m x ∧ x.2.2.mem = m' := by
  unfold runF at h
  split at h
  · rename_i hx
    simp only [Option.some.injEq] at h
    exact ⟨_, Classical.choose_spec hx, h⟩
  · cases h

/-- **Every successful run of `f` is `runF`'s.** -/
theorem runF_spec (p : Prog) (f : FnName) (vs : List Word) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) f vs
    ⦃fun _ s' => LocEq s' s₀ ∧ runF p f vs s₀.mem = some s'.mem; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs h
  subst hs
  obtain ⟨hl, h'⟩ := invoke_loc h
  refine ⟨hl, ?_⟩
  have := h' ⟨s.mem, Locals.init []⟩ rfl
  exact runF_of (x := (n, r, { s' with loc := Locals.init [] })) this

end L.Front
