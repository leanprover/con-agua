module

public import ConAgua.L.FuelMono

@[expose] public section

/-!
# A call's run and the caller's locals

`invoke_loc`: a call's run does not depend on the caller's locals, which it restores. The fuel
lemmas of `L/FuelMono.lean` (a run that succeeds with fuel `n` gives the same result with more
fuel, `exec_mono`) are re-exported here.
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

end L.Front
