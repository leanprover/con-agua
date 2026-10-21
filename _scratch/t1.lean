import ConAgua.Arena.WhnfBase
open L L.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- The result of calling `f` on `vs` from memory `m` (the caller's locals do not matter). -/
def callW (p : Prog) (n : Nat) (f : FnName) (vs : List Word) (m : Mem) :
    Option (List Word × Mem) :=
  match (invoke p (exec p n) f vs).run ⟨m, Locals.init []⟩ with
  | .ok (r, s) => some (r, s.mem)
  | .error _ => none

theorem invoke_run_loc (p : Prog) (k : Stmt → M Sig) (f : FnName) (vs : List Word) (s : St) :
    (invoke p k f vs).run s =
      ((invoke p k f vs).run ⟨s.mem, Locals.init []⟩).map
        (fun (r, s') => (r, ({ s' with loc := s.loc } : St))) := by
  simp only [invoke, lookupFn]
  cases p.lookup f with
  | none => rfl
  | some fd =>
    simp only [callFn, StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_modify]
    simp [Except.map]
    cases (k fd.body).run { mem := s.mem, loc := Locals.init vs } <;> rfl

/-- **Every call meets its own run.** -/
theorem callW_spec (p : Prog) (n : Nat) (f : FnName) (vs : List Word) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) f vs
    ⦃fun r s' => LocEq s' s₀ ∧ callW p n f vs s₀.mem = some (r, s'.mem); ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  subst hs
  rw [invoke_run_loc] at hrun
  simp only [callW]
  cases h : (invoke p (exec p n) f vs).run { mem := s.mem, loc := Locals.init [] } with
  | error e => simp [h, Except.map] at hrun
  | ok q =>
    simp [h, Except.map] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    exact ⟨rfl, rfl⟩

end L.Arena
