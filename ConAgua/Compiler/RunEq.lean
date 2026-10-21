module

public import ConAgua.Compiler.SimExpr

@[expose] public section

/-!
# One step of `L`, as a function of the state

The run of `step p K s` on a state, one equation per statement form, in terms of the pure
evaluators `evalP`/`evalCP`/`evalArgsP`.
-/

namespace L.Compiler

open L

/-- `evalArgs`, without the state. -/
def evalArgsP (σ : St) : List Expr → Except Err (List Word)
  | [] => .ok []
  | e :: es => do
    let v ← evalP σ e
    let vs ← evalArgsP σ es
    return v :: vs

theorem evalArgs_run (σ : St) (es : List Expr) : (evalArgs es).run σ = (evalArgsP σ es).map (·, σ) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [evalArgs, evalArgsP, StateT.run_bind, evalE_run]
    cases evalP σ e with
    | error => rfl
    | ok v =>
      simp only [Except.map, bind, Except.bind, ih]
      cases evalArgsP σ es <;> rfl

variable (p : Prog) (K : Stmt → M Sig) (σ : St)

theorem step_skip_run : (step p K .skip).run σ = .ok (.normal, σ) := rfl

theorem step_set_run (x : Var) (e : Expr) :
    (step p K (.set x e)).run σ = (evalP σ e).map fun v => (.normal, σ.setLoc x v) := by
  simp only [step, StateT.run_bind, evalE_run]
  cases evalP σ e <;> rfl

theorem step_seq_run (s t : Stmt) :
    (step p K (.seq s t)).run σ =
      match (step p K s).run σ with
      | .ok (.normal, σ') => (step p K t).run σ'
      | .ok (r, σ') => .ok (r, σ')
      | .error e => .error e := by
  simp only [step, StateT.run_bind]
  rcases (step p K s).run σ with e | ⟨r, σ'⟩
  · rfl
  · cases r <;> rfl

theorem step_ite_run (c : Cond) (s t : Stmt) :
    (step p K (.ite c s t)).run σ =
      match evalCP σ c with
      | .ok true => (step p K s).run σ
      | .ok false => (step p K t).run σ
      | .error e => .error e := by
  simp only [step, StateT.run_bind, evalC_run]
  rcases evalCP σ c with e | b
  · rfl
  · cases b <;> rfl

theorem step_while_run (c : Cond) (s : Stmt) :
    (step p K (.while c s)).run σ =
      match evalCP σ c with
      | .error e => .error e
      | .ok false => .ok (.normal, σ)
      | .ok true =>
        match (step p K s).run σ with
        | .ok (.normal, σ') => (K (.while c s)).run σ'
        | .ok (.brk, σ') => .ok (.normal, σ')
        | .ok (.ret v, σ') => .ok (.ret v, σ')
        | .error e => .error e := by
  simp only [step, StateT.run_bind, evalC_run]
  rcases evalCP σ c with e | b
  · rfl
  · cases b
    · rfl
    · simp only [Except.map, bind, Except.bind, ↓reduceIte, StateT.bind, StateT.run]
      rcases step p K s σ with e | ⟨r, σ'⟩
      · rfl
      · cases r <;> rfl

theorem step_brk_run : (step p K .brk).run σ = .ok (.brk, σ) := rfl

theorem step_ret_run (e : Expr) : (step p K (.ret e)).run σ = (evalP σ e).map fun v => (.ret v, σ) := by
  simp only [step, StateT.run_bind, evalE_run]
  cases evalP σ e <;> rfl

theorem step_abort_run : (step p K .abort).run σ = .error .abort := rfl

theorem step_call_run (x : Var) (f : FnName) (args : List Expr) :
    (step p K (.call x f args)).run σ =
      match evalArgsP σ args with
      | .error e => .error e
      | .ok vs =>
        match (invoke p K f vs).run σ with
        | .error e => .error e
        | .ok (r, σ') => .ok (.normal, σ'.setLoc x r) := by
  simp only [step, StateT.run_bind, evalArgs_run]
  rcases evalArgsP σ args with e | vs
  · rfl
  · simp only [Except.map, bind, Except.bind]
    rcases (invoke p K f vs).run σ with e | ⟨r, σ'⟩ <;> rfl

theorem evalP_error {σ : St} {e : Expr} {x : Err} (h : evalP σ e = .error x) : x = .oob := by
  induction e generalizing x with
  | const | var | len8 | len64 => simp [evalP] at h
  | bin op a b iha ihb =>
    simp only [evalP, bind, Except.bind] at h
    split at h
    · rename_i he; cases h; exact iha he
    · split at h
      · rename_i he; cases h; exact ihb he
      · cases h
  | ld8 a i ih | ld64 a i ih =>
    simp only [evalP, bind, Except.bind] at h
    split at h
    · rename_i he; cases h; exact ih he
    · split at h
      · cases h
      · cases h; rfl

theorem evalCP_error {σ : St} {c : Cond} {x : Err} (h : evalCP σ c = .error x) : x = .oob := by
  induction c generalizing x with
  | cmp op a b =>
    simp only [evalCP, bind, Except.bind] at h
    split at h
    · rename_i he; cases h; exact evalP_error he
    · split at h
      · rename_i he; cases h; exact evalP_error he
      · cases h
  | and p q ihp ihq | or p q ihp ihq =>
    simp only [evalCP, bind, Except.bind] at h
    split at h
    · rename_i he; cases h; exact ihp he
    · split at h
      all_goals first | exact ihq h | cases h
  | not p ih =>
    simp only [evalCP, bind, Except.bind] at h
    split at h
    · rename_i he; cases h; exact ih he
    · cases h

theorem evalArgsP_error {σ : St} {es : List Expr} {x : Err} (h : evalArgsP σ es = .error x) : x = .oob := by
  induction es generalizing x with
  | nil => cases h
  | cons e es ih =>
    simp only [evalArgsP, bind, Except.bind] at h
    split at h
    · rename_i he; cases h; exact evalP_error he
    · split at h
      · rename_i he; cases h; exact ih he
      · cases h

end L.Compiler
