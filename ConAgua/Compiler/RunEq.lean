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

/-- One step of `L` on statement `s` from state `σ`. -/
def stepRun (p : Prog) (K : Stmt → M Sig) (s : Stmt) (σ : St) : Except Err (Sig × St) :=
  (step p K s).run σ

variable (p : Prog) (K : Stmt → M Sig) (σ : St)

theorem step_skip_run : stepRun p K .skip σ = .ok (.normal, σ) := rfl

theorem step_set_run (x : Var) (e : Expr) :
    stepRun p K (.set x e) σ = (evalP σ e).map fun v => (.normal, σ.setLoc x v) := by
  unfold stepRun
  simp only [step, StateT.run_bind, evalE_run]
  cases evalP σ e <;> rfl

theorem step_st64_run (a : ArrId) (i e : Expr) :
    stepRun p K (.st64 a i e) σ =
      match evalP σ i with
      | .error x => .error x
      | .ok j =>
        match evalP σ e with
        | .error x => .error x
        | .ok v => if j.toNat < (σ.mem.arr64 a).size then .ok (.normal, { σ with mem := σ.mem.set64 a j v })
          else .error .oob := by
  unfold stepRun
  simp only [step, StateT.run_bind, evalE_run]
  rcases evalP σ i with x | j
  · rfl
  · simp only [Except.map, bind, Except.bind]
    rcases evalP σ e with x | v
    · rfl
    · simp only [L.st64, StateT.run_bind, StateT.run_get]
      by_cases h : j.toNat < (σ.mem.arr64 a).size
      · simp [h, StateT.bind, StateT.run, get, getThe, MonadStateOf.get, StateT.get, set, MonadStateOf.set,
          StateT.set, pure, StateT.pure, bind, Except.bind, Except.pure]
      · simp [h, StateT.bind, StateT.run, get, getThe, MonadStateOf.get, StateT.get, bind, Except.bind, Except.pure,
          pure, throw, throwThe, MonadExceptOf.throw, StateT.lift, Except.map]

theorem step_st8_run (a : ArrId) (i e : Expr) :
    stepRun p K (.st8 a i e) σ =
      match evalP σ i with
      | .error x => .error x
      | .ok j =>
        match evalP σ e with
        | .error x => .error x
        | .ok v => if j.toNat < (σ.mem.arr8 a).size then .ok (.normal, { σ with mem := σ.mem.set8 a j v })
          else .error .oob := by
  unfold stepRun
  simp only [step, StateT.run_bind, evalE_run]
  rcases evalP σ i with x | j
  · rfl
  · simp only [Except.map, bind, Except.bind]
    rcases evalP σ e with x | v
    · rfl
    · simp only [L.st8, StateT.run_bind, StateT.run_get]
      by_cases h : j.toNat < (σ.mem.arr8 a).size
      · simp [h, StateT.bind, StateT.run, get, getThe, MonadStateOf.get, StateT.get, set, MonadStateOf.set,
          StateT.set, pure, StateT.pure, bind, Except.bind, Except.pure]
      · simp [h, StateT.bind, StateT.run, get, getThe, MonadStateOf.get, StateT.get, bind, Except.bind, Except.pure,
          pure, throw, throwThe, MonadExceptOf.throw, StateT.lift, Except.map]

theorem step_seq_run (s t : Stmt) :
    stepRun p K (.seq s t) σ =
      match stepRun p K s σ with
      | .ok (.normal, σ') => stepRun p K t σ'
      | .ok (r, σ') => .ok (r, σ')
      | .error e => .error e := by
  unfold stepRun
  simp only [step, StateT.run_bind]
  rcases (step p K s).run σ with e | ⟨r, σ'⟩
  · rfl
  · cases r <;> rfl

theorem step_ite_run (c : Cond) (s t : Stmt) :
    stepRun p K (.ite c s t) σ =
      match evalCP σ c with
      | .ok true => stepRun p K s σ
      | .ok false => (step p K t).run σ
      | .error e => .error e := by
  unfold stepRun
  simp only [step, StateT.run_bind, evalC_run]
  rcases evalCP σ c with e | b
  · rfl
  · cases b <;> rfl

theorem step_while_run (c : Cond) (s : Stmt) :
    stepRun p K (.while c s) σ =
      match evalCP σ c with
      | .error e => .error e
      | .ok false => .ok (.normal, σ)
      | .ok true =>
        match stepRun p K s σ with
        | .ok (.normal, σ') => (K (.while c s)).run σ'
        | .ok (.brk, σ') => .ok (.normal, σ')
        | .ok (.ret v, σ') => .ok (.ret v, σ')
        | .error e => .error e := by
  unfold stepRun
  simp only [step, StateT.run_bind, evalC_run]
  rcases evalCP σ c with e | b
  · rfl
  · cases b
    · rfl
    · simp only [Except.map, bind, Except.bind, ↓reduceIte, StateT.bind, StateT.run]
      rcases step p K s σ with e | ⟨r, σ'⟩
      · rfl
      · cases r <;> rfl

theorem step_brk_run : stepRun p K .brk σ = .ok (.brk, σ) := rfl

theorem step_ret_run (e : Expr) : stepRun p K (.ret e) σ = (evalP σ e).map fun v => (.ret v, σ) := by
  unfold stepRun
  simp only [step, StateT.run_bind, evalE_run]
  cases evalP σ e <;> rfl

theorem step_abort_run : stepRun p K .abort σ = .error .abort := rfl

theorem step_call_run (x : Var) (f : FnName) (args : List Expr) :
    stepRun p K (.call x f args) σ =
      match evalArgsP σ args with
      | .error e => .error e
      | .ok vs =>
        match (invoke p K f vs).run σ with
        | .error e => .error e
        | .ok (r, σ') => .ok (.normal, σ'.setLoc x r) := by
  unfold stepRun
  simp only [step, StateT.run_bind, evalArgs_run]
  rcases evalArgsP σ args with e | vs
  · rfl
  · simp only [Except.map, bind, Except.bind]
    rcases (invoke p K f vs).run σ with e | ⟨r, σ'⟩ <;> rfl

theorem evalP_error {σ : St} {e : Expr} {x : Err} (h : evalP σ e = .error x) : x = .oob := by
  induction e generalizing x with
  | const | var | len8 | len64 => simp [evalP] at h
  | bin _ a b iha ihb | cmpw _ a b iha ihb =>
    simp only [evalP, bind, Except.bind] at h
    split at h
    · rename_i he; cases h; exact iha he
    · split at h
      · rename_i he; cases h; exact ihb he
      · cases h
  | ld8 _ i ih | ld64 _ i ih | ldc _ i ih =>
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
