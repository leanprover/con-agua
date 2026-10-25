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
      by_cases h : j.toNat < (σ.mem.arr64 a).size <;> simp [h, StateT.bind, StateT.run, get, getThe,
        MonadStateOf.get, StateT.get, set, MonadStateOf.set, StateT.set, pure, StateT.pure, bind, Except.bind,
        Except.pure, throw, throwThe, MonadExceptOf.throw, StateT.lift, Except.map]

theorem step_st64t_run (a : ArrId) (t i e : Expr) :
    stepRun p K (.st64t a t i e) σ =
      match evalP σ t with
      | .error x => .error x
      | .ok u =>
        match evalP σ i with
        | .error x => .error x
        | .ok j =>
          match evalP σ e with
          | .error x => .error x
          | .ok v => if j.toNat < (σ.mem.arr64 (tierA a u)).size then
              .ok (.normal, { σ with mem := σ.mem.set64 (tierA a u) j v })
            else .error .oob := by
  unfold stepRun
  simp only [step, StateT.run_bind, evalE_run]
  rcases evalP σ t with x | u
  · rfl
  · simp only [Except.map, bind, Except.bind, StateT.run_bind, evalE_run]
    rcases evalP σ i with x | j
    · rfl
    · simp only [Except.map, bind, Except.bind]
      rcases evalP σ e with x | v
      · rfl
      · simp only [L.st64, StateT.run_bind, StateT.run_get]
        by_cases h : j.toNat < (σ.mem.arr64 (tierA a u)).size
        · simp [h, StateT.bind, StateT.run, get, getThe, MonadStateOf.get, StateT.get, set, MonadStateOf.set,
            StateT.set, pure, StateT.pure, bind, Except.bind, Except.pure]
        · simp [h, StateT.bind, StateT.run, get, getThe, MonadStateOf.get, StateT.get, bind, Except.bind, Except.pure,
            pure, throw, throwThe, MonadExceptOf.throw, StateT.lift, Except.map]

/-! ## Blocks (lane blkcopy) -/

/-- `warr`, without the state. -/
def warrP (σ : St) : WArr → Except Err ArrId
  | .plain a => .ok a
  | .tier a t => (evalP σ t).map (tierA a)

theorem warr_run (σ : St) (w : WArr) : (warr w).run σ = (warrP σ w).map (·, σ) := by
  cases w with
  | plain a => rfl
  | tier a t =>
    simp only [warr, warrP, StateT.run_bind, evalE_run]
    cases evalP σ t <;> rfl

theorem step_scan8_run (x : Var) (s : BSrc) (i e : Expr) (c : List UInt8) {vi ve : Word}
    (hi : evalP σ i = .ok vi) (he : evalP σ e = .ok ve) :
    stepRun p K (.scan8 x s i e c) σ =
      if vi ≤ ve ∧ ve.toNat ≤ (σ.mem.src8 s).size then
        .ok (.normal, σ.setLoc x (UInt64.ofNat (scanN (σ.mem.src8 s) c vi.toNat ve.toNat)))
      else .error .oob := by
  unfold stepRun
  simp only [step, StateT.run_bind, evalE_run, hi]
  simp only [Except.map, bind, Except.bind]
  simp only [he, StateT.run_get, pure, Except.pure]
  by_cases h : vi ≤ ve ∧ ve.toNat ≤ (σ.mem.src8 s).size
  · simp only [h, and_self, ↓reduceIte]
    simp [StateT.bind, setLoc, StateT.run, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure,
      StateT.pure, bind, Except.bind, Except.pure]
  · simp only [h, ↓reduceIte]
    simp [StateT.run, throw, throwThe, MonadExceptOf.throw, StateT.lift, bind, Except.bind]

theorem step_copy64_run (d s : WArr) (di si n : Expr) {da sa : ArrId} {i j k : Word}
    (hd : warrP σ d = .ok da) (hs : warrP σ s = .ok sa) (hi : evalP σ di = .ok i) (hj : evalP σ si = .ok j)
    (hk : evalP σ n = .ok k) :
    stepRun p K (.copy64 d di s si n) σ =
      if i.toNat + k.toNat ≤ (σ.mem.arr64 da).size ∧ j.toNat + k.toNat ≤ (σ.mem.arr64 sa).size then
        .ok (.normal, { σ with mem := σ.mem.copy64 da i sa j k.toNat })
      else .error .oob := by
  unfold stepRun
  simp only [step, StateT.run_bind, evalE_run, warr_run, hd, hs, hi, hj, hk]
  simp only [Except.map, bind, Except.bind]
  simp only [hd, hs, hi, hj, hk, StateT.run_get, pure, Except.pure]
  by_cases h : i.toNat + k.toNat ≤ (σ.mem.arr64 da).size ∧ j.toNat + k.toNat ≤ (σ.mem.arr64 sa).size
  · simp only [h, and_self, ↓reduceIte]
    simp [StateT.bind, StateT.run, set, MonadStateOf.set, StateT.set, pure, StateT.pure, bind, Except.bind,
      Except.pure]
  · simp only [h, ↓reduceIte]
    simp [StateT.run, throw, throwThe, MonadExceptOf.throw, StateT.lift, bind, Except.bind]

theorem step_copy8w_run (d : WArr) (s : BSrc) (di si n : Expr) {da : ArrId} {i j k : Word}
    (hd : warrP σ d = .ok da) (hi : evalP σ di = .ok i) (hj : evalP σ si = .ok j)
    (hk : evalP σ n = .ok k) :
    stepRun p K (.copy8w d di s si n) σ =
      if i.toNat + k.toNat ≤ (σ.mem.arr64 da).size ∧ j.toNat + k.toNat ≤ (σ.mem.src8 s).size then
        .ok (.normal, { σ with mem := σ.mem.copy8w da i (σ.mem.src8 s) j k.toNat })
      else .error .oob := by
  unfold stepRun
  simp only [step, StateT.run_bind, evalE_run, warr_run, hd, hi, hj, hk]
  simp only [Except.map, bind, Except.bind]
  simp only [hd, hi, hj, hk, StateT.run_get, pure, Except.pure]
  by_cases h : i.toNat + k.toNat ≤ (σ.mem.arr64 da).size ∧ j.toNat + k.toNat ≤ (σ.mem.src8 s).size
  · simp only [h, and_self, ↓reduceIte]
    simp [StateT.bind, StateT.run, set, MonadStateOf.set, StateT.set, pure, StateT.pure, bind, Except.bind,
      Except.pure]
  · simp only [h, ↓reduceIte]
    simp [StateT.run, throw, throwThe, MonadExceptOf.throw, StateT.lift, bind, Except.bind]

theorem evalP_simple {e : Expr} (h : Expr.isSimple e = true) (σ' : St) : ∃ v, evalP σ' e = .ok v := by
  cases e <;> simp_all [Expr.isSimple, evalP]

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
      by_cases h : j.toNat < (σ.mem.arr8 a).size <;> simp [h, StateT.bind, StateT.run, get, getThe,
        MonadStateOf.get, StateT.get, set, MonadStateOf.set, StateT.set, pure, StateT.pure, bind, Except.bind,
        Except.pure, throw, throwThe, MonadExceptOf.throw, StateT.lift, Except.map]

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

theorem step_ret_run (es : List Expr) :
    stepRun p K (.ret es) σ = (evalArgsP σ es).map fun vs => (.ret vs, σ) := by
  unfold stepRun
  simp only [step, StateT.run_bind, evalArgs_run]
  cases evalArgsP σ es <;> rfl

theorem step_abort_run (e : Expr) :
    stepRun p K (.abort e) σ =
      match evalP σ e with
      | .error x => .error x
      | .ok v => .error (.abort v) := by
  unfold stepRun
  simp only [step, StateT.run_bind, evalE_run]
  cases evalP σ e <;> rfl

theorem step_gset_run (g : GVar) (e : Expr) :
    stepRun p K (.gset g e) σ = (evalP σ e).map fun v => (.normal, σ.setG g v) := by
  unfold stepRun
  simp only [step, StateT.run_bind, evalE_run]
  cases evalP σ e <;> rfl

theorem step_call_run (xs : List Var) (f : FnName) (args : List Expr) :
    stepRun p K (.call xs f args) σ =
      match evalArgsP σ args with
      | .error e => .error e
      | .ok vs =>
        match (invoke p K f vs).run σ with
        | .error e => .error e
        | .ok (rs, σ') => .ok (.normal, σ'.setLocs xs rs) := by
  unfold stepRun
  simp only [step, StateT.run_bind, evalArgs_run]
  rcases evalArgsP σ args with e | vs
  · rfl
  · simp only [Except.map, bind, Except.bind]
    rcases (invoke p K f vs).run σ with e | ⟨r, σ'⟩ <;> rfl

theorem evalP_error {σ : St} {e : Expr} {x : Err} (h : evalP σ e = .error x) : x = .oob := by
  induction e generalizing x with
  | const | var | len8 | len64 | glob => simp [evalP] at h
  | bin _ a b iha ihb | cmpw _ a b iha ihb =>
    simp only [evalP, bind, Except.bind] at h
    split at h
    · rename_i he; cases h; exact iha he
    · split at h
      · rename_i he; cases h; exact ihb he
      · cases h
  | ld8 _ i ih | ld64 _ i ih | ldc _ i ih | ld8x8 _ i ih =>
    simp only [evalP, bind, Except.bind] at h
    split at h
    · rename_i he; cases h; exact ih he
    · split at h
      · cases h
      · cases h; rfl
  | ld64t _ t i iht ihi =>
    simp only [evalP, bind, Except.bind] at h
    split at h
    · rename_i he; cases h; exact iht he
    · split at h
      · rename_i he; cases h; exact ihi he
      · split at h
        · cases h
        · cases h; rfl
  | len64t _ t ih =>
    simp only [evalP, bind, Except.bind] at h
    split at h
    · rename_i he; cases h; exact ih he
    · cases h

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
