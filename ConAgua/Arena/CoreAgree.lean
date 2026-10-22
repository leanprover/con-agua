import ConAgua.L.WriteSet

/-!
# Programs that agree on a call-closed set of functions run them alike

A refinement proved over a concrete program (`natArmProg`, by `decide +kernel` on its text) holds in
any program that defines the same functions under the same names: `exec` reads a program only
through `lookup` at the functions a body calls. `closedW ctl q A C fs` already says that every body
of `fs` in `q` calls only into `fs` (`Stmt.okW`'s `call` clause), so it is the closure witness.
-/

namespace L

theorem exec_agree {ctl : ArrId} {A : List ArrId} {C : List Word} {fs : List FnName} {p q : Prog}
    (hq : closedW ctl q A C fs = true) (hpq : ∀ f ∈ fs, p.lookup f = q.lookup f) :
    ∀ (n : Nat) (st : Stmt), st.okW ctl A C fs = true → exec p n st = exec q n st := by
  intro n
  induction n with
  | zero => intro st _; rfl
  | succ n ihn =>
    intro st hst
    show step p (exec p n) st = step q (exec q n) st
    induction st with
    | seq s t ihs iht =>
      simp only [Stmt.okW, Bool.and_eq_true] at hst
      simp only [step, ihs hst.1, iht hst.2]
    | ite c s t ihs iht =>
      simp only [Stmt.okW, Bool.and_eq_true] at hst
      simp only [step, ihs hst.1, iht hst.2]
    | «while» c s ih =>
      have hs : s.okW ctl A C fs = true := by simpa [Stmt.okW] using hst
      simp only [step, ih hs, ihn (.while c s) hst]
    | «call» xs f args =>
      have hf : f ∈ fs := by simpa [Stmt.okW] using hst
      have hinv : invoke p (exec p n) f = invoke q (exec q n) f := by
        funext vs
        simp only [invoke, lookupFn, hpq f hf]
        cases h : q.lookup f with
        | none => rfl
        | some fd =>
          have hb := closedW_lookup hq hf h
          simp only [callFn, pure_bind, ihn fd.body hb]
      simp only [step, hinv]
    | _ => rfl

/-- **A call into an agreeing program**: the same computation. -/
theorem invoke_agree {ctl : ArrId} {A : List ArrId} {C : List Word} {fs : List FnName} {p q : Prog}
    (hq : closedW ctl q A C fs = true) (hpq : ∀ f ∈ fs, p.lookup f = q.lookup f) (n : Nat)
    {f : FnName} (hf : f ∈ fs) (vs : List Word) :
    invoke p (exec p n) f vs = invoke q (exec q n) f vs := by
  simp only [invoke, lookupFn, hpq f hf]
  cases h : q.lookup f with
  | none => rfl
  | some fd =>
    have hb := closedW_lookup hq hf h
    simp only [callFn, pure_bind, exec_agree hq hpq n fd.body hb]

end L
