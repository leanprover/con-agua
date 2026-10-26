module

public import ConAgua.L.Logic

@[expose] public section

/-!
# L: error-precise triples, a call's whole run, and runs that claim no verdict

An L run that fails ends in an `Err`; the compiled program reports an abort's code `k` in `rax`
(`Err.code`). The low two bits of the code are the abort's **class** (`Err.cls`): `1` reject,
`2` decline, `0` everything else (out of bounds, a missing function, the fuel, an abort of class
`0`). The verdict theorem says what a run of class `1` or `2` means; this file has the L side's
generic pieces:

* `M.of_run_err`, `M.triple_of_run'`, `Triple.and_err`: triples whose exceptional post is not `⊤`
  (the error versions of `L/Logic.lean`'s bridges);
* `callE`: a call's whole run, its error included (`callW`, `Arena/WhnfBase.lean`, is its
  `Option`), and `callE_spec`: every call meets its own run, also when it fails;
* **`NoVerdict`**: a `Bool` check of the program text (`closedNV`) that a call-closed set of
  functions aborts only with class-`0` codes, and its consequence (`invoke_nv`, `callE_nv`): every
  error of such a function has class `0`, so it claims nothing. The induction on the fuel is
  `L/WriteSet.lean`'s.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L

/-! ## The class of an error -/

/-- An error's class: the low two bits of its code (`1` reject, `2` decline, `0` other; every
error other than an abort has code `0`). -/
def Err.cls (e : Err) : Word := e.code &&& 3

@[simp, grind =, lang_grind =] theorem Err.code_abort (k : Word) : (Err.abort k).code = k := rfl
@[simp, grind =, lang_grind =] theorem Err.code_oob : Err.oob.code = 0 := rfl
@[simp, grind =, lang_grind =] theorem Err.code_outOfFuel : Err.outOfFuel.code = 0 := rfl
@[simp, grind =, lang_grind =] theorem Err.code_noFun (f : FnName) : (Err.noFun f).code = 0 := rfl

@[simp, grind =] theorem Err.cls_abort (k : Word) : (Err.abort k).cls = k &&& 3 := rfl
@[simp, grind =] theorem Err.cls_oob : Err.oob.cls = 0 := by simp [Err.cls]
@[simp, grind =] theorem Err.cls_outOfFuel : Err.outOfFuel.cls = 0 := by simp [Err.cls]
@[simp, grind =] theorem Err.cls_noFun (f : FnName) : (Err.noFun f).cls = 0 := by simp [Err.cls]

/-- An error of class other than `0` is an abort. -/
theorem Err.eq_abort_of_cls {e : Err} (h : e.cls ≠ 0) : e = .abort e.code := by
  cases e <;> simp_all

/-- An error of class other than `0` has a code other than `0`. -/
theorem Err.code_ne_of_cls {e : Err} (h : e.cls ≠ 0) : e.code ≠ 0 := by
  intro h0; apply h; simp [Err.cls, h0]

/-! ## Triples with an exceptional post -/

/-- From a triple with an exceptional post to an erroring run. -/
theorem M.of_run_err {α : Type} {prog : M α} {s : St} {e : Err} {P : St → Prop}
    {Q : α → St → Prop} {E : Err → Prop} (hp : P s) (h : prog.run s = .error e)
    (hwp : ⦃fun s => P s⦄ prog ⦃fun r s'' => Q r s''; E⦄) : E e := by
  have hs := hwp.le_wp s hp
  rw [Std.WP.StateT.wp_apply_eq, h] at hs
  exact hs

/-- From statements about every run, ok and erroring, to a triple. -/
theorem M.triple_of_run' {α : Type} {prog : M α} {P : St → Prop} {Q : α → St → Prop}
    {E : Err → Prop}
    (h : ∀ (s : St) (a : α) (s' : St), P s → prog.run s = .ok (a, s') → Q a s')
    (he : ∀ (s : St) (e : Err), P s → prog.run s = .error e → E e) :
    ⦃fun s => P s⦄ prog ⦃fun r s'' => Q r s''; E⦄ := by
  refine ⟨fun s hp => ?_⟩
  rw [Std.WP.StateT.wp_apply_eq]
  cases hr : prog.run s with
  | error e => exact he s e hp hr
  | ok p => exact h s p.1 p.2 hp hr

/-- From a triple to a statement about every successful run (any exceptional post). -/
theorem M.of_run' {α : Type} {prog : M α} {s s' : St} {a : α} {P : St → Prop}
    {Q : α → St → Prop} {E : Err → Prop} (hp : P s) (h : prog.run s = .ok (a, s'))
    (hwp : ⦃fun s => P s⦄ prog ⦃fun r s'' => Q r s''; E⦄) : Q a s' := by
  have hs := hwp.le_wp s hp
  rw [Std.WP.StateT.wp_apply_eq, h] at hs
  exact hs

/-- **The conjunction rule**: an ok spec (exceptional post `⊤`) and an error spec (ok post `⊤`)
make one triple. So the error proofs are new theorems beside the untouched ok ones. -/
theorem Triple.and_err {α : Type} {prog : M α} {P : St → Prop} {Q : α → St → Prop}
    {E : Err → Prop} (hq : ⦃fun s => P s⦄ prog ⦃fun r s'' => Q r s''; ⊤⦄)
    (he : ⦃fun s => P s⦄ prog ⦃fun _ _ => True; E⦄) :
    ⦃fun s => P s⦄ prog ⦃fun r s'' => Q r s''; E⦄ :=
  M.triple_of_run' (fun _ _ _ hp hr => M.of_run hp hr hq) (fun _ _ hp hr => M.of_run_err hp hr he)

/-- `Triple.step_exec` with any exceptional post. -/
theorem Triple.step_exec' {p : Prog} {n : Nat} {s : Stmt} {P : St → Prop} {Q : Sig → St → Prop}
    {E : Err → Prop} (h : ⦃P⦄ exec p (n + 1) s ⦃Q; E⦄) : ⦃P⦄ step p (exec p n) s ⦃Q; E⦄ := h

/-- A byte load, error-precise: its value as the models read it, or an error with code `0`. -/
theorem ld8_specE (a : ArrId) (i : Word) (s₀ : St) :
    ⦃fun s => s = s₀⦄ ld8 a i
    ⦃fun r s' => s' = s₀ ∧ r = ((s₀.mem.arr8 a)[i.toNat]?.getD 0).toUInt64 ∧
      i.toNat < (s₀.mem.arr8 a).size; fun e => e.code = 0⦄ := by
  apply M.triple_of_run'
  · intro s r s' hs hrun
    subst hs
    simp only [ld8, StateT.run_bind, StateT.run_get, pure_bind] at hrun
    split at hrun
    · rename_i h
      simp only [StateT.run_pure, Except.ok.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      exact ⟨rfl, by simp [h], h⟩
    · simp [StateT.lift, StateT.run, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hrun
  · intro s e hs hrun
    subst hs
    simp only [ld8, StateT.run_bind, StateT.run_get, pure_bind] at hrun
    split at hrun
    · simp [StateT.run, pure, StateT.pure, Except.pure] at hrun
    · simp [StateT.lift, StateT.run, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hrun
      subst hrun; rfl

/-! ## A call's whole run -/

/-- **A call's whole run**, its error included: the results and the memory, or the error. -/
def callE (p : Prog) (n : Nat) (f : FnName) (vs : List Word) (m : Mem) :
    Except Err (List Word × Mem) :=
  match (invoke p (exec p n) f vs).run ⟨m, Locals.init []⟩ with
  | .ok (r, s) => .ok (r, s.mem)
  | .error e => .error e

theorem invoke_run_loc' (p : Prog) (k : Stmt → M Sig) (f : FnName) (vs : List Word) (s : St) :
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

/-- **Every call meets its own run, also when it fails.** -/
theorem callE_spec (p : Prog) (n : Nat) (f : FnName) (vs : List Word) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) f vs
    ⦃fun r s' => LocEq s' s₀ ∧ callE p n f vs s₀.mem = .ok (r, s'.mem);
     fun e => callE p n f vs s₀.mem = .error e⦄ := by
  apply M.triple_of_run'
  · intro s r s' hs hrun
    subst hs
    rw [invoke_run_loc'] at hrun
    simp only [callE]
    cases h : (invoke p (exec p n) f vs).run { mem := s.mem, loc := Locals.init [] } with
    | error e => simp [h, Except.map] at hrun
    | ok q =>
      simp [h, Except.map] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      exact ⟨rfl, rfl⟩
  · intro s e hs hrun
    subst hs
    rw [invoke_run_loc'] at hrun
    simp only [callE]
    cases h : (invoke p (exec p n) f vs).run { mem := s.mem, loc := Locals.init [] } with
    | error e' => simp [h, Except.map] at hrun; simp [hrun]
    | ok q => simp [h, Except.map] at hrun

theorem callE_zero (p : Prog) (f : FnName) (vs : List Word) (m : Mem) :
    ∃ e, callE p 0 f vs m = .error e ∧ e.cls = 0 := by
  simp only [callE, invoke, lookupFn]
  cases p.lookup f with
  | none => exact ⟨_, rfl, Err.cls_noFun f⟩
  | some fd => exact ⟨_, rfl, Err.cls_outOfFuel⟩

/-- **A triple applies to a run**: an ok run of the call meets the triple's post (at a state with
the run's memory and the caller's locals). -/
theorem triple_of_callE {p : Prog} {n : Nat} {f : FnName} {args : List Word} {s₀ : St}
    {Q : List Word → St → Prop} {E : Err → Prop}
    (h : ⦃fun s => s = s₀⦄ invoke p (exec p n) f args ⦃fun r s' => Q r s'; E⦄)
    {r : List Word} {m' : Mem} (hc : callE p n f args s₀.mem = .ok (r, m')) :
    ∃ s', s'.mem = m' ∧ Q r s' := by
  simp only [callE] at hc
  cases hr : (invoke p (exec p n) f args).run { mem := s₀.mem, loc := Locals.init [] } with
  | error e => simp [hr] at hc
  | ok q =>
    simp only [hr, Except.ok.injEq] at hc
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hc
    have hrun : (invoke p (exec p n) f args).run s₀ = .ok (q.1, { q.2 with loc := s₀.loc }) := by
      rw [invoke_run_loc', hr]; rfl
    exact ⟨{ q.2 with loc := s₀.loc }, rfl, L.M.of_run' (P := fun s => s = s₀) rfl hrun h⟩

/-- **A triple applies to a failing run**: the call's error meets the triple's exceptional post. -/
theorem triple_of_callE_err {p : Prog} {n : Nat} {f : FnName} {args : List Word} {s₀ : St}
    {Q : List Word → St → Prop} {E : Err → Prop}
    (h : ⦃fun s => s = s₀⦄ invoke p (exec p n) f args ⦃fun r s' => Q r s'; E⦄)
    {e : Err} (hc : callE p n f args s₀.mem = .error e) : E e := by
  simp only [callE] at hc
  cases hr : (invoke p (exec p n) f args).run { mem := s₀.mem, loc := Locals.init [] } with
  | ok q => simp [hr] at hc
  | error e' =>
    simp only [hr, Except.error.injEq] at hc
    subst hc
    have hrun : (invoke p (exec p n) f args).run s₀ = .error e' := by
      rw [invoke_run_loc', hr]; rfl
    exact L.M.of_run_err (P := fun s => s = s₀) rfl hrun h

/-! ## Runs that claim no verdict (`NoVerdict`)

A statement is `noV fs` if every `abort` in it has a constant code of class `0` and every call
goes to `fs`. If every function of `fs` has a `noV fs` body (`closedNV`), every run of a function
of `fs` fails, if at all, with an error of class `0`. -/

/-- An abort's code expression: a constant of class `0`. -/
def Expr.cls0 : Expr → Bool
  | .const k => k &&& 3 == 0
  | _ => false

/-- Aborts only with constant class-`0` codes; calls only into `fs`. -/
def Stmt.noV (fs : List FnName) : Stmt → Bool
  | .seq s t => s.noV fs && t.noV fs
  | .ite _ s t => s.noV fs && t.noV fs
  | .while _ s => s.noV fs
  | .call _ f _ => decide (f ∈ fs)
  | .abort e => e.cls0
  | _ => true

/-- Every function of `fs` that `p` defines has a `noV fs` body. -/
def closedNV (p : Prog) (fs : List FnName) : Bool :=
  fs.all fun f => match p.lookup f with
    | some fd => fd.body.noV fs
    | none => true

theorem closedNV_lookup {p : Prog} {fs : List FnName} (hp : closedNV p fs = true) {f : FnName}
    (hf : f ∈ fs) {fd : FunDecl} (h : p.lookup f = some fd) : fd.body.noV fs = true := by
  simp only [closedNV, List.all_eq_true] at hp
  have := hp f hf
  rw [h] at this
  exact this

/-- The exceptional post of a run that claims nothing. -/
abbrev NVE : Err → Prop := fun e => e.cls = 0

theorem evalE_nv (e : Expr) : ⦃fun _ => True⦄ evalE e ⦃fun _ _ => True; NVE⦄ := by
  induction e with
  | const w => vcgen [evalE] <;> grind
  | var x => vcgen [evalE] <;> grind
  | bin op a b iha ihb => vcgen [evalE, iha, ihb] <;> grind
  | ld8 a i ih => vcgen [evalE, ih, ld8] <;> grind
  | ld64 a i ih => vcgen [evalE, ih, ld64] <;> grind
  | len8 a => vcgen [evalE] <;> grind
  | len64 a => vcgen [evalE] <;> grind
  | cmpw c a b iha ihb => vcgen [evalE, iha, ihb] <;> grind
  | ldc d i ih => vcgen [evalE, ih, ldc] <;> grind
  | glob g => vcgen [evalE] <;> grind
  | ld64t a t i iht ihi => vcgen [evalE, iht, ihi, ld64] <;> grind
  | len64t a t ih => vcgen [evalE, ih] <;> grind
  | ld8x8 s i ih => vcgen [evalE, ih, ld8x8] <;> grind

theorem evalC_nv (c : Cond) : ⦃fun _ => True⦄ evalC c ⦃fun _ _ => True; NVE⦄ := by
  induction c with
  | cmp c a b => vcgen [evalC, evalE_nv a, evalE_nv b] <;> grind
  | and p q ihp ihq => vcgen [evalC, ihp, ihq] <;> grind
  | or p q ihp ihq => vcgen [evalC, ihp, ihq] <;> grind
  | not p ih => vcgen [evalC, ih] <;> grind

theorem evalArgs_nv (es : List Expr) : ⦃fun _ => True⦄ evalArgs es ⦃fun _ _ => True; NVE⦄ := by
  induction es with
  | nil => vcgen [evalArgs] <;> grind
  | cons e es ih => vcgen [evalArgs, evalE_nv e, ih] <;> grind

theorem warr_nv (w : WArr) : ⦃fun _ => True⦄ warr w ⦃fun _ _ => True; NVE⦄ := by
  cases w with
  | plain a => vcgen [warr] <;> grind
  | tier a t => vcgen [warr, evalE_nv t] <;> grind

section nv
variable {fs : List FnName}

/-- A continuation that claims nothing on `noV` statements. -/
def NVK (fs : List FnName) (k : Stmt → M Sig) : Prop :=
  ∀ st, st.noV fs = true → ⦃fun _ => True⦄ k st ⦃fun _ _ => True; NVE⦄

theorem invoke_nvK (p : Prog) (hp : closedNV p fs = true) (k : Stmt → M Sig) (hk : NVK fs k)
    (f : FnName) (hf : f ∈ fs) (vs : List Word) :
    ⦃fun _ => True⦄ invoke p k f vs ⦃fun _ _ => True; NVE⦄ := by
  cases h : p.lookup f with
  | none => simp only [invoke, lookupFn, h]; vcgen <;> grind
  | some fd =>
    rw [invoke_eq _ h]
    have hb := closedNV_lookup hp hf h
    simp only [callFn]
    vcgen [hk fd.body hb] <;> grind

theorem step_nv (p : Prog) (hp : closedNV p fs = true) (k : Stmt → M Sig) (hk : NVK fs k) :
    NVK fs (step p k) := by
  intro st hst
  induction st with
  | «skip» => vcgen [step] <;> grind
  | set x e => vcgen [step, setLoc, evalE_nv e] <;> grind
  | st8 a i e => vcgen [step, evalE_nv i, evalE_nv e, st8] <;> grind
  | st64 a i e => vcgen [step, evalE_nv i, evalE_nv e, st64] <;> grind
  | st64t a t i e => vcgen [step, evalE_nv t, evalE_nv i, evalE_nv e, st64] <;> grind
  | copy64 d di s si n =>
    vcgen [step, warr_nv d, warr_nv s, evalE_nv di, evalE_nv si, evalE_nv n] <;> grind
  | copy8w d di s si n => vcgen [step, warr_nv d, evalE_nv di, evalE_nv si, evalE_nv n] <;> grind
  | scan8 x s i e c => vcgen [step, setLoc, evalE_nv i, evalE_nv e] <;> grind
  | seq s t ihs iht =>
    simp only [Stmt.noV, Bool.and_eq_true] at hst
    vcgen [step, ihs hst.1, iht hst.2] <;> grind
  | ite c s t ihs iht =>
    simp only [Stmt.noV, Bool.and_eq_true] at hst
    vcgen [step, evalC_nv c, ihs hst.1, iht hst.2] <;> grind
  | «while» c s ih =>
    vcgen [step, evalC_nv c, ih hst, hk (.while c s) hst] <;> grind
  | brk => vcgen [step] <;> grind
  | ret es => vcgen [step, evalArgs_nv es] <;> grind
  | «call» xs f args =>
    simp only [Stmt.noV, decide_eq_true_eq] at hst
    vcgen [step, setLocs, evalArgs_nv args, invoke_nvK p hp k hk f hst] <;> grind
  | «abort» e =>
    cases e with
    | const w =>
      simp only [Stmt.noV, Expr.cls0, beq_iff_eq] at hst
      vcgen [step, evalE] <;> simp_all [Err.cls]
    | _ => simp [Stmt.noV, Expr.cls0] at hst
  | gset g e => vcgen [step, setG, evalE_nv e] <;> grind

theorem exec_nv (p : Prog) (hp : closedNV p fs = true) (n : Nat) : NVK fs (exec p n) := by
  induction n with
  | zero => intro st _; vcgen [exec] <;> grind
  | succ n ih => exact step_nv p hp (exec p n) ih

/-- **A run that claims nothing, from the text**: every error of a call of `f ∈ fs` has class
`0`. -/
theorem invoke_nv (p : Prog) (hp : closedNV p fs = true) (n : Nat) (f : FnName) (hf : f ∈ fs)
    (vs : List Word) : ⦃fun _ => True⦄ invoke p (exec p n) f vs ⦃fun _ _ => True; NVE⦄ :=
  invoke_nvK p hp _ (exec_nv p hp n) f hf vs

/-- **A failing call of `f ∈ fs` fails with class `0`.** -/
theorem callE_nv {p : Prog} (hp : closedNV p fs = true) {f : FnName} (hf : f ∈ fs) (n : Nat)
    (vs : List Word) (m : Mem) {e : Err} (h : callE p n f vs m = .error e) : e.cls = 0 :=
  triple_of_callE_err (s₀ := ⟨m, Locals.init []⟩) (Q := fun _ _ => True)
    (M.triple_of_run' (fun _ _ _ _ _ => trivial) fun s e hs hr => by
      subst hs; exact M.of_run_err (P := fun _ => True) trivial hr (invoke_nv p hp n f hf vs)) h

end nv

end L
