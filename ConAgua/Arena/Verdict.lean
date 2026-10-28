import ConAgua.L.ErrSpec
import ConAgua.Arena.WhnfBase

/-!
# The verdict claim: what an L error says about the twin

An L run that fails with an abort of class `1` (reject) or `2` (decline) claims that the twin's
run fails with an error of the same kind: `invalid` resp. `notImplemented` (`twinCls`). Every
other error (class `0`: out of bounds, the fuel, a capacity, a defensive check) claims nothing.
`ErrClaim T a e` is that claim about the twin computation `T` from the twin state `a`.

The per-function error refinements are built from four facts about the twin's monad (the
propagation is the monad's bind, on both sides, proved here once):

* `ErrClaim.bind_left`: the error came from the first step of a `bind` (a callee);
* `ErrClaim.bind_right`: the first step ran ok, the error came from the rest;
* `ErrClaim.fail`: a site of the function, the twin's `fail` with an error of the same class;
* `ErrClaim.of_cls0`: an error of class `0` claims nothing (`callE_nv` gives it for every
  callee outside the verdict closure).

On the L side, a call's run with its error is `callE` (`L/ErrSpec.lean`); `callW` is its
`Option` (`callW_eq_callE`), so the ok refinements apply to its ok runs (`callW_of_callE`).

`ErrClaimV` is the claim about a twin computation that reports its failures as a value
(`.ok (.error (ce, n))`: the frontend's stages, the fold); `VClaim` is the twin-free form a
stage's error spec has.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

/-- **The twin's error class**: `invalid` is a reject (`1`), `notImplemented` a decline (`2`),
`internal` and `native` neither (`0`). The exit codes `1` and `2` of con-ron's `exitCode`
(`ConRon/Arena/Main.lean`). -/
def twinCls : CheckError → Word
  | .invalid _ => 1
  | .notImplemented _ => 2
  | _ => 0

@[simp] theorem twinCls_invalid (s : String) : twinCls (.invalid s) = 1 := rfl
@[simp] theorem twinCls_notImplemented (s : String) : twinCls (.notImplemented s) = 2 := rfl
@[simp] theorem twinCls_internal (s : String) : twinCls (.internal s) = 0 := rfl
@[simp] theorem twinCls_native (s : String) : twinCls (.native s) = 0 := rfl

/-- **What an L error claims about the twin's run `T` from `a`**: an error of class other than
`0` means the twin fails with an error of that class. -/
def ErrClaim {α : Type} (T : AM α) (a : AState) (e : Err) : Prop :=
  e.cls ≠ 0 → ∃ ce, T.run a = .error ce ∧ twinCls ce = e.cls

/-! ## The kit -/

theorem ErrClaim.of_cls0 {α : Type} {T : AM α} {a : AState} {e : Err} (h : e.cls = 0) :
    ErrClaim T a e := fun h' => absurd h h'

theorem ErrClaim.bind_left {α β : Type} {x : AM α} {f : α → AM β} {a : AState} {e : Err}
    (h : ErrClaim x a e) : ErrClaim (x >>= f) a e := fun hk => by
  obtain ⟨ce, hce, hc⟩ := h hk
  exact ⟨ce, by simp only [StateT.run_bind, hce]; rfl, hc⟩

theorem ErrClaim.bind_right {α β : Type} {x : AM α} {f : α → AM β} {a a₁ : AState} {v : α}
    {e : Err} (hx : x.run a = .ok (v, a₁)) (h : ErrClaim (f v) a₁ e) :
    ErrClaim (x >>= f) a e := fun hk => by
  obtain ⟨ce, hce, hc⟩ := h hk
  exact ⟨ce, by simp only [StateT.run_bind, hx]; exact hce, hc⟩

/-- The twin's `fail` at a site, with an error of the abort's class. -/
theorem ErrClaim.fail {α : Type} (a : AState) (ce : CheckError) {e : Err}
    (hk : e.cls = twinCls ce) : ErrClaim (ConRon.Arena.fail ce : AM α) a e :=
  fun _ => ⟨ce, rfl, hk.symm⟩

/-- An abort with the code `k` at a twin `fail ce` site, the code's class the twin error's. -/
theorem ErrClaim.fail_abort {α : Type} (a : AState) (ce : CheckError) {k : Word}
    (hk : k &&& 3 = twinCls ce) : ErrClaim (ConRon.Arena.fail ce : AM α) a (.abort k) :=
  ErrClaim.fail a ce hk

/-- Rewriting the twin computation (its equation lemma, a `do` block reassociated). -/
theorem ErrClaim.congr {α : Type} {T T' : AM α} {a : AState} {e : Err} (h : T = T')
    (h' : ErrClaim T' a e) : ErrClaim T a e := h ▸ h'

/-- The twin computations agree on the run from `a`. -/
theorem ErrClaim.of_run_eq {α β : Type} {T : AM α} {T' : AM β} {a : AState} {e : Err}
    (h : ∀ ce, T'.run a = .error ce → T.run a = .error ce) (h' : ErrClaim T' a e) :
    ErrClaim T a e := fun hk => by
  obtain ⟨ce, hce, hc⟩ := h' hk
  exact ⟨ce, h ce hce, hc⟩

/-- `if` in the twin: the branch taken. -/
theorem ErrClaim.ite_pos {α : Type} {c : Prop} [Decidable c] {x y : AM α} {a : AState} {e : Err}
    (hc : c) (h : ErrClaim x a e) : ErrClaim (if c then x else y) a e := by
  rw [ite_eq_left hc]; exact h

theorem ErrClaim.ite_neg {α : Type} {c : Prop} [Decidable c] {x y : AM α} {a : AState} {e : Err}
    (hc : ¬ c) (h : ErrClaim y a e) : ErrClaim (if c then x else y) a e := by
  rw [ite_eq_right hc]; exact h

/-- The twin computations agree on the run from `a`. -/
theorem ErrClaim.of_run_eqW {α : Type} {T T' : AM α} {a a' : AState} {e : Err}
    (h : T.run a = T'.run a') (h' : ErrClaim T' a' e) : ErrClaim T a e := fun hk => by
  obtain ⟨ce, hce, hc⟩ := h' hk
  exact ⟨ce, h ▸ hce, hc⟩

/-- The twin's run from `a` fails where `T'`'s from `a'` does. -/
theorem ErrClaim.of_run_err {α β : Type} {T : AM α} {T' : AM β} {a a' : AState} {e : Err}
    (h : ∀ ce, T'.run a' = .error ce → T.run a = .error ce) (h' : ErrClaim T' a' e) :
    ErrClaim T a e := fun hk => by
  obtain ⟨ce, hce, hc⟩ := h' hk
  exact ⟨ce, h ce hce, hc⟩

/-! ## The L side: `callE` and `callW` -/

theorem callW_eq_callE (p : Prog) (n : Nat) (f : FnName) (vs : List Word) (m : Mem) :
    callW p n f vs m = (callE p n f vs m).toOption := by
  simp only [callW, callE]
  cases (invoke p (exec p n) f vs).run ⟨m, Locals.init []⟩ <;> rfl

/-- An ok run of `callE` is the ok run of `callW` (so the ok refinements apply to it). -/
theorem callW_of_callE {p : Prog} {n : Nat} {f : FnName} {vs : List Word} {m : Mem}
    {r : List Word} {m' : Mem} (h : callE p n f vs m = .ok (r, m')) :
    callW p n f vs m = some (r, m') := by
  rw [callW_eq_callE, h]; rfl

/-- An ok run of `callW` is the ok run of `callE` (so the unified refinements apply to it). -/
theorem callE_of_callW {p : Prog} {n : Nat} {f : FnName} {vs : List Word} {m : Mem}
    {r : List Word} {m' : Mem} (h : callW p n f vs m = some (r, m')) :
    callE p n f vs m = .ok (r, m') := by
  rw [callW_eq_callE] at h
  cases hE : callE p n f vs m <;> simp_all [Except.toOption]

/-- **A callee outside the verdict closure claims nothing.** -/
theorem ErrClaim.of_callE_nv {α : Type} {T : AM α} {a : AState} {p : Prog} {fs : List FnName}
    (hp : closedNV p fs = true) {f : FnName} (hf : f ∈ fs) {n : Nat} {vs : List Word} {m : Mem}
    {e : Err} (h : callE p n f vs m = .error e) : ErrClaim T a e :=
  ErrClaim.of_cls0 (callE_nv hp hf n vs m h)

/-- A word load, error-precise: its value as `rdW`, or `oob` (the loads of the `errors` and
`unified` models, `l_model … extra [ld64_rdW_specE]`). The error is exact: with a post over its
code, the generated steps of a `unified` model, whose error posts are over the class, fell
through to slow `simp_all` rounds and `grind` at every load (`checkValueGroupE` 8.6 s → 2.9 s). -/
theorem ld64_rdW_specE (a : ArrId) (i : Word) (s₀ : St) :
    ⦃fun s => s = s₀⦄ ld64 a i
    ⦃fun r s' => s' = s₀ ∧ r = rdW (s₀.mem.arr64 a) i ∧ i.toNat < (s₀.mem.arr64 a).size;
     fun e => e = .oob⦄ := by
  apply M.triple_of_run'
  · intro s r s' hs hrun
    subst hs
    simp only [ld64, StateT.run_bind, StateT.run_get, pure_bind] at hrun
    split at hrun
    · rename_i h
      simp only [StateT.run_pure] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      exact ⟨rfl, by simp [rdW, h], h⟩
    · simp [StateT.lift, StateT.run, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hrun
  · intro s e hs hrun
    subst hs
    simp only [ld64, StateT.run_bind, StateT.run_get, pure_bind] at hrun
    split at hrun
    · simp [StateT.run, pure, StateT.pure, Except.pure] at hrun
    · simp [StateT.lift, StateT.run, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hrun
      subst hrun; rfl

/-! ## The error spec of a core function

`CoreSpec` (`WhnfBase.lean`) is the ok refinement of a call; `CoreSpecE` is its error half: a
failing call claims the twin's failure, from the same start (`Triple.and_err` puts the two in one
triple). -/

/-- **The error spec shape**: a call of `f` from `s₀` that fails claims `T`'s failure from `a₀`. -/
def CoreSpecE {α : Type} (p : Prog) (n : Nat) (f : FnName) (args : List Word) (T : AM α)
    (s₀ : St) (a₀ : AState) : Prop :=
  ⦃fun s => s = s₀⦄ invoke p (exec p n) f args ⦃fun _ _ => True; ErrClaim T a₀⦄

/-- **An error spec applies to a failing run.** -/
theorem CoreSpecE.of_callE {α : Type} {p : Prog} {n : Nat} {f : FnName} {args : List Word}
    {T : AM α} {s₀ : St} {a₀ : AState} (h : CoreSpecE p n f args T s₀ a₀) {e : Err}
    (hc : callE p n f args s₀.mem = .error e) : ErrClaim T a₀ e :=
  triple_of_callE_err h hc

/-- An error spec from the failing runs (the shape the error refinements are proved in). -/
theorem CoreSpecE.of_runs {α : Type} {p : Prog} {n : Nat} {f : FnName} {args : List Word}
    {T : AM α} {s₀ : St} {a₀ : AState}
    (h : ∀ e, callE p n f args s₀.mem = .error e → ErrClaim T a₀ e) :
    CoreSpecE p n f args T s₀ a₀ := by
  apply M.triple_of_run' (fun _ _ _ _ _ => trivial)
  intro s e hs hr
  subst hs
  apply h
  rw [invoke_run_loc'] at hr
  simp only [callE]
  cases hq : (invoke p (exec p n) f args).run { mem := s.mem, loc := Locals.init [] } with
  | error e' => simp [hq, Except.map] at hr; simp [hr]
  | ok q => simp [hq, Except.map] at hr

/-- A call at fuel `0` fails with class `0`: its error spec holds. -/
theorem CoreSpecE.zero {α : Type} (p : Prog) (f : FnName) (args : List Word) (T : AM α)
    (s₀ : St) (a₀ : AState) : CoreSpecE p 0 f args T s₀ a₀ :=
  CoreSpecE.of_runs fun e he => by
    obtain ⟨e', he', h0⟩ := callE_zero p f args s₀.mem
    rw [he] at he'; cases he'
    exact ErrClaim.of_cls0 h0

/-! ## One refinement for both outcomes

A function's `unified` model (`l_model … unified`) is its run with the errors kept: an ok value
for an ok run, the run's error for every error of class other than `0`. `RefE G x T a R` relates
such a model value `x` to the twin computation `T` from `a`: an ok value is `T`'s ok run, the
results and the final states in `R`; an error claims `T`'s failure (`ErrClaim`) under `G`, what
the error claims assume about the program (the no-verdict closure, the core stubs' claims). So
one theorem per function, by one induction over its model, is both its ok refinement (which does
not need `G`) and its error claim; callers take either half from the call's run (`RefE.run_ok`,
`RefE.run_okW`, `RefE.run_err`, `RefE.coreSpecE`, `RefE.triple`), through the model's spec, whose
error post assumes `Gs` (the no-verdict closure, for the callees outside it). -/

/-- **One refinement for both outcomes**: the model value `x` against the twin computation `T`
from `a`; the errors' claims under `G`. -/
def RefE {α β : Type} (G : Prop) (x : Except Err α) (T : AM β) (a : AState)
    (R : α → β → AState → Prop) : Prop :=
  match x with
  | .ok v => ∃ y a', T.run a = .ok (y, a') ∧ R v y a'
  | .error e => G → ErrClaim T a e

section refE
variable {α β γ : Type} {G : Prop} {T : AM β} {a : AState} {R : α → β → AState → Prop}

@[simp] theorem RefE_ok {v : α} :
    RefE G (.ok v) T a R ↔ ∃ y a', T.run a = .ok (y, a') ∧ R v y a' := Iff.rfl

@[simp] theorem RefE_error {e : Err} :
    RefE G (.error e : Except Err α) T a R ↔ (G → ErrClaim T a e) := Iff.rfl

/-- An ok value: the twin's ok run. -/
theorem RefE.ret {v : α} {y : β} {a' : AState} (h : T.run a = .ok (y, a')) (hR : R v y a') :
    RefE G (.ok v) T a R := ⟨y, a', h, hR⟩

/-- An error of class `0` claims nothing. -/
theorem RefE.of_cls0 {e : Err} (h : e.cls = 0) : RefE G (.error e : Except Err α) T a R :=
  fun _ => ErrClaim.of_cls0 h

/-- The error came from the twin's first step (a callee). -/
theorem RefE.bind_left {x : AM γ} {f : γ → AM β} {e : Err} (h : G → ErrClaim x a e) :
    RefE G (.error e : Except Err α) (x >>= f) a R := fun hG => ErrClaim.bind_left (h hG)

/-- The twin's first step ran ok: the rest decides, for both outcomes. -/
theorem RefE.bind_right {x : AM γ} {f : γ → AM β} {a₁ : AState} {v : γ} {r : Except Err α}
    (hx : x.run a = .ok (v, a₁)) (h : RefE G r (f v) a₁ R) : RefE G r (x >>= f) a R := by
  cases r with
  | error e => exact fun hG => ErrClaim.bind_right hx (h hG)
  | ok w =>
    obtain ⟨y, a', hy, hR⟩ := h
    exact ⟨y, a', by simp only [StateT.run_bind, hx]; exact hy, hR⟩

/-- `if` in the twin: the branch taken. -/
theorem RefE.ite_pos {c : Prop} [Decidable c] {x y : AM β} {r : Except Err α} (hc : c)
    (h : RefE G r x a R) : RefE G r (if c then x else y) a R := by
  rw [ite_eq_left hc]; exact h

theorem RefE.ite_neg {c : Prop} [Decidable c] {x y : AM β} {r : Except Err α} (hc : ¬ c)
    (h : RefE G r y a R) : RefE G r (if c then x else y) a R := by
  rw [ite_eq_right hc]; exact h

/-! ### The halves, from the call's run (through the model's spec) -/

variable {p : Prog} {n : Nat} {f : FnName} {args : List Word} {s₀ : St} {Gs : Prop}
  {Q : List Word → St → Prop} {fx : Except Err α} {V : List Word → St → α}

/-- **The ok half**: an ok run of the call is the twin's ok run. -/
theorem RefE.run_ok
    (hs : ⦃fun s => s = s₀⦄ invoke p (exec p n) f args
      ⦃fun r s' => Q r s' ∧ fx = .ok (V r s'); fun ε => Gs → ε.cls ≠ 0 → fx = .error ε⦄)
    (h : RefE G fx T a R) {r : List Word} {m' : Mem} (hc : callE p n f args s₀.mem = .ok (r, m')) :
    ∃ s', s'.mem = m' ∧ Q r s' ∧ ∃ y a', T.run a = .ok (y, a') ∧ R (V r s') y a' := by
  obtain ⟨s', hm, hQ, hx⟩ := triple_of_callE hs hc
  rw [hx] at h
  exact ⟨s', hm, hQ, h⟩

/-- The ok half from `callW` (the ok models' reading of a call). -/
theorem RefE.run_okW
    (hs : ⦃fun s => s = s₀⦄ invoke p (exec p n) f args
      ⦃fun r s' => Q r s' ∧ fx = .ok (V r s'); fun ε => Gs → ε.cls ≠ 0 → fx = .error ε⦄)
    (h : RefE G fx T a R) {r : List Word} {m' : Mem} (hc : callW p n f args s₀.mem = some (r, m')) :
    ∃ s', s'.mem = m' ∧ Q r s' ∧ ∃ y a', T.run a = .ok (y, a') ∧ R (V r s') y a' :=
  RefE.run_ok hs h (callE_of_callW hc)

/-- **The error half**: a failing run of the call claims the twin's failure. -/
theorem RefE.run_err
    (hs : ⦃fun s => s = s₀⦄ invoke p (exec p n) f args
      ⦃fun r s' => Q r s' ∧ fx = .ok (V r s'); fun ε => Gs → ε.cls ≠ 0 → fx = .error ε⦄)
    (hGs : Gs) (hG : G) (h : RefE G fx T a R) {e : Err} (hc : callE p n f args s₀.mem = .error e) :
    ErrClaim T a e := by
  by_cases h0 : e.cls = 0
  · exact ErrClaim.of_cls0 h0
  rw [triple_of_callE_err hs hc hGs h0] at h
  exact h hG

/-- The error half as the error spec of the call (`CoreSpecE`). -/
theorem RefE.coreSpecE
    (hs : ⦃fun s => s = s₀⦄ invoke p (exec p n) f args
      ⦃fun r s' => Q r s' ∧ fx = .ok (V r s'); fun ε => Gs → ε.cls ≠ 0 → fx = .error ε⦄)
    (hGs : Gs) (hG : G) (h : RefE G fx T a R) : CoreSpecE p n f args T s₀ a :=
  CoreSpecE.of_runs fun _ hc => RefE.run_err hs hGs hG h hc

/-- The ok half as a triple (the shape of the `@[refines]` theorems). -/
theorem RefE.triple
    (hs : ⦃fun s => s = s₀⦄ invoke p (exec p n) f args
      ⦃fun r s' => Q r s' ∧ fx = .ok (V r s'); fun ε => Gs → ε.cls ≠ 0 → fx = .error ε⦄)
    (h : RefE G fx T a R) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) f args
    ⦃fun r s' => Q r s' ∧ ∃ y a', T.run a = .ok (y, a') ∧ R (V r s') y a'; ⊤⦄ :=
  M.triple_of_run fun _ _ _ hp hr => by
    obtain ⟨hQ, hx⟩ := M.of_run' (P := fun s => s = s₀) hp hr hs
    rw [hx] at h
    exact ⟨hQ, h⟩

end refE

/-! ### Weaker posts, other twins, tail calls -/

/-- `RefE` reads the twin only through its run from `a`. -/
theorem RefE.of_run_eq {α β : Type} {G : Prop} {x : Except Err α} {T T' : AM β} {a a' : AState}
    {R : α → β → AState → Prop} (h : T.run a = T'.run a') (h' : RefE G x T' a' R) :
    RefE G x T a R := by
  cases x with
  | ok v => obtain ⟨y, a₁, hy, hR⟩ := h'; exact ⟨y, a₁, h.trans hy, hR⟩
  | error e => exact fun hG => ErrClaim.of_run_eqW h (h' hG)

/-- A weaker post. -/
theorem RefE.mono {α β : Type} {G : Prop} {x : Except Err α} {T : AM β} {a : AState}
    {R R' : α → β → AState → Prop} (h : RefE G x T a R) (hR : ∀ v y a', R v y a' → R' v y a') :
    RefE G x T a R' := by
  cases x with
  | ok v => obtain ⟨y, a₁, hy, hr⟩ := h; exact ⟨y, a₁, hy, hR _ _ _ hr⟩
  | error e => exact h

/-- A tail call whose continuation passes the callee's errors on and maps its value (`f`), against
a twin that runs as the callee's twin `T'` from `a₁`. -/
theorem RefE.tail {α β γ : Type} {G G' : Prop} {x : Except Err α} {k : Except Err α → Except Err α}
    {f : α → α} {T : AM β} {T' : AM γ} {a a₁ : AState} {R : α → γ → AState → Prop}
    {R' : α → β → AState → Prop}
    (hk : ∀ e, k (.error e) = .error e) (hk' : ∀ v, k (.ok v) = .ok (f v)) (hG : G → G')
    (hT : ∀ y a', T'.run a₁ = .ok (y, a') → ∃ y', T.run a = .ok (y', a') ∧ ∀ v, R v y a' → R' (f v) y' a')
    (hTe : ∀ ce, T'.run a₁ = .error ce → T.run a = .error ce) (h : RefE G' x T' a₁ R) :
    RefE G (k x) T a R' := by
  cases x with
  | error e => rw [hk]; exact fun g => ErrClaim.of_run_err hTe (h (hG g))
  | ok v =>
    rw [hk']
    obtain ⟨y, a', hr, hR'⟩ := h
    obtain ⟨y', hr', hf⟩ := hT y a' hr
    exact ⟨y', a', hr', hf v hR'⟩

/-- `RefE.tail` against a twin with the same run. -/
theorem RefE.tail_eq {α β : Type} {G G' : Prop} {x : Except Err α} {k : Except Err α → Except Err α}
    {f : α → α} {T T' : AM β} {a a₁ : AState} {R R' : α → β → AState → Prop}
    (hk : ∀ e, k (.error e) = .error e) (hk' : ∀ v, k (.ok v) = .ok (f v)) (hG : G → G')
    (hT : T.run a = T'.run a₁) (hR : ∀ v y a', R v y a' → R' (f v) y a') (h : RefE G' x T' a₁ R) :
    RefE G (k x) T a R' :=
  RefE.tail hk hk' hG (fun y a' hr => ⟨y, hT.trans hr, fun v => hR v y a'⟩) (fun _ he => hT.trans he) h

/-! ## An ok fact and an error claim (`RefC`)

`RefE` relates an ok value to an ok run of a twin computation. Some functions' ok halves are not
such runs: a function that stands for a prefix of a twin function (`m2c_pre`; its ok value gives
the prefix's run, its error claims the failure of the prefix with every continuation), a check
whose ok result is a fact about the model (`vi_unsafe`: no type record is unsafe), or a function
whose twin reports failures as values (`ErrClaimV`, `VerdictClaimL`). `RefC G x Ok C`: an ok value
satisfies `Ok`, an error `e` the claim `C e` under `G`. The halves come from the call's run, as
`RefE`'s. -/

/-- **One refinement for both outcomes, by a fact and a claim**: an ok value of `x` satisfies
`Ok`, an error `e` the claim `C e` (under `G`). -/
def RefC {α : Type} (G : Prop) (x : Except Err α) (Ok : α → Prop) (C : Err → Prop) : Prop :=
  match x with
  | .ok v => Ok v
  | .error e => G → C e

section refC
variable {α : Type} {G : Prop} {Ok : α → Prop} {C : Err → Prop}

@[simp] theorem RefC_ok {v : α} : RefC G (.ok v) Ok C ↔ Ok v := Iff.rfl

@[simp] theorem RefC_error {e : Err} : RefC G (.error e : Except Err α) Ok C ↔ (G → C e) := Iff.rfl

/-- A weaker fact and a weaker claim. -/
theorem RefC.mono {Ok' : α → Prop} {C' : Err → Prop} {x : Except Err α} (h : RefC G x Ok C)
    (hOk : ∀ v, Ok v → Ok' v) (hC : ∀ e, G → C e → C' e) : RefC G x Ok' C' := by
  cases x with
  | ok v => exact hOk v h
  | error e => exact fun g => hC e g (h g)

variable {p : Prog} {n : Nat} {f : FnName} {args : List Word} {s₀ : St} {Gs : Prop}
  {Q : List Word → St → Prop} {fx : Except Err α} {V : List Word → St → α}

/-- **The ok half**: an ok run of the call satisfies the fact. -/
theorem RefC.run_ok
    (hs : ⦃fun s => s = s₀⦄ invoke p (exec p n) f args
      ⦃fun r s' => Q r s' ∧ fx = .ok (V r s'); fun ε => Gs → ε.cls ≠ 0 → fx = .error ε⦄)
    (h : RefC G fx Ok C) {r : List Word} {m' : Mem} (hc : callE p n f args s₀.mem = .ok (r, m')) :
    ∃ s', s'.mem = m' ∧ Q r s' ∧ Ok (V r s') := by
  obtain ⟨s', hm, hQ, hx⟩ := triple_of_callE hs hc
  rw [hx] at h
  exact ⟨s', hm, hQ, h⟩

/-- The ok half from `callW`. -/
theorem RefC.run_okW
    (hs : ⦃fun s => s = s₀⦄ invoke p (exec p n) f args
      ⦃fun r s' => Q r s' ∧ fx = .ok (V r s'); fun ε => Gs → ε.cls ≠ 0 → fx = .error ε⦄)
    (h : RefC G fx Ok C) {r : List Word} {m' : Mem} (hc : callW p n f args s₀.mem = some (r, m')) :
    ∃ s', s'.mem = m' ∧ Q r s' ∧ Ok (V r s') :=
  RefC.run_ok hs h (callE_of_callW hc)

/-- The ok half as a triple (the shape of the `@[refines]` theorems; `RefE.triple`'s counterpart). -/
theorem RefC.triple
    (hs : ⦃fun s => s = s₀⦄ invoke p (exec p n) f args
      ⦃fun r s' => Q r s' ∧ fx = .ok (V r s'); fun ε => Gs → ε.cls ≠ 0 → fx = .error ε⦄)
    (h : RefC G fx Ok C) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) f args ⦃fun r s' => Q r s' ∧ Ok (V r s'); ⊤⦄ :=
  M.triple_of_run fun _ _ _ hp hr => by
    obtain ⟨hQ, hx⟩ := M.of_run' (P := fun s => s = s₀) hp hr hs
    rw [hx] at h
    exact ⟨hQ, h⟩

/-- **The error half**: a failing run of the call satisfies the claim (`C0`: the claim holds for
every error of class `0`, as `ErrClaim`'s and `ErrClaimV`'s do). -/
theorem RefC.run_err
    (hs : ⦃fun s => s = s₀⦄ invoke p (exec p n) f args
      ⦃fun r s' => Q r s' ∧ fx = .ok (V r s'); fun ε => Gs → ε.cls ≠ 0 → fx = .error ε⦄)
    (C0 : ∀ e, e.cls = 0 → C e) (hGs : Gs) (hG : G) (h : RefC G fx Ok C) {e : Err}
    (hc : callE p n f args s₀.mem = .error e) : C e := by
  by_cases h0 : e.cls = 0
  · exact C0 e h0
  rw [triple_of_callE_err hs hc hGs h0] at h
  exact h hG

end refC

/-! ## A twin's prefix and the rest

A `do` block whose guards `if c then fail e` / `unless ← t do fail e` are followed by more code
elaborates with the continuation copied into each branch. The prefix as a function of its own
(`crgT`, `cchT`, `rgT`: the guards a refinement stands for) is split off by
`simp only [prefix, bind_assoc, ite_bindAM, fail_bindAM, pure_bind]`, which pushes the rest into
the prefix's branches (`crgT_bind`, `cchT_bind`, `rgT_bind`). -/

theorem ite_bindAM {α β : Type} (c : Prop) [Decidable c] (x y : AM α) (f : α → AM β) :
    ((if c then x else y) >>= f) = if c then x >>= f else y >>= f := by
  split <;> rfl

theorem fail_bindAM {α β : Type} (e : CheckError) (f : α → AM β) : (fail e >>= f) = fail e := rfl

/-! ## Twin computations that report failures as values

The frontend's stages and the fold return `.ok (.error (ce, n))` for a failing record (the
record's position `n`), and can also fail in the monad. `ErrClaimV T a e`: an L error of class
other than `0` means `T` fails either way with an error of that class. -/

/-- The twin computation `T` from `a` fails with an error of class `c`, in the monad or as a
value. -/
def TwinFailsV {α β : Type} (T : AM (Except (CheckError × α) β)) (a : AState) (c : Word) : Prop :=
  (∃ ce, T.run a = .error ce ∧ twinCls ce = c) ∨
    (∃ ce i a', T.run a = .ok (.error (ce, i), a') ∧ twinCls ce = c)

/-- **The claim about a twin computation that reports failures as values.** -/
def ErrClaimV {α β : Type} (T : AM (Except (CheckError × α) β)) (a : AState) (e : Err) : Prop :=
  e.cls ≠ 0 → TwinFailsV T a e.cls

theorem ErrClaimV.of_cls0 {α β : Type} {T : AM (Except (CheckError × α) β)} {a : AState} {e : Err}
    (h : e.cls = 0) : ErrClaimV T a e := fun h' => absurd h h'

/-- A failure in the monad is a failure. -/
theorem ErrClaimV.of_claim {α β : Type} {T : AM (Except (CheckError × α) β)} {a : AState}
    {e : Err} (h : ErrClaim T a e) : ErrClaimV T a e := fun hk => .inl (h hk)

end L.Arena
