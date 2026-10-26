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

/-- **A callee outside the verdict closure claims nothing.** -/
theorem ErrClaim.of_callE_nv {α : Type} {T : AM α} {a : AState} {p : Prog} {fs : List FnName}
    (hp : closedNV p fs = true) {f : FnName} (hf : f ∈ fs) {n : Nat} {vs : List Word} {m : Mem}
    {e : Err} (h : callE p n f vs m = .error e) : ErrClaim T a e :=
  ErrClaim.of_cls0 (callE_nv hp hf n vs m h)

/-- A word load, error-precise: its value as `rdW`, or an error with code `0` (the loads of the
`errors` models, `l_model … extra [ld64_rdW_specE]`). -/
theorem ld64_rdW_specE (a : ArrId) (i : Word) (s₀ : St) :
    ⦃fun s => s = s₀⦄ ld64 a i
    ⦃fun r s' => s' = s₀ ∧ r = rdW (s₀.mem.arr64 a) i ∧ i.toNat < (s₀.mem.arr64 a).size;
     fun e => e.code = 0⦄ := by
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
