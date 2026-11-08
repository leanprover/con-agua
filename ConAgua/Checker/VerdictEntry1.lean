module

public import ConAgua.Checker.VerdictTop
import ConAgua.Checker.CheckARun
public import ConAgua.L.GrindAttr
meta import ConAgua.Checker.VerdictTop
meta import ConAgua.Checker.CheckARun
meta import ConAgua.L.GrindAttr
import ConAgua.Checker.LoopProgTac
import ConAgua.Checker.NoVerdictClosed
public import ConAgua.Checker.PipeFinal
import all ConAgua.Checker.Entry

@[expose] public section

/-!
# Entry 1's verdict claim from its stages

`check_a(c)` (`Checker/Entry.lean`) runs the stages, phase A's fold and `par_compact`. Of these,
only `builtin_prelude`, `front_run` and `install_fold_go` can fail with a class other than `0`;
the others are in `nvFns` (`checkerProg_nv`). A stage's **error spec** (`StageSpecE`): a failing
call from memory satisfying the stage's precondition, with a class other than `0`, claims the
twin's failure (`V c`, here `TwinVerdict [b] c`). The stage preconditions `Q3`, `Q4`, `Q7` hold
the twin's run of the stages before (`Pipeline.lean`), so a stage's error spec is the stage's own
error refinement and the twin's prefix (`TwinVerdict.prelude`, `.front`, `.fold`).

* `checkA_err_of_stages`: `check_a`'s error from the stages' ok specs and the three error specs
  (the vcgen of `checkA_of_stages`, with error posts);
* `check_err_dispatchA`: `check` with the mode word `1` or `3` fails only as `check_a` does;
* `entry1Verdict_of`: `Entry1Verdict checkerProg` from the three error specs at the checker's
  stage relations (`checkerRels`).
-/

namespace L.Checker

open L L.Arena ConAgua.Final ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

/-- **A stage's error spec**: from memory satisfying `Pre`, a failing call of `f` with a class
other than `0` gives `V` at that class. -/
def StageSpecE (p : Prog) (f : FnName) (args : List Word) (Pre : Mem → Prop) (V : Word → Prop) : Prop :=
  ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ (s₀ : St), ⦃fun s => s = s₀⦄ invoke p (exec p n) f args
    ⦃fun _ _ => True; fun e => Pre s₀.mem → e.cls ≠ 0 → V e.cls⦄

/-- A call of a function outside the verdict closure, at any start: its errors have class `0`. -/
theorem nv_at {p : Prog} {fs : List FnName} (hp : closedNV p fs = true) {f : FnName} (hf : f ∈ fs)
    (n : Nat) (vs : List Word) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) f vs ⦃fun _ _ => True; NVE⦄ :=
  M.triple_of_run' (fun _ _ _ _ _ => trivial)
    fun _ _ _ hr => M.of_run_err (P := fun _ => True) trivial hr (invoke_nv p hp n f hf vs)

/-- **`check_a(c)`'s error from its stages.** -/
theorem checkA_err_of_stages {p : Prog} (hp : p.lookup "check_a" = some checkAL)
    {fs : List FnName} (hnv : closedNV p fs = true)
    (hm1 : "cap_check" ∈ fs) (hm2 : "pb_check" ∈ fs) (hm2p : "presize_tables" ∈ fs)
    (hm3 : "intern_reserved_pins" ∈ fs)
    (hm6 : "prepare_prelude" ∈ fs) (hm7 : "intern_all_pins" ∈ fs) (hm8 : "par_compact" ∈ fs)
    {Q0 Q1 Q2 Q2p Q3 Q4 Q5 Q6 Q7 : Mem → Prop} {V : Word → Prop}
    (h1 : StageSpec p "cap_check" Q0 fun _ => Q1)
    (h2 : StageSpec p "pb_check" Q1 fun _ => Q2)
    (h2p : StageSpec p "presize_tables" Q2 fun _ => Q2p)
    (h3 : StageSpec p "intern_reserved_pins" Q2p fun _ => Q3)
    (h4 : StageSpec p "builtin_prelude" Q3 fun _ => Q4)
    (h5 : StageSpec p "front_run" Q4 fun r m => r.headD 0 = 0 → Q5 m)
    (h6 : StageSpec p "prepare_prelude" Q5 fun _ => Q6)
    (h7 : StageSpec p "intern_all_pins" Q6 fun _ => Q7)
    (e4 : StageSpecE p "builtin_prelude" [] Q3 V)
    (e5 : StageSpecE p "front_run" [] Q4 V)
    (e8 : ∀ n, n ≤ 2 ^ 62 → ∀ (s₀ : St) (cnt : Word),
      ⦃fun s => s = s₀⦄ invoke p (exec p n) "install_fold_go" [0, cnt, 0]
      ⦃fun _ s' => LocEq s' s₀; fun e => Q7 s₀.mem →
        (∀ h : 0 < (s₀.mem.arr64 L.Front.DECL).size, cnt = (s₀.mem.arr64 L.Front.DECL)[0]) →
        e.cls ≠ 0 → V e.cls⦄)
    (c : Word) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_a" [c]
    ⦃fun _ _ => True; fun e => Q0 s₀.mem → e.cls ≠ 0 → V e.cls⦄ := by
  sorry

/-- **`check` with the mode word `1` or `3` fails only as `check_a` does.** -/
theorem check_err_dispatchA {p : Prog} (hp : p.lookup "check" = some checkL) (n : Nat) (s₀ : St)
    (E : Err → Prop)
    (hA : ∀ (s₁ : St) (c : Word), ⦃fun s => s = s₁⦄ invoke p (exec p n) "check_a" [c]
      ⦃fun _ _ => True; fun e => s₁.mem = s₀.mem → E e⦄) (hE : E (.abort 0)) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "check" []
    ⦃fun _ _ => True; fun e => (s₀.mem.glob MODE = 1 ∨ s₀.mem.glob MODE = 3) → E e⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, (hA · ·),
    (L.invoke_loc p (exec p n) "check_b" [] ·)]
  all_goals (try simp only at *)
  all_goals grind [lang_grind]

/-- A failing run is a failing call from the run's start. -/
theorem run_err {p : Prog} {N : Nat} {f : FnName} {m : Mem} {e : Err}
    (h : L.run p N f [] m = .error e) :
    (invoke p (exec p N) f []).run { mem := m, loc := Locals.init [] } = .error e := by
  simp only [L.run] at h
  cases hr : (invoke p (exec p N) f []).run { mem := m, loc := Locals.init [] } with
  | error e' => rw [hr] at h; cases h; rfl
  | ok v => rw [hr] at h; cases h

/-- The error specs of the three stages that can claim a verdict, at the checker's stage
relations. -/
structure Entry1StagesE : Prop where
  prelude : ∀ b pb sz, InputsOK b pb sz →
    StageSpecE checkerProg "builtin_prelude" [] (Q3 b (checkerRels b pb sz)) (TwinVerdict [b])
  front : ∀ b pb sz, InputsOK b pb sz →
    StageSpecE checkerProg "front_run" [] (Q4 b (checkerRels b pb sz)) (TwinVerdict [b])
  fold : ∀ b pb sz, InputsOK b pb sz → ∀ n, n ≤ 2 ^ 62 → ∀ (s₀ : St) (cnt : Word),
    ⦃fun s => s = s₀⦄ invoke checkerProg (exec checkerProg n) "install_fold_go" [0, cnt, 0]
    ⦃fun _ s' => LocEq s' s₀; fun e => Q7 b (checkerRels b pb sz) s₀.mem →
      (∀ h : 0 < (s₀.mem.arr64 L.Front.DECL).size, cnt = (s₀.mem.arr64 L.Front.DECL)[0]) →
      e.cls ≠ 0 → TwinVerdict [b] e.cls⦄

/-- **Entry 1's verdict claim from its stages' error specs.** -/
theorem entry1Verdict_of (h : Entry1StagesE) : Entry1Verdict checkerProg := by
  sorry

end L.Checker
