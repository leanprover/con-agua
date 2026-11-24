module

public import ConAgua.Checker.CmpSeqRun
import ConAgua.Front.FrontRunRef
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import all ConAgua.Checker.Entry
import all ConAgua.Checker.CmpSeqEntry
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# Modes `8` and `9` failing in place (lane compare2, the sJ variant)

The error halves of `cq_check8` and `cq_check9`: a failing run of `check` with the mode word `8`
(resp. `9`) on the region fails with class `0` (the switch, the flush, `check`'s own abort) or is a
failing `check_jobs(PLO, PHI)` call on `cqSM N` (resp. `cqCM N`), with the same error.
-/

namespace L.Checker

open L L.Arena L.Front
open Std.WP
open scoped Lean.Order
set_option experimental.vcgen true

/-- `invoke_agree`'s error half (as `Verdict/ThreadsE.lean`'s `invoke_agree_err`). -/
theorem cq_invoke_agree_err {p : Prog} {S : TieredArray → Bool} {S8 : ArrId → Bool} {fs : List FnName}
    (hp : readsIn p S S8 fs = true) {f : FnName} (hf : f ∈ fs) {n : Nat} {vs : List Word}
    {s₁ s₂ : St} (hm : Agree S S8 s₁.mem s₂.mem) (hl : s₁.loc = s₂.loc) {e : Err}
    (h : (invoke p (exec p n) f vs).run s₁ = .error e) :
    (invoke p (exec p n) f vs).run s₂ = .error e := by
  have := L.invoke_agree hp hf n vs hm hl
  rw [h] at this
  revert this
  cases (invoke p (exec p n) f vs).run s₂ with
  | ok r => intro h'; exact h'.elim
  | error e' => intro h'; cases h'; rfl

/-- **`check`'s dispatch to modes `8` and `9`, error half.** -/
theorem check_err_dispatch89 {p : Prog} (hp : p.lookup "check" = some checkL) (n : Nat) (s₀ : St)
    (E : Err → Prop)
    (h8 : ∀ s₁ : St, ⦃fun s => s = s₁⦄ invoke p (exec p n) "check_bs" []
      ⦃fun _ _ => True; fun e => s₁.mem = s₀.mem → s₀.mem.glob MODE = 8 → E e⦄)
    (h9 : ∀ s₁ : St, ⦃fun s => s = s₁⦄ invoke p (exec p n) "check_bc" []
      ⦃fun _ _ => True; fun e => s₁.mem = s₀.mem → s₀.mem.glob MODE = 9 → E e⦄)
    (hE : E (.abort 0)) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "check" []
    ⦃fun _ _ => True; fun e => (s₀.mem.glob MODE = 8 ∨ s₀.mem.glob MODE = 9) → E e⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, (h8 ·), (h9 ·),
    (L.invoke_loc p (exec p n) "check_a" [·] ·), (L.invoke_loc p (exec p n) "check_b" [] ·),
    (L.invoke_loc p (exec p n) "check_c1" [] ·), (L.invoke_loc p (exec p n) "check_c2" [] ·),
    (L.invoke_loc p (exec p n) "check_c3" [·] ·)]
  all_goals (try simp only at *)
  all_goals grind [lang_grind]

/-- A failing run of `check` from a region with the mode word `8` or `9` fails as the dispatch's
triple says. -/
theorem cq_run_err {p : Prog} (hp : p.lookup "check" = some checkL) {W : Mem} (E : Err → Prop)
    (hE0 : ∀ e, e.cls = 0 → E e) {n₀ : Nat}
    (h8 : ∀ n (s₁ : St), n < n₀ → ⦃fun s => s = s₁⦄ invoke p (exec p n) "check_bs" []
      ⦃fun _ _ => True; fun e => s₁.mem = W → W.glob MODE = 8 → E e⦄)
    (h9 : ∀ n (s₁ : St), n < n₀ → ⦃fun s => s = s₁⦄ invoke p (exec p n) "check_bc" []
      ⦃fun _ _ => True; fun e => s₁.mem = W → W.glob MODE = 9 → E e⦄)
    (hmode : W.glob MODE = 8 ∨ W.glob MODE = 9) {e : Err}
    (hrun : L.run p n₀ "check" [] W = .error e) : E e := by
  have hr : (invoke p (exec p n₀) "check" []).run ⟨W, Locals.init []⟩ = .error e := by
    simp only [L.run] at hrun
    cases h : (invoke p (exec p n₀) "check" []).run ⟨W, Locals.init []⟩ with
    | ok x => rw [h] at hrun; cases hrun
    | error e' => rw [h] at hrun; cases hrun; rfl
  cases n₀ with
  | zero =>
    obtain ⟨e', he', h0⟩ := callE_zero p "check" [] W
    rw [callE_of_run_err (s := ⟨W, Locals.init []⟩) hr] at he'
    cases he'
    exact hE0 e h0
  | succ n =>
    exact M.of_run_err (P := fun s => s = ⟨W, Locals.init []⟩) rfl hr
      (check_err_dispatch89 hp n ⟨W, Locals.init []⟩ E (fun s₁ => h8 n s₁ (by omega))
        (fun s₁ => h9 n s₁ (by omega)) (hE0 _ rfl)) hmode

/-- **Mode `8` failing in place**: a failing run of `check` with the mode word `8` on a region `W`
that agrees with `N` but in `OUT`, `HDRF`, `CTLF` and the bytes fails with class `0` or as the
jobs' `check_jobs(PLO, PHI)` call on `cqSM N`. -/
theorem cq_check8_err {p : Prog} (hQ : CqSeqProg p) {W N : Mem}
    (hAg : Agree phaseBPa (fun _ => false) W N) (hmode : W.glob MODE = 8)
    {n : Nat} (hN : n ≤ 2 ^ 62) {e : Err} (hrun : L.run p n "check" [] W = .error e) :
    e.cls = 0 ∨ ∃ k, k ≤ 2 ^ 62 ∧ callE p k "check_jobs" [(cqSM N).glob PLO, (cqSM N).glob PHI] (cqSM N) = .error e := by
  obtain ⟨fs, hfs, -, hrd⟩ := hQ.reads
  refine cq_run_err hQ.check (fun e => e.cls = 0 ∨
      ∃ k, k ≤ 2 ^ 62 ∧ callE p k "check_jobs" [(cqSM N).glob PLO, (cqSM N).glob PHI] (cqSM N) = .error e)
    (fun _ h => .inl h) (fun n s₁ hn => ?_)
    (fun n s₁ _ => M.triple_of_run' (fun _ _ _ _ _ => trivial) fun _ _ _ _ _ h => by
      rw [hmode] at h; cases h) (.inl hmode) hrun
  apply M.triple_of_run' (fun _ _ _ _ _ => trivial)
  rintro s e rfl h1 e1 -
  have hAg1 : Agree phaseBPa (fun _ => false) s.mem N := by rw [e1]; exact hAg
  have h2 := cq_invoke_agree_err (s₂ := ⟨N, s.loc⟩) hrd hfs hAg1 rfl h1
  cases n with
  | zero =>
    obtain ⟨e', he', h0⟩ := callE_zero p "check_bs" [] N
    rw [callE_of_run_err h2] at he'
    cases he'
    exact .inl h0
  | succ k =>
    rcases M.of_run_err (P := fun x => x = ⟨N, s.loc⟩) rfl h2
      (checkBS_spec hQ.bs k (hQ.bankS k) (hQ.ctlS k) (hQ.flush k) ⟨N, s.loc⟩) with h | h
    · exact .inl h
    · dsimp only at h; exact .inr ⟨k, by omega, h⟩

/-- **Mode `9` failing in place** (`cq_check8_err` for `check_bc`, on `cqCM N`). -/
theorem cq_check9_err {p : Prog} (hQ : CqSeqProg p) {W N : Mem}
    (hAg : Agree phaseBPa (fun _ => false) W N) (hmode : W.glob MODE = 9)
    {n : Nat} (hN : n ≤ 2 ^ 62) {e : Err} (hrun : L.run p n "check" [] W = .error e) :
    e.cls = 0 ∨ ∃ k, k ≤ 2 ^ 62 ∧ callE p k "check_jobs" [(cqCM N).glob PLO, (cqCM N).glob PHI] (cqCM N) = .error e := by
  obtain ⟨fs, -, hfs, hrd⟩ := hQ.reads
  refine cq_run_err hQ.check (fun e => e.cls = 0 ∨
      ∃ k, k ≤ 2 ^ 62 ∧ callE p k "check_jobs" [(cqCM N).glob PLO, (cqCM N).glob PHI] (cqCM N) = .error e)
    (fun _ h => .inl h)
    (fun n s₁ _ => M.triple_of_run' (fun _ _ _ _ _ => trivial) fun _ _ _ _ _ h => by
      rw [hmode] at h; cases h) (fun n s₁ hn => ?_) (.inr hmode) hrun
  apply M.triple_of_run' (fun _ _ _ _ _ => trivial)
  rintro s e rfl h1 e1 -
  have hAg1 : Agree phaseBPa (fun _ => false) s.mem N := by rw [e1]; exact hAg
  have h2 := cq_invoke_agree_err (s₂ := ⟨N, s.loc⟩) hrd hfs hAg1 rfl h1
  cases n with
  | zero =>
    obtain ⟨e', he', h0⟩ := callE_zero p "check_bc" [] N
    rw [callE_of_run_err h2] at he'
    cases he'
    exact .inl h0
  | succ k =>
    rcases M.of_run_err (P := fun x => x = ⟨N, s.loc⟩) rfl h2
      (checkBC_spec hQ.bc k (hQ.bankC k) (hQ.ctlC k) (hQ.flush k) ⟨N, s.loc⟩) with h | h
    · exact .inl h
    · dsimp only at h; exact .inr ⟨k, by omega, h⟩

end L.Checker
