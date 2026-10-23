import ConAgua.Checker.Entry

/-!
# `cap_check()` checks the capacities (lane `pipeline`)

`cap_check()`'s body is a `foldr` over the word arrays `0‥wordArrays - 1` of
`if 2^63 ≤ len(b.u64) { abort }`, then `if len(CTL.u64) < ctlMin { abort }; return 0`
(`capCheckBody`, `Checker/Entry.lean`). A run that returns leaves the state alone, and every
word array's length *as a word* is below `2^63` (`CapsW`). `len64` is the size modulo `2^64`, so
the actual sizes are below `2^63` only for sizes below `2^64` (`WordsFit`, which every memory the
x64 layout can hold meets): then `CapsOK`. The proof is by induction over the list, on runs
(`capFold_run`), not by unrolling the 214 branches.
-/

namespace L.Checker

open L L.Arena
open Std.WP
open scoped Lean.Order

/-- **The capacities `check` needs**: every word array the checker names is shorter than `2^63`
words, and `CTL` has at least `ctlMin` words. -/
def CapsOK (m : Mem) : Prop :=
  (∀ a < wordArrays, (m.arr64 a).size < 2 ^ 63) ∧ ctlMin ≤ (m.arr64 CTL).size

/-- What `cap_check` observes: the lengths as words (`len64`, the size modulo `2^64`). -/
def CapsW (m : Mem) : Prop :=
  (∀ a < wordArrays, (m.len64 a).toNat < 2 ^ 63) ∧ ctlMin ≤ (m.arr64 CTL).size

/-- Every word array the checker names has a size that is a word. -/
def WordsFit (m : Mem) : Prop := ∀ a < wordArrays, (m.arr64 a).size < 2 ^ 64

theorem CapsW.capsOK {m : Mem} (h : CapsW m) (hf : WordsFit m) : CapsOK m := by
  refine ⟨fun a ha => ?_, h.2⟩
  have h1 := h.1 a ha
  have h2 := hf a ha
  simp only [Mem.len64, UInt64.toNat_ofNat'] at h1
  rwa [Nat.mod_eq_of_lt h2] at h1

theorem run_throw' {α : Type} (e : Err) (s : St) : StateT.run (throw e : M α) s = .error e := rfl

theorem error_bind' {α β : Type} (e : Err) (f : α → Except Err β) :
    (Except.error e >>= f) = .error e := rfl

theorem error_map' {α β : Type} (e : Err) (f : α → β) : (f <$> (Except.error e : Except Err α)) = .error e := rfl

/-- One array's check (the `foldr`'s step). -/
def capStep (b : Nat) (s : Stmt) : Stmt :=
  .seq (.ite (.cmp .ule (.const 9223372036854775808) (.len64 b)) .abort .skip) s

/-- The `CTL` check and the return. -/
def capTail : Stmt :=
  .seq (.ite (.cmp .ult (.len64 CTL) (.const (UInt64.ofNat ctlMin))) .abort .skip) (.ret [.const 0])

theorem capCheckBody_eq : capCheckBody = (List.range wordArrays).foldr capStep capTail := rfl

/-- A run of the checks of the arrays `l`, then `t`, that returns: every array of `l` has a
length below `2^63` as a word, and the run is `t`'s. -/
theorem capFold_run {p : Prog} {k : Stmt → M Sig} (t : Stmt) :
    ∀ (l : List Nat) (s : St) (r : Sig) (s' : St), (step p k (l.foldr capStep t)).run s = .ok (r, s') →
      (∀ b ∈ l, (s.mem.len64 b).toNat < 2 ^ 63) ∧ (step p k t).run s = .ok (r, s') := by
  intro l
  induction l with
  | nil => intro s r s' h; exact ⟨fun _ h => absurd h List.not_mem_nil, h⟩
  | cons b l ih =>
    intro s r s' h
    simp [List.foldr_cons, capStep, step, evalC, evalE, Cmp.eval] at h
    by_cases hb : (9223372036854775808 : Word) ≤ s.mem.len64 b
    · simp [hb, run_throw', error_bind'] at h
    · simp [hb] at h
      obtain ⟨h1, h2⟩ := ih s r s' h
      refine ⟨fun c hc => ?_, h2⟩
      rcases List.mem_cons.1 hc with rfl | hc
      · simp only [UInt64.not_le, UInt64.lt_iff_toNat_lt] at hb
        simpa using hb
      · exact h1 c hc

theorem capTail_run {p : Prog} {k : Stmt → M Sig} (s : St) (r : Sig) (s' : St)
    (h : (step p k capTail).run s = .ok (r, s')) :
    ctlMin ≤ (s.mem.arr64 CTL).size ∧ r = .ret [0] ∧ s' = s := by
  simp [capTail, step, evalC, evalE, evalArgs, Cmp.eval] at h
  by_cases hc : s.mem.len64 CTL < UInt64.ofNat ctlMin
  · simp [hc, run_throw', error_bind'] at h
  · simp [hc] at h
    change Except.ok _ = _ at h
    cases h
    refine ⟨?_, rfl, rfl⟩
    simp only [UInt64.not_lt, UInt64.le_iff_toNat_le, Mem.len64, UInt64.toNat_ofNat'] at hc
    have : ctlMin % 2 ^ 64 = ctlMin := by simp [ctlMin]
    rw [this] at hc
    exact Nat.le_trans hc (Nat.mod_le _ _)

/-- **`cap_check()` observes the capacities**: a run that returns leaves the state alone, and
the lengths as words meet `CapsW`. -/
theorem capCheck_specW (p : Prog) (hp : p.lookup "cap_check" = some capCheckL) (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "cap_check" []
    ⦃fun _ s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ CapsW s₀.mem; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  subst hs
  rw [invoke_eq _ hp] at hrun
  cases n with
  | zero => simp [callFn, exec, run_throw', error_map'] at hrun
  | succ n =>
    simp only [callFn, exec, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_set] at hrun
    cases hb : (step p (exec p n) capCheckL.body).run { s with loc := Locals.init [] } with
    | error e => rw [hb] at hrun; cases hrun
    | ok q =>
      obtain ⟨r₁, s₁⟩ := q
      rw [hb] at hrun
      simp at hrun
      obtain ⟨-, rfl⟩ := hrun
      have hb' : (step p (exec p n) ((List.range wordArrays).foldr capStep capTail)).run
          { s with loc := Locals.init [] } = .ok (r₁, s₁) := hb
      obtain ⟨h1, h2⟩ := capFold_run capTail _ _ _ _ hb'
      obtain ⟨h3, -, rfl⟩ := capTail_run _ _ _ h2
      exact ⟨rfl, rfl, fun a ha => h1 a (List.mem_range.2 ha), h3⟩

/-- **`cap_check()` checks the capacities**: a run that returns leaves the state alone, and on a
memory whose word arrays' sizes are words (`WordsFit`) the capacities are `CapsOK`. -/
theorem capCheck_spec (p : Prog) (hp : p.lookup "cap_check" = some capCheckL) (n : Nat) (s₀ : St)
    (hf : WordsFit s₀.mem) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "cap_check" []
    ⦃fun _ s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ CapsOK s₀.mem; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨h1, h2, h3⟩ := M.of_run (P := fun s => s = s₀) hs hrun (capCheck_specW p hp n s₀)
  exact ⟨h1, h2, h3.capsOK hf⟩

end L.Checker
