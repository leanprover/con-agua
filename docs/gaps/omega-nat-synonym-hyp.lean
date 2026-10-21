/-
# omega: a hypothesis at a type synonym of `Nat` is ignored

Toolchain: leanprover/lean4:nightly-2026-10-20 (Lean (version 4.37.0-nightly-2026-10-20, x86_64-unknown-linux-gnu, commit c260aee449e6bda694d253413ba713249803b4cb, Release)).

Expected: every example is proved; `Var` is an `abbrev` for `Nat`.
Observed: the first three fail ("omega could not prove the goal"): a variable `x : Var` (and
`x < n`, which elaborates to `@LT.lt Var instLTNat x n`) is not recognised as a natural number,
not even with the hypothesis restated at `@LT.lt Nat` or a type ascription `(x : Nat)`.
`simp only [Var] at *` (fourth example) or `change` to `@LT.lt Nat`/`@LE.le Nat` in both the
hypothesis and the goal make it work.

Found in con-agua: L's locals have type `L.Var := Nat`, and well-formedness gives `x < nlocals`.
Workaround there: `simp only [L.Var] at *` before `omega`.
-/

abbrev Var := Nat

example (x : Var) (n : Nat) (h : x < n) : x + 1 ≤ n := by
  omega  -- fails

example (x : Var) (n : Nat) (h : x < n) : x + 1 ≤ n := by
  have h' : @LT.lt Nat _ x n := h
  omega  -- fails too

example (x : Var) (n : Nat) (h : (x : Nat) < n) : x + 1 ≤ n := by
  omega  -- fails too

example (x : Var) (n : Nat) (h : x < n) : x + 1 ≤ n := by
  simp only [Var] at *
  omega
