/-
# vcgen: a `have` before `induction` hides the induction hypothesis

Toolchain: leanprover/lean4:nightly-2026-10-20.

Expected: both proofs go through; they differ only in where the unrelated fact `h` is
introduced.

Observed: the second fails with "No spec found for program loop n": with a hypothesis
introduced by `have` before `induction … generalizing s₀`, `vcgen` does not use `ih` for the
recursive call (passing `ih` explicitly does not help).

Found in con-agua `ConAgua/Scan/Member.lean` (`nextMemberLoop_spec`, a `have hb' : b.size < 2 ^ 64`
derived from the section's `hb` before the induction on fuel). Workaround: introduce such facts
inside the `succ` case.
-/
import Std.WP
import Std.Tactic.Do
set_option experimental.vcgen true
open Std.WP
open scoped Lean.Order

def loop : Nat → StateT Nat (Except String) Unit
  | 0 => pure ()
  | n+1 => do modify (· + 1); loop n

-- works
theorem loop_spec (n : Nat) (s₀ : Nat) (k : Nat) (hk : k < 10) :
    ⦃fun s => s = s₀⦄ loop n ⦃fun _ s => s = s₀ + n; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [loop] <;> grind
  | succ n ih =>
    rw [loop]
    have h : k < 11 := by omega
    vcgen [ih] <;> grind

-- fails
theorem loop_spec' (n : Nat) (s₀ : Nat) (k : Nat) (hk : k < 10) :
    ⦃fun s => s = s₀⦄ loop n ⦃fun _ s => s = s₀ + n; ⊤⦄ := by
  have h : k < 11 := by omega
  induction n generalizing s₀ with
  | zero => vcgen [loop] <;> grind
  | succ n ih =>
    rw [loop]
    vcgen [ih] <;> grind
