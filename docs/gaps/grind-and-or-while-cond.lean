/-
# grind: a `while` guarded by a compound `&&`/`||` condition does not close by `finish`

Toolchain: leanprover/lean4:nightly-2026-09-21 (Lean 4.36.0-nightly-2026-09-21, ca39d2bc).

Expected: `finish` closes the loop spec's normal-exit verification condition, the same way it
does for every single-comparison `while` in this project (`findLoop`, `strCloseLoop`,
`skipBracedLoop` in `ConAgua/L/Examples.lean`).

Observed: `finish` fails on `vc11.2` ("case vc11.2" below), the branch where the FIRST conjunct
of the `while` condition (`i < len(a)`) is already false, so the loop should exit immediately —
the branch needs nothing but `s✝.mem.len8 0 = UInt64.ofNat b.size` (from `hm`) and `hb : b.size <
2 ^ 64` to see that `¬ i < len` and `¬ b.size ≤ i` are contradictory. Raising `finish`'s search
(`gen`) or the `lia` solver's own step budget (`liaSteps := 50000`) does not help, so this reads
as a genuine gap in the compound condition's case split, not merely a search depth limit (the
`[grind] Goal diagnostics` dump even shows the `lia` solver hitting its default step threshold
along the way, which is itself suspicious for a goal this arithmetically small).

Found in con-agua (`ConAgua/Scan/Leaves.lean`, `skip_ws`/`skip_digits`): both `scan_fast.rs`
functions have Rust's `while i < b.len() && is_ws(b[i])` — the motivating example in DESIGN.md's
"Expressions" for `Cond`'s short-circuit `&&`/`||` in the first place. Workaround used there:
write the loop with the array bound alone in the `while` and an explicit `return i` when the byte
fails the test (the `findLoop`/`strCloseLoop` idiom), which both `skip_ws`/`skip_digits` prove
with no trouble. This file is the compound-condition shape that does not.
-/

import ConAgua.L.Examples

open L L.Examples
open Std.WP
open scoped Lean.Order
set_option experimental.vcgen true

namespace Gap

abbrev IN : ArrId := 0

/-- `scan_fast.rs`'s own `skip_ws`, condition and all (contrast `L.Scan.Leaves.skipWsLoop`,
which drops the `&&` for exactly this reason). -/
def skipWsLoop : Stmt := lblk (i) {
  while i < len(IN.u8) && (IN.u8[i] == 32 || IN.u8[i] == 9 || IN.u8[i] == 13) {
    i += 1
  }
}

def skipWsN (b : Array UInt8) (i : Nat) : Nat :=
  if h : i < b.size then
    if b[i] = 32 ∨ b[i] = 9 ∨ b[i] = 13 then skipWsN b (i + 1) else i
  else i
termination_by b.size - i

variable (b : Array UInt8) (i : Nat)
theorem skipWsN_ws (k : Nat) (hk : k = i + 1) (h : i < b.size)
    (hc : b[i] = 32 ∨ b[i] = 9 ∨ b[i] = 13) : skipWsN b i = skipWsN b k := by
  subst hk; rw [skipWsN]; simp [h, hc]
theorem skipWsN_other (h : i < b.size) (hc : ¬ (b[i] = 32 ∨ b[i] = 9 ∨ b[i] = 13)) :
    skipWsN b i = i := by rw [skipWsN]; simp [h, hc]
theorem skipWsN_end (h : b.size ≤ i) : skipWsN b i = i := by rw [skipWsN]; simp; omega
grind_pattern [lang_grind] skipWsN_ws => skipWsN b i, b[i], skipWsN b k
grind_pattern [lang_grind] skipWsN_other => skipWsN b i, b[i]
grind_pattern [lang_grind] skipWsN_end => skipWsN b i

section
variable (p : Prog) (b : Array UInt8) (hb : b.size < 2 ^ 64)
include hb

/-- Fails: `finish` cannot close `vc11.2` (the `i ≥ len` exit of the compound condition). -/
theorem skipWsLoop_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b)
    (hi : (s₀.loc 0).toNat ≤ b.size) :
    ⦃fun s => s = s₀⦄
    exec p n skipWsLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r = .normal ∧
      s'.loc 0 = UInt64.ofNat (skipWsN b (s₀.loc 0).toNat); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := skipWsLoop) rfl]
    sym only [lang_grind] => vcgen [step, evalE, evalC, setLoc, ld8, ih] <;> finish

end
end Gap
