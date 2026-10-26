import ConAgua.Checker.ParDriverTwin
import ConAgua.Final.TwinVerdict

/-!
# The verdict claim at the entries of `check`

The driver's runs that can report a reject or a decline are entry 1 (`check` with the mode word
`1` or `3`: the stages and phase A, `check_a`) and entry 2 (`check` with the mode word `2`: phase
B, `check_b`). `SeqVerdicts` states, for each, what a failing run with an abort of class `1` or `2`
claims: the twin's pipeline on the same bytes fails with an error of that class (`TwinVerdict`).
The entry-2 statement has `drv_twinAccepts`' hypotheses: entry 1 returned `2^63 + k` on its
memory, and entry 2 runs on a memory that keeps phase B's arrays.

`SeqVerdicts checkerProg` is what the per-function error refinements add up to; the final verdict
theorem (`checkerFile_verdict`, `Final/VerdictFinal.lean`) takes it as its hypothesis until it is
proved.
-/

open ConRon.Arena ConAgua.Final

namespace L.Checker

open L L.Arena L.Rom

/-- **Entry 1's verdict claim**: a run of `check` from the loaded memory with the mode word `1`
or `3` that fails with an error of class other than `0` claims the twin's failure with that class. -/
def Entry1Verdict (p : Prog) : Prop :=
  ∀ (b pb : ByteArray) (s8 s64 : List Nat), InputsOK b pb s64 → ∀ (w : Word), (w = 1 ∨ w = 3) →
    ∀ (N : Nat), N < 2 ^ 62 → ∀ (e : Err), L.run p N "check" [] (loadMemM b pb s8 s64 w) = .error e →
      e.cls ≠ 0 → TwinVerdict [b] e.cls

/-- **Entry 2's verdict claim** (the sequential driver's): after entry 1 returned `2^63 + k`,
a run of `check` with the mode word `2` on a memory that keeps entry 1's phase-B arrays, the range
`[0, k)`, an empty seed and the view in the header, that fails with an error of class other than
`0`, claims the twin's failure with that class. -/
def Entry2Verdict (p : Prog) : Prop :=
  ∀ (b pb : ByteArray) (s8 s64 : List Nat), InputsOK b pb s64 →
    ∀ (N₁ : Nat), N₁ < 2 ^ 62 → ∀ (rs₁ : List Word) (m₁ : Mem),
    L.run p N₁ "check" [] (loadMemM b pb s8 s64 3) = .ok (rs₁, m₁) →
    9223372036854775808 ≤ (rs₁.headD 0).toNat →
    ∀ (N₂ : Nat), N₂ ≤ 2 ^ 62 → ∀ (w : Mem),
    (∀ a, phaseBS a = true → w.arr64 a = m₁.arr64 a) → w.glob MODE = 2 → w.glob PLO = 0 →
    w.glob PHI = rs₁.headD 0 - 9223372036854775808 → (w.arr64 CTLF).size = 0 →
    rd64 w HDRF 3 = rd64 m₁ OUT 3 →
    ∀ (e : Err), L.run p N₂ "check" [] w = .error e → e.cls ≠ 0 → TwinVerdict [b] e.cls

/-- **The sequential driver's verdict claims.** -/
structure SeqVerdicts (p : Prog) : Prop where
  entry1 : Entry1Verdict p
  entry2 : Entry2Verdict p

end L.Checker
