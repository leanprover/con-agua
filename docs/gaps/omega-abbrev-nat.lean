/-
# `omega` does not see through an `abbrev` of `Nat`

Toolchain: leanprover/lean4:nightly-2026-10-20.

Expected: both examples are proved by `omega` (`ArrId` is `abbrev ArrId := Nat`).
Observed: the first fails with "No usable constraints found"; the second (plain `Nat`) is proved.
`change` to `(b : Nat)` does not help either (the instances stay `ArrId`'s).

Found in con-agua: `ArenaR.frame_above` (`ConAgua/Arena/ArenaRel.lean`), array ids are `L.ArrId`.
Workaround: `Nat.not_le_of_lt` / `Nat.not_lt_of_le` by hand.
-/

abbrev ArrId := Nat

example (b : ArrId) (hb : 42 ≤ b ∧ b < 47) (h : b < 42 ∨ 47 ≤ b) : False := by omega

example (b : Nat) (hb : 42 ≤ b ∧ b < 47) (h : b < 42 ∨ 47 ≤ b) : False := by omega
