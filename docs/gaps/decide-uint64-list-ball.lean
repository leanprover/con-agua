/-
# `decide`: a bounded `∀` over a `List UInt64` hits the recursion limit

Toolchain: leanprover/lean4:nightly-2026-10-20 (Lean (version 4.37.0-nightly-2026-10-20, x86_64-unknown-linux-gnu, commit c260aee449e6bda694d253413ba713249803b4cb, Release)).

Expected: both examples are proved by `decide` (two `UInt64` comparisons each).
Observed: the first is proved; the second fails with "maximum recursion depth has been reached"
(the `List` bounded-`∀` instance over `UInt64` membership). In con-agua, with the lists built
from schema fields (`S.ca + 1`), the same goals instead ran into the heartbeat limit, and
`decide +kernel` did not finish in two minutes.

Found in con-agua: `Apart S A₀ C₀ A C` (`ConAgua/Arena/Frame.lean`), the disjointness of a table
from a writer, has a clause `∀ x ∈ C₀, x ∉ C` over `CTL` word indices. Workaround there: a `simp`
with the array ids and schemas unfolded (the `apart` macro in `ConAgua/Arena/ArenaRel.lean`).
-/

example : (0 : UInt64) ∉ ([22, 23] : List UInt64) := by decide

example : ∀ x ∈ ([0] : List UInt64), x ∉ ([22, 23] : List UInt64) := by decide
