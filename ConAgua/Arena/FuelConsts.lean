import ConAgua.Arena.Pins

/-!
# The twin's fuel constants in L (lane `tails`)

The twin threads two fuel constants (`ConRon/Arena/Core.lean`); L has no function for either:

* `coreWalkFuel` (`4·10⁹`): every walk entry starts its counter word at the literal
  `4000000000`, whose value is `coreWalkFuel` (`coreWalkFuel_word`; the entries' refinements use
  `coreWalkFuel_toNat`, `FVarRangeRefine.lean`).
* `checkFuel` (`2⁶²`): the knot's fuel. L's knot runs on L's own fuel, which the final theorem
  bounds by `2⁶²` (`ConAgua/Final/Statement.lean`, `N < 2^62`); the knot's refinements hold at
  every twin fuel at least the L fuel, so at `checkFuel` (`checkFuel_ge`, as `IndTwin.lean`'s
  `stage_fuel`).

Two more twin definitions with no L function of their own, by the L facts the checker uses:

* `reservedBasisNames` (`pinReserved`): L keeps the list as the pin table's words `PINS[55‥70]`
  (read by `reserved_contains`, `reserved_contains_w`); under a filled table they decode to it
  (`reservedBasisNames_words`).
* `liftFueled`: every L level comparison returns only when the twin's fueled comparison gives
  `some`, where `liftFueled` is that value (`liftFueled_some`); at `none` the twin declines and L
  aborts.
-/

namespace L.Arena

open ConRon.Arena

/-- **The walks' counter literal is `coreWalkFuel`.** -/
@[refines ConRon.Arena.coreWalkFuel]
theorem coreWalkFuel_word : (4000000000 : Word).toNat = coreWalkFuel := rfl

/-- **Every L fuel below `2⁶²` is at most `checkFuel`**: the knot's refinements, stated for every
twin fuel at least the L fuel, apply at the twin's `checkFuel`. -/
@[refines ConRon.Arena.checkFuel]
theorem checkFuel_ge {n : Nat} (hn : n < 2 ^ 62) : n ≤ checkFuel := by
  unfold checkFuel; omega

/-- **The reserved names are the pin table's words `PINS[55‥70]`.** -/
@[refines ConRon.Arena.reservedBasisNames]
theorem reservedBasisNames_words {m : Mem} {a : AState} (hP : PinsR m a.pins) (h0 : pinW m 0 ≠ 0) :
    reservedBasisNames.run a = .ok ((List.range 16).map fun i => decI (pinW m (55 + i)), a) :=
  pinReserved_run (hP.full h0)

/-- **`liftFueled` at a returned comparison is that comparison**, the state unchanged. -/
@[refines ConRon.Arena.liftFueled]
theorem liftFueled_some {α : Type} (what : String) (x : α) (a : AState) :
    (liftFueled what (some x)).run a = .ok (x, a) := rfl

end L.Arena
