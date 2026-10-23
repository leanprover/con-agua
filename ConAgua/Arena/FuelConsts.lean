import ConAgua.Arena.FVarRangeRefine
import ConAgua.Census.Attr

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

end L.Arena
