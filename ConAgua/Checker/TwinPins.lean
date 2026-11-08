module

import ConRon.Bridge.Checker.Names
import ConRon.Bridge.Checker.DeclVal
public import ConRon.Bridge.Checker.Basis
import ConRon.Bridge.Checker.Pins
public import ConRon.Arena.Checker

@[expose] public section

/-!
# `internAllPins` leaves the pin table (lane `pipeline`)

con-ron's `internAllPins_run` walks the stage's steps (`IStepS`, which keep the pin table) but
does not export `s'.pins = s.pins`; `internAllPins_pins` is that walk for that conjunct.
-/

namespace L.Checker.TwinCaches

open ConRon.Arena ConRon.Arena.Frontend

section pins
open ConLeche ConRon.Bridge

/-- con-ron: ConRon/Bridge/Checker/Pins.lean:625-746 ConRon.Bridge.internAllPins_run — the same walk, for the conjunct
-- con-ron: CHANGED since 97eead2d — `ConRon.Bridge.internAllPins_run` is gone upstream; re-check the L code and its proofs, then delete this line
that lemma does not export: `internAllPins` leaves the pin table (it builds the pin SETS, its
result). -/
theorem internAllPins_pins {ps : List NatOpPinSet} {r : List INatOpPinSet}
    {s s' : AState} (hok : StateOK s) (hpins : PinsOK s) (hoff : s.store.scratchOn = false)
    (hrun : internAllPins ps s = .ok (r, s')) : s'.pins = s.pins := by
  sorry

end pins

end L.Checker.TwinCaches
