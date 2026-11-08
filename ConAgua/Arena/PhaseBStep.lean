module

public import ConAgua.Arena.FreezeRel

@[expose] public section

/-!
# One pending group from `PhaseBStart` (lane parmode, from lane parallel's `PhaseBEntry`)

The threads' entry 2 checks pending groups one at a time, in any order, each on the state the
previous one left. con-ron's phase-B invariant `TwinPend` is stated over the remaining groups in
order; over all of them it holds again after any one (`TwinPend.dup`: a group of the list may be
checked first), because each check ends in `dropScratch` and grows the persistent tier only
(`TwinPend.step`).

`PhaseBStart.step`: `check_pending(j, v)` from `PhaseBStart … m a v` refines `checkPending` on
group `j` and ends in `PhaseBStart` again, at the twin's state after it.
-/

-- ronsync2: phase B is gone upstream (#143, every record is a job); the module is kept empty so
-- that its importers resolve.
